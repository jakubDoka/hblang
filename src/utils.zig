const std = @import("std");

pub const freestanding = @import("builtin").target.os.tag == .freestanding;

pub fn undistributeComutative(
    a: anytype,
    b: @TypeOf(a),
    c: @TypeOf(a),
    d: @TypeOf(a),
) ?struct { @TypeOf(a), @TypeOf(a), @TypeOf(a) } {
    if (a == b) return .{ a, c, d };
    if (a == c) return .{ a, b, d };
    if (a == d) return .{ a, b, c };

    if (b == c) return .{ b, a, d };
    if (b == d) return .{ b, a, c };

    if (c == d) return .{ c, a, b };

    return null;
}

pub fn undistribute(
    a: anytype,
    b: @TypeOf(a),
    c: @TypeOf(a),
    d: @TypeOf(a),
    is_rhs: bool,
) ?struct { @TypeOf(a), @TypeOf(a), @TypeOf(a) } {
    if (b == d and is_rhs) return .{ a, c, b };
    if (a == c and !is_rhs) return .{ a, b, d };
    return null;
}

pub fn dedupeSorted(comptime T: type, slice: []T) usize {
    if (slice.len == 0) return 0;

    var write_index: usize = 1;
    var last = slice[0];

    for (slice[1..]) |value| {
        if (value != last) {
            slice[write_index] = value;
            last = value;
            write_index += 1;
        }
    }
    return write_index;
}

pub fn ensureSlot(self: anytype, gpa: std.mem.Allocator, id: usize) !*std.meta.Child(@TypeOf(self.items)) {
    if (self.items.len <= id) {
        // this can happen when we fuck up
        std.debug.assert(id < std.math.maxInt(u32) - 1000);

        const prev_len = self.items.len;
        try self.resize(gpa, id + 1);
        @memset(self.items[prev_len..], .invalid);
    }
    return &self.items[id];
}

pub fn panic(comptime format: []const u8, args: anytype) noreturn {
    if (debug and !freestanding) std.debug.panic(format, args) else unreachable;
}

pub fn setColor(cfg: std.io.tty.Config, writer: *std.Io.Writer, color: std.io.tty.Color) error{WriteFailed}!void {
    if (@import("builtin").target.os.tag != .freestanding) cfg.setColor(writer, color) catch return error.WriteFailed;
}

pub const Pool = struct {
    arena: Arena,
    free: [sclass_count]?*Header = @splat(null),

    const max_alloc_size = 1024 * 1024 * 256;
    const page_size = 1024 * 4;
    const sclass_offset = std.math.log2_int(usize, page_size);
    const sclass_count = std.math.log2_int(usize, max_alloc_size) - sclass_offset;

    const Header = struct {
        next: ?*Header,
    };

    pub fn sclassOf(size: usize) usize {
        std.debug.assert(size <= max_alloc_size);
        return std.math.log2_int_ceil(usize, size) -| sclass_offset;
    }

    pub fn staleMemory(self: *Pool) usize {
        var total: usize = 0;

        var unit: usize = page_size;
        for (self.free) |header| {
            var cursor = header;
            while (cursor) |hdr| {
                total += unit;
                cursor = hdr.next;
            }
            unit *= 2;
        }

        return total;
    }

    pub fn allocator(self: *Pool) std.mem.Allocator {
        const alc_impl = enum {
            fn alloc(ptr: *anyopaque, size: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
                const slf: *Pool = @ptrCast(@alignCast(ptr));
                const alignm = @max(alignment.toByteUnits(), @alignOf(Header));
                std.debug.assert(alignm <= page_size);
                const size_class = sclassOf(size);

                if (slf.free[size_class]) |fr| {
                    slf.free[size_class] = fr.next;
                    return @ptrCast(fr);
                }

                return slf.arena.allocator().rawAlloc(
                    @as(usize, 1) << @intCast(size_class + sclass_offset),
                    std.mem.Alignment.fromByteUnits(alignm),
                    ret_addr,
                );
            }
            fn free(ptr: *anyopaque, mem: []u8, _: std.mem.Alignment, _: usize) void {
                @memset(mem, undefined);
                const slf: *Pool = @ptrCast(@alignCast(ptr));
                const size_class = sclassOf(mem.len);
                const header: *Header = @ptrCast(@alignCast(mem.ptr));
                header.next = slf.free[size_class];
                slf.free[size_class] = header;
            }
            fn remap(_: *anyopaque, mem: []u8, _: std.mem.Alignment, new_len: usize, _: usize) ?[*]u8 {
                return if (sclassOf(mem.len) == sclassOf(new_len)) return mem.ptr else null;
            }
            fn resize(_: *anyopaque, mem: []u8, _: std.mem.Alignment, new_len: usize, _: usize) bool {
                return sclassOf(mem.len) == sclassOf(new_len);
            }
        };

        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alc_impl.alloc,
                .free = alc_impl.free,
                .remap = alc_impl.remap,
                .resize = alc_impl.resize,
            },
        };
    }
};

pub const lane = opaque {
    pub const Barrier = struct {
        mutex: std.Thread.Mutex = .{},
        cond: std.Thread.Condition = .{},
        waiting: usize = 0,

        pub fn sync(self: *Barrier, up_to: usize) void {
            self.mutex.lock();
            defer self.mutex.unlock();

            self.waiting += 1;

            if (self.waiting == up_to) {
                self.waiting = 0;
                self.cond.broadcast();
            } else {
                self.cond.wait(&self.mutex);
            }
        }
    };

    pub const SpinBarrier = struct {
        waiting: std.atomic.Value(usize) = .init(0),
        generation: std.atomic.Value(usize) = .init(0),

        pub fn sync(self: *SpinBarrier, up_to: usize) void {
            const generation = self.generation.load(.acquire);
            const current_waiting = self.waiting.fetchAdd(1, .acquire) + 1;

            if (current_waiting == up_to) {
                self.waiting.store(0, .release);
                self.generation.store(generation + 1, .release);
            } else {
                while (self.generation.load(.acquire) == generation) {}
            }
        }
    };

    pub const ThreadCtx = struct {
        lane_idx: usize,
        lane_count: usize,
        shared: *SharedCtx,
    };

    pub const SharedCtx = struct {
        // eliminate needless contention
        _: void align(std.atomic.cache_line) = {},

        broadcast_buffer: u64 = undefined,
        barrier: Barrier = .{},
        spin_barrier: SpinBarrier = .{},
    };

    pub const single_threaded = @import("builtin").single_threaded;

    pub var shared_ = SharedCtx{};
    pub threadlocal var ctx: ThreadCtx = if (single_threaded) .{
        .lane_idx = 0,
        .lane_count = 1,
        .shared = &shared_,
    } else undefined;

    pub fn initSingleThreaded() void {
        ctx = .{
            .lane_idx = 0,
            .lane_count = 1,
            .shared = &shared_,
        };
    }

    pub inline fn isSingleThreaded() bool {
        return single_threaded or ctx.lane_count == 1;
    }

    /// Current thread will become the thread 0
    pub fn boot(lane_count: usize, cx: anytype, comptime entry: fn (@TypeOf(cx)) void) void {
        if (isSingleThreaded()) {
            entry(cx);
            return;
        }

        var arg_buf: [4096]u8 = undefined;
        var arg_alloc = std.heap.FixedBufferAllocator.init(&arg_buf);

        var shared = SharedCtx{};

        const threads = arg_alloc.allocator().alloc(std.Thread, lane_count) catch unreachable;

        const task = struct {
            pub fn init(idx: usize, cnt: usize, shred: *SharedCtx, c: @TypeOf(cx)) void {
                ctx = .{ .lane_idx = idx, .lane_count = cnt, .shared = shred };
                entry(c);
            }
        };

        for (1..lane_count) |i| {
            threads[i] = std.Thread.spawn(
                .{ .allocator = arg_alloc.allocator() },
                task.init,
                .{ i, lane_count, &shared, cx },
            ) catch unreachable;
        }

        task.init(0, lane_count, &shared, cx);

        for (threads[1..]) |thread| {
            thread.join();
        }
    }

    pub fn range(values_count: usize) struct { start: usize, end: usize } {
        if (isSingleThreaded()) return .{ .start = 0, .end = values_count };

        const thread_idx = ctx.lane_idx;
        const thread_count = ctx.lane_count;

        const values_per_thread = values_count / thread_count;
        const leftover_values_count = values_count % thread_count;

        const thread_has_leftover = (thread_idx < leftover_values_count);
        const leftovers_before_this_thread_idx =
            if (thread_has_leftover) thread_idx else leftover_values_count;
        const thread_first_value_idx = (values_per_thread * thread_idx +
            leftovers_before_this_thread_idx);
        const thread_opl_value_idx = (thread_first_value_idx + values_per_thread +
            if (thread_has_leftover) @as(usize, 1) else 0);

        return .{ .start = thread_first_value_idx, .end = thread_opl_value_idx };
    }

    const SyncCtx = struct {
        spin: bool = false,

        pub const spinning = @This(){ .spin = true };
    };

    pub fn sync(args: SyncCtx) void {
        if (isSingleThreaded()) return;

        if (false and args.spin) {
            ctx.shared.spin_barrier.sync(ctx.lane_count);
        } else {
            ctx.shared.barrier.sync(ctx.lane_count);
        }
    }

    pub inline fn isRoot() bool {
        if (isSingleThreaded()) return true;

        return ctx.lane_idx == 0;
    }

    pub inline fn count() usize {
        return ctx.lane_count;
    }

    pub inline fn index() u16 {
        return @intCast(ctx.lane_idx);
    }

    pub fn productBroadcast(scratch: *Arena, to_extract: anytype) []@TypeOf(to_extract) {
        if (isSingleThreaded()) {
            const slot = scratch.create(@TypeOf(to_extract));
            slot.* = to_extract;
            return slot[0..1];
        }

        // TODO: this has one extra sync that is not needed
        //
        var buffer: []@TypeOf(to_extract) = undefined;
        if (lane.isRoot()) {
            buffer = scratch.alloc(@TypeOf(to_extract), count());
        }
        broadcast(&buffer, .{});

        buffer[ctx.lane_idx] = to_extract;

        sync(.spinning);

        return buffer;
    }

    pub fn broadcast(to_sync: anytype, args: struct {
        spin: bool = false,
        from: usize = 0,

        const spinning = @This(){ .spin = true };
    }) void {
        if (isSingleThreaded()) return;

        if (@sizeOf(@TypeOf(to_sync.*)) != 8) {
            const to_sync_generic: u64 = @intFromPtr(to_sync);

            if (ctx.lane_idx == args.from) {
                ctx.shared.broadcast_buffer = to_sync_generic;
            }

            sync(.{ .spin = args.spin });

            if (ctx.lane_idx != args.from) {
                to_sync.* = @as(@TypeOf(to_sync), @ptrFromInt(ctx.shared.broadcast_buffer)).*;
            }
        } else {
            const to_sync_generic: *u64 = @ptrCast(to_sync);

            if (ctx.lane_idx == args.from) {
                ctx.shared.broadcast_buffer = to_sync_generic.*;
            }

            sync(.{ .spin = args.spin });

            if (ctx.lane_idx != args.from) {
                to_sync_generic.* = ctx.shared.broadcast_buffer;
            }
        }

        sync(.spinning);
    }

    pub const FixedQueue = struct {
        cursor: std.atomic.Value(usize) = .init(0),

        pub fn next(self: *FixedQueue, max: usize) ?usize {
            const cursor = self.cursor.fetchAdd(1, .acquire);
            return if (cursor < max) cursor else null;
        }
    };

    pub fn WorkStealingQueue(comptime Elem: type) type {
        return struct {
            queues: if (!single_threaded) []SubQueue else void,

            wait_mutex: std.Thread.Mutex = .{},
            wait_cond: std.Thread.Condition = .{},
            wait_count: if (!single_threaded) usize else void = if (!single_threaded) 0,

            const SubQueue = struct {
                _: void align(std.atomic.cache_line) = {},

                // TODO: maybe we can go wild and make this wait free
                tasks: std.ArrayList(Elem) = .empty,
                lock: std.Thread.Mutex = .{},
            };

            const Self = @This();

            pub fn init(scratch: *Arena, lane_cap: usize) Self {
                errdefer unreachable;

                if (isSingleThreaded()) return undefined;

                const queues = scratch.alloc(SubQueue, ctx.lane_count);
                for (queues) |*queue| queue.* = .{ .tasks = try .initCapacity(scratch.allocator(), lane_cap) };
                return .{ .queues = queues };
            }

            pub fn push(self: *Self, task: []Elem) usize {
                if (isSingleThreaded()) return task.len;

                var pushed: usize = 0;
                defer for (0..pushed) |_| self.wait_cond.signal();

                const queue = &self.queues[lane.ctx.lane_idx];
                queue.lock.lock();
                defer queue.lock.unlock();

                const max_push = @min(task.len, queue.tasks.capacity - queue.tasks.items.len);

                queue.tasks.appendSliceAssumeCapacity(task[task.len - max_push ..]);

                pushed = max_push;

                return task.len - max_push;
            }

            pub fn pop(self: *Self) ?Elem {
                if (isSingleThreaded()) return null;

                const queue = &self.queues[lane.ctx.lane_idx];
                {
                    queue.lock.lock();
                    defer queue.lock.unlock();

                    if (queue.tasks.pop()) |task| {
                        @branchHint(.likely);
                        return task;
                    }
                }

                // TODO: we should make a better access pattern, if that actually matters
                while (true) {
                    // steal
                    for (self.queues) |*other| {
                        if (other == queue) continue;

                        if (other.lock.tryLock()) {
                            defer other.lock.unlock();

                            if (other.tasks.pop()) |task| {
                                return task;
                            }
                        }
                    }

                    // steal harder
                    for (self.queues) |*other| {
                        if (other == queue) continue;

                        other.lock.lock();
                        defer other.lock.unlock();

                        if (other.tasks.pop()) |task| {
                            return task;
                        }
                    }

                    // wait for more work, possibly terminate
                    self.wait_mutex.lock();
                    defer self.wait_mutex.unlock();

                    self.wait_count += 1;

                    if (self.wait_count == self.queues.len) {
                        self.wait_cond.broadcast();
                        return null;
                    } else {
                        self.wait_cond.wait(&self.wait_mutex);

                        if (self.wait_count == self.queues.len) {
                            return null;
                        }

                        self.wait_count -= 1;
                    }
                }
            }
        };
    }

    pub const Queue = WorkStealingQueue(u8);

    pub fn share(scratch: *Arena, value: anytype) *@TypeOf(value) {
        var vl: *@TypeOf(value) = undefined;

        if (lane.isRoot()) {
            vl = scratch.create(@TypeOf(value));
            vl.* = value;
        }
        lane.broadcast(&vl, .{});

        return vl;
    }

    pub const max_groups = 64;

    pub const Group = struct {
        prev: ThreadCtx = undefined,
        group_idx: usize = 0,
        alive_groups: std.bit_set.IntegerBitSet(max_groups) = .initEmpty(),

        /// Restores previous grouping of the thread, should be called on all
        /// members of the group unconditionally.
        pub fn deinit(self: Group, args: SyncCtx) void {
            if (isSingleThreaded()) return;
            ctx = self.prev;

            sync(args);
        }

        /// This account for dead groups that happne if thread count is
        /// insufficient to encompass all groups .eg if only 1 thread is available,
        /// all groups get folded to it.
        ///
        /// Compared to lane.isRoot this is true for all members of the group.
        pub fn is(self: Group, id: usize) bool {
            if (isSingleThreaded()) return true;
            if (self.group_idx == id) return true;
            return !self.alive_groups.isSet(id) and id > self.group_idx;
        }
    };

    /// Split the current thread group into multiple goups where the ratio is
    /// specified by the `groups` slice, the current group is partitioned in a best
    /// effort manner, some groups may be too small and dont get assigned any
    /// threads, you should use `Group.isRoot` to determine if you are in the group
    /// which acouts for empty groups
    ///
    /// ther must be at least 2 groups and at most 64 groups (hopefully enough for everyone)
    pub fn splitHeter(groups: []const usize, scratch: *Arena, args: SyncCtx) Group {
        return splitWithStrategy(groups, projectHeter, scratch, args);
    }

    pub fn splitWithStrategy(
        cx: anytype,
        strategy: fn (@TypeOf(cx), usize, usize) Projection,
        scratch: *Arena,
        args: SyncCtx,
    ) Group {
        var group = Group{};

        if (isSingleThreaded()) {
            group.alive_groups.set(0);
            return group;
        }

        group.prev = ctx;

        const projection = strategy(cx, ctx.lane_idx, ctx.lane_count);

        std.debug.assert(projection.group_count > 1);
        std.debug.assert(projection.group_count <= max_groups);

        group.group_idx = projection.group;

        var new_ctxes: []?*SharedCtx = undefined;
        if (isRoot()) {
            // we dont need this memory beyond this scope but deallocating it
            // here would require extra sync which is not worth it
            new_ctxes = scratch.alloc(?*SharedCtx, projection.group_count);
            @memset(new_ctxes, null);
        }

        broadcast(&new_ctxes, .{ .spin = args.spin });

        if (projection.idx == 0) {
            const new_shared = scratch.create(SharedCtx);
            new_shared.* = .{};
            new_ctxes[projection.group] = new_shared;
        }

        sync(.spinning);

        for (new_ctxes, 0..) |slt, i| {
            if (slt != null) group.alive_groups.set(i);
        }

        ctx.shared = new_ctxes[projection.group].?;
        ctx.lane_idx = projection.idx;
        ctx.lane_count = projection.count;

        return group;
    }

    const Projection = struct { idx: usize, count: usize, group: usize, group_count: usize };

    pub fn projectHeter(
        groups: []const usize,
        cur: usize,
        cur_total: usize,
    ) Projection {
        var total: usize = 0;
        for (groups) |g| total += g;

        var last_group_transition: usize = 0;
        var last_group: usize = 0;
        var group_accum: usize = groups[last_group] * cur_total;

        for (0..cur + 1) |i| {
            if (i * total >= group_accum) {
                last_group_transition = i;
                last_group += 1;
                group_accum += groups[last_group] * cur_total;
            }
        }

        const group_start = last_group_transition;
        const final_goup = last_group;

        for (cur + 1..cur_total) |i| {
            if (i * total >= group_accum) {
                last_group_transition = i;
                last_group += 1;
                group_accum += groups[last_group] * cur_total;
                break;
            }
        } else {
            last_group_transition = cur_total;
        }

        return Projection{
            .idx = cur - group_start,
            .count = last_group_transition - group_start,
            .group = final_goup,
            .group_count = groups.len,
        };
    }
};

pub const foo = RollingQueue(u8);

pub fn _RollingQueue(comptime T: type) type {
    return struct {
        const Self = @This();

        const Slot = struct {
            seq: std.atomic.Value(usize) = .init(0),
            value: T = undefined,
        };

        buffer: []Slot,
        mask: usize,
        head: std.atomic.Value(usize) = .init(0),
        tail: std.atomic.Value(usize) = .init(0),

        pub fn init(scratch: *Arena, capacity: usize) Self {
            std.debug.assert(std.math.isPowerOfTwo(capacity));

            const buf = scratch.alloc(Slot, capacity);

            for (buf, 0..) |*slot, i| {
                slot.seq.store(i, .unordered);
            }

            return .{
                .buffer = buf,
                .mask = capacity - 1,
            };
        }

        pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            allocator.free(self.buffer);
            allocator.destroy(self);
        }

        /// Pushes a value into the queue.
        /// Returns false if the queue is full.
        pub fn push(self: *Self, value: T) bool {
            var tail = self.tail.load(.unordered);

            while (true) {
                const slot = &self.buffer[tail & self.mask];
                const seq = slot.seq.load(.acquire);
                const diff = @as(isize, @intCast(seq)) - @as(isize, @intCast(tail));

                if (diff == 0) {
                    // slot ready to be written
                    if (self.tail.cmpxchgStrong(tail, tail + 1, .monotonic, .monotonic)) |old| {
                        tail = old;
                        continue; // lost race
                    }

                    // write value and publish
                    slot.value = value;
                    slot.seq.store(tail + 1, .release);
                    return true;
                } else if (diff < 0) {
                    // queue full
                    return false;
                } else {
                    // another thread progressed; reload tail
                    tail = self.tail.load(.unordered);
                }
            }
        }

        /// Pops a value from the queue.
        /// Returns null if the queue is empty.
        pub fn pop(self: *Self) ?T {
            var head = self.head.load(.unordered);

            while (true) {
                const slot = &self.buffer[head & self.mask];
                const seq = slot.seq.load(.acquire);
                const diff = @as(isize, @intCast(seq)) - @as(isize, @intCast(head + 1));

                if (diff == 0) {
                    // slot ready to be read
                    if (self.head.cmpxchgStrong(head, head + 1, .monotonic, .monotonic)) |old| {
                        head = old;
                        continue; // lost race
                    }

                    const val = slot.value;
                    // mark slot as free for reuse
                    slot.seq.store(head + self.mask + 1, .release);
                    return val;
                } else if (diff < 0) {
                    // queue empty
                    return null;
                } else {
                    head = self.head.load(.unordered);
                }
            }
        }
    };
}

pub const Lobby = struct {
    lock: std.Thread.Mutex = .{},
    cond: std.Thread.Condition = .{},

    pub fn wait(self: *Lobby) void {
        self.lock.lock();
        defer self.lock.unlock();

        self.cond.wait(&self.lock);
    }

    pub fn signal(self: *Lobby) void {
        self.lock.lock();
        defer self.lock.unlock();

        self.cond.signal();
    }

    pub fn done(self: *Lobby) void {
        self.lock.lock();
        defer self.lock.unlock();

        self.cond.broadcast();
    }
};

pub fn RollingQueue(comptime Elem: type) type {
    return struct {
        finished: std.atomic.Value(usize) = .init(0),
        reading: std.atomic.Value(usize) = .init(0),
        red: std.atomic.Value(usize) = .init(0),
        writing: std.atomic.Value(usize) = .init(0),
        written: std.atomic.Value(usize) = .init(0),

        read_futex: std.atomic.Value(u32) = .init(0),

        buffer: []Elem,

        const futex = std.Thread.Futex;

        const Self = @This();

        pub fn init(scratch: *Arena, cap: usize) Self {
            return .initBuffer(scratch.alloc(Elem, cap));
        }

        pub fn initBuffer(buffer: []Elem) Self {
            std.debug.assert(std.math.isPowerOfTwo(buffer.len));
            return .{ .buffer = buffer };
        }

        pub fn pop(self: *Self) ?Elem {
            while (true) switch (self.tryPop()) {
                .ready => |elem| return elem,
                .exhaused => return null,
                .retry => {
                    futex.wait(&self.read_futex, 0);
                },
            };
        }

        pub fn complete(self: *Self) bool {
            const final = self.finished.fetchAdd(1, .release) + 1;
            return final == self.written.load(.unordered);
        }

        pub fn tryPop(self: *Self) union(enum) { ready: Elem, exhaused, retry } {
            if (self.finished.load(.unordered) == self.written.load(.unordered)) {
                if (true) unreachable;
                return .exhaused;
            }

            const to_read = while (true) {
                const reading = self.reading.load(.unordered);
                const written = self.written.load(.unordered);

                if (reading == written) {
                    return .retry;
                }

                std.debug.assert(reading < written);

                if (self.reading.cmpxchgWeak(reading, reading + 1, .monotonic, .monotonic) != null) {
                    continue;
                }

                break reading;
            };

            std.debug.assert(std.math.isPowerOfTwo(self.buffer.len));
            const red = self.buffer[to_read % self.buffer.len];
            self.buffer[to_read % self.buffer.len] = undefined;

            while (self.red.cmpxchgWeak(to_read, to_read + 1, .monotonic, .monotonic) != null) {}

            return .{ .ready = red };
        }

        pub fn push(self: *Self, elem: Elem) void {
            std.debug.assert(self.tryPush(elem));
        }

        pub fn tryPush(self: *Self, elem: Elem) bool {
            const to_write = while (true) {
                const red = self.red.load(.unordered);
                const writing = self.writing.load(.unordered);

                if (writing == self.buffer.len + red) {
                    return false;
                }

                if (self.writing.cmpxchgWeak(writing, writing + 1, .monotonic, .monotonic) != null) {
                    continue;
                }

                break writing;
            };

            std.debug.assert(std.math.isPowerOfTwo(self.buffer.len));
            self.buffer[to_write % self.buffer.len] = elem;

            while (self.written.cmpxchgWeak(to_write, to_write + 1, .monotonic, .monotonic) != null) {}

            futex.wake(&self.read_futex, std.math.maxInt(u32));

            return true;
        }
    };
}

test "lane.RollingQueue.sanity" {
    if (true) return;

    var buff: [16]u8 = undefined;
    var buffer = RollingQueue(u8).initBuffer(&buff);

    buffer.push(1);
    try std.testing.expectEqual(1, buffer.pop());

    for (0..10) |_| {
        for (0..13) |i| {
            buffer.push(@intCast(i));
        }

        for (0..13) |i| {
            try std.testing.expectEqual(@as(u8, @intCast(i)), buffer.pop().?);
        }
    }

    const threads = 16;

    lane.boot(threads, {}, struct {
        pub fn entry(_: void) void {
            Arena.initScratch(1024 * 1024 * 16);
            defer Arena.deinitScratch();

            var tmp = Arena.scrath(null);
            defer tmp.deinit();

            var queue_slot: RollingQueue(u8) = undefined;
            if (lane.isRoot()) {
                queue_slot = .init(tmp.arena, threads);
            }

            var queue = &queue_slot;
            lane.broadcast(&queue, .{});

            queue.push(@intCast(lane.ctx.lane_idx));

            for (0..10000) |_| {
                const byte = queue.pop() orelse {
                    std.debug.print("{}\n", .{queue});

                    unreachable;
                };
                while (!queue.tryPush(byte)) {}
            }

            lane.sync(.{});

            if (lane.isRoot()) {
                var slots: [threads]bool = undefined;
                for (0..threads) |i| {
                    slots[queue_slot.buffer[i]] = true;
                }

                for (0..threads) |i| {
                    std.debug.assert(slots[i]);
                }
            }
        }
    }.entry);
}

test "lane.project" {
    const TestCase = struct {
        groups: []const usize,
        expected: []const usize,
    };

    const test_cases = [_]TestCase{ .{
        .groups = &.{ 1, 1 },
        .expected = &.{0},
    }, .{
        .groups = &.{ 1, 1 },
        .expected = &.{ 0, 1 },
    }, .{
        .groups = &.{ 2, 1 },
        .expected = &.{ 0, 0 },
    }, .{
        .groups = &.{ 3, 1 },
        .expected = &.{ 0, 0 },
    }, .{
        .groups = &.{ 4, 4 },
        .expected = &.{ 0, 1 },
    }, .{
        .groups = &.{ 4, 2 },
        .expected = &.{ 0, 0, 1 },
    }, .{
        .groups = &.{ 4, 3 },
        .expected = &.{ 0, 0, 1 },
    }, .{
        .groups = &.{ 3, 2 },
        .expected = &.{ 0, 0, 0, 0, 1, 1 },
    }, .{
        .groups = &.{ 3, 3, 3 },
        .expected = &.{ 0, 0, 1, 1, 2, 2 },
    } };

    for (test_cases, 0..) |tc, i| {
        var last_group: usize = tc.expected[0];
        var last_boundary: usize = 0;
        for (tc.expected, 0..) |vl, t| {
            errdefer std.debug.print("testcase {}:{} failed: {}\n", .{ i, t, tc });
            const proj = lane.projectHeter(tc.groups, t, tc.expected.len);

            if (proj.group != last_group) {
                last_boundary = t;
                last_group = proj.group;
            }

            try std.testing.expectEqual(vl, proj.group);
            try std.testing.expectEqual(t - last_boundary, proj.idx);

            var group_count: usize = 0;
            for (tc.expected) |g| {
                if (g == proj.group) group_count += 1;
            }
            try std.testing.expect(group_count == proj.count);
        }
    }
}

test "lane.sanity" {
    lane.boot(16, {}, struct {
        pub fn entry(_: void) void {
            Arena.initScratch(1024 * 1024 * 16);
            defer Arena.deinitScratch();

            var tmp = Arena.scrath(null);
            defer tmp.deinit();

            var dataset: []usize = undefined;
            if (lane.isRoot()) {
                dataset = tmp.arena.alloc(usize, 1024 * 1024);
            }
            lane.broadcast(&dataset, .spinning);

            const range = lane.range(dataset.len);

            for (dataset[range.start..range.end], range.start..) |*item, i| {
                item.* = i;
            }

            var root_sum: std.atomic.Value(usize) = .init(0);
            var root_sum_ref = &root_sum;
            lane.broadcast(&root_sum_ref, .{});

            var local_count: usize = 0;
            for (dataset[range.start..range.end]) |item| {
                local_count += item;
            }

            _ = root_sum_ref.fetchAdd(local_count, .acq_rel);

            lane.sync(.{});

            if (lane.isRoot()) {
                var sum: usize = 0;
                for (0..dataset.len) |item| {
                    sum += item;
                }
                std.testing.expectEqual(sum, root_sum.load(.unordered)) catch unreachable;
            }
        }
    }.entry);
}

test "lane.sanity.split" {
    lane.boot(16, {}, struct {
        pub fn entry(_: void) void {
            Arena.initScratch(1024 * 1024 * 16);
            defer Arena.deinitScratch();

            var tmp = Arena.scrath(null);
            defer tmp.deinit();

            {
                const group = lane.splitHeter(&.{ 2, 1, 1 }, tmp.arena, .{});
                defer group.deinit(.{});

                for (0..3) |i| {
                    if (group.is(i)) {
                        var counter: std.atomic.Value(usize) = .init(0);
                        var counter_ref = &counter;

                        lane.broadcast(&counter_ref, .{});

                        _ = counter_ref.fetchAdd(1, .acq_rel);

                        lane.sync(.spinning);

                        if (lane.isRoot()) {
                            std.testing.expectEqual(lane.count(), counter.load(.unordered)) catch unreachable;
                        }
                    }
                }
            }
        }
    }.entry);
}

pub const Arena = struct {
    start: [*]align(page_size) u8,
    end: [*]align(page_size) u8,
    pos: [*]u8,

    const page_size = std.heap.pageSize();

    threadlocal var inited: bool = false;
    pub threadlocal var scratch: [2]Arena = undefined;

    pub const Scratch = struct {
        prev_pos: [*]u8,
        arena: *Arena,

        pub fn deinit(self: *Scratch) void {
            @memset(self.prev_pos[0 .. @intFromPtr(self.arena.pos) - @intFromPtr(self.prev_pos)], undefined);
            self.arena.pos = self.prev_pos;
            self.* = undefined;
        }
    };

    pub fn initScratch(cap: usize) void {
        if (std.debug.runtime_safety) {
            std.debug.assert(!inited);
            inited = true;
        }
        for (&scratch) |*slt| slt.* = init(cap);
    }

    pub fn deinitScratch() void {
        if (std.debug.runtime_safety) {
            std.debug.assert(inited);
            inited = false;
        }
        for (&scratch) |*slt| slt.deinit();
    }

    pub fn resetScratch() void {
        for (&scratch) |*slt| slt.reset();
    }

    pub fn consumed(arena: *Arena) u64 {
        return @intCast(arena.pos - arena.start);
    }

    pub fn reset(arena: *Arena) void {
        arena.pos = arena.start;
    }

    pub fn allocated(self: *Arena) usize {
        return @intFromPtr(self.end) - @intFromPtr(self.pos);
    }

    pub fn getCapacity(self: *Arena) usize {
        return @intFromPtr(self.end) - @intFromPtr(self.start);
    }

    pub fn subslice(self: *Arena, capacity: usize) Arena {
        const cap = std.mem.alignBackward(usize, capacity, page_size);
        const ptr = self.allocRaw(page_size, cap);
        return .{
            .start = @alignCast(ptr),
            .end = @alignCast(ptr + cap),
            .pos = ptr,
        };
    }

    pub fn scrath(except: ?*anyopaque) Scratch {
        for (&scratch) |*slt| if (@as(*anyopaque, slt) != except)
            return slt.checkpoint();
        unreachable;
    }

    pub fn init(cap: usize) Arena {
        const pages = std.mem.alignForward(usize, cap, page_size);
        const ptr = std.heap.page_allocator.rawAlloc(pages, .fromByteUnits(page_size), @returnAddress()).?;
        return .{
            .end = @alignCast(ptr + pages),
            .start = @alignCast(ptr),
            .pos = @alignCast(ptr),
        };
    }

    pub fn allocator(self: *Arena) std.mem.Allocator {
        const alc_impl = enum {
            fn alloc(ptr: *anyopaque, size: usize, alignment: std.mem.Alignment, _: usize) ?[*]u8 {
                const slf: *Arena = @ptrCast(@alignCast(ptr));
                return slf.allocRaw(alignment.toByteUnits(), size);
            }
            fn free(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize) void {}
            fn remap(ptr: *anyopaque, mem: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
                if (@This().resize(ptr, mem, alignment, new_len, ret_addr)) return mem.ptr;
                return null;
            }
            fn resize(ptr: *anyopaque, mem: []u8, _: std.mem.Alignment, new_len: usize, _: usize) bool {
                const slf: *Arena = @ptrCast(@alignCast(ptr));
                if (mem.ptr + mem.len == slf.pos) {
                    slf.pos += new_len;
                    slf.pos -= mem.len;
                    return true;
                }
                return false;
            }
        };

        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alc_impl.alloc,
                .free = alc_impl.free,
                .remap = alc_impl.remap,
                .resize = alc_impl.resize,
            },
        };
    }

    pub fn deinit(self: *Arena) void {
        std.heap.page_allocator.rawFree(self.start[0 .. self.end - self.start], .fromByteUnits(page_size), @returnAddress());
        self.* = undefined;
    }

    pub fn checkpoint(self: *Arena) Scratch {
        return .{ .prev_pos = self.pos, .arena = self };
    }

    pub fn dupe(self: *Arena, comptime Elem: type, values: []const Elem) []Elem {
        const new = self.alloc(Elem, values.len);
        @memcpy(new, values);
        return new;
    }

    pub fn allocAligned(self: *Arena, comptime T: type, count: usize, comptime alignment: usize) []align(alignment) T {
        const ptr: [*]align(alignment) T = @ptrCast(@alignCast(self.allocRaw(alignment, @sizeOf(T) * count)));
        const mem = ptr[0..count];
        @memset(mem, undefined);
        return mem;
    }

    pub fn alloc(self: *Arena, comptime T: type, count: usize) []T {
        return self.allocAligned(T, count, @alignOf(T));
    }

    pub fn allocZ(self: *Arena, comptime T: type, count: usize) [:0]T {
        const ptr: [*]T = @ptrCast(@alignCast(self.allocRaw(@alignOf(T), @sizeOf(T) * (count + 1))));
        ptr[count] = 0;
        return ptr[0..count :0];
    }

    pub fn allocRaw(self: *Arena, alignment: usize, size: usize) [*]u8 {
        self.pos = @ptrFromInt(std.mem.alignForward(usize, @intFromPtr(self.pos), alignment));
        self.pos += size;
        if (@intFromPtr(self.end) < @intFromPtr(self.pos)) {
            @panic("out of memory");
        }
        return self.pos - size;
    }

    pub fn makeArrayList(self: *Arena, comptime T: type, cap: usize) std.ArrayList(T) {
        return .initBuffer(self.alloc(T, cap));
    }

    pub fn create(self: *Arena, comptime T: type) *T {
        return &self.alloc(T, 1).ptr[0];
    }
};

const IdRepr = u32;

pub fn EnumId(comptime T: type) type {
    return enum(IdRepr) {
        _,

        const Tag = std.meta.Tag(T);

        const Repr = packed struct(IdRepr) {
            taga: std.meta.Tag(Tag),
            index: std.meta.Int(.unsigned, @bitSizeOf(IdRepr) - @bitSizeOf(Tag)),
        };

        pub fn compact(taga: Tag, indexa: usize) @This() {
            return @enumFromInt(@as(IdRepr, @bitCast(Repr{ .taga = @intFromEnum(taga), .index = @intCast(indexa) })));
        }

        pub fn zeroSized(taga: Tag) @This() {
            return compact(taga, 0);
        }

        pub fn tag(self: @This()) Tag {
            const repr: Repr = @bitCast(@intFromEnum(self));
            return @enumFromInt(repr.taga);
        }

        pub fn index(self: @This()) u32 {
            const repr: Repr = @bitCast(@intFromEnum(self));
            return repr.index;
        }
    };
}

pub fn EnumSlice(comptime T: type) type {
    return struct {
        start: u32 = 0,
        end: u32 = 0,

        const Elem = T;

        pub fn isEmpty(self: @This()) bool {
            return self.start == self.end;
        }

        pub fn len(self: @This()) usize {
            return (self.end - self.start) / @sizeOf(Elem);
        }

        pub fn slice(self: @This(), start: usize, end: usize) @This() {
            std.debug.assert(start <= end);
            std.debug.assert(end * @sizeOf(Elem) <= self.end);
            return .{ .start = @intCast(self.start + start * @sizeOf(Elem)), .end = @intCast(self.start + end * @sizeOf(Elem)) };
        }
    };
}

pub fn EnumStore(comptime T: type) type {
    return struct {
        store: std.ArrayListAlignedUnmanaged(u8, .fromByteUnits(payload_align)) = .{},

        const Self = @This();
        const payload_align = b: {
            var max_align: u29 = 1;
            for (std.meta.fields(T)) |field| {
                max_align = @max(max_align, @alignOf(field.type));
            }
            break :b max_align;
        };
        const fields = @typeInfo(T).@"union".fields;

        pub const Id = EnumId(T);

        pub fn dupe(self: *const Self, gpa: std.mem.Allocator) !Self {
            return .{ .store = try self.store.clone(gpa) };
        }

        pub fn allocDyn(self: *Self, gpa: std.mem.Allocator, value: T) !Id {
            return switch (value) {
                inline else => |v, t| try self.alloc(gpa, t, v),
            };
        }

        pub fn TagPayload(comptime kind: std.meta.Tag(T)) type {
            return fields[@intFromEnum(kind)].type;
        }

        pub fn alloc(
            self: *Self,
            gpa: std.mem.Allocator,
            comptime tag: std.meta.Tag(T),
            value: TagPayload(tag),
        ) !Id {
            const Value = @TypeOf(value);
            (try self.allocLow(gpa, Value, 1))[0] = value;
            return .compact(tag, self.store.items.len - @sizeOf(Value));
        }

        pub fn allocSlice(
            self: *Self,
            comptime E: type,
            gpa: std.mem.Allocator,
            slice: []const E,
        ) !EnumSlice(E) {
            std.mem.copyForwards(E, try self.allocLow(gpa, E, slice.len), slice);
            return .{
                .start = @intCast(self.store.items.len - @sizeOf(E) * slice.len),
                .end = @intCast(self.store.items.len),
            };
        }

        fn allocLow(self: *Self, gpa: std.mem.Allocator, comptime E: type, count: usize) ![]E {
            if (count == 0) return &.{};
            std.debug.assert(@alignOf(E) <= payload_align);
            const alignment: usize = @alignOf(E);
            const padded_len = std.mem.alignForward(usize, self.store.items.len, alignment);
            const required_space = padded_len + @sizeOf(E) * count;
            try self.store.resize(gpa, required_space);
            const dest: [*]E = @ptrCast(@alignCast(self.store.items.ptr + padded_len));
            return dest[0..count];
        }

        pub fn get(self: *const Self, id: Id) AsRef(T) {
            const Layout = extern struct { ptr: *align(payload_align) const anyopaque, tag: usize };
            return @as(*const AsRef(T), @ptrCast(&Layout{ .tag = @intFromEnum(id.tag()), .ptr = @ptrCast(@alignCast(&self.store.items[id.index()])) })).*;
        }

        pub inline fn getTyped(
            self: *const Self,
            comptime tag: std.meta.Tag(T),
            id: Id,
        ) ?*TagPayload(tag) {
            if (tag != id.tag()) return null;
            return @ptrCast(@alignCast(&self.store.items[id.index()]));
        }

        pub fn getTypedPtr(
            self: *Self,
            comptime tag: std.meta.Tag(T),
            id: Id,
        ) ?*TagPayload(tag) {
            if (tag != id.tag()) return null;
            const Value = TagPayload(tag);
            const loc: *Value = @ptrCast(@alignCast(&self.store.items[id.index()]));
            return loc;
        }

        pub fn view(self: *const Self, slice: anytype) []@TypeOf(slice).Elem {
            const slc = self.store.items[slice.start..slice.end];
            if (slc.len == 0) return &.{};
            const len = slc.len / @sizeOf(@TypeOf(slice).Elem);
            const ptr: [*]@TypeOf(slice).Elem = @ptrCast(@alignCast(slc.ptr));
            return ptr[0..len];
        }

        pub fn deinit(self: *Self, gpa: std.mem.Allocator) void {
            self.store.deinit(gpa);
            self.* = undefined;
        }
    };
}

pub fn AsRef(comptime E: type) type {
    const info = @typeInfo(E).@"union";

    var field_arr = info.fields[0..].*;

    for (&field_arr) |*f| {
        if (f.type != void) {
            f.type = *f.type;
            f.alignment = @alignOf(*f.type);
        }
    }

    return @Type(.{ .@"union" = .{
        .layout = .auto,
        .tag_type = std.meta.Tag(E),
        .fields = &field_arr,
        .decls = &.{},
    } });
}

pub fn dbg(value: anytype) @TypeOf(value) {
    if (@TypeOf(value) == []const u8) {
        std.debug.print("{s}\n", .{value});
    } else {
        std.debug.print("{any}\n", .{value});
    }
    return value;
}

const debug = @import("builtin").mode == .Debug;

pub fn isErr(value: anytype) bool {
    value catch return true;
    return false;
}

pub fn findReadmeSnippet(comptime name: []const u8) ![]const u8 {
    var readme: []const u8 = @embedFile("README.md");
    const headingPat = "#### " ++ name ++ "\n```hb";
    const index = std.mem.indexOf(u8, readme, headingPat) orelse return error.NoStart;
    readme = readme[index + headingPat.len ..];
    const endPat = "```";
    const code = readme[0 .. std.mem.indexOf(u8, readme, endPat) orelse return error.NoEnd];
    readme = readme[code.len + endPat.len ..];
    return code;
}

pub fn TaggedIndex(comptime R: type, comptime T: type) type {
    return packed struct(R) {
        tag_bits: std.meta.Tag(T),
        index: std.meta.Int(.unsigned, @bitSizeOf(R) - @bitSizeOf(T)),

        pub const Tag = T;
        pub const Repr = R;

        pub fn init(tag_bits: T, index: usize) @This() {
            return .{ .tag_bits = @intFromEnum(tag_bits), .index = @intCast(index) };
        }

        pub fn tag(self: @This()) T {
            return @enumFromInt(self.tag_bits);
        }
    };
}

pub fn toTuple(ty: anytype) TupleOf(@TypeOf(ty)) {
    var res: TupleOf(@TypeOf(ty)) = undefined;
    inline for (std.meta.fields(@TypeOf(ty)), 0..) |field, i| res[i] = @field(ty, field.name);
    return res;
}

pub fn TupleOf(comptime T: type) type {
    const fields = std.meta.fields(T);
    var types: [fields.len]std.builtin.Type.StructField = undefined;
    for (fields, &types, 0..) |field, *ty, i| ty.* = .{
        .name = &[1:0]u8{'0' + i},
        .type = field.type,
        .default_value = null,
        .alignment = @alignOf(field.type),
        .is_comptime = false,
    };
    return @Type(.{ .Struct = .{
        .fields = &types,
        .decls = &.{},
        .is_tuple = true,
        .layout = .auto,
    } });
}

pub fn EntStore(comptime M: type) type {
    return struct {
        const Tag = std.meta.DeclEnum(M);

        pub const Data = b: {
            var fields: [decls.len]std.builtin.Type.UnionField = undefined;

            for (decls, &fields) |d, *f| {
                const Ty = @field(M, d.name);
                const Dt = if (@hasDecl(Ty, "identity")) Ty else EntId(Ty);
                f.* = .{
                    .name = d.name,
                    .type = Dt,
                    .alignment = @alignOf(Dt),
                };
            }

            break :b @Type(.{ .@"union" = .{
                .layout = .auto,
                .tag_type = Tag,
                .fields = &fields,
                .decls = &.{},
            } });
        };

        rpr: Store = .{},

        const decls = std.meta.declarations(M);
        const Store = b: {
            var fields: [decls.len]std.builtin.Type.StructField = undefined;

            for (decls, &fields) |d, *f| {
                const Arr = SegmentedList(@field(M, d.name), 1024 * 16, 1024 * 1024);
                f.* = .{
                    .name = d.name,
                    .type = Arr,
                    .alignment = @alignOf(Arr),
                    .is_comptime = false,
                    .default_value_ptr = &Arr{},
                };
            }
            break :b @Type(.{ .@"struct" = .{
                .layout = .auto,
                .fields = &fields,
                .decls = &.{},
                .is_tuple = false,
            } });
        };
        const store_fields = std.meta.fields(Store);
        const data_fields = std.meta.fields(Data);
        const Self = @This();

        pub fn isValid(self: *Self, comptime kind: Tag, idx: usize) bool {
            return idx < @field(self.rpr, @tagName(kind)).meta.len;
        }

        pub fn fieldName(comptime Ty: type) std.builtin.Type.StructField {
            return for (decls, store_fields) |d, sf| {
                if (@field(M, d.name) == Ty) return sf;
            } else @compileError(@typeName(Ty));
        }

        pub fn add(self: *Self, gpa: *Arena, vl: anytype) EntId(@TypeOf(vl)) {
            @field(self.rpr, fieldName(@TypeOf(vl)).name).addOne(gpa).* = vl;
            return @enumFromInt(@field(self.rpr, fieldName(@TypeOf(vl)).name).meta.len - 1);
        }

        pub fn pop(self: *Self, vl: anytype) void {
            std.debug.assert(@field(self.rpr, fieldName(@TypeOf(vl).Data).name).meta.len == @intFromEnum(vl) + 1);
            _ = @field(self.rpr, fieldName(@TypeOf(vl).Data).name).pop().?;
        }

        pub fn get(self: *Self, id: anytype) if (@hasDecl(@TypeOf(id), "identity")) @TypeOf(id) else *@TypeOf(id).Data {
            if (@hasDecl(@TypeOf(id), "identity")) return id;
            return @field(self.rpr, fieldName(@TypeOf(id).Data).name).at(@intFromEnum(id));
        }

        pub fn TagPayload(comptime kind: Tag) type {
            return data_fields[@intFromEnum(kind)].type;
        }

        pub inline fn unwrap(self: *Self, id: Data, comptime kind: Tag) ?*if (@hasDecl(TagPayload(kind), "identity"))
            TagPayload(kind)
        else
            TagPayload(kind).Data {
            if (id != kind) return null;
            const i = @field(id, @tagName(kind));
            if (@hasDecl(TagPayload(kind), "identity")) return i;
            return @field(self.rpr, @tagName(kind)).at(@intFromEnum(i));
        }
    };
}

pub fn EntId(comptime D: type) type {
    if (@hasDecl(D, "Id")) return D.Id;

    return enum(u32) {
        _,
        pub const Data = D;

        pub fn get(self: @This(), cont: anytype) *D {
            return cont.store.get(self);
        }
    };
}

pub fn SegmentedList(comptime T: type, comptime first_segment_size: usize, comptime max_segment_size: usize) type {
    return struct {
        pub const first_segment_size_exp = std.math.log2_int(usize, first_segment_size);

        pub const shelf_count = std.math.log2_int(usize, max_segment_size / first_segment_size) + 1;

        shelfs: [shelf_count][*]T = undefined,
        meta: packed struct(usize) {
            active_shelf_count: ShelfIndex = 0,
            len: std.meta.Int(.unsigned, @bitSizeOf(usize) - @bitSizeOf(ShelfIndex)) = 0,
        } = .{},

        const Self = @This();
        const ShelfIndex = std.math.Log2Int(usize);

        pub fn toSlice(self: *const Self, gpa: *Arena) []T {
            const continuous = gpa.alloc(T, self.meta.len);

            var cursor: usize = 0;
            var remining = self.meta.len;
            var shelf_size: usize = first_segment_size;
            for (self.shelfs) |shelf| {
                const to_copy = @min(shelf_size, remining);
                @memcpy(continuous[cursor..][0..to_copy], shelf[0..to_copy]);
                cursor += to_copy;
                remining -= to_copy;
                shelf_size *= 2;
            }

            return continuous;
        }

        pub fn addOne(self: *Self, gpa: *Arena) *T {
            self.ensureCapacity(gpa, self.meta.len + 1);
            const shelf_index = shelfIndex(self.meta.len);
            const box_index = boxIndex(self.meta.len, shelf_index);
            self.meta.len += 1;
            return &self.shelfs[shelf_index][box_index];
        }

        pub fn pop(self: *Self) ?T {
            if (self.meta.len == 0) return null;

            defer self.meta.len -= 1;
            return self.at(self.meta.len - 1).*;
        }

        pub fn at(self: Self, index: usize) *T {
            std.debug.assert(index < self.meta.len);
            const shelf_index = shelfIndex(index);
            const box_index = boxIndex(index, shelf_index);
            return &self.shelfs[shelf_index][box_index];
        }

        pub fn ensureCapacity(self: *Self, arena: *Arena, new_capacity: usize) void {
            const new_cap_shelf_count = shelfCount(new_capacity);
            const old_shelf_count = self.meta.active_shelf_count;
            if (new_cap_shelf_count <= old_shelf_count) {
                @branchHint(.likely);
                return;
            }

            var i: ShelfIndex = old_shelf_count;
            while (i < new_cap_shelf_count) : (i += 1) {
                self.shelfs[i] = arena.alloc(T, shelfSize(i)).ptr;
            }
            self.meta.active_shelf_count = new_cap_shelf_count;
        }

        fn shelfSize(shelf_index: ShelfIndex) usize {
            return @as(usize, 1) << (shelf_index + (first_segment_size_exp + 1));
        }

        fn shelfIndex(list_index: usize) ShelfIndex {
            return std.math.log2_int(usize, list_index + first_segment_size * 2) - first_segment_size_exp - 1;
        }

        fn boxIndex(list_index: usize, shelf_index: ShelfIndex) usize {
            return list_index + first_segment_size * 2 - (@as(usize, 1) << ((first_segment_size_exp + 1) + shelf_index));
        }

        fn shelfCount(box_count: usize) ShelfIndex {
            return @intCast(std.math.log2_int_ceil(usize, box_count + first_segment_size * 2) - first_segment_size_exp - 1);
        }
    };
}

pub const Foo = SegmentedList(usize, 1024, 1024 * 1024);

test "segmented list" {
    var arena = Arena.init(1024 * 1024);
    var list = SegmentedList(usize, 1024, 1024 * 128){};

    for (0..1024 * 32) |i| {
        list.addOne(&arena).* = i;
    }

    for (0..1024 * 32) |i| {
        try std.testing.expectEqual(i, list.at(i).*);
    }
}

pub fn SharedQueue(comptime T: type) type {
    return struct {
        shards: []Shard,
        progress: usize = 0,
        cached_counter: usize = 0,
        self_id: usize = std.math.maxInt(usize),
        tasks: []const []T,

        const Self = @This();

        pub const Shard = struct {
            _align: void align(std.atomic.cache_line) = {},
            reserved: std.atomic.Value(usize) = .init(0),
            available: std.atomic.Value(usize) = .init(0),
            waker: std.Thread.ResetEvent = .{},
        };

        pub fn size_of(thread_count: usize, capacity: usize) usize {
            return @sizeOf(T) * capacity * thread_count +
                @sizeOf(Shard) * thread_count +
                @sizeOf([]T) * thread_count;
        }

        pub fn init(arena: *Arena, thread_count: usize, capacity: usize) Self {
            const shards = arena.alloc(Shard, thread_count);
            @memset(shards, .{});

            const tasks = arena.alloc([]T, thread_count);
            for (tasks) |*t| {
                t.* = arena.alloc(T, capacity);
            }

            return .{ .shards = shards, .tasks = tasks };
        }

        pub fn enque(self: *Self, tasks: []const T) void {
            const push_to = (if (!std.meta.hasMethod(T, "hash")) b: {
                comptime std.debug.assert(std.meta.hasUniqueRepresentation(T));
                break :b std.hash.Wyhash.hash(0, @ptrCast(tasks));
            } else T.hash(tasks)) & self.shards.len - 1;

            const target = &self.shards[@intCast(push_to)];

            const idx = target.reserved.fetchAdd(tasks.len, .monotonic);
            @memcpy(self.tasks[@intCast(push_to)][idx..][0..tasks.len], tasks);
            while (target.available.cmpxchgWeak(idx, idx + tasks.len, .release, .monotonic) != null) {}
            target.waker.set();
        }

        pub fn dequeue(self: *Self) ?T {
            const shard = &self.shards[self.self_id];
            if (self.progress == self.cached_counter) {
                self.cached_counter = shard.available.load(.acquire);
                if (self.progress == self.cached_counter) return null;
            }
            self.progress += 1;
            return self.tasks[self.self_id][self.progress - 1];
        }

        pub fn dequeueWait(self: *Self, timeout_ms: usize) ?T {
            const shard = &self.shards[self.self_id];

            while (true) {
                shard.waker.reset();

                // the thread pushed while we were setting the waker
                if (self.dequeue()) |task| return task;

                if (@import("builtin").single_threaded) return null;

                // timeout means no more tasks
                shard.waker.timedWait(timeout_ms * std.time.ns_per_ms) catch {
                    return self.dequeue();
                };

                // if we were woken up, we still might not have tasks, which
                // happens so rarely it doesn't matter, so just try again
                return self.dequeue() orelse continue;
            }
        }
    };
}

pub fn TimeMetrics(comptime StatNames: type) type {
    return struct {
        total: u64 = 0,
        stats: Stats = .{},

        const Self = @This();

        const max_name_len = b: {
            var max: usize = 0;
            for (std.meta.fields(StatNames)) |f| {
                max = @max(max, f.name.len);
            }
            break :b std.fmt.comptimePrint("{d}", .{max});
        };

        const Stats = @Type(b: {
            var fields: [std.meta.fields(StatNames).len]std.builtin.Type.StructField = undefined;
            for (std.meta.fields(StatNames), &fields) |f, *sf| {
                sf.* = .{
                    .name = f.name,
                    .type = u64,
                    .alignment = @alignOf(u64),
                    .is_comptime = false,
                    .default_value_ptr = &@as(u64, 0),
                };
            }
            break :b .{
                .@"struct" = .{
                    .layout = .auto,
                    .fields = &fields,
                    .decls = &.{},
                    .is_tuple = false,
                },
            };
        });

        pub const Scope = if (freestanding) struct {
            pub fn end(_: *@This()) void {}
        } else struct {
            total: *u64,
            stat: *u64,
            timer: std.time.Timer,
            prev_total: u64,

            pub fn end(self: *@This()) void {
                const elapsed = self.timer.lap() - (self.total.* - self.prev_total);
                self.stat.* += elapsed;
                self.total.* += elapsed;
                self.* = undefined;
            }
        };

        pub fn init() Self {
            return .{};
        }

        // THIS handles the nesting
        pub fn begin(self: *Self, comptime name: StatNames) Scope {
            return if (freestanding) .{} else .{
                .stat = &@field(self.stats, @tagName(name)),
                .timer = std.time.Timer.start() catch unreachable,
                .total = &self.total,
                .prev_total = self.total,
            };
        }

        pub fn logStats(self: *Self, out: *std.Io.Writer) void {
            errdefer unreachable;
            try out.print("time metrics:\n", .{});

            var total: u64 = 0;
            inline for (std.meta.fields(Stats)) |f| {
                total += @field(self.stats, f.name);
            }

            const ftotal = @as(f64, @floatFromInt(total));
            try out.print("  total: {d:.9}s\n", .{ftotal / std.time.ns_per_s});

            inline for (std.meta.fields(Stats)) |f| {
                const fvl = @as(f64, @floatFromInt(@field(self.stats, f.name)));
                try out.print("  {s:<" ++ max_name_len ++ "}: ({d:>6.2}%) {d:>10.9}s\n", .{
                    f.name,
                    (fvl / ftotal) * 100,
                    fvl / std.time.ns_per_s,
                });
            }
        }
    };
}

test "queue shard" {
    if (true) return;

    const tasks_per_thread = 1024 * 1024;

    const thread = struct {
        fn runShardThread(ashard: SharedQueue(u64), waker: *std.Thread.ResetEvent) void {
            waker.wait();

            var shard = ashard;
            for (0..tasks_per_thread) |i| {
                var tasks: u64 = i + shard.self_id * tasks_per_thread;
                shard.enque((&tasks)[0..1]);
                shard.enque((&tasks)[0..1]);
                _ = shard.dequeue() orelse shard.dequeueWait(10);
            }
        }
    };

    const thread_count = 8;

    var arena = Arena.init(SharedQueue(u64).size_of(thread_count, tasks_per_thread * thread_count));
    var shard = SharedQueue(u64).init(&arena, thread_count, tasks_per_thread * thread_count);

    const Thrd = struct {
        thread: std.Thread,
    };

    const tsrgs = std.testing.allocator.alloc(Thrd, thread_count) catch unreachable;
    var waker = std.Thread.ResetEvent{};
    defer std.testing.allocator.free(tsrgs);
    for (tsrgs, 0..) |*thrd, i| {
        shard.self_id = i;
        thrd.* = .{ .thread = try std.Thread.spawn(.{}, thread.runShardThread, .{ shard, &waker }) };
    }

    waker.set();

    for (tsrgs) |thrd| {
        thrd.thread.join();
    }

    var bitset = try std.DynamicBitSetUnmanaged.initEmpty(std.testing.allocator, thread_count * tasks_per_thread);
    defer bitset.deinit(std.testing.allocator);

    for (shard.tasks, shard.shards) |thrd, shrd| {
        for (thrd[0..shrd.available.load(.unordered)]) |task| {
            bitset.set(@bitCast(task));
        }
    }

    std.debug.assert(bitset.count() == thread_count * tasks_per_thread);
}

test "dequeueWait" {
    if (true) return;

    const thread = struct {
        fn run(queue: SharedQueue(usize)) void {
            var q = queue;
            for (0..10) |i| {
                q.enque(&.{i});
                std.Thread.sleep(10 * std.time.ns_per_ms);
            }
        }
    };

    var arena = Arena.init(1024 * 1024);
    var queue = SharedQueue(usize).init(&arena, 1, 100);
    queue.self_id = 0;

    var tread = std.Thread.spawn(.{}, thread.run, .{queue}) catch unreachable;

    for (0..10) |i| {
        const task = queue.dequeueWait(100).?;
        std.debug.assert(task == i);
    }

    defer tread.join();
}

pub const LineIndex = struct {
    nlines: []const u32,

    pub fn lineCol(self: LineIndex, pos: u32) struct { u32, u32 } {
        var start: usize, var end = .{ 0, self.nlines.len };

        while (start < end) {
            const mid = (start + end) / 2;
            if (pos < self.nlines[mid]) {
                end = mid;
            } else {
                start = mid + 1;
            }
        }

        return .{ @intCast(start), pos - self.nlines[start - 1] };
    }

    pub fn init(file_content: []const u8, arena: *Arena) LineIndex {
        var line_count: usize = 1;
        for (file_content) |c| {
            if (c == '\n') line_count += 1;
        }

        var nlines = arena.alloc(u32, line_count);
        nlines[0] = 0;

        line_count = 1;
        for (file_content, 0..) |c, i| {
            if (c == '\n') {
                nlines[line_count] = @intCast(i + 1);
                line_count += 1;
            }
        }

        return .{ .nlines = nlines };
    }
};

test LineIndex {
    const file_content =
        \\akjdshkdfj
        \\ksjdhks
        \\akjdsk
        \\akjdshkdfj
        \\ksjdhks
        \\akjdsk
    ;

    var arena = Arena.init(4096);
    defer arena.deinit();

    const line_index = LineIndex.init(file_content, &arena);

    var line: u32 = 1;
    var last_nl: usize = 0;
    for (file_content, 0..) |c, i| {
        const lin, const col = line_index.lineCol(@intCast(i));
        try std.testing.expectEqual(line, lin);
        try std.testing.expectEqual(i - last_nl, col);
        if (c == '\n') {
            line += 1;
            last_nl = i + 1;
        }
    }
}
