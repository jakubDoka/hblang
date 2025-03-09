const std = @import("std");

pub const Arena = struct {
    start: [*]align(page_size) u8,
    end: [*]align(page_size) u8,
    pos: [*]u8,

    const page_size = std.heap.pageSize();

    pub const Scratch = struct {
        prev_pos: [*]u8,
        arena: *Arena,

        pub fn deinit(self: *Scratch) void {
            @memset(self.arena.pos[0 .. @intFromPtr(self.prev_pos) - @intFromPtr(self.arena.pos)], undefined);
            self.arena.pos = self.prev_pos;
            self.* = undefined;
        }
    };

    threadlocal var scratch: [2]Arena = undefined;

    pub fn initScratch(cap: usize) void {
        for (&scratch) |*slt| slt.* = init(cap);
    }

    pub fn deinitScratch() void {
        for (&scratch) |*slt| slt.deinit();
    }

    pub fn allocated(self: *Arena) usize {
        return @intFromPtr(self.end) - @intFromPtr(self.pos);
    }

    pub fn scrath(except: ?*Arena) Scratch {
        for (&scratch) |*slt| if (slt != except) return slt.checkpoint();
        unreachable;
    }

    pub fn init(cap: usize) Arena {
        const pages = std.mem.alignForward(usize, cap, page_size);
        const ptr = std.heap.page_allocator.rawAlloc(pages, .fromByteUnits(page_size), @returnAddress()).?;
        return .{
            .end = @alignCast(ptr + pages),
            .start = @alignCast(ptr),
            .pos = @alignCast(ptr + pages),
        };
    }

    pub fn allocator(self: *Arena) std.mem.Allocator {
        const alc_impl = enum {
            fn alloc(ptr: *anyopaque, size: usize, alignment: std.mem.Alignment, _: usize) ?[*]u8 {
                const slf: *Arena = @alignCast(@ptrCast(ptr));
                const alignm = alignment.toByteUnits();
                slf.pos = @ptrFromInt(std.mem.alignBackward(usize, @intFromPtr(slf.pos - size), alignm));
                std.debug.assert(@intFromPtr(slf.start) < @intFromPtr(slf.pos));
                return slf.pos;
            }
            fn free(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize) void {}
            fn remap(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize, _: usize) ?[*]u8 {
                return null;
            }
            fn resize(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize, _: usize) bool {
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

    pub fn alloc(self: *Arena, comptime T: type, count: usize) []T {
        const size = @sizeOf(T) * count;
        self.pos = @ptrFromInt(std.mem.alignBackward(usize, @intFromPtr(self.pos - size), @alignOf(T)));
        std.debug.assert(@intFromPtr(self.start) < @intFromPtr(self.pos));
        const ptr: [*]T = @alignCast(@ptrCast(self.pos));
        const mem = ptr[0..count];
        @memset(mem, undefined);
        return mem;
    }

    pub fn create(self: *Arena, comptime T: type) *T {
        return &@call(.always_inline, alloc, .{ self, T, 1 }).ptr[0];
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
            std.debug.assert(start < end);
            std.debug.assert(end * @sizeOf(Elem) <= self.end);
            return .{ .start = @intCast(self.start + start * @sizeOf(Elem)), .end = @intCast(self.start + end * @sizeOf(Elem)) };
        }
    };
}

pub fn EnumStore(comptime T: type) type {
    return struct {
        store: std.ArrayListAlignedUnmanaged(u8, payload_align) = .{},

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
            const dest: [*]E = @alignCast(@ptrCast(self.store.items.ptr + padded_len));
            return dest[0..count];
        }

        pub fn get(self: *const Self, id: Id) T {
            switch (id.tag()) {
                inline else => |t| {
                    const Value = TagPayload(t);
                    const loc: *const Value = if (Value != void) @ptrCast(@alignCast(&self.store.items[id.index()])) else &{};
                    return @unionInit(T, @tagName(t), loc.*);
                },
            }
        }

        pub fn getTyped(
            self: *const Self,
            comptime tag: std.meta.Tag(T),
            id: Id,
        ) ?TagPayload(tag) {
            if (tag != id.tag()) return null;
            const Value = TagPayload(tag);
            const loc: *Value = @ptrCast(@alignCast(&self.store.items[id.index()]));
            return loc.*;
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

pub fn dbg(value: anytype) @TypeOf(value) {
    if (@TypeOf(value) == []const u8)
        std.debug.print("{s}\n", .{value});
    std.debug.print("{any}\n", .{value});
    return value;
}

const debug = @import("builtin").mode == .Debug;

pub const StaticTrace = struct {
    index: if (debug) usize else void,
    frames: if (debug) [frame_limit]usize else void,

    const frame_limit = 10;

    pub fn init(return_addr: usize) StaticTrace {
        if (!debug) return undefined;
        var trace: StaticTrace = undefined;
        var stack_trace = std.builtin.StackTrace{
            .index = undefined,
            .instruction_addresses = &trace.frames,
        };
        std.debug.captureStackTrace(return_addr, &stack_trace);
        trace.index = stack_trace.index;
        return trace;
    }

    pub fn dump(self: *StaticTrace) void {
        if (!debug) return;
        std.debug.dumpStackTrace(.{
            .index = self.index,
            .instruction_addresses = &self.frames,
        });
    }
};

pub fn isErr(value: anytype) bool {
    value catch return true;
    return false;
}

pub inline fn alignTo(offset: anytype, alignment: @TypeOf(offset)) @TypeOf(offset) {
    return (offset + alignment - 1) & ~(alignment - 1);
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
