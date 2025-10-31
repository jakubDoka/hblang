const std = @import("std");
const Set = std.DynamicBitSetUnmanaged;

const utils = @import("../utils.zig");
const Builder = @import("Builder.zig");
const graph = @import("graph.zig");
const static_anal = @import("static_anal.zig");
const root = @import("hb");
const lane = root.utils.lane;

out: Data,
vtable: *const VTable,

pub const max_func = std.math.maxInt(u32);

pub const RunError = error{
    Timeout,
    Unreachable,
    OutOfMemory,
    MalformedBinary,
    SegmentationFault,
    InvalidCall,
    InvalidInstruction,
};

const VTable = struct {
    emitFunc: *const fn (self: *Machine, func: *BuilderFunc, opts: EmitOptions) void,
    emitData: *const fn (self: *Machine, opts: DataOptions) void,
    merge: *const fn (self: *Machine, others: []*Machine) bool,
    finalize: *const fn (self: *Machine, opts: FinalizeOptions) void,
    disasm: *const fn (self: *Machine, opts: DisasmOpts) void,
    run: *const fn (self: *Machine, env: RunEnv) RunError!usize,
    deinit: *const fn (self: *Machine) void,
};

const BuilderFunc = graph.Func(Builder);
const Machine = @This();

pub const Null = struct {
    mach: Machine = .init(Null),

    const Func = graph.Func(Null);

    pub const classes = enum {};

    pub const i_know_the_api = {};

    comptime {
        const s = Null{};
        _ = s;
    }

    pub fn emitFunc(_: *@This(), _: *Func, _: EmitOptions) void {}
    pub fn emitData(_: *@This(), _: DataOptions) void {}
    pub fn finalize(_: *@This(), _: FinalizeOptions) void {}
    pub fn disasm(_: *@This(), _: DisasmOpts) void {}
    pub fn run(_: *@This(), _: RunEnv) RunError!usize {
        return 0;
    }
    pub fn deinit(_: *@This()) void {}
};

const InlineFunc = graph.Func(Builder);

pub const FuncId = packed struct(u32) { thread: u8, index: u24 };

pub const Data = struct {
    declaring_sym: ?SymIdx = null,
    files: []const File = &.{},
    funcs: std.ArrayList(SymIdx) = .empty,
    globals: std.ArrayList(SymIdx) = .empty,
    syms: std.ArrayList(Sym) = .empty,
    names: std.ArrayList(u8) = .empty,
    code: std.ArrayList(u8) = .empty,
    relocs: std.ArrayList(Reloc) = .empty,
    remote_funcs: std.ArrayList(RemoteFunc) = .empty,
    inline_funcs: std.ArrayList(InlineFunc) = .empty,
    line_info: std.ArrayList(u8) = .empty,
    line_info_relocs: std.ArrayList(Reloc) = .empty,

    pub const DeferCtx = struct {
        root_sym: SymIdx,
        sym_slot: SymIdx = .invalid,
    };

    pub const RemoteFunc = struct {
        local_sym: u32,
        remote_sym: u32,
        thread: u32,
    };

    pub const File = struct {
        name: []const u8,
        size: u32,
    };

    pub const UUID = [2]u64;
    pub const UUIDHasher = std.hash.SipHash128(1, 1);

    pub fn uuidConst(id: []const u8) UUID {
        var h = UUIDHasher.init(&@splat(0));
        h.update(id);
        return @bitCast(h.finalResult());
    }

    pub const Sym = struct {
        name: u32,
        offset: u32,
        size: u32,
        reloc_offset: u32,
        reloc_count: u32,
        kind: Kind,
        linkage: Linkage,
        readonly: bool,
        is_inline: bool,
        inline_func: u32 = no_inline_func,
        stack_size: u32 = 0,
        uuid: UUID,

        pub const no_inline_func = std.math.maxInt(u32);
    };

    pub const Kind = enum {
        func,
        data,
        prealloc,
        tls_prealloc,

        invalid,
    };

    pub const Linkage = enum {
        local,
        exported,
        imported,
    };

    pub const Reloc = struct {
        target: SymIdx,
        offset: u32,
        meta: packed struct(u32) {
            slot_size: SlotSize,
            addend: i31,
        },

        const SlotSize = enum(u1) {
            @"4",
            @"8",
            pub fn bytes(self: SlotSize) u8 {
                return switch (self) {
                    .@"4" => 4,
                    .@"8" => 8,
                };
            }
        };
    };

    pub const SymIdx = enum(u32) { invalid = std.math.maxInt(u32), _ };

    pub fn projectSyms(
        self: *Data,
        gpa: std.mem.Allocator,
        comptime Node: type,
        func: *graph.Func(Node),
    ) void {
        errdefer unreachable;
        for (func.getSyms().outputs()) |s| {
            switch (s.get().extra2()) {
                inline .FuncAddr, .Call, .GlobalAddr => |extra, t| {
                    const lookup = if (t == .GlobalAddr)
                        &self.globals
                    else
                        &self.funcs;
                    const slot = try utils.ensureSlot(lookup, gpa, extra.id);
                    extra.id = @intFromEnum(try self.declSym(gpa, slot));
                },
                else => utils.panic("{f} has no sym", .{s}),
            }
        }
    }

    pub fn setInlineFunc(
        self: *Data,
        gpa: std.mem.Allocator,
        comptime Node: type,
        func: *graph.Func(Node),
        to: u32,
    ) void {
        errdefer unreachable;

        self.syms.items[@intFromEnum(self.funcs.items[to])].inline_func = @intCast(self.inline_funcs.items.len);
        try self.inline_funcs.append(gpa, @as(*InlineFunc, @ptrCast(func)).*);
        func.arena = .init(func.arena.child_allocator);
    }

    pub fn getInlineFunc(self: *Data, comptime Backend: type, at: u32, force_inline: bool) ?*graph.Func(Backend) {
        if (self.funcs.items.len <= at or self.funcs.items[at] == .invalid) return null;
        const sym = &self.syms.items[at];
        if (!sym.is_inline and !force_inline) return null;
        return if (sym.inline_func != Sym.no_inline_func)
            @ptrCast(&self.inline_funcs.items[sym.inline_func])
        else
            null;
    }

    pub fn readFromSym(self: Data, id: u32, offset: i64, size: u64, force_readonly: bool) ?union(enum) { value: i64, global: u32 } {
        if (self.globals.items.len <= id) return null;
        const sym = &self.syms.items[@intFromEnum(self.globals.items[id])];

        if (!sym.readonly and !force_readonly) return null;

        var value: i64 = 0;

        if (sym.offset + offset + @as(i64, @intCast(size)) >
            @as(i64, @intCast(self.code.items.len)) or
            sym.offset + offset < 0) return null;

        @memcpy(
            @as(*[@sizeOf(@TypeOf(value))]u8, @ptrCast(&value))[0..@intCast(size)],
            self.code.items[@intCast(sym.offset + offset)..][0..@intCast(size)],
        );

        // TODO: use binary search
        for (self.relocs.items[sym.reloc_offset..][0..sym.reloc_count]) |rel| {
            if (rel.offset == offset) {
                const sm = &self.syms.items[@intFromEnum(rel.target)];
                const gid: u32 = @bitCast(self.code.items[sm.offset - 4 ..][0..4].*);
                return .{ .global = gid };
            }
        }

        return .{ .value = value };
    }

    pub fn reset(self: *Data) void {
        inline for (std.meta.fields(Data)[2..]) |f| {
            @field(self, f.name).items.len = 0;
        }
    }

    pub fn lookupName(self: *const Data, name: u32) [:0]const u8 {
        return self.names.items[name..][0..std.mem.indexOfScalar(u8, self.names.items[name..], 0).? :0];
    }

    pub fn addFuncReloc(
        self: *Data,
        gpa: std.mem.Allocator,
        target: u32,
        slot_size: Reloc.SlotSize,
        addend: i31,
        back_shift: u32,
    ) !void {
        return self.addReloc(gpa, try utils.ensureSlot(&self.funcs, gpa, target), slot_size, addend, back_shift);
    }

    pub fn addPlaceholderFuncReloc(self: *Data, gpa: std.mem.Allocator, target: u32) !void {
        try self.addPlaceholderReloc(gpa, try utils.ensureSlot(&self.funcs, gpa, target));
    }

    pub fn addGlobalReloc(
        self: *Data,
        gpa: std.mem.Allocator,
        target: u32,
        slot_size: Reloc.SlotSize,
        addend: i31,
        back_shift: u32,
    ) !void {
        return self.addReloc(gpa, try utils.ensureSlot(&self.globals, gpa, target), slot_size, addend, back_shift);
    }

    pub fn addPlaceholderGlobalReloc(self: *Data, gpa: std.mem.Allocator, target: u32) !void {
        try self.addPlaceholderReloc(gpa, try utils.ensureSlot(&self.globals, gpa, target));
    }

    pub fn addReloc(self: *Data, gpa: std.mem.Allocator, target: *SymIdx, slot_size: Reloc.SlotSize, addend: i31, back_shift: u32) !void {
        try self.relocs.append(gpa, .{
            .target = try self.declSym(gpa, target),
            .offset = @intCast(self.code.items.len -
                self.syms.items[@intFromEnum(self.declaring_sym.?)].offset -
                back_shift),
            .meta = .{
                .addend = addend,
                .slot_size = slot_size,
            },
        });
    }

    pub fn addPlaceholderReloc(self: *Data, gpa: std.mem.Allocator, target: *SymIdx) !void {
        try self.relocs.append(gpa, .{
            .target = try self.declSym(gpa, target),
            .offset = 0,
            .meta = .{ .addend = 0, .slot_size = .@"4" },
        });
    }

    pub fn deinit(self: *Data, gpa: std.mem.Allocator) void {
        inline for (std.meta.fields(Data)[2..]) |f| {
            @field(self, f.name).deinit(gpa);
        }
        self.* = undefined;
    }

    pub fn declSym(
        self: *Data,
        gpa: std.mem.Allocator,
        slot: *SymIdx,
    ) !SymIdx {
        if (slot.* == .invalid) {
            slot.* = @enumFromInt(self.syms.items.len);
            (try self.syms.addOne(gpa)).kind = .invalid;
        }
        return slot.*;
    }

    pub fn importFunc(
        self: *Data,
        gpa: std.mem.Allocator,
        id: u32,
        name: []const u8,
        uuid: UUID,
    ) !void {
        try self.importSym(gpa, try utils.ensureSlot(&self.funcs, gpa, id), name, .func, uuid);
    }

    pub fn importSym(
        self: *Data,
        gpa: std.mem.Allocator,
        sym: *SymIdx,
        name: []const u8,
        kind: Kind,
        uuid: UUID,
    ) !void {
        _ = try self.declSym(gpa, sym);
        self.syms.items[@intFromEnum(sym.*)] = .{
            .name = @intCast(self.names.items.len),
            .offset = 0,
            .size = 0,
            .reloc_offset = 0,
            .reloc_count = 0,
            .kind = kind,
            .linkage = .imported,
            .readonly = true,
            .is_inline = false,
            .uuid = uuid,
        };
        try self.names.appendSlice(gpa, name);
        try self.names.append(gpa, 0);
    }

    pub fn startDefineFunc(
        self: *Data,
        gpa: std.mem.Allocator,
        name: []const u8,
        opts: EmitOptions,
    ) !struct { *Sym, SymIdx, SymIdx } {
        const slot = switch (opts.id) {
            .arbitrary => |id| blk: {
                std.debug.assert(id != max_func and id != graph.indirect_call);
                break :blk try utils.ensureSlot(&self.funcs, gpa, id);
            },
            .sym => |sym_idx| &sym_idx.sym_slot,
        };

        return .{ try self.startDefineSym(
            gpa,
            slot,
            name,
            .func,
            opts.linkage,
            true,
            opts.is_inline,
            opts.uuid,
        ), slot.*, if (opts.id == .sym) opts.id.sym.root_sym else slot.* };
    }

    pub fn defineGlobal(
        self: *Data,
        gpa: std.mem.Allocator,
        push_uninit: bool,
        linkage: Linkage,
        func_addend: u32,
        opts: DataOptions,
    ) !void {
        // this is there to support N(1) reverse lookup form a memory offset
        // to global id
        try self.code.appendSlice(gpa, std.mem.asBytes(&opts.id));

        _ = try self.startDefineSym(
            gpa,
            try utils.ensureSlot(&self.globals, gpa, opts.id),
            opts.name,
            if (opts.value == .init) .data else if (opts.thread_local) .tls_prealloc else .prealloc,
            linkage,
            opts.readonly,
            false,
            opts.uuid,
        );

        if (opts.value == .init) {
            try self.code.appendSlice(gpa, opts.value.init);
            for (opts.relocs) |rel| {
                if (rel.is_func) {
                    try self.addFuncReloc(
                        gpa,
                        rel.target,
                        .@"8",
                        @intCast(func_addend),
                        @intCast(opts.value.init.len - rel.offset),
                    );
                } else {
                    try self.addGlobalReloc(gpa, rel.target, .@"8", 0, @intCast(opts.value.init.len - rel.offset));
                }
                std.debug.assert(rel.target != opts.id);
            }
        } else {
            if (push_uninit) {
                try self.code.appendNTimes(gpa, 0, opts.value.uninit);
            }
        }

        self.endDefineSym(self.globals.items[opts.id]);
        self.syms.items[@intFromEnum(self.globals.items[opts.id])].size =
            if (opts.value == .init) @intCast(opts.value.init.len) else @intCast(opts.value.uninit);
    }

    pub fn getFuncSym(self: *Data, id: u32) *Sym {
        return &self.syms.items[@intFromEnum(self.funcs.items[id])];
    }

    pub fn startDefineSym(
        self: *Data,
        gpa: std.mem.Allocator,
        sym: *SymIdx,
        name: []const u8,
        kind: Kind,
        linkage: Linkage,
        readonly: bool,
        is_inline: bool,
        uuid: UUID,
    ) !*Sym {
        _ = try self.declSym(gpa, sym);

        std.debug.assert(self.declaring_sym == null);
        self.declaring_sym = sym.*;

        const slot = &self.syms.items[@intFromEnum(sym.*)];

        const needs_name = slot.kind == .invalid;
        std.debug.assert(needs_name or slot.kind == kind);

        slot.* = .{
            .name = if (needs_name) @intCast(self.names.items.len) else @intCast(slot.name),
            .offset = @intCast(self.code.items.len),
            .size = undefined,
            .reloc_offset = @intCast(self.relocs.items.len),
            .reloc_count = undefined,
            .kind = kind,
            .linkage = linkage,
            .readonly = readonly,
            .is_inline = is_inline,
            .uuid = uuid,
        };

        if (needs_name) {
            try self.names.appendSlice(gpa, name);
            try self.names.append(gpa, 0);
        }

        return slot;
    }

    pub fn endDefineFunc(self: *Data, emid: EmitOptions.Id) void {
        switch (emid) {
            .arbitrary => |id| {
                std.debug.assert(id != std.math.maxInt(u32));
                self.endDefineSym(self.funcs.items[id]);
            },
            .sym => |sym| self.endDefineSym(sym.sym_slot),
        }
    }

    pub fn endDefineSym(self: *Data, sym: SymIdx) void {
        std.debug.assert(self.declaring_sym != null);
        self.declaring_sym = null;

        const slot = &self.syms.items[@intFromEnum(sym)];
        slot.size = @intCast(self.code.items.len - slot.offset);
        slot.reloc_count = @intCast(self.relocs.items.len - slot.reloc_offset);
    }

    pub fn makeRelocOffsetsGlobal(self: *Data, idx: SymIdx) void {
        const sym = &self.syms.items[@intFromEnum(idx)];
        for (self.relocs.items[sym.reloc_offset..][0..sym.reloc_count]) |*rel| {
            rel.offset += sym.offset;
        }
    }

    const trivial_group = std.math.maxInt(u32);

    const strong_group_ref_flag: u32 = 1 << 31;

    pub fn deduplicate(self: *Data) void {
        errdefer unreachable;
        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        // Trajan algorithm
        //
        const strong_groups = tmp.arena.alloc(u32, self.syms.items.len);

        var strong_group_meta = std.ArrayList([]const u32){};

        const indexes = tmp.arena.alloc(packed struct(u32) {
            in_stack: bool,
            self_recursive: bool,
            index: u30,
        }, self.syms.items.len);

        const unvisited = @TypeOf(indexes[0]){
            .in_stack = false,
            .self_recursive = false,
            .index = 0,
        };

        @memset(indexes, unvisited);

        const low_links = tmp.arena.alloc(u32, self.syms.items.len);

        const depth_estimate = std.math.log2_int_ceil(usize, self.syms.items.len) + 4;

        var stack = tmp.arena.makeArrayList(u32, depth_estimate);

        const Frame = struct {
            node: u32,
            dep_idx: u32 = 0,
        };
        var recursion_stack = tmp.arena.makeArrayList(Frame, depth_estimate);

        var next_index: u30 = 1;
        for (0..self.syms.items.len) |idx| {
            if (indexes[idx] != unvisited) continue;

            recursion_stack.appendAssumeCapacity(.{ .node = @intCast(idx) });

            while (recursion_stack.items.len > 0) {
                const frame = &recursion_stack.items[recursion_stack.items.len - 1];
                const sym = &self.syms.items[frame.node];

                if (frame.dep_idx == 0) {
                    indexes[frame.node].index = next_index;
                    low_links[frame.node] = next_index;
                    next_index += 1;
                    try stack.append(tmp.arena.allocator(), @intCast(frame.node));
                    indexes[frame.node].in_stack = true;
                } else {
                    const prev_node = @intFromEnum(self.relocs.items[sym.reloc_offset + frame.dep_idx - 1].target);
                    std.debug.assert(indexes[prev_node] != unvisited);
                    low_links[frame.node] = @min(low_links[frame.node], low_links[prev_node]);
                }

                if (frame.dep_idx == sym.reloc_count) {
                    // got a strong group, idk why
                    if (indexes[frame.node].index == low_links[frame.node]) {
                        if (stack.getLast() == frame.node and
                            !indexes[frame.node].self_recursive)
                        {
                            strong_groups[frame.node] = trivial_group;
                            _ = stack.pop().?;
                        } else {
                            var i = stack.items.len;
                            while (true) {
                                i -= 1;
                                const node = stack.items[i];
                                std.debug.assert(indexes[node].in_stack);
                                indexes[node].in_stack = false;
                                strong_groups[node] = @intCast(strong_group_meta.items.len);
                                if (node == frame.node) break;
                            }

                            const SortCtx = struct {
                                self: *Data,
                                group: u32,
                            };

                            // Reindex the in group refs

                            std.sort.pdq(u32, stack.items[i..], SortCtx{
                                .self = self,
                                .group = @intCast(strong_group_meta.items.len),
                            }, enum {
                                fn lessThenFn(slf: SortCtx, lhs: u32, rhs: u32) bool {
                                    const data = slf.self;

                                    const lhss = &data.syms.items[lhs];
                                    const rhss = &data.syms.items[rhs];

                                    const code_order = std.mem.order(
                                        u8,
                                        data.code.items[lhss.offset..][0..lhss.size],
                                        data.code.items[rhss.offset..][0..rhss.size],
                                    );

                                    // if we encounter equals we are basically
                                    // damned but that has low likelyhoot of
                                    // happening
                                    return code_order == .lt;
                                }
                            }.lessThenFn);

                            // NOTE: we reuse the low-link memory to store
                            // index lookup, this is fine since trojan will not
                            // need them after this strong group is discovered
                            const idx_lookup = low_links;
                            for (stack.items[i..], 0..) |si, j| {
                                idx_lookup[si] = @intCast(j);
                            }

                            // NOTE: we basically convert this to a DAG this way
                            for (stack.items[i..]) |si| {
                                const sm = &self.syms.items[si];
                                for (self.relocs.items[sm.reloc_offset..][0..sm.reloc_count]) |*rel| {
                                    const sidx = @intFromEnum(rel.target);
                                    if (strong_groups[sidx] == strong_group_meta.items.len) {
                                        rel.target = @enumFromInt(strong_group_ref_flag | idx_lookup[sidx]);
                                    }
                                }
                            }

                            try strong_group_meta.append(
                                tmp.arena.allocator(),
                                tmp.arena.dupe(u32, stack.items[i..]),
                            );
                            stack.items.len = i;
                        }
                    }
                    _ = recursion_stack.pop();
                    continue;
                }

                if (sym.kind == .invalid) {
                    utils.panic("{} {}\n", .{ frame.node, sym });
                }
                const next_node = @intFromEnum(self.relocs.items[sym.reloc_offset + frame.dep_idx].target);
                frame.dep_idx += 1;

                indexes[frame.node].self_recursive = indexes[frame.node].self_recursive or
                    next_node == frame.node;

                if (indexes[next_node] == unvisited) {
                    try recursion_stack.append(tmp.arena.allocator(), .{ .node = next_node });
                    continue; // we do not sync low_link here, instead when we pop the frame
                }

                if (indexes[next_node].in_stack) {
                    low_links[frame.node] = @min(low_links[frame.node], low_links[next_node]);
                }
            }
        }

        const InverseSym = struct {
            dependants_offset: u32 = undefined,
            dependants_count: u16 = 0,
            dependants_cap: u16 = 0,
            done_relocs: u16 = 0,
            dag_edge_cound: u16 = 0,
        };

        const isims = tmp.arena.alloc(InverseSym, self.syms.items.len);
        @memset(isims, .{});

        for (self.relocs.items) |rel| {
            if (@intFromEnum(rel.target) & strong_group_ref_flag != 0) continue;
            isims[@intFromEnum(rel.target)].dependants_cap += 1;
        }

        var cursor: u32 = 0;
        for (isims) |*isim| {
            isim.dependants_offset = cursor;
            cursor += isim.dependants_cap;
        }

        const RevReloc = struct {
            dep: SymIdx,
            reloc_idx: u32,
        };

        const rev_relocs = tmp.arena.alloc(RevReloc, self.relocs.items.len);
        for (self.syms.items, 0..) |sym, i| {
            if (sym.kind == .invalid) continue;
            for (self.relocs.items[sym.reloc_offset..][0..sym.reloc_count], 0..) |*rel, j| {
                if (@intFromEnum(rel.target) & strong_group_ref_flag != 0) {
                    isims[i].dag_edge_cound += 1;
                    continue;
                }

                const dst = &isims[@intFromEnum(rel.target)];
                std.debug.assert(dst.dependants_count < dst.dependants_cap);
                rev_relocs[dst.dependants_offset + dst.dependants_count] = .{
                    .dep = @enumFromInt(i),
                    .reloc_idx = @intCast(j),
                };
                dst.dependants_count += 1;
            }
        }

        var dedup_map = std.HashMapUnmanaged(
            SymIdx,
            void,
            *Data,
            std.hash_map.default_max_load_percentage,
        ){};
        try dedup_map.ensureTotalCapacityContext(tmp.arena.allocator(), @intCast(isims.len), self);

        var worklist = tmp.arena.makeArrayList(SymIdx, isims.len);
        for (0..isims.len, self.syms.items, isims) |i, s, is| {
            if (s.kind != .invalid and s.readonly and s.linkage != .imported and s.reloc_count == is.dag_edge_cound) {
                worklist.appendAssumeCapacity(@enumFromInt(i));
            }
        }

        while (worklist.pop()) |n| {
            const entry = dedup_map.getOrPutAssumeCapacityContext(n, self);

            const isim = &isims[@intFromEnum(n)];
            for (rev_relocs[isim.dependants_offset..][0..isim.dependants_count]) |rel| {
                const sym = &self.syms.items[@intFromEnum(rel.dep)];
                self.relocs.items[sym.reloc_offset + rel.reloc_idx].target = entry.key_ptr.*;
                const oisim = &isims[@intFromEnum(rel.dep)];
                oisim.done_relocs += 1;
                if (oisim.done_relocs == oisim.dependants_count and sym.readonly) {
                    std.debug.assert(sym.kind != .invalid);
                    worklist.appendAssumeCapacity(rel.dep);
                }
            }
        }

        // NOTE: this restores the strong group edges from the normalized form
        for (strong_group_meta.items) |members| {
            for (members) |member| {
                const sym = &self.syms.items[member];
                for (self.relocs.items[sym.reloc_offset..][0..sym.reloc_count]) |*rel| {
                    if (@intFromEnum(rel.target) & strong_group_ref_flag == 0) continue;
                    rel.target = @enumFromInt(members[@intFromEnum(rel.target) & ~strong_group_ref_flag]);
                }
            }
        }

        // NOTE: dead code elimination will handle the rest
    }

    pub fn hash(self: *Data, v: SymIdx) u64 {
        var hasher = std.hash.Wyhash.init(0);

        const vi = @intFromEnum(v);

        const vs = &self.syms.items[vi];
        std.debug.assert(vs.readonly and vs.linkage != .imported);

        hasher.update(std.mem.asBytes(&vs.kind));
        hasher.update(self.code.items[vs.offset..][0..vs.size]);
        hasher.update(@ptrCast(self.relocs.items[vs.reloc_offset..][0..vs.reloc_count]));

        return hasher.final();
    }

    pub fn eql(self: *Data, a: SymIdx, b: SymIdx) bool {
        const as = &self.syms.items[@intFromEnum(a)];
        const bs = &self.syms.items[@intFromEnum(b)];
        std.debug.assert(as.readonly and as.linkage != .imported);
        std.debug.assert(bs.readonly and as.linkage != .imported);
        return as.kind == bs.kind and std.mem.eql(
            u8,
            self.code.items[as.offset..][0..as.size],
            self.code.items[bs.offset..][0..bs.size],
        ) and std.mem.eql(
            u8,
            @ptrCast(self.relocs.items[as.reloc_offset..][0..as.reloc_count]),
            @ptrCast(self.relocs.items[bs.reloc_offset..][0..bs.reloc_count]),
        );
    }

    pub fn eliminateDeadCode(self: *Data) void {
        errdefer unreachable;
        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        var visited_syms = try Set.initEmpty(tmp.arena.allocator(), self.syms.items.len);
        var frontier = std.ArrayList(SymIdx).empty;

        for (self.syms.items, 0..) |sym, i| {
            if (sym.linkage == .exported) {
                visited_syms.set(i);
                try frontier.append(tmp.arena.allocator(), @enumFromInt(i));
            }
        }

        while (frontier.pop()) |fid| {
            const f = &self.syms.items[@intFromEnum(fid)];

            std.debug.assert(f.kind != .invalid);

            for (self.relocs.items[f.reloc_offset..][0..f.reloc_count]) |rel| {
                if (visited_syms.isSet(@intFromEnum(rel.target))) continue;
                visited_syms.set(@intFromEnum(rel.target));
                try frontier.append(tmp.arena.allocator(), rel.target);
            }
        }

        for (self.syms.items, 0..) |*sym, i| {
            if (!visited_syms.isSet(i)) {
                sym.kind = .invalid;
            }
        }
    }
};

pub const RunEnv = struct {
    name: []const u8,
    code: []const u8,
    output: ?*std.Io.Writer = null,
    logs: ?*std.Io.Writer = null,
    colors: std.io.tty.Config = .no_color,
};

pub const DataOptions = struct {
    id: u32,
    name: []const u8 = &.{},
    relocs: []const Reloc = &.{},
    alignment: u64 = 1,
    value: ValueSpec,
    readonly: bool,
    thread_local: bool,
    uuid: Data.UUID,

    pub const Reloc = packed struct(u64) {
        target: u32,
        offset: u31,
        is_func: bool = false,
    };

    pub const ValueSpec = union(enum) { init: []const u8, uninit: usize };
};

pub const OptOptions = struct {
    mode: Mode = .debug,
    arena: ?*utils.Arena = null,
    error_buf: ?*std.ArrayList(static_anal.Error) = null,

    pub const Mode = enum { release, debug };

    pub fn shouldDefer(
        self: @This(),
        id: u32,
        comptime Backend: type,
        func: *graph.Func(Backend),
        backend: *Backend,
    ) bool {
        switch (self.mode) {
            .release => {
                backend.mach.out.setInlineFunc(backend.gpa, Backend, func, id);
                return true;
            },
            .debug => {
                self.optimizeDebug(Backend, backend, func);
                return false;
            },
        }
    }

    pub fn idealizeDead(comptime Backend: type, ctx: anytype, func: *graph.Func(Backend)) void {
        const Func = graph.Func(Backend);

        std.debug.assert(!func.start.isDead());
        func.iterPeeps(ctx, Func.idealizeDead);
        std.debug.assert(!func.start.isDead());
    }

    pub fn idealizeGeneric(comptime Backend: type, ctx: anytype, func: *graph.Func(Backend), minimal_only: bool) void {
        const Func = graph.Func(Backend);

        std.debug.assert(!func.start.isDead());

        if (minimal_only) {
            func.iterPeeps(ctx, Backend.idealize);
        } else {
            func.iterPeeps(ctx, Func.idealize);
        }
    }

    pub fn idealizeMach(comptime Backend: type, ctx: anytype, func: *graph.Func(Backend)) void {
        if (@hasDecl(Backend, "idealizeMach")) {
            func.iterPeeps(ctx, Backend.idealizeMach);
        }
    }

    pub fn doGcm(comptime Backend: type, func: *graph.Func(Backend)) void {
        func.gcm.buildCfg();
    }

    pub fn doStaticAnal(
        self: OptOptions,
        comptime Backend: type,
        func: *graph.Func(Backend),
    ) void {
        func.static_anal.analize(self.arena.?, self.error_buf.?);
    }

    pub fn doMem2Reg(comptime Backend: type, func: *graph.Func(Backend)) void {
        func.mem2reg.run();
    }

    pub fn doAliasAnal(comptime Backend: type, func: *graph.Func(Backend)) void {
        if (0 == 1) func.alias_anal.run();
    }

    pub fn optimizeRelease(self: OptOptions, comptime Backend: type, ctx: anytype, func: *graph.Func(Backend)) void {
        idealizeDead(Backend, ctx, func);
        doMem2Reg(Backend, func);
        idealizeGeneric(Backend, ctx, func, false);
        idealizeMach(Backend, ctx, func);
        doGcm(Backend, func);
        if (self.error_buf != null) {
            self.doStaticAnal(Backend, func);
        }
    }

    pub fn optimizeDebug(self: OptOptions, comptime Backend: type, ctx: anytype, func: *graph.Func(Backend)) void {
        idealizeDead(Backend, ctx, func);
        idealizeGeneric(Backend, ctx, func, true);
        idealizeMach(Backend, ctx, func);
        doGcm(Backend, func);
        if (self.error_buf != null) {
            self.doStaticAnal(Backend, func);
        }
    }

    pub fn finalizeRelease(
        self: OptOptions,
        comptime Backend: type,
        backend: *Backend,
        opts: FinalizeOptionsInterface,
    ) void {
        errdefer unreachable;

        var metrics = utils.TimeMetrics(enum {
            regalloc,
            mem2reg,
            generic,
            mach,
            gcm,
            dead,
            static_anal,
            dedup,
            elim,
        }).init();

        var tmp = utils.Arena.scrath(self.arena);
        defer tmp.deinit();

        const bout: *Data = &backend.mach.out;

        // do the exhausitve optimization pass with inlining, this should
        // hanlde stacked inlines as well
        //

        // might be faster like this

        const funcs: []graph.Func(Backend) = @ptrCast(bout.inline_funcs.items);

        var emit_waste: usize = 0;
        var dead_waste: usize = 0;
        var mem2reg_waste: usize = 0;
        var generic_waste: usize = 0;
        var mach_waste: usize = 0;
        var gcm_waste: usize = 0;
        var total_waste: usize = 0;
        var regalloc = root.backend.Regalloc{};

        const Ctx = struct {
            stage_1_queue: lane.FixedQueue = .{},
            stage_2_queue: lane.FixedQueue = .{},
            stage_3_queue: lane.FixedQueue = .{},
            stage_4_queue: lane.FixedQueue = .{},

            funcs: []FuncMeta,

            code_indices: []u32,
            reloc_indices: []u32,
            line_info_indices: []u32,
            line_info_relocs_indices: []u32,

            final_out: Data = undefined,

            // TODO: we can save 4 bytes here
            const FuncMeta = struct {
                backedge: Data.SymIdx,
                thread: u32,
                index: Data.SymIdx,
                reg_alloc_results: []u16,
            };
        };

        var ctx: *Ctx = undefined;
        if (lane.isRoot()) {
            ctx = tmp.arena.create(Ctx);
            ctx.* = Ctx{
                .funcs = tmp.arena.alloc(Ctx.FuncMeta, bout.inline_funcs.items.len),
                .code_indices = tmp.arena.alloc(u32, lane.count()),
                .reloc_indices = tmp.arena.alloc(u32, lane.count()),
                .line_info_indices = tmp.arena.alloc(u32, lane.count()),
                .line_info_relocs_indices = tmp.arena.alloc(u32, lane.count()),
            };

            for (bout.syms.items, 0..) |sym, i| {
                if (sym.kind != .func) continue;
                ctx.funcs[sym.inline_func].backedge = @enumFromInt(i);
            }
        }
        lane.broadcast(&ctx, .{});

        for (bout.syms.items) |sym| {
            std.debug.assert(!sym.is_inline); // TODO
        }

        var arena = utils.Arena.init(1024 * 1024 * 1024);

        while (ctx.stage_2_queue.next(funcs.len)) |i| {
            const sym = &funcs[i];

            sym.arena.child_allocator = arena.allocator();

            emit_waste += sym.waste;

            var dead = metrics.begin(.dead);
            idealizeDead(Backend, backend, sym);
            dead.end();

            dead_waste += sym.waste;

            var mem2reg = metrics.begin(.mem2reg);
            doMem2Reg(Backend, sym);
            mem2reg.end();

            mem2reg_waste += sym.waste;
        }

        lane.sync(.{});

        while (ctx.stage_2_queue.next(funcs.len)) |i| {
            const sym = &funcs[i];
            sym.arena.child_allocator = arena.allocator();

            var generic = metrics.begin(.generic);
            idealizeGeneric(Backend, backend, sym, false);
            generic.end();

            doAliasAnal(Backend, sym);

            generic_waste += sym.waste;
        }

        lane.sync(.{});

        while (ctx.stage_3_queue.next(funcs.len)) |i| {
            const sym = &funcs[i];
            const res = &ctx.funcs[i].reg_alloc_results;

            sym.arena.child_allocator = arena.allocator();

            var mach = metrics.begin(.mach);
            idealizeMach(Backend, backend, sym);
            mach.end();

            mach_waste += sym.waste;

            var gcm = metrics.begin(.gcm);
            doGcm(Backend, sym);
            gcm.end();

            gcm_waste += sym.waste;
            if (self.error_buf != null) {
                var static_anal_met = metrics.begin(.static_anal);
                self.doStaticAnal(Backend, sym);
                static_anal_met.end();
            }

            var regalloc_met = metrics.begin(.regalloc);
            res.* = regalloc.ralloc(Backend, @ptrCast(sym));
            regalloc_met.end();

            total_waste += sym.waste;
        }

        if (lane.isRoot()) {
            ctx.final_out = backend.mach.out;
            backend.mach.out = .{};

            if (@hasDecl(Backend, "preEmmisionHook")) {
                for (opts.others) |other| {
                    Backend.preEmmisionHook(@ptrCast(other), &ctx.final_out);
                }
            }
        }

        lane.sync(.{});

        const local = opts.others[lane.index()];
        local.out.reset();

        while (ctx.stage_4_queue.next(funcs.len)) |i| {
            const func = &funcs[i];

            var index: Data.DeferCtx = .{ .root_sym = ctx.funcs[i].backedge };

            local.emitFunc(@ptrCast(func), .{
                .name = "",
                .id = .{ .sym = &index },
                .linkage = .local,
                .is_inline = false,
                .optimizations = .{ .allocs = ctx.funcs[i].reg_alloc_results },
                .builtins = opts.builtins,
                .files = opts.files,
                .uuid = @splat(0),
            });

            ctx.funcs[i].index = index.sym_slot;
            ctx.funcs[i].thread = lane.index();
        }

        lane.sync(.{});

        //var code_cursor: u32 = ctx.final_out.code.items.len;
        //_ = code_cursor; // autofix
        //var relocs_cursor: u32 = ctx.final_out.relocs.items.len;
        //_ = relocs_cursor; // autofix
        //var li_cursor: u32 = ctx.final_out.li.items.len;
        //_ = li_cursor; // autofix
        //var li_relocs_cursor: u32 = ctx.final_out.li_relocs.items.len;
        //_ = li_relocs_cursor; // autofix

        //lane.sync(.{});

        //if (lane.isRoot()) {
        //    var total_code: u32 = ctx.final_out.code.items.len;
        //    var total_relocs: u32 = ctx.final_out.relocs.items.len;
        //    var total_li: u32 = ctx.final_out.li.items.len;
        //    var total_li_relocs: u32 = ctx.final_out.li_relocs.items.len;

        //    for (opts.others) |other| {
        //        ctx.code_indices[other.out.code.items.len] = total_code;
        //        ctx.reloc_indices[other.out.relocs.items.len] = total_relocs;
        //        ctx.li_indices[other.out.li.items.len] = total_li;
        //        ctx.li_relocs_indices[other.out.li_relocs.items.len] = total_li_relocs;

        //        total_code += @intCast(other.out.code.items.len);
        //        total_relocs += @intCast(other.out.relocs.items.len);
        //        total_li += @intCast(other.out.li.items.len);
        //        total_li_relocs += @intCast(other.out.li_relocs.items.len);
        //    }

        //    ctx.final_out.code.resize(backend.gpa, total_code);
        //    ctx.final_out.relocs.resize(backend.gpa, total_relocs);
        //    ctx.final_out.line_info.resize(backend.gpa, total_li);
        //    ctx.final_out.line_info_relocs.resize(backend.gpa, total_li_relocs);
        //}

        if (lane.isRoot()) {
            if (@hasDecl(Backend, "preLinkHook")) {
                for (opts.others) |other| {
                    Backend.preLinkHook(@ptrCast(other), &ctx.final_out);
                }
            }

            var total_code: usize = 0;
            var total_code_relocs: usize = 0;
            var total_li: usize = 0;
            var total_li_relocs: usize = 0;
            for (opts.others) |other| {
                total_code += other.out.code.items.len;
                total_code_relocs += other.out.relocs.items.len;
                total_li += other.out.line_info.items.len;
                total_li_relocs += other.out.line_info_relocs.items.len;
            }

            try ctx.final_out.code.ensureUnusedCapacity(backend.gpa, total_code);
            try ctx.final_out.relocs.ensureUnusedCapacity(backend.gpa, total_code_relocs);
            try ctx.final_out.line_info.ensureUnusedCapacity(backend.gpa, total_li);
            try ctx.final_out.line_info_relocs.ensureUnusedCapacity(backend.gpa, total_li_relocs);

            for (ctx.final_out.syms.items) |*dsym| {
                if (dsym.kind != .func) continue;
                const meta = ctx.funcs[dsym.inline_func];
                const sout = &opts.others[meta.thread].out;
                const ssym = sout.syms.items[@intFromEnum(meta.index)];

                dsym.offset = @intCast(ctx.final_out.code.items.len);
                dsym.reloc_offset = @intCast(ctx.final_out.relocs.items.len);
                dsym.stack_size = ssym.stack_size;

                ctx.final_out.code.appendSliceAssumeCapacity(
                    sout.code.items[ssym.offset..][0..ssym.size],
                );

                ctx.final_out.relocs.appendSliceAssumeCapacity(
                    sout.relocs.items[ssym.reloc_offset..][0..ssym.reloc_count],
                );

                dsym.size = ssym.size;
                dsym.reloc_count = ssym.reloc_count;
            }

            for (opts.others) |other| {
                for (other.out.line_info_relocs.items) |*lr| {
                    lr.offset += @intCast(ctx.final_out.line_info.items.len);
                }
                ctx.final_out.line_info.appendSliceAssumeCapacity(other.out.line_info.items);
                ctx.final_out.line_info_relocs.appendSliceAssumeCapacity(other.out.line_info_relocs.items);
            }

            backend.mach.out.deinit(backend.gpa);
            backend.mach.out = ctx.final_out;

            if (opts.logs) |d| {
                try d.writeAll("backend:\n");

                inline for (std.meta.fields(Data)[3..]) |f| {
                    try d.print("  {s:<12}: {}\n", .{ f.name, @field(bout, f.name).items.len });
                }

                try d.print("  emit waste   :  {}\n", .{emit_waste});
                try d.print("  dead waste   : +{}\n", .{dead_waste - emit_waste});
                try d.print("  mem2reg waste: +{}\n", .{mem2reg_waste - dead_waste});
                try d.print("  generic waste: +{}\n", .{generic_waste - mem2reg_waste});
                try d.print("  mach waste   : +{}\n", .{mach_waste -| generic_waste});
                try d.print("  gcm waste    : +{}\n", .{gcm_waste -| mach_waste});
                try d.print("  waste        : +{}\n", .{total_waste -| gcm_waste});
            }

            var dedup = metrics.begin(.dedup);
            bout.deduplicate();
            dedup.end();

            var elim = metrics.begin(.elim);
            bout.eliminateDeadCode();
            elim.end();

            if (opts.logs) |d| {
                var alive_syms: usize = 0;
                var alive_code: usize = 0;
                for (bout.syms.items) |s| {
                    if (s.kind != .invalid) {
                        alive_syms += 1;
                        alive_code += s.size;
                    }
                }

                try d.print("  dead syms   : {}\n", .{bout.syms.items.len - alive_syms});
                try d.print("  dead code   : {}\n", .{bout.code.items.len - alive_code});

                try d.writeAll("regalloc:\n");
                inline for (std.meta.fields(@TypeOf(regalloc))) |f| {
                    try d.print("  {s:<12}: {}\n", .{ f.name, @field(regalloc, f.name) });
                }

                metrics.logStats(d);
            }
        }
    }

    pub fn finalize(
        self: OptOptions,
        comptime Backend: type,
        backend: *Backend,
        opts: FinalizeOptionsInterface,
    ) bool {
        if (self.mode == .release) {
            finalizeRelease(self, Backend, backend, opts);
        } else {
            if (lane.isRoot()) {
                if (@hasDecl(Backend, "preLinkHook"))
                    backend.preLinkHook(&backend.mach.out);
            }
        }

        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        var err = lane.share(tmp.arena, std.atomic.Value(bool).init(false));
        if (self.error_buf) |eb| if (eb.items.len != 0) {
            err.store(true, .unordered);
        };

        lane.sync(.{});
        const errored = err.raw;
        lane.sync(.{});

        return errored;
    }
};

pub const Builtins = struct {
    memcpy: u32 = std.math.maxInt(u32),
};

pub const EmitOptions = struct {
    id: Id,
    name: []const u8 = &.{},
    is_inline: bool,
    linkage: Data.Linkage,
    optimizations: Optimizations,
    special: ?Special = null,
    builtins: Builtins,
    files: []const utils.LineIndex = &.{},
    uuid: Data.UUID,

    pub const Id = union(enum) { arbitrary: u32, sym: *Data.DeferCtx };

    pub const Optimizations = union(enum) {
        opts: OptOptions,
        allocs: []const u16,
    };

    pub fn apply(
        self: EmitOptions,
        comptime Backend: type,
        func: *graph.Func(Backend),
        backend: *Backend,
    ) ?[]const u16 {
        switch (self.optimizations) {
            .opts => |pts| {
                backend.mach.out.projectSyms(backend.gpa, Backend, func);
                if (pts.shouldDefer(self.id.arbitrary, Backend, func, backend)) return null;
                return root.backend.Regalloc.rallocIgnoreStats(Backend, func);
            },
            .allocs => |pts| return pts,
        }
    }

    pub const Special = enum { entry, memcpy };
};

const Vidsibility = enum { local, exported, imported };

pub const DisasmOpts = struct {
    name: []const u8,
    bin: []const u8,
    out: ?*std.Io.Writer,
    colors: std.io.tty.Config = .no_color,

    pub fn print(self: DisasmOpts, comptime fmt: []const u8, args: anytype) void {
        if (self.colors == .no_color) {
            if (self.out) |o| o.print(fmt, args) catch unreachable;
        } else {
            std.debug.print(fmt, args);
        }
    }
};

pub const FinalizeOptionsInterface = struct {
    output_scratch: ?*utils.Arena = null,
    optimizations: OptOptions,
    builtins: Builtins,
    logs: ?*std.Io.Writer = null,
    files: []const utils.LineIndex,
    others: []*Machine,
};

pub const SupportedTarget = enum {
    @"hbvm-ableos",
    @"x86_64-windows",
    @"x86_64-linux",
    @"wasm-freestanding",
    null,

    pub fn fromStr(str: []const u8) ?SupportedTarget {
        inline for (std.meta.fields(SupportedTarget)) |f| {
            if (std.mem.startsWith(u8, str, f.name)) {
                return @field(SupportedTarget, f.name);
            }
        }

        return null;
    }

    pub fn toMachine(triple: SupportedTarget, scratch: *utils.Arena, gpa: std.mem.Allocator) *Machine {
        switch (triple) {
            .@"hbvm-ableos" => {
                const slot = scratch.create(root.hbvm.HbvmGen);
                slot.* = root.hbvm.HbvmGen{ .gpa = gpa };
                return &slot.mach;
            },
            .@"x86_64-windows" => {
                const slot = scratch.create(root.x86_64.X86_64Gen);
                slot.* = root.x86_64.X86_64Gen{ .gpa = gpa, .object_format = .coff };
                return &slot.mach;
            },
            .@"x86_64-linux" => {
                const slot = scratch.create(root.x86_64.X86_64Gen);
                slot.* = root.x86_64.X86_64Gen{ .gpa = gpa, .object_format = .elf };
                return &slot.mach;
            },
            .@"wasm-freestanding" => {
                const slot = scratch.create(root.wasm.WasmGen);
                slot.* = root.wasm.WasmGen{ .gpa = gpa };
                return &slot.mach;
            },
            .null => {
                const slot = scratch.create(Null);
                slot.* = Null{};
                return &slot.mach;
            },
        }
    }

    pub fn toCallConv(triple: SupportedTarget) graph.CallConv {
        return switch (triple) {
            .@"hbvm-ableos" => .ablecall,
            .@"x86_64-windows" => .fastcall,
            .@"x86_64-linux" => .systemv,
            .@"wasm-freestanding" => .wasmcall,
            .null => .systemv,
        };
    }
};

pub fn init(comptime Type: type) Machine {
    const fns = struct {
        fn getSelf(self: *Machine) *Type {
            return @alignCast(@fieldParentPtr("mach", self));
        }
        fn emitFunc(self: *Machine, func: *BuilderFunc, opts: EmitOptions) void {
            const fnc: *graph.Func(Type) = @ptrCast(@alignCast(func));
            getSelf(self).emitFunc(fnc, opts);
        }
        fn emitData(self: *Machine, opts: DataOptions) void {
            getSelf(self).emitData(opts);
        }
        fn merge(self: *Machine, others: []*Machine) bool {
            std.debug.assert(@as(*anyopaque, getSelf(self)) == @as(*anyopaque, self));

            return if (@hasDecl(Type, "merge")) getSelf(self).merge(@ptrCast(others)) else false;
        }
        fn finalize(self: *Machine, opts: FinalizeOptions) void {
            return getSelf(self).finalize(opts);
        }
        fn disasm(self: *Machine, opts: DisasmOpts) void {
            return getSelf(self).disasm(opts);
        }
        fn run(self: *Machine, env: RunEnv) !usize {
            return getSelf(self).run(env);
        }
        fn deinit(self: *Machine) void {
            getSelf(self).deinit();
        }
    };

    return .{
        .out = .{},
        .vtable = comptime &VTable{
            .emitFunc = fns.emitFunc,
            .emitData = fns.emitData,
            .merge = fns.merge,
            .finalize = fns.finalize,
            .disasm = fns.disasm,
            .run = fns.run,
            .deinit = fns.deinit,
        },
    };
}

/// generate apropriate final output for a function
///
/// this also runs optimization passes, this assumes to be callef from a single
/// lane
pub fn emitFunc(self: *Machine, func: *BuilderFunc, opts: EmitOptions) void {
    self.vtable.emitFunc(self, func, opts);
}

/// generate apropriate final output for a data section
/// this assumes to be called from a single lane
pub fn emitData(self: *Machine, opts: DataOptions) void {
    self.vtable.emitData(self, opts);
}

pub const FinalizeOptions = struct {
    output: ?*std.io.Writer,
    interface: FinalizeOptionsInterface,
};

/// package the final output (.eg object file)
/// this function should also restart the state for next emmiting
pub fn finalize(self: *Machine, out: ?*std.io.Writer, opts: FinalizeOptionsInterface) void {
    var ots = opts;
    var machines: [1]*Machine = .{self};
    if (ots.others.len == 0) ots.others = &machines;

    return self.vtable.finalize(self, .{ .output = out, .interface = ots });
}

/// output the final code into a byte array, for testing purposes
pub fn finalizeBytes(self: *Machine, gpa: std.mem.Allocator, opts: FinalizeOptionsInterface) std.ArrayList(u8) {
    var out = std.Io.Writer.Allocating.init(gpa);
    self.finalize(&out.writer, opts);
    return out.toArrayList();
}

/// visualize already compiled code, its best to include different colors
/// for registers for better readability, for testing purposes
pub fn disasm(self: *Machine, opts: DisasmOpts) void {
    self.vtable.disasm(self, opts);
}

/// run the compiled code, for testing purposes
pub fn run(self: *Machine, env: RunEnv) !usize {
    return self.vtable.run(self, env);
}

pub fn mergeOut(
    self: *Machine,
    others: []*Machine,
    gpa: std.mem.Allocator,
    opts: OptOptions.Mode,
) void {
    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const Ctx = struct {
        total_syms: usize = 0,
        projections: [][]Data.SymIdx,
        total_inline_funcs: usize = 0,

        unique_syms: usize = 0,

        unique_code_indices: []usize,
        unique_relocs_indices: []usize,
        unique_syms_indices: []usize,
        unique_inline_funcs_indices: []usize,
        unique_name_indices: []usize,
        line_info_indices: []usize,
        line_info_relocs_indices: []usize,

        out: Data = .{},
    };

    var ctx: *Ctx = undefined;
    if (lane.isRoot()) {
        var total_syms: usize = 0;
        var total_inline_funcs: usize = 0;
        const projections = tmp.arena.alloc([]Data.SymIdx, others.len);
        for (others, projections) |other, *p| {
            p.* = tmp.arena.alloc(Data.SymIdx, other.out.syms.items.len);
            total_syms += other.out.syms.items.len;
            total_inline_funcs += other.out.inline_funcs.items.len;
        }

        const Hasher = struct {
            pub fn hash(_: @This(), key: Data.UUID) u64 {
                return key[0] ^ key[1];
            }

            pub fn eql(_: @This(), a: Data.UUID, b: Data.UUID) bool {
                return a[0] == b[0] and a[1] == b[1];
            }
        };

        var merge_map = std.HashMapUnmanaged(
            Data.UUID,
            Data.SymIdx,
            Hasher,
            std.hash_map.default_max_load_percentage,
        ).empty;
        try merge_map.ensureTotalCapacity(tmp.arena.allocator(), @intCast(total_syms));

        var unique_relocs: usize = 0;
        var unique_code: usize = 0;
        var unique_syms: usize = 0;
        var unique_inline_funcs: usize = 0;
        var unique_names: usize = 0;
        var line_info: usize = 0;
        var line_info_relocs: usize = 0;

        const unique_code_indices = tmp.arena.alloc(usize, lane.count());
        const unique_relocs_indices = tmp.arena.alloc(usize, lane.count());
        const unique_syms_indices = tmp.arena.alloc(usize, lane.count());
        const unique_inline_funcs_indices = tmp.arena.alloc(usize, lane.count());
        const unique_name_indices = tmp.arena.alloc(usize, lane.count());
        // NOTE: we dont put any effort into deduping the line info
        const line_info_indices = tmp.arena.alloc(usize, lane.count());
        const line_info_relocs_indices = tmp.arena.alloc(usize, lane.count());

        for (
            others,
            projections,
            0..,
        ) |other, local_projs, i| {
            const syms = other.out.syms.items;

            unique_code_indices[i] = unique_code;
            unique_relocs_indices[i] = unique_relocs;
            unique_syms_indices[i] = unique_syms;
            unique_inline_funcs_indices[i] = unique_inline_funcs;
            unique_name_indices[i] = unique_names;
            line_info_indices[i] = line_info;
            line_info_relocs_indices[i] = line_info_relocs;

            for (local_projs, syms) |*proj, *sym| {
                if (sym.kind == .invalid) continue;

                const entry = merge_map.getOrPutAssumeCapacity(sym.uuid);
                if (entry.found_existing) {
                    sym.kind = .invalid;
                } else {
                    entry.value_ptr.* = @enumFromInt(unique_syms);
                    unique_syms += 1;

                    unique_relocs += sym.reloc_count;
                    unique_code += sym.size;
                    unique_names += other.out.lookupName(sym.name).len + 1;

                    if (sym.kind == .func and opts == .release) {
                        std.debug.assert(sym.inline_func != Data.Sym.no_inline_func);

                        unique_inline_funcs += 1;
                    }
                }
                std.debug.assert(@intFromEnum(entry.value_ptr.*) < unique_syms);
                proj.* = entry.value_ptr.*;
            }
            line_info += other.out.line_info.items.len;
            line_info_relocs += other.out.line_info_relocs.items.len;
        }

        ctx = tmp.arena.create(Ctx);
        ctx.* = .{
            .total_syms = total_syms,
            .projections = projections,
            .total_inline_funcs = total_inline_funcs,
            .unique_syms = unique_syms,
            .unique_code_indices = unique_code_indices,
            .unique_relocs_indices = unique_relocs_indices,
            .unique_syms_indices = unique_syms_indices,
            .unique_inline_funcs_indices = unique_inline_funcs_indices,
            .unique_name_indices = unique_name_indices,
            .line_info_indices = line_info_indices,
            .line_info_relocs_indices = line_info_relocs_indices,
        };

        try ctx.out.syms.resize(gpa, unique_syms);
        try ctx.out.relocs.resize(gpa, unique_relocs);
        try ctx.out.code.resize(gpa, unique_code);
        try ctx.out.inline_funcs.resize(gpa, unique_inline_funcs);
        try ctx.out.names.resize(gpa, unique_names);
        try ctx.out.line_info.resize(gpa, line_info);
        try ctx.out.line_info_relocs.resize(gpa, line_info_relocs);
    }
    lane.broadcast(&ctx, .{});

    const projections = ctx.projections;
    const unique_syms = ctx.total_syms;

    const other = others[lane.index()];
    const local_projs = projections[lane.index()];

    for (other.out.remote_funcs.items) |rf| {
        const local_sym = other.out.funcs.items[rf.local_sym];
        if (other.out.syms.items[@intFromEnum(local_sym)].kind == .invalid)
            continue;
        const remote_sym = others[rf.thread]
            .out.funcs.items[rf.remote_sym];
        const local_idx = local_projs[@intFromEnum(local_sym)];
        // NOTE: this avoids data races
        projections[rf.thread][@intFromEnum(remote_sym)] = local_idx;
    }

    lane.sync(.{});

    const syms = other.out.syms.items;
    const relocs = other.out.relocs.items;

    for (syms) |*sym| {
        if (sym.kind == .invalid) continue;

        if (opts == .release and sym.kind == .func) {
            std.debug.assert(sym.size == 0);
            std.debug.assert(sym.reloc_count == 0);
            std.debug.assert(sym.inline_func != Data.Sym.no_inline_func);

            const inline_func = &other.out.inline_funcs.items[sym.inline_func];
            for (inline_func.getSyms().outputs()) |s| {
                switch (s.get().extra2()) {
                    inline .FuncAddr, .Call, .GlobalAddr => |extra| {
                        extra.id = @intFromEnum(local_projs[extra.id]);
                    },
                    else => utils.panic("{f} has no sym", .{s}),
                }
            }
        } else {
            for (relocs[sym.reloc_offset..][0..sym.reloc_count]) |*rel| {
                rel.target = local_projs[@intFromEnum(rel.target)];
                if (@intFromEnum(rel.target) >= unique_syms) {
                    utils.panic("invalid relocation target {x}", .{rel.target});
                }
            }
        }
    }

    lane.sync(.{});

    const code = other.out.code.items;

    var sym_cursor: usize = ctx.unique_syms_indices[lane.index()];
    var code_cursor: usize = ctx.unique_code_indices[lane.index()];
    var reloc_cursor: usize = ctx.unique_relocs_indices[lane.index()];
    var inline_func_cursor: usize = ctx.unique_inline_funcs_indices[lane.index()];
    var name_cursor: usize = ctx.unique_name_indices[lane.index()];

    for (syms) |sym| {
        if (sym.kind == .invalid) continue;

        const name = other.out.lookupName(sym.name);

        var new_sym = sym;
        new_sym.offset = @intCast(code_cursor);
        new_sym.reloc_offset = @intCast(reloc_cursor);
        new_sym.name = @intCast(name_cursor);

        @memcpy(ctx.out.names.items[name_cursor..][0..name.len], name);
        ctx.out.names.items[name_cursor + name.len] = 0;
        name_cursor += name.len + 1;

        @memcpy(
            ctx.out.code.items[code_cursor..][0..sym.size],
            code[sym.offset..][0..sym.size],
        );
        code_cursor += sym.size;

        @memcpy(
            ctx.out.relocs.items[reloc_cursor..][0..sym.reloc_count],
            relocs[sym.reloc_offset..][0..sym.reloc_count],
        );
        reloc_cursor += sym.reloc_count;

        if (sym.kind == .func and opts == .release) {
            std.debug.assert(sym.inline_func != Data.Sym.no_inline_func);
            ctx.out.inline_funcs.items[inline_func_cursor] =
                other.out.inline_funcs.items[sym.inline_func];
            new_sym.inline_func = @intCast(inline_func_cursor);
            inline_func_cursor += 1;
        }

        ctx.out.syms.items[sym_cursor] = new_sym;
        sym_cursor += 1;
    }

    const line_info_offset: usize = ctx.line_info_indices[lane.index()];
    const line_info_reloc_offset: usize = ctx.line_info_relocs_indices[lane.index()];

    @memcpy(
        ctx.out.line_info.items[line_info_offset..][0..other.out.line_info.items.len],
        other.out.line_info.items,
    );

    for (other.out.line_info_relocs.items) |*reloc| {
        reloc.offset += @intCast(line_info_offset);
        reloc.target = local_projs[@intFromEnum(reloc.target)];
    }
    @memcpy(
        ctx.out.line_info_relocs.items[line_info_reloc_offset..][0..other.out.line_info_relocs.items.len],
        other.out.line_info_relocs.items,
    );

    lane.sync(.{});

    if (lane.isRoot()) {
        ctx.out.files = self.out.files;
        self.out.deinit(gpa);
        self.out = ctx.out;
    }

    lane.sync(.{});
}

/// frees the internal resources
pub fn deinit(self: *Machine) void {
    self.vtable.deinit(self);
}
