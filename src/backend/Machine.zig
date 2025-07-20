data: *anyopaque,
_emitFunc: *const fn (self: *anyopaque, func: *BuilderFunc, opts: EmitOptions) void,
_emitData: *const fn (self: *anyopaque, opts: DataOptions) void,
_finalize: *const fn (self: *anyopaque, opts: FinalizeOptions) void,
_disasm: *const fn (self: *anyopaque, opts: DisasmOpts) void,
_run: *const fn (self: *anyopaque, env: RunEnv) anyerror!usize,
_deinit: *const fn (self: *anyopaque) void,

const std = @import("std");
const graph = @import("graph.zig");
const static_anal = @import("static_anal.zig");
const Builder = @import("Builder.zig");
const BuilderFunc = graph.Func(Builder);
const Machine = @This();
const utils = @import("../utils.zig");
const Set = std.DynamicBitSetUnmanaged;

pub const Null = struct {
    const Func = graph.Func(Null);

    pub const classes = enum {};

    pub const i_know_the_api = {};

    comptime {
        var s = Null{};
        _ = init(&s);
    }

    pub fn emitFunc(_: *@This(), _: *Func, _: EmitOptions) void {}
    pub fn emitData(_: *@This(), _: DataOptions) void {}
    pub fn finalize(_: *@This(), _: FinalizeOptions) void {}
    pub fn disasm(_: *@This(), _: DisasmOpts) void {}
    pub fn run(_: *@This(), _: RunEnv) !usize {
        return 0;
    }
    pub fn deinit(_: *@This()) void {}
};

const InlinFunc = graph.Func(Builder);

pub const Data = struct {
    declaring_sym: ?SymIdx = null,
    funcs: std.ArrayListUnmanaged(SymIdx) = .empty,
    globals: std.ArrayListUnmanaged(SymIdx) = .empty,
    syms: std.ArrayListUnmanaged(Sym) = .empty,
    names: std.ArrayListUnmanaged(u8) = .empty,
    code: std.ArrayListUnmanaged(u8) = .empty,
    relocs: std.ArrayListUnmanaged(Reloc) = .empty,
    inline_funcs: std.ArrayListUnmanaged(InlinFunc) = .empty,

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

        pub const no_inline_func = std.math.maxInt(u32);
    };

    pub const Kind = enum {
        func,
        data,
        prealloc,

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
        addend: i16,
        slot_size: u16,
    };

    pub const SymIdx = enum(u32) { invalid = std.math.maxInt(u32), _ };

    pub fn setInlineFunc(self: *Data, gpa: std.mem.Allocator, comptime Node: type, func: *graph.Func(Node), to: u32) void {
        errdefer unreachable;

        self.syms.items[@intFromEnum(self.funcs.items[to])].inline_func = @intCast(self.inline_funcs.items.len);
        try self.inline_funcs.append(gpa, @as(*InlinFunc, @ptrCast(func)).*);
        func.arena = .init(gpa);
    }

    pub fn getInlineFunc(self: *Data, comptime Backend: type, at: u32, force_inline: bool) ?*const graph.Func(Backend) {
        if (self.funcs.items.len <= at or self.funcs.items[at] == .invalid) return null;
        const sym = &self.syms.items[@intFromEnum(self.funcs.items[at])];
        if (!sym.is_inline and !force_inline) return null;
        return if (sym.inline_func != Sym.no_inline_func)
            @ptrCast(&self.inline_funcs.items[sym.inline_func])
        else
            null;
    }

    pub fn readFromSym(self: Data, id: u32, offset: i64, size: u64) ?union(enum) { value: i64, global: u32 } {
        if (self.globals.items.len <= id) return null;
        const sym = &self.syms.items[@intFromEnum(self.globals.items[id])];

        if (!sym.readonly) return null;

        var value: i64 = 0;

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

    pub fn addFuncReloc(self: *Data, gpa: std.mem.Allocator, target: u32, slot_size: u8, addend: i16, back_shift: u32) !void {
        return self.addReloc(gpa, try utils.ensureSlot(&self.funcs, gpa, target), slot_size, addend, back_shift);
    }

    pub fn addGlobalReloc(self: *Data, gpa: std.mem.Allocator, target: u32, slot_size: u8, addend: i16, back_shift: u32) !void {
        return self.addReloc(gpa, try utils.ensureSlot(&self.globals, gpa, target), slot_size, addend, back_shift);
    }

    pub fn addReloc(self: *Data, gpa: std.mem.Allocator, target: *SymIdx, slot_size: u8, addend: i16, back_shift: u32) !void {
        try self.relocs.append(gpa, .{
            .target = try self.declSym(gpa, target),
            .offset = @intCast(self.code.items.len -
                self.syms.items[@intFromEnum(self.declaring_sym.?)].offset -
                back_shift),
            .addend = addend,
            .slot_size = slot_size,
        });
    }

    pub fn deinit(self: *Data, gpa: std.mem.Allocator) void {
        inline for (std.meta.fields(Data)[2..]) |f| {
            @field(self, f.name).deinit(gpa);
        }
        self.* = undefined;
    }

    pub fn declGlobal(self: *Data, gpa: std.mem.Allocator, id: u32) !SymIdx {
        return self.declSym(gpa, try utils.ensureSlot(&self.globals, gpa, id));
    }

    pub fn declFunc(self: *Data, gpa: std.mem.Allocator, id: u32) !SymIdx {
        return self.declSym(gpa, try utils.ensureSlot(&self.funcs, gpa, id));
    }

    pub fn declSym(
        self: *Data,
        gpa: std.mem.Allocator,
        slot: *SymIdx,
    ) !SymIdx {
        if (slot.* == .invalid) {
            (try self.syms.addOne(gpa)).kind = .invalid;
            slot.* = @enumFromInt(self.syms.items.len - 1);
        }
        return slot.*;
    }

    pub fn importFunc(self: *Data, gpa: std.mem.Allocator, id: u32, name: []const u8) !void {
        try self.importSym(gpa, try utils.ensureSlot(&self.funcs, gpa, id), name, .func);
    }

    pub fn importSym(
        self: *Data,
        gpa: std.mem.Allocator,
        sym: *SymIdx,
        name: []const u8,
        kind: Kind,
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
        };
        try self.names.appendSlice(gpa, name);
        try self.names.append(gpa, 0);
    }

    pub fn startDefineFunc(
        self: *Data,
        gpa: std.mem.Allocator,
        id: u32,
        name: []const u8,
        kind: Kind,
        linkage: Linkage,
        is_inline: bool,
    ) !void {
        std.debug.assert(id != std.math.maxInt(u32));
        const slot = try utils.ensureSlot(&self.funcs, gpa, id);
        try self.startDefineSym(
            gpa,
            slot,
            name,
            kind,
            linkage,
            true,
            is_inline,
        );
    }

    pub fn defineGlobal(
        self: *Data,
        gpa: std.mem.Allocator,
        id: u32,
        name: []const u8,
        kind: Kind,
        linkage: Linkage,
        data: []const u8,
        relocs: []const DataOptions.Reloc,
        readonly: bool,
    ) !void {
        // this is there to support N(1) reverse lookup form a memory offset
        // to global id
        try self.code.appendSlice(gpa, std.mem.asBytes(&id));

        try self.startDefineSym(
            gpa,
            try utils.ensureSlot(&self.globals, gpa, id),
            name,
            kind,
            linkage,
            readonly,
            false,
        );

        try self.code.appendSlice(gpa, data);
        for (relocs) |rel| {
            try self.addGlobalReloc(gpa, rel.target, 8, 0, @intCast(data.len - rel.offset));
            std.debug.assert(rel.target != id);
        }

        self.endDefineSym(self.globals.items[id]);
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
    ) !void {
        _ = try self.declSym(gpa, sym);

        std.debug.assert(self.declaring_sym == null);
        self.declaring_sym = sym.*;

        self.syms.items[@intFromEnum(sym.*)] = .{
            .name = @intCast(self.names.items.len),
            .offset = @intCast(self.code.items.len),
            .size = undefined,
            .reloc_offset = @intCast(self.relocs.items.len),
            .reloc_count = undefined,
            .kind = kind,
            .linkage = linkage,
            .readonly = readonly,
            .is_inline = is_inline,
        };
        try self.names.appendSlice(gpa, name);
        try self.names.append(gpa, 0);
    }

    pub fn endDefineFunc(self: *Data, id: u32) void {
        std.debug.assert(id != std.math.maxInt(u32));
        self.endDefineSym(self.funcs.items[id]);
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

        var strong_group_meta = std.ArrayListUnmanaged([]const u32){};

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

    pub fn elimitaneDeadCode(self: *Data) void {
        errdefer unreachable;
        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        const sym_to_idx = tmp.arena.alloc(u32, self.syms.items.len);

        for (self.funcs.items, 0..) |sym, i| {
            if (sym == .invalid) continue;
            sym_to_idx[@intFromEnum(sym)] = @intCast(i);
        }

        for (self.globals.items, 0..) |sym, i| {
            if (sym == .invalid) continue;
            sym_to_idx[@intFromEnum(sym)] = @intCast(i);
        }

        var visited_syms = try Set.initEmpty(tmp.arena.allocator(), self.syms.items.len);
        var frontier = std.ArrayList(SymIdx).init(tmp.arena.allocator());

        for (self.funcs.items) |fid| {
            if (fid == .invalid) continue;
            const f = &self.syms.items[@intFromEnum(fid)];
            if (f.kind == .func and f.linkage == .exported) {
                visited_syms.set(@intFromEnum(fid));
                try frontier.append(fid);
            }
        }

        for (self.globals.items) |gid| {
            if (gid == .invalid) continue;
            const g = &self.syms.items[@intFromEnum(gid)];
            if (g.kind == .data and g.linkage == .exported) {
                visited_syms.set(@intFromEnum(gid));
                try frontier.append(gid);
            }
        }

        while (frontier.pop()) |fid| {
            const f = &self.syms.items[@intFromEnum(fid)];

            for (self.relocs.items[f.reloc_offset..][0..f.reloc_count]) |rel| {
                if (visited_syms.isSet(@intFromEnum(rel.target))) continue;
                visited_syms.set(@intFromEnum(rel.target));
                try frontier.append(rel.target);
            }
        }

        for (sym_to_idx, self.syms.items, 0..) |idx, *sym, i| {
            if (!visited_syms.isSet(i)) {
                switch (sym.kind) {
                    .func => self.funcs.items[idx] = .invalid,
                    .data => self.globals.items[idx] = .invalid,
                    else => unreachable,
                }
                sym.kind = .invalid;
            }
        }
    }
};

pub const RunEnv = struct {
    name: []const u8,
    code: []const u8,
    output: std.io.AnyWriter = std.io.null_writer.any(),
    logs: std.io.AnyWriter = std.io.null_writer.any(),
    colors: std.io.tty.Config = .no_color,
};

pub const DataOptions = struct {
    id: u32,
    name: []const u8 = &.{},
    relocs: []const Reloc = &.{},
    value: ValueSpec,
    readonly: bool,

    pub const Reloc = struct {
        target: u32,
        offset: u32,
    };

    pub const ValueSpec = union(enum) { init: []const u8, uninit: usize };
};

pub const OptOptions = struct {
    do_dead_code_elimination: bool,
    do_inlining: bool,
    do_generic_peeps: bool,
    do_machine_peeps: bool,
    mem2reg: bool,
    do_gcm: bool,
    verbose: bool = false,
    do_uninit_analisys: bool,
    arena: ?*utils.Arena = null,
    error_buf: ?*std.ArrayListUnmanaged(static_anal.Error) = null,

    pub const all = @This(){
        .do_dead_code_elimination = true,
        .do_inlining = true,
        .do_generic_peeps = true,
        .do_machine_peeps = true,
        .mem2reg = true,
        .do_gcm = true,
        .do_uninit_analisys = true,
    };

    pub const none = @This(){
        .do_dead_code_elimination = true,
        .do_inlining = false,
        .mem2reg = false,
        .do_generic_peeps = false,
        .do_machine_peeps = true,
        .do_gcm = true,
        .do_uninit_analisys = false,
    };

    pub fn asPostInlining(self: @This()) @This() {
        std.debug.assert(self.do_inlining);
        var s = self;
        s.verbose = false;
        s.do_inlining = false;
        s.do_gcm = false;
        s.mem2reg = false;
        s.arena = null;
        s.error_buf = null;
        return s;
    }

    pub fn asPreInline(self: @This()) @This() {
        var s = self;
        s.verbose = false;
        s.do_machine_peeps = false;
        s.do_gcm = false;
        s.arena = null;
        s.error_buf = null;
        return s;
    }

    pub fn shouldDefer(
        self: @This(),
        id: u32,
        is_inline: bool,
        comptime B: type,
        func: *graph.Func(B),
        backend: *B,
    ) bool {
        if (self.do_inlining or is_inline) {
            self.asPreInline().execute(B, backend, func) catch unreachable;
            backend.out.setInlineFunc(backend.gpa.allocator(), B, func, id);
        }

        return self.do_inlining;
    }

    pub fn execute(self: @This(), comptime Backend: type, ctx: anytype, func: *graph.Func(Backend)) !void {
        const Func = graph.Func(Backend);
        const Node = Func.Node;

        std.debug.assert(func.start.id != std.math.maxInt(u16));

        if (self.do_dead_code_elimination) {
            func.iterPeeps(ctx, struct {
                fn wrap(cx: @TypeOf(ctx), fnc: *Func, nd: *Node, wl: *Func.WorkList) ?*Node {
                    return @TypeOf(func.*).idealizeDead(cx, fnc, nd, wl);
                }
            }.wrap);
            std.debug.assert(func.start.id != std.math.maxInt(u16));
        }

        if (self.mem2reg) {
            func.mem2reg.run();
        }

        if (self.do_generic_peeps) {
            func.iterPeeps(ctx, struct {
                fn wrap(cx: @TypeOf(ctx), fnc: *Func, nd: *Node, wl: *Func.WorkList) ?*Node {
                    return @TypeOf(func.*).idealize(cx, fnc, nd, wl);
                }
            }.wrap);
        } else if (@hasDecl(Backend, "idealize")) {
            func.iterPeeps(ctx, Backend.idealize);
        }

        if (self.do_machine_peeps and @hasDecl(Backend, "idealizeMach")) {
            func.iterPeeps(ctx, Backend.idealizeMach);
        }

        if (self.do_gcm) {
            func.gcm.buildCfg();
        }

        if (!utils.freestanding and self.verbose)
            func.fmtScheduled(
                std.io.getStdErr().writer().any(),
                std.io.tty.detectConfig(std.io.getStdErr()),
            );

        if (self.error_buf) |eb| {
            func.static_anal.analize(self.arena.?, eb, self.do_uninit_analisys);
            if (self.error_buf.?.items.len != 0) return error.HasErrors;
        }
    }

    pub fn finalize(optimizations: @This(), builtins: Builtins, comptime Backend: type, backend: *Backend) bool {
        errdefer unreachable;

        if (optimizations.do_inlining) {
            var tmp = utils.Arena.scrath(optimizations.arena);
            defer tmp.deinit();

            const bout: *Data = &backend.out;
            const gpa: std.mem.Allocator = backend.gpa.allocator();

            var out: Data = .{};
            defer out.deinit(gpa);

            // do the exhausitve optimization pass with inlining, this should
            // hanlde stacked inlines as well
            //
            const pi_opts = optimizations.asPostInlining();

            const sym_to_idx = tmp.arena.alloc(u32, bout.syms.items.len);

            for (bout.funcs.items, 0..) |sym, i| {
                if (sym == .invalid) continue;
                sym_to_idx[@intFromEnum(sym)] = @intCast(i);
            }

            for (bout.globals.items, 0..) |sym, i| {
                if (sym == .invalid) continue;
                sym_to_idx[@intFromEnum(sym)] = @intCast(i);
            }

            for (bout.syms.items, sym_to_idx) |sym, i| {
                if (sym.kind != .func) continue;
                if (sym.linkage == .imported) {
                    try out.startDefineFunc(
                        gpa,
                        @intCast(i),
                        bout.lookupName(sym.name),
                        sym.kind,
                        sym.linkage,
                        false,
                    );
                    out.endDefineFunc(@intCast(i));
                    continue;
                }
                const inline_func = &bout.inline_funcs.items[sym.inline_func];
                pi_opts.execute(Backend, backend, @ptrCast(inline_func)) catch {
                    inline_func.corrupted = true;
                };
            }

            // we take out the current `out` that just encodes the code spec and
            // and emit all functions to the new out without opts
            //
            std.mem.swap(Data, &out, bout);

            for (out.syms.items, sym_to_idx) |sym, i| {
                switch (sym.kind) {
                    .func => {
                        if (sym.linkage == .imported) continue;
                        const func = &out.inline_funcs.items[sym.inline_func];
                        backend.emitFunc(@ptrCast(func), .{
                            .name = out.lookupName(sym.name),
                            .id = @intCast(i),
                            .linkage = sym.linkage,
                            .is_inline = false,
                            .optimizations = b: {
                                var op = OptOptions.none;
                                op.do_gcm = true;
                                op.error_buf = optimizations.error_buf;
                                op.arena = optimizations.arena;
                                op.verbose = optimizations.verbose;
                                break :b op;
                            },
                            .builtins = builtins,
                        });
                    },
                    .data => {
                        var tmpa = tmp.arena.checkpoint();
                        defer tmpa.deinit();

                        const relocs = tmpa.arena.alloc(DataOptions.Reloc, sym.reloc_count);
                        for (
                            out.relocs.items[sym.reloc_offset..][0..sym.reloc_count],
                            relocs,
                        ) |rel, *dst| {
                            dst.* = .{
                                .target = sym_to_idx[@intFromEnum(rel.target)],
                                .offset = rel.offset,
                            };
                        }

                        backend.emitData(.{
                            .name = out.lookupName(sym.name),
                            .id = @intCast(i),
                            .value = .{ .init = out.code.items[sym.offset..][0..sym.size] },
                            .relocs = relocs,
                            .readonly = sym.readonly,
                        });
                    },
                    .prealloc => unreachable,
                    .invalid => {},
                }
            }

            if (optimizations.error_buf) |eb| if (eb.items.len != 0) return true;

            bout.deduplicate();
            bout.elimitaneDeadCode();
        }

        if (optimizations.error_buf) |eb| if (eb.items.len != 0) return true;

        return false;
    }
};

pub const Builtins = struct {
    memcpy: u32 = std.math.maxInt(u32),
};

pub const EmitOptions = struct {
    id: u32,
    name: []const u8 = &.{},
    is_inline: bool,
    linkage: Data.Linkage,
    optimizations: OptOptions = .all,
    special: ?Special = null,
    builtins: Builtins,

    pub const Special = enum { entry, memcpy };
};

const Vidsibility = enum { local, exported, imported };

pub const DisasmOpts = struct {
    name: []const u8,
    bin: []const u8,
    out: std.io.AnyWriter = std.io.null_writer.any(),
    colors: std.io.tty.Config = .no_color,
};

pub const FinalizeOptions = struct {
    output: std.io.AnyWriter,
    optimizations: OptOptions = .all,
    builtins: Builtins,
};

pub const FinalizeBytesOptions = struct {
    gpa: std.mem.Allocator,
    optimizations: OptOptions = .all,
    builtins: Builtins,
};

pub fn init(data: anytype) Machine {
    const Type = @TypeOf(data.*);
    if (!@hasDecl(Type, "classes")) @compileError("expected `pub const classes = enum { ... }` to be present");

    const fns = struct {
        fn emitFunc(self: *anyopaque, func: *BuilderFunc, opts: EmitOptions) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            const fnc: *graph.Func(Type) = @alignCast(@ptrCast(func));
            slf.emitFunc(fnc, opts);
        }
        fn emitData(self: *anyopaque, opts: DataOptions) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            slf.emitData(opts);
        }
        fn finalize(self: *anyopaque, opts: FinalizeOptions) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            return slf.finalize(opts);
        }
        fn disasm(self: *anyopaque, opts: DisasmOpts) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            return slf.disasm(opts);
        }
        fn run(self: *anyopaque, env: RunEnv) !usize {
            const slf: *Type = @alignCast(@ptrCast(self));
            return slf.run(env);
        }
        fn deinit(self: *anyopaque) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            slf.deinit();
        }
    };

    return .{
        .data = data,
        ._emitFunc = fns.emitFunc,
        ._emitData = fns.emitData,
        ._finalize = fns.finalize,
        ._disasm = fns.disasm,
        ._run = fns.run,
        ._deinit = fns.deinit,
    };
}

/// generate apropriate final output for a function
///
/// this also runs optimization passes
pub fn emitFunc(self: Machine, func: *BuilderFunc, opts: EmitOptions) void {
    self._emitFunc(self.data, func, opts);
}

pub fn emitData(self: Machine, opts: DataOptions) void {
    self._emitData(self.data, opts);
}

/// package the final output (.eg object file)
/// this function should also restart the state for next emmiting
pub fn finalize(self: Machine, opts: FinalizeOptions) void {
    return self._finalize(self.data, opts);
}

pub fn finalizeBytes(self: Machine, opts: FinalizeBytesOptions) std.ArrayListUnmanaged(u8) {
    var out = std.ArrayListUnmanaged(u8).empty;
    self.finalize(.{
        .output = out.writer(opts.gpa).any(),
        .optimizations = opts.optimizations,
        .builtins = opts.builtins,
    });
    return out;
}

/// visualize already compiled code, its best to include different colors
/// for registers for better readability
pub fn disasm(self: Machine, opts: DisasmOpts) void {
    self._disasm(self.data, opts);
}

pub fn run(self: Machine, env: RunEnv) !usize {
    return self._run(self.data, env);
}

/// frees the internal resources
pub fn deinit(self: *Machine) void {
    self._deinit(self.data);
    self.* = undefined;
}
