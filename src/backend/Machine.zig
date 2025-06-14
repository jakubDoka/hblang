test init {
    const ExampleMachine = struct {
        const Func = graph.Func(Node);

        pub const Node = union(enum) {
            CustomNode: bool,

            pub const is_basic_block_start: []const Func.Kind = &.{};
            pub const is_mem_op: []const Func.Kind = &.{};
            pub const is_basic_block_end: []const Func.Kind = &.{.CustomNode};
            pub const is_pinned: []const Func.Kind = &.{.CustomNode};

            pub fn isInterned(kind: Func.Kind) bool {
                // this is not a good idea since its supposed to be a control flow
                return kind == .CustomNode;
            }

            pub fn isSwapped(node: *Func.Node) bool {
                // means the output basic blocks should be reversed for reducing jumps
                return node.kind == .CustomNode and node.extra(.CustomNode).*;
            }

            pub fn idealize(func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
                _ = worklist;
                // relpace node whih the return value
                if (node.kind == .Start)
                    return func.addNode(.CustomNode, .top, &.{}, false);

                return null;
            }
        };

        pub fn emitFunc(self: *@This(), func: *Func, opts: EmitOptions) void {
            opts.optimizations.execute(Node, func);
            _ = self;
            unreachable;
        }

        pub fn emitData(self: *@This(), opts: DataOptions) void {
            _ = self;
            _ = opts;
            unreachable;
        }

        pub fn finalize(self: *@This(), out: std.io.AnyWriter) void {
            _ = out;
            _ = self;
            unreachable;
        }

        pub fn disasm(self: *@This(), opts: DisasmOpts) void {
            _ = self;
            _ = opts;
            unreachable;
        }

        pub fn run(self: *@This(), env: RunEnv) !usize {
            _ = self;
            _ = env;
            return 0;
        }

        pub fn deinit(self: *@This()) void {
            _ = self;
        }
    };

    var em = ExampleMachine{};
    _ = init(&em);
}

data: *anyopaque,
name: []const u8,
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
const BuilderFunc = Builder.Func;
const Machine = @This();
const root = @import("../utils.zig");
const Set = std.DynamicBitSetUnmanaged;

pub const InlineFunc = struct {
    start: *anyopaque,
    end: *anyopaque,
    node_count: usize,

    pub fn toFunc(
        self: *const InlineFunc,
        arena: *std.heap.ArenaAllocator,
        comptime Node: type,
    ) graph.Func(Node) {
        const Func = graph.Func(Node);

        errdefer unreachable;

        var tmp = root.Arena.scrath(null);
        defer tmp.deinit();

        const self_start: *Func.Node = @alignCast(@ptrCast(self.start));
        const self_end: *Func.Node = @alignCast(@ptrCast(self.end));

        var func = Func{
            .arena = arena.*,
            .root = self_start,
            .end = self_end,
            .next_id = @intCast(self.node_count),
        };

        internBatch(
            Node,
            self_start,
            self_end,
            0,
            &func,
            .{ .count = self.node_count },
        );

        const entry = self_start.outputs()[0];
        std.debug.assert(entry.kind == .Entry);

        var params = std.ArrayListUnmanaged(graph.DataType){};
        for (self_start.outputs()) |o| {
            // NOTE: we dont initialize the killed args because all code only
            // acesses the initialized ones
            //
            if (o.kind == .Arg) {
                if (params.items.len <= o.extra(.Arg).*) {
                    try params.resize(func.arena.allocator(), o.extra(.Arg).* + 1);
                }
                params.items[o.extra(.Arg).*] = o.data_type;
            }
        }

        const rets = try func.arena.allocator()
            .alloc(graph.DataType, self_end.dataDeps().len);
        for (self_end.dataDeps(), rets) |dep, *ret| ret.* = dep.?.data_type;

        func.params = params.items;
        func.returns = rets;

        return func;
    }

    pub fn cloneNodes(
        comptime Node: type,
        start: *graph.FuncNode(Node),
        end: *graph.FuncNode(Node),
        node_count: usize,
        arena: *std.heap.ArenaAllocator,
        already_present: usize,
        scrath: *root.Arena,
    ) struct {
        new_node_table: []*graph.FuncNode(Node),
        new_nodes: []*graph.FuncNode(Node),
    } {
        errdefer unreachable;

        const Func = graph.Func(Node);

        var tmp = root.Arena.scrath(scrath);
        defer tmp.deinit();

        const new_node_table = scrath.alloc(*Func.Node, node_count);
        var new_nodes = scrath.makeArrayList(*Func.Node, node_count);

        var work = try Func.WorkList.init(tmp.arena.allocator(), node_count);
        work.add(start);
        work.add(end);
        var i: usize = 0;
        while (i < work.list.items.len) : (i += 1) {
            const node = work.list.items[i];
            for (node.outputs()) |o| work.add(o);
            for (node.inputs()) |inp| if (inp != null) work.add(inp.?);

            const node_size = node.size();
            const new_slot = try arena.allocator()
                .alignedAlloc(u8, @alignOf(Func.Node), node_size);
            @memcpy(new_slot, @as([*]const u8, @ptrCast(node)));
            const new_node: *Func.Node = @ptrCast(new_slot);

            if (new_node.input_len != new_node.input_ordered_len) {
                new_node.input_len = @intCast(std.mem.indexOfScalarPos(
                    ?*Func.Node,
                    node.inputs(),
                    new_node.input_ordered_len,
                    null,
                ) orelse new_node.input_len);

                std.debug.assert(new_node.input_len >= new_node.input_ordered_len);
            }

            if (new_node.asCfg()) |cfg| cfg.ext.idepth = 0;
            if (new_node.subclass(graph.Region)) |cfg| cfg.ext.cached_lca = null;

            new_node.input_base = (try arena.allocator()
                .dupe(?*Func.Node, new_node.inputs())).ptr;
            new_node.output_base = (try arena.allocator()
                .dupe(*Func.Node, new_node.outputs())).ptr;
            new_node_table[new_node.id] = new_node;
            new_node.id = @intCast(already_present + i);
            new_node.output_cap = new_node.output_len;
            new_nodes.appendAssumeCapacity(new_node);
        }

        // remap inputs and outputs
        for (new_nodes.items) |node| {
            for (node.inputs()) |*inp| if (inp.* != null) {
                inp.* = new_node_table[inp.*.?.id];
            };

            for (node.outputs()) |*out| {
                out.* = new_node_table[out.*.id];
            }
        }

        for (new_nodes.items) |n| {
            std.debug.assert(n.id < already_present + i);
            std.debug.assert(n.id >= already_present);
        }

        return .{
            .new_node_table = new_node_table,
            .new_nodes = new_nodes.items,
        };
    }

    pub fn internBatch(
        comptime Node: type,
        start: *graph.FuncNode(Node),
        end: *graph.FuncNode(Node),
        already_present: usize,
        into: *graph.Func(Node),
        new_nodes: union(enum) { new: []*graph.FuncNode(Node), count: usize },
    ) void {
        errdefer unreachable;

        const Func = graph.Func(Node);

        var tmp = root.Arena.scrath(null);
        defer tmp.deinit();

        const node_count = switch (new_nodes) {
            .new => |n| n.len,
            .count => |c| c,
        };

        var interned = try Set.initEmpty(
            tmp.arena.allocator(),
            already_present + node_count,
        );
        var work = try Func.WorkList.init(tmp.arena.allocator(), node_count);
        work.add(start);
        work.add(end);

        var deffered_phi_stack = std.ArrayListUnmanaged(*Func.Node){};

        var limit: usize = 100000;
        while (work.pop()) |node| {
            limit -= 1;
            if (node.id < already_present) {
                // NOTE: this can happen, dont ask me how
                continue;
            }
            if (interned.isSet(node.id)) continue;

            if (Func.Node.isInterned(node.kind, node.inputs())) {
                var ready = true;
                for (node.outputs()) |use| {
                    if (use != node and
                        Func.Node.isInterned(use.kind, use.inputs()) and
                        !interned.isSet(use.id))
                    {
                        work.add(use);
                        ready = false;
                    }
                }
                if (!ready) b: {
                    if (node.kind == .Phi and node.inputs()[0].?.kind == .Loop) {
                        if (std.mem.indexOfScalar(
                            *Func.Node,
                            deffered_phi_stack.items,
                            node,
                        )) |idx| {
                            // we have a cycle so just intern
                            _ = deffered_phi_stack.swapRemove(idx);
                            break :b;
                        } else {
                            try deffered_phi_stack.append(tmp.arena.allocator(), node);
                        }
                    }

                    continue;
                } else {
                    if (node.kind == .Phi and node.inputs()[0].?.kind == .Loop) {
                        if (std.mem.indexOfScalar(
                            *Func.Node,
                            deffered_phi_stack.items,
                            node,
                        )) |idx| {
                            // we have a cycle so just intern
                            _ = deffered_phi_stack.swapRemove(idx);
                        }
                    }
                }

                interned.set(node.id);
                const slot = into.internNode(
                    node.kind,
                    node.data_type,
                    node.inputs(),
                    node.anyextra(),
                );
                if (slot.found_existing) {
                    into.subsumeNoKill(slot.key_ptr.node, node);
                    node.kill();
                } else {
                    slot.key_ptr.node = node;
                    for (node.inputs()) |on| if (on) |n| {
                        work.add(n);
                    };
                }
            } else {
                interned.set(node.id);

                for (node.inputs()) |on| if (on) |n| {
                    work.add(n);
                };

                for (node.outputs()) |o| work.add(o);
            }
        }

        if (new_nodes == .new) {
            var malformed = false;
            for (new_nodes.new) |n| {
                // TODO: there is a better way
                if (n.id == std.math.maxInt(u16)) continue;
                if (!interned.isSet(n.id)) {
                    std.debug.print("{}\n", .{n});
                    malformed = true;
                }
            }
            if (malformed) {
                std.debug.print("\n", .{});
                std.debug.print("{}\n", .{end});
                into.fmtUnscheduled(
                    std.io.getStdErr().writer().any(),
                    .escape_codes,
                );
                unreachable;
            }
        }
    }

    pub fn inlineInto(
        self: *const InlineFunc,
        comptime Node: type,
        func: *graph.Func(Node),
        dest: *graph.Func(Node).Node,
        func_work: *graph.Func(Node).WorkList,
    ) void {
        errdefer unreachable;

        func.gcm.loop_tree_built.assertUnlocked();

        const Func = graph.Func(Node);

        const arena = &func.arena;
        const self_start: *Func.Node = @alignCast(@ptrCast(self.start));
        const self_end: *Func.Node = @alignCast(@ptrCast(self.end));

        const prev_next_id = func.next_id;

        var tmp = root.Arena.scrathFromAlloc(func_work.list.allocator);
        defer tmp.deinit();

        const cloned = cloneNodes(
            Node,
            self_start,
            self_end,
            self.node_count,
            arena,
            func.next_id,
            tmp.arena,
        );

        func.next_id += @intCast(cloned.new_nodes.len);

        const end = cloned.new_node_table[self_end.id];
        const start = cloned.new_node_table[self_start.id];

        internBatch(Node, start, end, prev_next_id, func, .{ .new = cloned.new_nodes });

        const entry = start.outputs()[0];
        std.debug.assert(entry.kind == .Entry);

        const entry_mem: ?*Func.Node = for (start.outputs()) |o| {
            if (o.kind == .Mem) break o;
        } else null;
        var exit_mem = end.inputs()[1];

        const into_entry_mem = func.root.outputs()[1];
        std.debug.assert(into_entry_mem.kind == .Mem);

        const call_end = dest.outputs()[0];
        if (call_end.kind != .CallEnd)
            func.fmtUnscheduled(
                std.io.getStdErr().writer().any(),
                .escape_codes,
            );
        std.debug.assert(call_end.kind == .CallEnd);

        var after_entry: *Func.Node = for (entry.outputs()) |o| {
            if (o.isCfg()) break o;
        } else unreachable;
        std.debug.assert(after_entry.isBasicBlockEnd() or
            after_entry.kind == .Region or after_entry.kind == .Loop);
        std.debug.assert(after_entry.kind != .Entry);
        std.debug.assert(after_entry.kind != .Start);

        const before_return = end.inputs()[0];
        std.debug.assert(before_return == null or before_return.?.isBasicBlockStart());

        const before_dest = dest.inputs()[0].?;
        std.debug.assert(before_dest.isBasicBlockStart());

        const call_end_entry_mem = for (call_end.outputs()) |o| {
            if (o.kind == .Mem) break o;
        } else null;

        if (entry_mem != null) {
            for (tmp.arena.dupe(*Func.Node, entry_mem.?.outputs())) |use| {
                if (use.kind == .Local) {
                    func.setInputNoIntern(use, 1, into_entry_mem);
                }
            }
        }

        // NOTE: not scheduled yet so args are on the Start
        for (dest.dataDeps(), 0..) |dep, j| {
            const arg = for (start.outputs()) |o| {
                if (o.kind == .Arg and o.extra(.Arg).* == j) break o;
            } else continue;
            func.subsume(dep.?, arg);
        }

        for (end.dataDeps(), 0..) |dep, j| {
            const ret = for (call_end.outputs()) |o| {
                if (o.kind == .Ret and o.extra(.Ret).* == j) break o;
            } else continue;
            func.subsume(dep.?, ret);
        }

        if (entry_mem == exit_mem) {
            if (entry_mem != null) {
                // NOTE: this is still needed since there can be loads
                func.subsume(dest.inputs()[1].?, entry_mem.?);
            }
            if (call_end_entry_mem != null) {
                func.subsume(dest.inputs()[1].?, call_end_entry_mem.?);
            }
            exit_mem = dest.inputs()[1].?;
        } else {
            func.subsume(dest.inputs()[1].?, entry_mem.?);
            if (call_end_entry_mem != null) {
                func.subsume(exit_mem.?, call_end_entry_mem.?);
            }
        }

        if (exit_mem) |em| {
            for (em.outputs()) |o| {
                func_work.add(o);
            }
        }

        func.subsume(before_dest, entry);

        if (end.inputs()[2]) |trap_region| {
            if (func.end.inputs()[2] == null) {
                func.setInputNoIntern(func.end, 2, func.addNode(.TrapRegion, .top, &.{}, .{}));
            }
            const dest_trap_region = func.end.inputs()[2].?;

            for (trap_region.inputs()) |inp| {
                func.connect(inp.?, dest_trap_region);
            }
        }

        if (after_entry.kind == .Return) {
            func.subsume(before_dest, call_end);
        } else if (before_return != null) {
            func.subsume(before_return.?, call_end);
        }
        dest.data_type = .bot;
        func_work.add(dest);

        end.kill();

        for (cloned.new_nodes) |nn| if (nn.id != std.math.maxInt(u16)) {
            func_work.add(nn);
        };
    }

    pub fn init(
        arena: *std.heap.ArenaAllocator,
        comptime Node: type,
        func: *graph.Func(Node),
    ) InlineFunc {
        errdefer unreachable;

        func.gcm.loop_tree_built.assertUnlocked();

        var tmp = root.Arena.scrath(null);
        defer tmp.deinit();

        const cloned = cloneNodes(
            Node,
            func.root,
            func.end,
            func.next_id,
            arena,
            0,
            tmp.arena,
        );

        return InlineFunc{
            .start = cloned.new_node_table[func.root.id],
            .end = cloned.new_node_table[func.end.id],
            .node_count = cloned.new_nodes.len,
        };
    }
};

pub const Data = struct {
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
        nodes: u32 = std.math.maxInt(u32),
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

    declaring_sym: ?SymIdx = null,
    inline_func_nodes: std.heap.ArenaAllocator.State = .{},
    funcs: std.ArrayListUnmanaged(SymIdx) = .empty,
    globals: std.ArrayListUnmanaged(SymIdx) = .empty,
    syms: std.ArrayListUnmanaged(Sym) = .empty,
    names: std.ArrayListUnmanaged(u8) = .empty,
    code: std.ArrayListUnmanaged(u8) = .empty,
    relocs: std.ArrayListUnmanaged(Reloc) = .empty,
    inline_funcs: std.ArrayListUnmanaged(InlineFunc) = .empty,

    pub fn setInlineFunc(self: *Data, gpa: std.mem.Allocator, comptime Node: type, func: *graph.Func(Node), to: u32) void {
        errdefer unreachable;

        var arena = self.inline_func_nodes.promote(gpa);
        const ifunc = InlineFunc.init(&arena, Node, func);
        self.inline_func_nodes = arena.state;
        try self.inline_funcs.append(gpa, ifunc);

        self.syms.items[@intFromEnum(self.funcs.items[to])].nodes =
            @intCast(self.inline_funcs.items.len - 1);
    }

    pub fn getInlineFunc(self: *Data, at: u32) ?*const InlineFunc {
        if (self.funcs.items.len <= at or self.funcs.items[at] == .invalid) return null;
        const sym = &self.syms.items[@intFromEnum(self.funcs.items[at])];
        if (!sym.is_inline) return null;
        const nodes = sym.nodes;
        return if (nodes == std.math.maxInt(u32)) null else &self.inline_funcs.items[nodes];
    }

    pub fn readFromSym(self: Data, id: u32, offset: i64, size: u64) ?i64 {
        if (self.globals.items.len <= id) return null;
        const sym = &self.syms.items[@intFromEnum(self.globals.items[id])];

        if (!sym.readonly) return null;

        var value: i64 = 0;

        @memcpy(
            @as(*[@sizeOf(@TypeOf(value))]u8, @ptrCast(&value))[0..@intCast(size)],
            self.code.items[@intCast(sym.offset + offset)..][0..@intCast(size)],
        );

        return value;
    }

    pub fn reset(self: *Data) void {
        // TODO: clear the inline_func_nodes
        inline for (std.meta.fields(Data)[2..]) |f| {
            @field(self, f.name).items.len = 0;
        }
    }

    pub fn lookupName(self: *const Data, name: u32) [:0]const u8 {
        return self.names.items[name..][0..std.mem.indexOfScalar(u8, self.names.items[name..], 0).? :0];
    }

    pub fn addFuncReloc(self: *Data, gpa: std.mem.Allocator, target: u32, slot_size: u8, addend: i16) !void {
        return self.addReloc(gpa, try root.ensureSlot(&self.funcs, gpa, target), slot_size, addend);
    }

    pub fn addGlobalReloc(self: *Data, gpa: std.mem.Allocator, target: u32, slot_size: u8, addend: i16) !void {
        return self.addReloc(gpa, try root.ensureSlot(&self.globals, gpa, target), slot_size, addend);
    }

    pub fn addReloc(self: *Data, gpa: std.mem.Allocator, target: *SymIdx, slot_size: u8, addend: i16) !void {
        try self.relocs.append(gpa, .{
            .target = try self.declSym(gpa, target),
            .offset = @intCast(self.code.items.len),
            .addend = addend,
            .slot_size = slot_size,
        });
    }

    pub fn deinit(self: *Data, gpa: std.mem.Allocator) void {
        self.inline_func_nodes.promote(gpa).deinit();
        inline for (std.meta.fields(Data)[2..]) |f| {
            @field(self, f.name).deinit(gpa);
        }
        self.* = undefined;
    }

    pub fn declGlobal(self: *Data, gpa: std.mem.Allocator, id: u32) !SymIdx {
        return self.declSym(gpa, try root.ensureSlot(&self.globals, gpa, id));
    }

    pub fn declFunc(self: *Data, gpa: std.mem.Allocator, id: u32) !SymIdx {
        return self.declSym(gpa, try root.ensureSlot(&self.funcs, gpa, id));
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
        return self.startDefineSym(
            gpa,
            try root.ensureSlot(&self.funcs, gpa, id),
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
        readonly: bool,
    ) !void {
        try self.startDefineSym(
            gpa,
            try root.ensureSlot(&self.globals, gpa, id),
            name,
            kind,
            linkage,
            readonly,
            false,
        );
        try self.code.appendSlice(gpa, data);
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
    value: ValueSpec,
    readonly: bool,

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
    arena: ?*root.Arena = null,
    error_buf: ?*std.ArrayListUnmanaged(static_anal.Error) = null,

    pub const all = @This(){
        .do_dead_code_elimination = true,
        .do_inlining = true,
        .do_generic_peeps = true,
        .do_machine_peeps = true,
        .mem2reg = true,
        .do_gcm = true,
    };

    pub const none = @This(){
        .do_dead_code_elimination = false,
        .do_inlining = false,
        .mem2reg = false,
        .do_generic_peeps = false,
        .do_machine_peeps = true,
        .do_gcm = true,
    };

    pub fn asPostInlining(self: @This()) @This() {
        std.debug.assert(self.do_inlining);
        var s = self;
        s.do_inlining = false;
        s.do_gcm = false;
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
        func: *graph.Func(B.Node),
        backend: *B,
    ) bool {
        if (self.do_inlining or is_inline) {
            self.asPreInline().execute(B.Node, backend, func);
            backend.out.setInlineFunc(backend.gpa, B.Node, func, id);
        }

        return self.do_inlining;
    }

    pub fn execute(self: @This(), comptime MachNode: type, ctx: anytype, func: *graph.Func(MachNode)) void {
        const freestanding = @import("builtin").target.os.tag == .freestanding;

        const Func = graph.Func(MachNode);
        const Node = Func.Node;

        std.debug.assert(func.root.id != std.math.maxInt(u16));

        if (self.do_dead_code_elimination) {
            func.iterPeeps(ctx, struct {
                fn wrap(cx: @TypeOf(ctx), fnc: *Func, nd: *Node, wl: *Func.WorkList) ?*Node {
                    return @TypeOf(func.*).idealizeDead(cx, fnc, nd, wl);
                }
            }.wrap);
            std.debug.assert(func.root.id != std.math.maxInt(u16));
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
        } else if (@hasDecl(MachNode, "idealize")) {
            func.iterPeeps(ctx, MachNode.idealize);
        }

        if (self.do_machine_peeps and @hasDecl(MachNode, "idealizeMach")) {
            func.iterPeeps(ctx, MachNode.idealizeMach);
        }

        if (self.do_gcm) {
            func.gcm.buildCfg();
        }

        if (!freestanding and self.verbose)
            func.fmtScheduled(
                std.io.getStdErr().writer().any(),
                std.io.tty.detectConfig(std.io.getStdErr()),
            );

        if (self.error_buf) |eb| {
            func.static_anal.analize(self.arena.?, eb);
        }
    }

    pub fn finalize(optimizations: @This(), comptime B: type, backend: *B) void {
        errdefer unreachable;

        if (optimizations.do_inlining) {
            var tmp = root.Arena.scrath(optimizations.arena);
            defer tmp.deinit();

            const bout: *Data = &backend.out;
            const gpa: std.mem.Allocator = backend.gpa;
            const Func = graph.Func(B.Node);
            const Node = B.Node;

            var out: Data = .{};
            defer out.deinit(gpa);

            // do the exhausitve optimization pass with inlining, this should
            // hanlde stacked inlines as well
            //
            const pi_opts = optimizations.asPostInlining();
            var arena = bout.inline_func_nodes.promote(gpa);
            const funcs = tmp.arena.alloc(Func, bout.inline_funcs.items.len);
            for (bout.funcs.items, 0..) |sym_id, i| {
                if (sym_id == .invalid) continue;
                const sym = &bout.syms.items[@intFromEnum(sym_id)];
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
                const inline_func = &bout.inline_funcs.items[sym.nodes];
                funcs[sym.nodes] = inline_func.toFunc(&arena, Node);
                pi_opts.execute(Node, backend, &funcs[sym.nodes]);
                inline_func.node_count = funcs[sym.nodes].next_id;

                arena = funcs[sym.nodes].arena;
            }

            // we take out the current `out` that just encodes the code spec and
            // and emit all functions to the new out without opts
            //
            std.mem.swap(Data, &out, bout);

            for (out.globals.items, 0..) |sym_id, i| {
                if (sym_id == .invalid) continue;
                const sym = &out.syms.items[@intFromEnum(sym_id)];
                backend.emitData(.{
                    .name = out.lookupName(sym.name),
                    .id = @intCast(i),
                    .value = .{ .init = out.code.items[sym.offset..][0..sym.size] },
                    .readonly = sym.readonly,
                });
            }

            for (out.funcs.items, 0..) |sym_id, i| {
                if (sym_id == .invalid) continue;
                const sym = &out.syms.items[@intFromEnum(sym_id)];
                if (sym.linkage == .imported) continue;
                var func = &funcs[sym.nodes];
                func.arena = arena;

                backend.emitFunc(func, .{
                    .name = out.lookupName(sym.name),
                    .id = @intCast(i),
                    .entry = i == backend.entry,
                    .linkage = sym.linkage,
                    .is_inline = false,
                    .optimizations = b: {
                        var op = OptOptions.none;
                        op.do_gcm = true;
                        op.error_buf = optimizations.error_buf;
                        op.arena = optimizations.arena;
                        break :b op;
                    },
                });
                arena = func.arena;
            }

            out.inline_func_nodes = arena.state;
        }
    }
};

pub const EmitOptions = struct {
    id: u32,
    name: []const u8 = &.{},
    entry: bool = false,
    is_inline: bool,
    linkage: Data.Linkage,
    optimizations: OptOptions = .all,
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
};

pub const FinalizeBytesOptions = struct {
    gpa: std.mem.Allocator,
    optimizations: OptOptions = .all,
};

pub fn init(name: []const u8, data: anytype) Machine {
    const Type = @TypeOf(data.*);
    if (!@hasDecl(Type, "Node")) @compileError("expected `pub const Node = enum(union) { ... }` to be present");

    const fns = struct {
        fn emitFunc(self: *anyopaque, func: *BuilderFunc, opts: EmitOptions) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            const fnc: *graph.Func(Type.Node) = @alignCast(@ptrCast(func));
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
        .name = name,
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
