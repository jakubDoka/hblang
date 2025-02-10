pub fn Func(comptime Mach: type) type {
    return @TypeOf(_Func(Mach));
}

const std = @import("std");
const Lexer = @import("Lexer.zig");
const Types = @import("Types.zig");

fn _Func(comptime Mach: type) struct {
    arena: std.heap.ArenaAllocator,
    tmp_arena: std.heap.ArenaAllocator,
    interner: std.hash_map.HashMapUnmanaged(InternedNode, void, void, 70) = .{},
    next_id: u16 = 0,
    block_count: u16 = undefined,
    instr_count: u16 = undefined,
    root: *Node = undefined,
    end: *Node = undefined,

    pub const Builtin = union(enum) {
        Start: Cfg,
        // [Start]
        Arg: usize,
        // [Start]
        Entry: Cfg,
        // [Start]
        Mem: void,
        // [Cfg, ret]
        Return: Cfg,
        // [?Cfg]
        CInt: i64,
        // [?Cfg, lhs, rhs]
        BinOp: Lexer.Lexeme,
        // [?Cfg, Mem]
        Local: usize,
        // [?Cfg, thread, ptr]
        Load,
        // [?Cfg, thread, ptr, value, ...antideps]
        Store,
        // [?Cfg, ...lane]
        Split,
        // [?Cfg, ...lane]
        Join,
        // [Cfg, ..args]
        Call: extern struct {
            base: Cfg = .{},
            id: Types.Func,
        },
        // [Call]
        CallEnd: Cfg,
        // [CallEnd]
        Ret: void,
        // [Cfg, cond],
        If: Cfg,
        // [If]
        Then: Cfg,
        // [If]
        Else: Cfg,
        // [lCfg, rCfg]
        Region: Cfg,
        // [entryCfg, backCfg]
        Loop: Cfg,
        // [Cfg]
        Jmp: Cfg,
        // [Region, lhs, rhs]
        Phi,
        // [Cfg, inp]
        MachMove,

        pub const is_basic_block_start = .{ .Entry, .CallEnd, .Then, .Else, .Region, .Loop };
        pub const is_basic_block_end = .{ .Return, .Call, .If, .Jmp };
        pub const is_mem_op = .{ .Load, .Local, .Store, .Return, .Call };
        pub const is_pinned = .{ .Ret, .Phi, .Mem };
        pub const is_load = .{.Load};
        pub const is_store = .{.Store};

        pub const Cfg = extern struct {
            idepth: u16 = 0,
            antidep: u16 = 0,
        };
    };

    pub const all_classes = std.meta.fields(Builtin) ++ std.meta.fields(Mach);

    const Self = @This();

    pub const WorkList = struct {
        list: std.ArrayList(*Node),
        in_list: std.DynamicBitSet,

        pub fn init(gpa: std.mem.Allocator, cap: usize) !WorkList {
            return .{
                .list = try .initCapacity(gpa, cap * 2),
                .in_list = try .initEmpty(gpa, cap * 2),
            };
        }

        pub fn add(self: *WorkList, node: *Node) void {
            std.debug.assert(node.id != std.math.maxInt(u16));
            if (self.in_list.isSet(node.id)) return;
            self.in_list.set(node.id);
            self.list.appendAssumeCapacity(node);
        }

        pub fn pop(self: *WorkList) ?*Node {
            var node = self.list.popOrNull() orelse return null;
            while (node.id == std.math.maxInt(u16)) {
                node = self.list.popOrNull() orelse return null;
            }
            self.in_list.unset(node.id);
            return node;
        }
    };

    pub const InternedNode = struct {
        hash: u64,
        node: *Node,
    };

    pub const CfgNode = LayoutOf(Builtin.Cfg);

    pub const Kind = b: {
        var builtin = @typeInfo(std.meta.Tag(Builtin));
        builtin.@"enum".tag_type = u16;
        const field_ref = std.meta.fields(std.meta.Tag(Mach));
        var fields = field_ref[0..field_ref.len].*;
        for (&fields, builtin.@"enum".fields.len..) |*f, i| {
            f.value = i;
        }
        builtin.@"enum".fields = builtin.@"enum".fields ++ fields;
        break :b @Type(builtin);
    };

    pub fn bakeBitset(name: []const u8) std.EnumSet(Kind) {
        var set = std.EnumSet(Kind).initEmpty();
        if (@hasDecl(Builtin, name)) for (@field(Builtin, name)) |k| set.insert(k);
        if (@hasDecl(Mach, name)) for (@field(Mach, name)) |k| set.insert(k);
        return set;
    }

    pub fn ClassFor(comptime kind: Kind) type {
        return all_classes[@intFromEnum(kind)].type;
    }

    pub fn LayoutFor(comptime kind: Kind) type {
        return LayoutOf(ClassFor(kind));
    }

    pub fn LayoutOf(comptime Class: type) type {
        return extern struct {
            base: Node,
            ext: Class,

            pub fn idepth(cfg: *CfgNode) u16 {
                const extra: *Builtin.Cfg = &cfg.ext;

                if (extra.idepth != 0) return extra.idepth;
                extra.idepth = switch (cfg.base.kind) {
                    .Start => return 0,
                    .Region => idepth(idom(cfg)),
                    else => idepth(cfg.base.cfg0().?) + 1,
                };
                return extra.idepth;
            }

            fn findLca(left: *CfgNode, right: *CfgNode) *CfgNode {
                var lc, var rc = .{ left, right };
                while (lc != rc) {
                    if (!lc.base.isCfg()) std.debug.panic("{}", .{lc.base});
                    if (!rc.base.isCfg()) std.debug.panic("{}", .{rc.base});
                    const diff = @as(i64, idepth(lc)) - idepth(rc);
                    if (diff >= 0) lc = lc.base.cfg0().?;
                    if (diff <= 0) rc = rc.base.cfg0().?;
                }
                return lc;
            }

            fn idom(cfg: *CfgNode) *CfgNode {
                return switch (cfg.base.kind) {
                    .Region => findLca(cfg.base.inputs()[0].?.asCfg().?, cfg.base.inputs()[1].?.asCfg().?),
                    else => cfg.base.cfg0().?,
                };
            }

            fn better(cfg: *CfgNode, best: *CfgNode) bool {
                return idepth(cfg) > idepth(best) or
                    (cfg.base.kind == .Jmp and cfg.base.outputs()[0].kind == .Loop) or
                    best.base.isBasicBlockEnd();
            }
        };
    }

    fn callCheck(comptime name: []const u8, value: anytype) bool {
        return @hasDecl(Mach, name) and @field(Mach, name)(value);
    }

    pub const DataType = enum(u16) {
        void,
        mem,
        dead,
    };

    const is_basic_block_start = bakeBitset("is_basic_block_start");
    const is_basic_block_end = bakeBitset("is_basic_block_end");
    const is_mem_op = bakeBitset("is_mem_op");
    const is_pinned = bakeBitset("is_pinned");
    const is_load = bakeBitset("is_load");

    pub const Node = extern struct {
        kind: Kind,
        id: u16,
        schedule: u16 = undefined,
        data_type: DataType = .void,

        input_ordered_len: u16,
        input_len: u16,
        output_len: u16 = 0,
        output_cap: u16 = 0,

        input_base: [*]?*Node,
        output_base: [*]*Node,

        pub fn useBlock(self: *Node, use: *Node, scheds: []const ?*CfgNode) *CfgNode {
            if (use.kind == .Phi) {
                std.debug.assert(use.inputs()[0].?.kind == .Region or use.inputs()[0].?.kind == .Loop);
                for (use.inputs()[0].?.inputs(), use.inputs()[1..]) |b, u| {
                    if (u.? == self) {
                        return subclass(b.?, Builtin.Cfg).?;
                    }
                }
            }
            return scheds[use.id].?;
        }

        pub fn dataDeps(self: *Node) []?*Node {
            if (self.kind == .Phi and self.data_type == .mem) return &.{};
            const start: usize = @intFromBool(self.isMemOp());
            return self.input_base[1 + start .. self.input_ordered_len];
        }

        pub fn anyextra(self: *const Node) *const anyopaque {
            const any: *const extern struct { n: Node, ex: u8 } = @ptrCast(self);
            return &any.ex;
        }

        pub fn format(self: *const Node, comptime _: anytype, _: anytype, writer: anytype) !void {
            const colors = .escape_codes;

            self.fmt(null, writer, colors);
        }

        pub fn fmt(
            self: *const Node,
            scheduled: ?u16,
            writer: anytype,
            colors: std.io.tty.Config,
        ) void {
            logNid(writer, self.id, colors);
            const name = @tagName(self.kind);

            writer.print(" = {s}", .{name}) catch unreachable;

            var add_colon_space = false;

            const utils = struct {
                fn logExtra(writ: anytype, ex: anytype, comptime fir: bool) !void {
                    switch (@typeInfo(@TypeOf(ex.*))) {
                        .@"struct" => |s| {
                            comptime var fields = std.mem.reverseIterator(s.fields);
                            comptime var first = fir;
                            inline while (fields.next()) |f| {
                                if (comptime std.mem.eql(u8, f.name, "antidep")) {
                                    continue;
                                }

                                comptime var prefix: []const u8 = "";
                                if (!first) prefix = ", ";
                                first = false;

                                const is_base = comptime std.mem.eql(u8, f.name, "base");
                                if (!is_base) {
                                    prefix = prefix ++ f.name ++ ": ";
                                }

                                try writ.writeAll(prefix);
                                try logExtra(writ, &@field(ex, f.name), is_base);
                            }
                        },
                        .@"enum" => |e| if (e.is_exhaustive) {
                            try writ.print("{s}", .{@tagName(ex.*)});
                        } else {
                            try writ.print("{}", .{ex.*});
                        },
                        else => try writ.print("{}", .{ex.*}),
                    }
                }
            };

            switch (self.kind) {
                inline else => |t| {
                    const ext = self.extraConst(t);
                    if (@TypeOf(ext.*) != void) {
                        if (!add_colon_space) {
                            writer.writeAll(": ") catch unreachable;
                            add_colon_space = true;
                        }

                        utils.logExtra(writer, ext, true) catch unreachable;
                    }
                },
            }

            for (self.input_base[0..self.input_len][@min(@intFromBool(scheduled != null and
                (!self.isCfg() or !self.isBasicBlockStart())), self.input_base[0..self.input_len].len)..]) |oo| if (oo) |o|
            {
                if (!add_colon_space) {
                    writer.writeAll(": ") catch unreachable;
                    add_colon_space = true;
                } else {
                    writer.writeAll(", ") catch unreachable;
                }
                logNid(writer, o.id, colors);
            };

            if (scheduled == null) {
                writer.writeAll(" [") catch unreachable;
                for (self.output_base[0..self.output_len]) |o| {
                    writer.writeAll(", ") catch unreachable;
                    logNid(writer, o.id, colors);
                }
                writer.writeAll("]") catch unreachable;
            }
        }

        pub fn isSwapped(node: *Node) bool {
            return callCheck("isSwapped", node);
        }

        pub fn mem(self: *Node) *Node {
            std.debug.assert(self.kind == .Load or self.kind == .Store);
            return self.inputs()[1].?;
        }

        pub fn base(self: *Node) *Node {
            std.debug.assert(self.kind == .Load or self.kind == .Store);
            return self.inputs()[2].?;
        }

        pub fn value(self: *Node) *Node {
            std.debug.assert(self.kind == .Store);
            return self.inputs()[3].?;
        }

        pub fn isLazyPhi(self: *Node, on_loop: *Node) bool {
            return self.kind == .Phi and self.inputs()[0] == on_loop and self.inputs()[2] == null;
        }

        pub fn inputs(self: *Node) []?*Node {
            return self.input_base[0..self.input_len];
        }

        pub fn kill(self: *Node) void {
            std.debug.assert(self.output_len == 0);
            for (self.inputs()) |oi| if (oi) |i| {
                i.removeUse(self);
            };
            self.* = undefined;
            self.id = std.math.maxInt(u16);
        }

        pub fn cfg0(self: *Node) ?*CfgNode {
            if (self.kind == .Start) return subclass(self, Builtin.Cfg);
            return subclass((self.inputs()[0] orelse return null), Builtin.Cfg);
        }

        pub fn removeUse(self: *Node, use: *Node) void {
            const outs = self.outputs();
            const index = std.mem.indexOfScalar(*Node, outs, use).?;
            std.mem.swap(*Node, &outs[index], &outs[outs.len - 1]);
            self.output_len -= 1;
        }

        pub fn outputs(self: *Node) []*Node {
            return self.output_base[0..self.output_len];
        }

        pub fn extraConst(self: *const Node, comptime kind: Kind) *const ClassFor(kind) {
            std.debug.assert(self.kind == kind);
            const ptr: *const LayoutFor(kind) = @ptrCast(self);
            return &ptr.ext;
        }

        pub fn extra(self: *Node, comptime kind: Kind) *ClassFor(kind) {
            std.debug.assert(self.kind == kind);
            const ptr: *LayoutFor(kind) = @ptrCast(self);
            return &ptr.ext;
        }

        pub fn isSubbclass(Full: type, Sub: type) bool {
            var Cursor = Full;
            while (true) {
                if (Cursor == Sub) return true;
                if (@typeInfo(Cursor) != .@"struct" or !@hasField(Cursor, "base")) return false;
                Cursor = @TypeOf(@as(Cursor, undefined).base);
            }
        }

        pub fn bakeSubclassBitset(comptime Sub: type) std.EnumSet(Kind) {
            var bitset = std.EnumSet(Kind).initEmpty();
            for (all_classes, 0..) |c, i| {
                if (isSubbclass(c.type, Sub)) bitset.insert(@enumFromInt(i));
            }
            return bitset;
        }

        pub fn isSub(self: *const Node, comptime Sub: type) bool {
            return (comptime bakeSubclassBitset(Sub)).contains(self.kind);
        }

        pub fn subclass(self: *Node, comptime Sub: type) ?*LayoutOf(Sub) {
            if (!self.isSub(Sub)) return null;
            return @ptrCast(self);
        }

        pub fn isInterned(kind: Kind, inpts: []const ?*Node) bool {
            return switch (kind) {
                .CInt, .BinOp, .Load => true,
                .Phi => inpts[2] != null,
                else => callCheck("isInterned", kind),
            };
        }

        pub fn asCfg(self: *Node) ?*CfgNode {
            return self.subclass(Builtin.Cfg);
        }

        pub fn isCfg(self: *const Node) bool {
            return self.isSub(Builtin.Cfg);
        }

        pub inline fn isLoad(self: *const Node) bool {
            return is_load.contains(self.kind);
        }

        pub inline fn isPinned(self: *const Node) bool {
            return is_pinned.contains(self.kind);
        }

        pub inline fn isMemOp(self: *const Node) bool {
            return is_mem_op.contains(self.kind);
        }

        pub inline fn isBasicBlockStart(self: *const Node) bool {
            return is_basic_block_start.contains(self.kind);
        }

        pub inline fn isBasicBlockEnd(self: *const Node) bool {
            return is_basic_block_end.contains(self.kind);
        }

        pub const size_map = b: {
            var arr: [all_classes.len]u8 = undefined;
            for (all_classes, &arr) |f, *s| s.* = @sizeOf(f.type);
            const m = arr;
            break :b m;
        };

        pub fn hash(kind: Kind, inpts: []const ?*Node, extr: *const anyopaque) u64 {
            var hasher = std.hash.Fnv1a_64.init();
            hasher.update(@as(*const [2]u8, @ptrCast(&kind)));
            hasher.update(@as([*]const u8, @ptrCast(inpts.ptr))[0 .. inpts.len * @sizeOf(?*Node)]);
            hasher.update(@as([*]const u8, @ptrCast(extr))[0..size_map[@intFromEnum(kind)]]);
            return hasher.final();
        }

        pub fn cmp(
            akind: Kind,
            bkind: Kind,
            ainputs: []const ?*Node,
            binputs: []const ?*Node,
            aextra: *const anyopaque,
            bextra: *const anyopaque,
        ) bool {
            return akind == bkind and
                std.mem.eql(?*Node, ainputs, binputs) and
                std.mem.eql(
                u8,
                @as([*]const u8, @ptrCast(aextra))[0..size_map[@intFromEnum(akind)]],
                @as([*]const u8, @ptrCast(bextra))[0..size_map[@intFromEnum(bkind)]],
            );
        }
    };

    pub fn init(gpa: std.mem.Allocator) Self {
        var self = Self{
            .arena = .init(gpa),
            .tmp_arena = .init(gpa),
        };
        self.root = self.addNode(.Start, &.{}, .{});
        return self;
    }

    pub fn deinit(self: *Self) void {
        self.arena.deinit();
        self.tmp_arena.deinit();
        self.* = undefined;
    }

    pub fn reset(self: *Self) void {
        std.debug.assert(self.arena.reset(.free_all));
        self.next_id = 0;
        self.root = self.addNode(.Start, &.{}, .{});
        self.interner = .{};
    }

    const Inserter = struct {
        kind: Kind,
        inputs: []const ?*Node,
        extra: *const anyopaque,

        pub fn hash(_: anytype, k: InternedNode) u64 {
            return k.hash;
        }

        pub fn eql(s: @This(), a: InternedNode, b: InternedNode) bool {
            if (a.hash != b.hash) return false;
            return Node.cmp(s.kind, b.node.kind, s.inputs, b.node.inputs(), s.extra, b.node.anyextra());
        }
    };

    const InsertMap = std.hash_map.HashMapUnmanaged(InternedNode, void, Inserter, 70);

    pub fn internNode(self: *Self, kind: Kind, inputs: []const ?*Node, extra: *const anyopaque) InsertMap.GetOrPutResult {
        const map: *InsertMap = @ptrCast(&self.interner);

        return map.getOrPutContext(self.arena.allocator(), .{
            .node = undefined,
            .hash = Node.hash(kind, inputs, extra),
        }, Inserter{ .kind = kind, .inputs = inputs, .extra = extra }) catch unreachable;
    }

    pub fn addNode(self: *Self, comptime kind: Kind, inputs: []const ?*Node, extra: ClassFor(kind)) *Node {
        return self.addNodeUntyped(kind, inputs, extra);
    }

    pub fn addNodeUntyped(self: *Self, kind: Kind, inputs: []const ?*Node, extra: anytype) *Node {
        if (Node.isInterned(kind, inputs)) {
            const entry = self.internNode(kind, inputs, &extra);
            if (!entry.found_existing) entry.key_ptr.node = self.addNodeNoIntern(kind, inputs, extra);
            return entry.key_ptr.node;
        } else {
            return self.addNodeNoIntern(kind, inputs, extra);
        }
    }

    pub fn addNodeNoIntern(self: *Self, kind: Kind, inputs: []const ?*Node, extra: anytype) *Node {
        const Layout = extern struct {
            base: Node,
            extra: @TypeOf(extra),
        };

        const node = self.arena.allocator().create(Layout) catch unreachable;
        const owned_inputs = self.arena.allocator().dupe(?*Node, inputs) catch unreachable;

        node.* = .{
            .base = .{
                .input_base = owned_inputs.ptr,
                .input_len = @intCast(owned_inputs.len),
                .input_ordered_len = @intCast(owned_inputs.len),
                .output_base = (self.arena.allocator().alloc(*Node, 0) catch unreachable).ptr,
                .kind = kind,
                .id = self.next_id,
            },
            .extra = extra,
        };

        for (owned_inputs) |on| if (on) |def| {
            self.addUse(def, &node.base);
        };

        self.next_id += 1;

        return &node.base;
    }

    pub fn isDead(node: ?*Node) bool {
        return node == null or node.?.data_type == .dead;
    }

    pub fn subsumeNoKill(self: *Self, this: *Node, target: *Node) void {
        for (target.outputs()) |use| {
            const index = std.mem.indexOfScalar(?*Node, use.inputs(), target) orelse {
                std.debug.panic("{} {any} {}", .{ this, target.outputs(), use });
            };

            use.inputs()[index] = this;
            self.addUse(this, use);
        }

        target.output_len = 0;
    }

    pub fn subsume(self: *Self, this: *Node, target: *Node) void {
        self.subsumeNoKill(this, target);
        target.kill();
    }

    pub fn setInput(self: *Self, use: *Node, idx: usize, def: ?*Node) void {
        if (use.inputs()[idx] == def) return;
        if (use.inputs()[idx]) |n| {
            n.removeUse(use);
        }

        use.inputs()[idx] = def;
        if (def) |d| {
            self.addUse(d, use);
        }
    }

    pub fn addDep(self: *Self, use: *Node, def: *Node) void {
        if (use.input_ordered_len == use.input_len or std.mem.indexOfScalar(?*Node, use.input_base[use.input_ordered_len..use.input_len], null) == null) {
            const new_cap = @max(use.input_len, 1) * 2;
            const new_inputs = self.arena.allocator().realloc(use.inputs(), new_cap) catch unreachable;
            @memset(new_inputs[use.input_len..], null);
            use.input_base = new_inputs.ptr;
            use.input_len = new_cap;
        }

        for (use.input_base[use.input_ordered_len..use.input_len]) |*slot| {
            if (slot.* == null) {
                slot.* = def;
                break;
            }
        } else unreachable;
    }

    pub fn addUse(self: *Self, def: *Node, use: *Node) void {
        if (def.output_len == def.output_cap) {
            const new_cap = @max(def.output_cap, 1) * 2;
            const new_outputs = self.arena.allocator().realloc(def.outputs(), new_cap) catch unreachable;
            def.output_base = new_outputs.ptr;
            def.output_cap = new_cap;
        }

        def.output_base[def.output_len] = use;
        def.output_len += 1;
    }

    pub inline fn beginTmpAlloc(self: *Self) std.mem.Allocator {
        std.debug.assert(self.tmp_arena.reset(.retain_capacity));
        return self.tmp_arena.allocator();
    }

    pub const Frame = struct { *Node, []const ?*Node };

    pub fn traversePostorder(ctx: anytype, inp: *Node, stack: *std.ArrayList(Frame), visited: *std.DynamicBitSet) void {
        const Ctx = if (@typeInfo(@TypeOf(ctx)) == .pointer) @TypeOf(ctx.*) else @TypeOf(ctx);
        const dir = Ctx.dir;

        stack.append(.{ inp, @field(Node, dir)(inp) }) catch unreachable;
        visited.set(inp.id);
        while (stack.items.len > 0) {
            const frame = &stack.items[stack.items.len - 1];
            if (frame[1].len == 0) {
                _ = stack.pop();
                ctx.each(frame[0]);
                continue;
            }
            const node = frame[1][0];
            frame[1] = frame[1][1..];
            if (node) |n| if ((!@hasDecl(Ctx, "filter") or ctx.filter(n)) and !visited.isSet(n.id)) {
                visited.set(n.id);
                stack.append(.{ n, @field(Node, dir)(n) }) catch unreachable;
            };
        }
    }

    pub fn gcm(self: *Self) void {
        const tmp = self.beginTmpAlloc();

        var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
        var stack = std.ArrayList(Frame).init(tmp);

        const cfg_rpo = cfg_rpo: {
            var rpo = std.ArrayList(*CfgNode).init(tmp);

            traversePostorder(struct {
                rpo: *std.ArrayList(*CfgNode),
                pub const dir = "outputs";
                pub fn each(ctx: @This(), node: *Node) void {
                    ctx.rpo.append(node.asCfg().?) catch unreachable;
                }
                pub fn filter(_: @This(), node: *Node) bool {
                    return node.isCfg();
                }
            }{ .rpo = &rpo }, self.root, &stack, &visited);

            std.mem.reverse(*CfgNode, rpo.items);

            break :cfg_rpo rpo.items;
        };

        if (false) add_mach_moves: {
            for (cfg_rpo) |n| if (n.base.kind == .Loop) {
                for (tmp.dupe(*Node, n.base.outputs()) catch unreachable) |o| if (o.kind == .Phi) {
                    std.debug.assert(o.inputs().len == 3);
                    const lhs = self.addNode(.MachMove, &.{ null, o.inputs()[1].? }, {});
                    const rhs = self.addNode(.MachMove, &.{ null, o.inputs()[2].? }, {});
                    const new_phy = self.addNode(.Phi, &.{ &n.base, lhs, rhs }, {});
                    const fin = self.addNode(.MachMove, &.{ null, new_phy }, {});
                    self.subsume(fin, o);
                };
            };
            break :add_mach_moves;
        }

        sched_early: {
            for (cfg_rpo) |cfg| {
                for (cfg.base.inputs()) |oinp| if (oinp) |inp| {
                    shedEarly(self, inp, cfg_rpo[1], &stack, &visited);
                };

                if (cfg.base.kind == .Region or cfg.base.kind == .Loop) {
                    for (tmp.dupe(*Node, cfg.base.outputs()) catch unreachable) |o| {
                        if (o.kind == .Phi) {
                            shedEarly(self, o, cfg_rpo[1], &stack, &visited);
                        }
                    }
                }
            }

            break :sched_early;
        }

        sched_late: {
            const late_scheds = tmp.alloc(?*CfgNode, self.next_id) catch unreachable;
            @memset(late_scheds, null);
            const nodes = tmp.alloc(?*Node, self.next_id) catch unreachable;
            @memset(nodes, null);
            var work_list = std.ArrayList(*Node).init(tmp);
            visited.setRangeValue(.{ .start = 0, .end = visited.capacity() }, false);

            work_list.append(self.end) catch unreachable;
            visited.set(self.end.id);

            task: while (work_list.popOrNull()) |t| {
                visited.unset(t.id);
                std.debug.assert(late_scheds[t.id] == null);

                if (t.asCfg()) |c| {
                    late_scheds[c.base.id] = if (c.base.isBasicBlockStart()) c else c.base.cfg0();
                } else if (t.isPinned()) {
                    late_scheds[t.id] = t.cfg0().?;
                } else {
                    todo(.Proj, "pin projs to the parent");

                    for (t.outputs()) |o| {
                        if (late_scheds[o.id] == null) {
                            continue :task;
                        }
                    }

                    if (t.isLoad()) {
                        for (t.mem().outputs()) |p| {
                            if (p.kind == .Store and late_scheds[p.id] == null) {
                                continue :task;
                            }
                        }
                    }

                    schedule_late: {
                        const early = t.cfg0() orelse unreachable;

                        var olca: ?*CfgNode = null;
                        for (t.outputs()) |o| {
                            const other = t.useBlock(o, late_scheds);
                            olca = if (olca) |l| l.findLca(other) else other;
                        }
                        var lca = olca.?;

                        if (t.isLoad()) add_antideps: {
                            var cursor = lca;
                            while (cursor != early.idom()) : (cursor = cursor.idom()) {
                                std.debug.assert(cursor.base.kind != .Start);
                                cursor.ext.antidep = t.id;
                            }

                            for (t.mem().outputs()) |o| switch (o.kind) {
                                .Store, .Call => {
                                    const sdef = o.cfg0().?;
                                    var lcar = late_scheds[o.id].?;
                                    while (lcar != sdef.idom()) : (lcar = lcar.idom()) {
                                        if (lcar.ext.antidep == t.id) {
                                            lca = lcar.findLca(lca);
                                            if (lca == sdef) {
                                                self.addDep(o, t);
                                                self.addUse(t, o);
                                            }
                                            break;
                                        }
                                    }
                                },
                                .Phi => {
                                    for (o.inputs()[1..], o.cfg0().?.base.inputs()) |inp, oblk| if (inp.? == t.mem()) {
                                        const sdef = t.mem().cfg0().?;
                                        var lcar = oblk.?.asCfg().?;
                                        while (lcar != sdef.idom()) : (lcar = lcar.idom()) {
                                            if (lcar.ext.antidep == t.id) {
                                                lca = lcar.findLca(lca);
                                            }
                                        }
                                    };
                                },
                                .Local => {},
                                .Return => {},
                                else => if (!o.isLoad()) std.debug.panic("{any}", .{o.kind}),
                            };

                            break :add_antideps;
                        }

                        var best = lca;
                        var cursor = best.base.cfg0().?;
                        while (cursor != early.idom()) : (cursor = cursor.idom()) {
                            std.debug.assert(cursor.base.kind != .Start);
                            if (cursor.better(best)) best = cursor;
                        }

                        if (best.base.isBasicBlockEnd()) {
                            best = best.idom();
                        }

                        nodes[t.id] = t;
                        late_scheds[t.id] = best;

                        break :schedule_late;
                    }
                }

                for (t.inputs()) |odef| if (odef) |def| {
                    if (late_scheds[def.id] == null) {
                        if (!visited.isSet(def.id)) {
                            visited.set(def.id);
                            work_list.append(def) catch unreachable;
                        }

                        for (def.outputs()) |out| {
                            if (out.isLoad() and late_scheds[out.id] == null and !visited.isSet(def.id)) {
                                visited.set(def.id);
                                work_list.append(def) catch unreachable;
                            }
                        }
                    }
                };
            }

            for (nodes, late_scheds) |on, l| if (on) |n| {
                todo(.Proj, "ignore them");
                self.setInput(n, 0, &l.?.base);
            };

            break :sched_late;
        }

        compact_ids: {
            visited.setRangeValue(.{ .start = 0, .end = visited.capacity() }, false);
            self.block_count = 0;
            self.instr_count = 0;
            self.root.schedule = 0;

            const postorder = collectPostorder(self, tmp, &visited);
            for (postorder) |bb| {
                const node = &bb.base;
                node.schedule = self.block_count;
                self.block_count += 1;

                const NodeMeta = struct {
                    unscheduled_deps: u16 = 0,
                    ready_unscheduled_deps: u16 = 0,
                    priority: u16,
                };

                // init meta
                const extra = tmp.alloc(NodeMeta, node.outputs().len) catch unreachable;
                for (node.outputs(), extra, 0..) |o, *e, i| {
                    o.schedule = @intCast(i);
                    e.* = .{ .priority = if (o.isCfg())
                        0
                    else if (o.kind == .Phi or o.kind == .Mem or o.kind == .Ret)
                        100
                    else
                        50 };
                    if (o.kind != .Phi) {
                        for (o.inputs()[1..]) |j| if (j != null) if (j.?.inputs()[0] == o.inputs()[0]) {
                            e.unscheduled_deps += 1;
                        };
                    }
                }

                const outs = node.outputs();
                var ready: usize = 0;
                for (outs) |*o| {
                    if (extra[o.*.schedule].unscheduled_deps == 0) {
                        std.mem.swap(*Node, &outs[ready], o);
                        ready += 1;
                    }
                }

                var scheduled: usize = 0;
                while (scheduled < outs.len) {
                    std.debug.assert(ready != scheduled);

                    var pick = scheduled;
                    for (outs[scheduled + 1 .. ready], scheduled + 1..) |o, i| {
                        if (extra[o.schedule].priority > extra[outs[pick].schedule].priority) {
                            pick = i;
                        }
                    }

                    const n = outs[pick];
                    for (n.outputs()) |def| if (def.inputs()[0] == n.inputs()[0] and def.kind != .Phi) {
                        extra[def.schedule].unscheduled_deps -= 1;
                    };

                    std.mem.swap(*Node, &outs[scheduled], &outs[pick]);
                    scheduled += 1;

                    for (outs[ready..]) |*o| {
                        if (extra[o.*.schedule].unscheduled_deps == 0) {
                            std.debug.assert(o.*.kind != .Phi);
                            std.mem.swap(*Node, &outs[ready], o);
                            ready += 1;
                        }
                    }
                }

                for (node.outputs()) |o| {
                    o.schedule = self.instr_count;
                    self.instr_count += 1;
                }
            }

            break :compact_ids;
        }
    }

    fn shedEarly(self: *Self, node: *Node, early: *CfgNode, stack: *std.ArrayList(Frame), visited: *std.DynamicBitSet) void {
        std.debug.assert(early.base.kind != .Start);
        if (visited.isSet(node.id)) return;
        visited.set(node.id);

        for (node.inputs()) |i| if (i) |ii| if (ii.kind != .Phi) {
            shedEarly(self, ii, early, stack, visited);
        };

        if (!node.isPinned()) {
            var best = early;
            if (node.inputs()[0]) |n| if (n.asCfg()) |cn| {
                if (n.kind != .Start) best = cn;
            };

            for (node.inputs()[1..]) |oin| if (oin) |in| {
                if (in.cfg0().?.idepth() > best.idepth()) {
                    best = in.cfg0().?;
                }
            };

            std.debug.assert(best.base.kind != .Start);
            self.setInput(node, 0, &best.base);
        }
    }

    pub fn iterPeeps(self: *Self) void {
        const tmp = self.beginTmpAlloc();

        var worklist = WorkList.init(tmp, self.next_id) catch unreachable;
        worklist.add(self.end);
        var i: usize = 0;
        while (i < worklist.list.items.len) : (i += 1) {
            for (worklist.list.items[i].inputs()) |oi| if (oi) |o| {
                worklist.add(o);
            };

            for (worklist.list.items[i].outputs()) |o| {
                worklist.add(o);
            }
        }

        while (worklist.pop()) |t| {
            if (t.outputs().len == 0 and t != self.end) {
                for (t.inputs()) |ii| if (ii) |ia| worklist.add(ia);
                t.kill();
                continue;
            }

            if (idealize(self, t, &worklist)) |nt| {
                for (t.inputs()) |ii| if (ii) |ia| worklist.add(ia);
                for (t.outputs()) |o| worklist.add(o);
                self.subsume(nt, t);
                continue;
            }

            if (Mach.idealize(self, t, &worklist)) |nt| {
                self.subsume(nt, t);
                continue;
            }
        }

        i = 0;
        worklist.add(self.end);
        while (i < worklist.list.items.len) : (i += 1) {
            for (worklist.list.items[i].inputs()) |oi| if (oi) |o| {
                worklist.add(o);
            };

            for (worklist.list.items[i].outputs()) |o| {
                worklist.add(o);
            }
        }
    }

    pub fn collectDfs(self: *Self, arena: std.mem.Allocator, visited: *std.DynamicBitSet) []*CfgNode {
        var postorder = std.ArrayList(*CfgNode).init(arena);
        collectPostorder3(self, self.root, arena, &postorder, visited, true);
        return postorder.items;
    }

    pub fn collectPostorder3(
        self: *Self,
        node: *Node,
        arena: std.mem.Allocator,
        pos: *std.ArrayList(*CfgNode),
        visited: *std.DynamicBitSet,
        comptime only_basic: bool,
    ) void {
        if (visited.isSet(node.id)) {
            return;
        }
        visited.set(node.id);
        pos.append(node.asCfg().?) catch unreachable;
        for (node.outputs()) |o| if (o.isCfg()) collectPostorder3(self, o, arena, pos, visited, only_basic);
    }

    // TODO: does not work
    pub fn mem2reg(self: *Self) void {
        const tmp = self.beginTmpAlloc();

        var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
        const postorder = self.collectDfs(tmp, &visited);

        for (postorder, 0..) |bb, i| {
            bb.base.schedule = @intCast(i);
        }

        var local_count: u16 = 0;
        std.debug.assert(self.root.outputs()[1].kind == .Mem);
        for (self.root.outputs()[1].outputs()) |o| {
            if (o.kind == .Local) b: {
                for (o.outputs()) |oo| {
                    if ((oo.kind != .Store and !oo.isLoad()) or oo.base() != o) {
                        o.schedule = std.math.maxInt(u16);
                        break :b;
                    }
                }
                const extra = o.extra(.Local);
                std.debug.assert(extra.* == 8);
                o.schedule = local_count;
                local_count += 1;
                continue;
            }
        }

        const Local = union(enum) {
            Node: *Node,
            Loop: *Join,

            const Join = struct { done: bool, ctrl: *Node, items: []?L };

            const L = @This();

            fn resolve(func: *Self, scope: []?L, index: usize) *Node {
                return switch (scope[index].?) {
                    .Node => |n| n,
                    .Loop => |loop| {
                        if (!loop.done) {
                            const initVal = resolve(func, loop.items, index);

                            if (!loop.items[index].?.Node.isLazyPhi(loop.ctrl)) {
                                loop.items[index].? = .{ .Node = func.addNode(.Phi, &.{ loop.ctrl, initVal, null }, {}) };
                            }
                        }
                        scope[index] = loop.items[index];
                        return scope[index].?.Node;
                    },
                };
            }
        };

        const BBState = union(enum) {
            Fork: struct {
                saved: []?Local,
            },
            Join: *Local.Join,
        };

        var locals = tmp.alloc(?Local, local_count) catch unreachable;
        @memset(locals, null);

        var states = tmp.alloc(?BBState, postorder.len) catch unreachable;
        @memset(states, null);

        var to_remove = std.ArrayList(*Node).init(tmp);
        for (postorder[1..]) |bbc| {
            const bb = &bbc.base;

            var parent_succs: usize = 0;
            const parent = bb.inputs()[0].?;
            std.debug.assert(parent.isCfg());
            for (parent.outputs()) |o| parent_succs += @intFromBool(o.isCfg());
            std.debug.assert(parent_succs >= 1 and parent_succs <= 2);
            // handle fork
            if (parent_succs == 2) {
                // this is the second branch, restore the value
                if (states[parent.schedule]) |s| {
                    locals = s.Fork.saved;
                } else {
                    // we will visit this eventually
                    states[parent.schedule] = .{ .Fork = .{ .saved = tmp.dupe(?Local, locals) catch unreachable } };
                }
            }

            for (tmp.dupe(*Node, bb.outputs()) catch unreachable) |o| {
                if (o.kind == .Load and o.base().kind == .Local and o.base().schedule != std.math.maxInt(u16)) {
                    to_remove.append(o) catch unreachable;
                    self.subsumeNoKill(Local.resolve(self, locals, o.base().schedule), o);
                }

                if (o.kind == .Store and o.base().kind == .Local and o.base().schedule != std.math.maxInt(u16)) {
                    to_remove.append(o) catch unreachable;
                    locals[o.base().schedule] = .{ .Node = o.value() };
                }
            }

            const child: *Node = for (bb.outputs()) |o| {
                if (o.isCfg()) break o;
            } else continue;
            var child_preds: usize = 0;
            for (child.inputs()) |b| child_preds += @intFromBool(b != null and b.?.isCfg() and b.?.inputs()[0] != null);
            std.debug.assert(child_preds >= 1 and child_preds <= 2);
            // handle joins
            if (child_preds == 2) {
                // eider we arrived from the back branch or the other side of the split
                if (states[child.schedule]) |s| {
                    std.debug.assert(s.Join.ctrl == child);
                    for (s.Join.items, locals, 0..) |lhs, rhsm, i| {
                        if (lhs == null) continue;
                        if (lhs.? == .Node and lhs.?.Node.isLazyPhi(s.Join.ctrl)) {
                            var rhs = rhsm;
                            if (rhs.? == .Loop and rhs.?.Loop != s.Join) {
                                rhs = .{ .Node = Local.resolve(self, locals, i) };
                            }
                            if (rhs.? == .Node) {
                                self.setInput(lhs.?.Node, 2, rhs.?.Node);
                            } else {
                                const prev = lhs.?.Node.inputs()[1].?;
                                self.subsume(prev, lhs.?.Node);
                                s.Join.items[i].?.Node = prev;
                            }
                        }
                    }
                    s.Join.done = true;
                } else {
                    // first time seeing, this ca also be a region, needs renaming I guess
                    const loop = tmp.create(Local.Join) catch unreachable;
                    loop.* = .{
                        .done = false,
                        .ctrl = child,
                        .items = tmp.dupe(?Local, locals) catch unreachable,
                    };
                    @memset(locals, .{ .Loop = loop });
                    states[child.schedule] = .{ .Join = loop };
                }
            }
        }

        for (to_remove.items) |tr| {
            if (tr.kind == .Load) tr.kill() else {
                self.subsume(tr.mem(), tr);
            }
        }
    }

    fn idealize(self: *Self, node: *Node, worklist: *WorkList) ?*Node {
        const inps = node.inputs();

        var is_dead = node.kind == .Region and isDead(inps[0]) and isDead(inps[1]);
        is_dead = is_dead or (node.kind != .Start and node.kind != .Region and
            node.isCfg() and isDead(inps[0]));

        if (is_dead) {
            node.data_type = .dead;
            for (node.outputs()) |o| worklist.add(o);
            return null;
        }

        if (node.kind == .Region) b: {
            std.debug.assert(node.inputs().len == 2);
            const idx = for (node.inputs(), 0..) |in, i| {
                if (isDead(in)) break i;
            } else break :b;

            var iter = std.mem.reverseIterator(node.outputs());
            while (iter.next()) |o| if (o.kind == .Phi) {
                for (o.outputs()) |oo| worklist.add(oo);
                self.subsume(o.inputs()[(1 - idx) + 1].?, o);
            };

            return node.inputs()[1 - idx].?.inputs()[0];
        }

        if (node.kind == .Loop) b: {
            if (!isDead(node.inputs()[1])) break :b;

            var iter = std.mem.reverseIterator(node.outputs());
            while (iter.next()) |o| if (o.kind == .Phi) {
                for (o.outputs()) |oo| worklist.add(oo);
                self.subsume(o.inputs()[1].?, o);
            };

            return node.inputs()[0].?.inputs()[0];
        }

        if (node.kind == .Store) {
            if (node.base().kind == .Local and node.cfg0() != null) {
                const dinps = self.arena.allocator().dupe(?*Node, node.inputs()) catch unreachable;
                dinps[0] = null;
                const st = self.addNode(.Store, dinps, {});
                worklist.add(st);
                return st;
            }

            if (node.base().kind == .Local and node.outputs().len == 1 and node.outputs()[0].kind == .Return) {
                return node.mem();
            }
        }

        if (node.kind == .Load) {
            var earlier = node.mem();

            if (node.base().kind == .Local and node.cfg0() != null) {
                const ld = self.addNode(.Load, &.{ null, inps[1], inps[2] }, {});
                worklist.add(ld);
                return ld;
            }

            while (earlier.kind == .Store and
                (earlier.cfg0() == node.cfg0() or node.cfg0() == null) and
                noAlias(earlier.base(), node.base()))
            {
                earlier = earlier.mem();
            }

            if (earlier.kind == .Store and
                earlier.base() == node.base() and
                earlier.data_type == node.data_type)
            {
                return earlier.value();
            }

            if (earlier.kind == .Phi) {
                std.debug.assert(earlier.inputs().len == 3);
                var l, var r = .{ earlier.inputs()[1].?, earlier.inputs()[2].? };

                while (l.kind == .Store and
                    (l.cfg0() == node.cfg0() or node.cfg0() == null) and
                    noAlias(l.base(), node.base()))
                {
                    l = l.mem();
                }

                while (r.kind == .Store and
                    (r.cfg0() == node.cfg0() or node.cfg0() == null) and
                    noAlias(r.base(), node.base()))
                {
                    r = r.mem();
                }

                if (l.kind == .Store and r.kind == .Store and
                    l.base() == r.base() and l.base() == node.base() and
                    l.data_type == r.data_type and l.data_type == node.data_type)
                {
                    return self.addNode(.Phi, &.{ earlier.inputs()[0].?, l.value(), r.value() }, {});
                }
            }

            if (earlier != node.mem()) {
                return self.addNode(.Load, &.{ inps[0], earlier, inps[2] }, {});
            }
        }

        if (node.kind == .Phi) {
            const region, const l, const r = .{ inps[0].?, inps[1].?, inps[2].? };

            if (r == node) return l;

            if (region.kind == .Loop) b: {
                var cursor = r;
                var looped = false;

                for (node.outputs()) |o| {
                    if (o.kind != .Store and o.kind != .Return) break :b;
                }

                w: while (!looped) {
                    for (cursor.outputs()) |o| {
                        if (o == node) {
                            looped = true;
                        } else if (o.kind != .Store) {
                            looped = false;
                            break :w;
                        }
                    }
                }

                if (looped) {
                    return l;
                }
            }
        }

        return null;
    }

    pub fn noAlias(lbase: *Node, rbase: *Node) bool {
        if (lbase.kind == .Local and rbase.kind == .Local) return lbase != rbase;
        if (lbase.kind == .Local and rbase.kind == .Arg) return true;
        if (lbase.kind == .Arg and rbase.kind == .Local) return true;
        return false;
    }

    pub fn logNid(wr: anytype, nid: usize, cc: std.io.tty.Config) void {
        cc.setColor(wr, @enumFromInt(1 + nid % 15)) catch unreachable;
        wr.print("%{d}", .{nid}) catch unreachable;
        cc.setColor(wr, .reset) catch unreachable;
    }

    pub fn todo(comptime variant: anytype, comptime message: []const u8) void {
        if (@hasField(Kind, @tagName(variant))) @compileError(message);
    }

    pub fn collectPostorder(self: *Self, arena: std.mem.Allocator, visited: *std.DynamicBitSet) []*CfgNode {
        var postorder = std.ArrayList(*CfgNode).init(arena);

        collectPostorder2(self, self.root, arena, &postorder, visited, true);

        return postorder.items;
    }

    pub fn collectPostorderAll(self: *Self, arena: std.mem.Allocator, visited: *std.DynamicBitSet) []*CfgNode {
        var postorder = std.ArrayList(*CfgNode).init(arena);
        self.collectPostorder2(self.root, arena, &postorder, visited, false);
        return postorder.items;
    }

    pub fn collectPostorder2(
        self: *Self,
        node: *Node,
        arena: std.mem.Allocator,
        pos: *std.ArrayList(*CfgNode),
        visited: *std.DynamicBitSet,
        comptime only_basic: bool,
    ) void {
        switch (node.kind) {
            .Region => {
                if (!visited.isSet(node.id)) {
                    visited.set(node.id);
                    if (node.inputs()[0].?.inputs()[0] != null and node.inputs()[1].?.inputs()[0] != null) {
                        return;
                    }
                }
            },
            else => {
                if (visited.isSet(node.id)) {
                    return;
                }
                visited.set(node.id);
            },
        }

        if (!only_basic or node.isBasicBlockStart()) pos.append(node.asCfg().?) catch unreachable;
        if (node.isSwapped()) {
            var iter = std.mem.reverseIterator(node.outputs());
            while (iter.next()) |o| if (o.isCfg()) collectPostorder2(self, o, arena, pos, visited, only_basic);
        } else {
            for (node.outputs()) |o| if (o.isCfg()) collectPostorder2(self, o, arena, pos, visited, only_basic);
        }
    }

    pub fn fmtScheduled(self: *Self, writer: anytype, colors: std.io.tty.Config) void {
        const tmp = self.beginTmpAlloc();

        var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;

        self.root.fmt(self.block_count, writer, colors);
        writer.writeAll("\n") catch unreachable;
        for (collectPostorder(self, tmp, &visited)) |p| {
            p.base.fmt(self.block_count, writer, colors);

            writer.writeAll("\n") catch unreachable;
            for (p.base.outputs()) |o| {
                writer.writeAll("  ") catch unreachable;
                o.fmt(self.instr_count, writer, colors);
                writer.writeAll("\n") catch unreachable;
            }
        }
    }

    pub fn fmtLog(self: *Self) void {
        self.fmt(std.io.getStdErr().writer(), std.io.tty.detectConfig(std.io.getStdErr()));
    }

    pub fn fmtUnscheduled(self: *Self, writer: anytype, colors: std.io.tty.Config) void {
        const tmp = self.beginTmpAlloc();

        var worklist = Self.WorkList.init(tmp, self.next_id) catch unreachable;

        worklist.add(self.end);
        var i: usize = 0;
        while (i < worklist.list.items.len) : (i += 1) {
            for (worklist.list.items[i].inputs()) |oi| if (oi) |o| {
                worklist.add(o);
            };

            for (worklist.list.items[i].outputs()) |o| {
                worklist.add(o);
            }
        }

        std.mem.reverse(*Node, worklist.list.items);

        for (worklist.list.items) |p| {
            p.fmt(null, writer, colors);
            writer.writeAll("\n") catch unreachable;
        }
    }
} {
    return undefined;
}
