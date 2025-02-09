arena: std.heap.ArenaAllocator,
tmp_arena: std.heap.ArenaAllocator,
next_id: u16 = 0,
block_count: u16 = undefined,
instr_count: u16 = undefined,
root: *Node = undefined,
end: *Node = undefined,

const std = @import("std");
const Lexer = @import("Lexer.zig");
const Types = @import("Types.zig");
const Func = @This();

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

pub const DataType = enum(u16) {
    void,
    dead,
};

pub const Node = extern struct {
    kind: NodeKind,
    id: u16,
    schedule: u16 = undefined,
    data_type: DataType = .void,

    input_ordered_len: u16,
    input_len: u16,
    output_len: u16 = 0,
    output_cap: u16 = 0,

    input_base: [*]?*Node,
    output_base: [*]*Node,

    const User = packed struct(usize) {
        pointer: usize,

        pub fn node(self: User) *Node {
            return @ptrFromInt(self.pointer);
        }
    };

    pub fn format(self: *const Node, comptime _: anytype, _: anytype, writer: anytype) !void {
        const colors = .escape_codes;
        self.fmt(null, writer, colors, @import("HbvmGen.zig").Mach);
    }

    pub fn mem(self: *Node) *Node {
        std.debug.assert(self.kind == .Load or self.kind == .Store);
        return self.inputs()[1].?;
    }

    pub fn base(self: *Node) *Node {
        std.debug.assert(self.kind == .Load or self.kind == .Store);
        return self.inputs()[2].?;
    }

    pub fn isLazyPhi(self: *Node, on_loop: *Node) bool {
        return self.kind == .Phi and self.inputs()[0] == on_loop and self.inputs()[2] == null;
    }

    pub fn inputs(self: *Node) []?*Node {
        return self.input_base[0..self.input_len];
    }

    pub fn dataDeps(self: *Node) []?*Node {
        const start: usize = @intFromBool(isMemOp(self.kind));
        return self.input_base[1 + start .. self.input_ordered_len];
    }

    pub fn kill(self: *Node) void {
        std.debug.assert(self.output_len == 0);
        for (self.inputs()) |oi| if (oi) |i| {
            i.removeUse(self);
        };
        self.* = undefined;
        self.id = std.math.maxInt(u16);
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

    pub fn machExtra(self: *Node, comptime Mach: type, comptime kind: std.meta.Tag(Mach)) *std.meta.TagPayload(Mach, kind) {
        std.debug.assert(splitKind(self.kind, Mach).Specific == kind);
        const ptr: *MachLayoutFor(Mach, kind) = @ptrCast(self);
        return &ptr.extra;
    }

    pub fn machExtraConst(self: *const Node, comptime Mach: type, comptime kind: std.meta.Tag(Mach)) *const std.meta.TagPayload(Mach, kind) {
        std.debug.assert(splitKind(self.kind, Mach).Specific == kind);
        const ptr: *const MachLayoutFor(Mach, kind) = @ptrCast(self);
        return &ptr.extra;
    }

    pub fn extraConst(self: *const Node, comptime kind: BuiltinNodeKind) *const ExtFor(kind) {
        std.debug.assert(self.kind == toKind(kind));
        const ptr: *const LayoutFor(kind) = @ptrCast(self);
        return &ptr.extra;
    }

    pub fn extra(self: *Node, comptime kind: BuiltinNodeKind) *ExtFor(kind) {
        std.debug.assert(self.kind == toKind(kind));
        const ptr: *LayoutFor(kind) = @ptrCast(self);
        return &ptr.extra;
    }

    pub fn subclass(self: *Node, comptime Ext: type) ?*SubclassFor(Ext) {
        switch (toBuiltinKind(self.kind) orelse return null) {
            inline else => |t| if (comptime isSubbclass(ExtFor(t), Ext)) {
                return @ptrCast(self);
            },
        }

        return null;
    }

    fn isSubbclass(Full: type, Sub: type) bool {
        var Cursor = Full;
        while (true) {
            if (Cursor == Sub) return true;
            if (@typeInfo(Cursor) != .@"struct" or !@hasField(Cursor, "base")) return false;
            Cursor = @TypeOf(@as(Cursor, undefined).base);
        }
    }

    pub fn machSubclass(self: *Node, comptime Ext: type) ?*SubclassFor(Ext) {
        switch (splitKind(self.kind, Ext).Specific) {
            inline else => |t| if (ExtFor(t) == Ext) {
                return @ptrCast(self);
            },
        }

        return null;
    }

    pub fn cfg0(self: *Node) ?*SubclassFor(Extra.Cfg) {
        if (self.kind == .Start) return self.subclass(Extra.Cfg);
        return (self.inputs()[0] orelse return null).subclass(Extra.Cfg);
    }

    pub fn useBlock(self: *Node, use: *Node, scheds: []const ?*CfgNode) *CfgNode {
        if (use.kind == .Phi) {
            std.debug.assert(use.inputs()[0].?.kind == .Region or use.inputs()[0].?.kind == .Loop);
            for (use.inputs()[0].?.inputs(), use.inputs()[1..]) |b, u| {
                if (u.? == self) {
                    return b.?.subclass(Extra.Cfg).?;
                }
            }
        }
        return scheds[use.id].?;
    }

    fn fmt(
        self: *const Node,
        scheduled: ?u16,
        writer: anytype,
        colors: std.io.tty.Config,
        comptime Mach: type,
    ) void {
        logNid(writer, self.id, colors);
        const name = switch (splitKind(self.kind, Mach)) {
            inline else => |t| @tagName(t),
        };

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

        switch (splitKind(self.kind, Mach)) {
            inline else => |b, tg| switch (b) {
                inline else => |t| {
                    const ext = switch (tg) {
                        .Builtin => self.extraConst(t),
                        .Specific => self.machExtraConst(Mach, t),
                    };
                    if (@TypeOf(ext.*) != void) {
                        if (!add_colon_space) {
                            writer.writeAll(": ") catch unreachable;
                            add_colon_space = true;
                        }

                        utils.logExtra(writer, ext, true) catch unreachable;
                    }
                },
            },
        }

        for (self.input_base[0..self.input_len][@min(@intFromBool(scheduled != null and
            (!isCfg(self.kind) or !isBasicBlockStart(self.kind))), self.input_base[0..self.input_len].len)..]) |oo| if (oo) |o|
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
};

pub const CfgNode = SubclassFor(Extra.Cfg);

pub const Extra = union(enum(u16)) {
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
    Local: extern union {
        size: usize,
        offset: usize,
    },
    // [?Cfg, thread, ptr]
    Load,
    // [?Cfg, thread, ptr, value, ...antideps]
    Store,
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
    If: extern struct {
        base: Cfg = .{},
        swapped: bool = false,
    },
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

    pub const Cfg = extern struct {
        idepth: u16 = 0,
        antidep: u16 = 0,
    };
};

pub const BuiltinNodeKind = std.meta.Tag(Extra);

pub const NodeKind = b: {
    var enm = @typeInfo(BuiltinNodeKind);
    enm.@"enum".is_exhaustive = false;
    break :b @Type(enm);
};

fn toKind(kind: anytype) NodeKind {
    return @enumFromInt(@intFromEnum(kind));
}

fn toBuiltinKind(kind: NodeKind) ?BuiltinNodeKind {
    if (@typeInfo(BuiltinNodeKind).@"enum".fields.len > @intFromEnum(kind)) {
        return @enumFromInt(@intFromEnum(kind));
    }

    return null;
}

fn splitKind(kind: NodeKind, comptime Mach: type) union(enum) { Builtin: BuiltinNodeKind, Specific: std.meta.Tag(Mach) } {
    if (@typeInfo(BuiltinNodeKind).@"enum".fields.len > @intFromEnum(kind)) {
        return .{ .Builtin = @enumFromInt(@intFromEnum(kind)) };
    } else {
        return .{ .Specific = @enumFromInt(@intFromEnum(kind)) };
    }
}

pub fn isPinned(k: NodeKind) bool {
    return isCfg(k) or k == .Ret or k == .Phi or k == .Mem;
}

pub fn isMemOp(k: NodeKind) bool {
    return switch (k) {
        .Load, .Local, .Store => true,
        else => false,
    };
}

pub fn isCfg(k: NodeKind) bool {
    return switch (toBuiltinKind(k) orelse return false) {
        inline else => |t| return comptime Node.isSubbclass(ExtFor(t), Extra.Cfg),
    };
}

pub fn isBasicBlockStart(k: NodeKind) bool {
    std.debug.assert(isCfg(k));
    return switch (k) {
        .Entry, .CallEnd, .Then, .Else, .Region, .Loop => true,
        else => false,
    };
}

pub fn isBasicBlockEnd(k: NodeKind) bool {
    std.debug.assert(isCfg(k));
    return switch (k) {
        .Return, .Call, .If, .Jmp => true,
        else => false,
    };
}

pub fn ExtFor(comptime kind: BuiltinNodeKind) type {
    return std.meta.TagPayload(Extra, kind);
}

fn MachLayoutFor(comptime Mach: type, comptime kind: std.meta.Tag(Mach)) type {
    return extern struct {
        base: Node,
        extra: std.meta.TagPayload(Mach, kind),
    };
}

fn LayoutFor(comptime kind: BuiltinNodeKind) type {
    return extern struct {
        base: Node,
        extra: ExtFor(kind),
    };
}

fn SubclassFor(comptime Ext: type) type {
    return extern struct {
        base: Node,
        extra: Ext,

        pub fn idepth(cfg: *@This()) u16 {
            const extra: *Extra.Cfg = &cfg.extra;

            if (extra.idepth != 0) return extra.idepth;
            extra.idepth = switch (cfg.base.kind) {
                .Start => return 0,
                .Region => cfg.idom().idepth(),
                else => cfg.base.cfg0().?.idepth() + 1,
            };
            return extra.idepth;
        }

        fn findLca(left: *@This(), right: *@This()) *@This() {
            var lc, var rc = .{ left, right };
            while (lc != rc) {
                if (!isCfg(lc.base.kind)) std.debug.panic("{}", .{lc.base});
                if (!isCfg(rc.base.kind)) std.debug.panic("{}", .{rc.base});
                if (lc.idepth() >= rc.idepth()) lc = lc.base.cfg0().?;
                if (rc.idepth() >= lc.idepth()) rc = rc.base.cfg0().?;
            }
            return lc;
        }

        fn idom(cfg: *@This()) *@This() {
            return switch (cfg.base.kind) {
                .Region => findLca(cfg.base.inputs()[0].?.subclass(Extra.Cfg).?, cfg.base.inputs()[1].?.subclass(Extra.Cfg).?),
                else => cfg.base.cfg0().?,
            };
        }

        fn better(cfg: *@This(), best: *@This()) bool {
            return cfg.idepth() > best.idepth() or
                (cfg.base.kind == .Jmp and cfg.base.outputs()[0].kind == .Loop) or
                isBasicBlockEnd(best.base.kind);
        }
    };
}

pub fn init(gpa: std.mem.Allocator) Func {
    var self = Func{
        .arena = std.heap.ArenaAllocator.init(gpa),
        .tmp_arena = std.heap.ArenaAllocator.init(gpa),
    };
    self.root = self.addNode(.Start, &.{}, .{});
    return self;
}

pub fn deinit(self: *Func) void {
    self.arena.deinit();
    self.tmp_arena.deinit();
    self.* = undefined;
}

pub fn reset(self: *Func) void {
    std.debug.assert(self.arena.reset(.free_all));
    self.next_id = 0;
    self.root = self.addNode(.Start, &.{}, .{});
}

pub fn addMachNode(
    self: *Func,
    comptime Mach: type,
    comptime kind: std.meta.Tag(Mach),
    inputs: []const ?*Node,
    extra: std.meta.TagPayload(Mach, kind),
) *Node {
    return self.addNodeLow(toKind(kind), inputs, extra);
}

pub fn addNode(self: *Func, comptime kind: BuiltinNodeKind, inputs: []const ?*Node, extra: ExtFor(kind)) *Node {
    return self.addNodeLow(toKind(kind), inputs, extra);
}

pub fn addNodeLow(self: *Func, comptime kind: NodeKind, inputs: []const ?*Node, extra: anytype) *Node {
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

pub fn iterPeeps(self: *Func, comptime Mach: type) void {
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

        if (self.idealize(t, &worklist)) |nt| {
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

fn isDead(node: ?*Node) bool {
    return node == null or node.?.data_type == .dead;
}

fn idealize(self: *Func, node: *Node, worklist: *WorkList) ?*Node {
    const inps = node.inputs();

    var is_dead = node.kind == .Region and isDead(inps[0]) and isDead(inps[1]);
    is_dead = is_dead or (node.kind != .Start and node.kind != .Region and
        isCfg(node.kind) and isDead(inps[0]));

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

    return null;
}

pub fn subsume(self: *Func, this: *Node, target: *Node) void {
    for (target.outputs()) |use| {
        const index = std.mem.indexOfScalar(?*Node, use.inputs(), target) orelse {
            std.debug.panic("{} {any} {}", .{ this, target.outputs(), use });
        };

        use.inputs()[index] = this;
        self.addUse(this, use);
    }

    target.output_len = 0;
    target.kill();
}

pub fn setInput(self: *Func, use: *Node, idx: usize, def: ?*Node) void {
    if (use.inputs()[idx] == def) return;
    if (use.inputs()[idx]) |n| {
        n.removeUse(use);
    }

    use.inputs()[idx] = def;
    if (def) |d| {
        self.addUse(d, use);
    }
}

pub fn addDep(self: *Func, use: *Node, def: *Node) void {
    if (use.input_ordered_len == use.input_len) {
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

pub fn addUse(self: *Func, def: *Node, use: *Node) void {
    if (def.output_len == def.output_cap) {
        const new_cap = @max(def.output_cap, 1) * 2;
        const new_outputs = self.arena.allocator().realloc(def.outputs(), new_cap) catch unreachable;
        def.output_base = new_outputs.ptr;
        def.output_cap = new_cap;
    }

    def.output_base[def.output_len] = use;
    def.output_len += 1;
}

pub inline fn beginTmpAlloc(self: *Func) std.mem.Allocator {
    std.debug.assert(self.tmp_arena.reset(.retain_capacity));
    return self.tmp_arena.allocator();
}

pub const Frame = struct { *Node, []const ?*Node };

pub fn gcm(self: *Func) void {
    const tmp = self.beginTmpAlloc();

    var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
    var stack = std.ArrayList(Frame).init(tmp);

    const cfg_rpo = cfg_rpo: {
        var rpo = std.ArrayList(*CfgNode).init(tmp);

        traversePostorder(struct {
            rpo: *std.ArrayList(*CfgNode),
            const dir = "outputs";
            fn each(ctx: @This(), node: *Node) void {
                ctx.rpo.append(node.subclass(Extra.Cfg).?) catch unreachable;
            }
            fn filter(_: @This(), node: *Node) bool {
                return isCfg(node.kind);
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
                self.shedEarly(inp, cfg_rpo[1], &stack, &visited);
            };

            if (cfg.base.kind == .Region or cfg.base.kind == .Loop) {
                for (tmp.dupe(*Node, cfg.base.outputs()) catch unreachable) |o| {
                    if (o.kind == .Phi) {
                        self.shedEarly(o, cfg_rpo[1], &stack, &visited);
                    }
                }
            }
        }

        break :sched_early;
    }

    sched_late: {
        const late_scheds = tmp.alloc(?*SubclassFor(Extra.Cfg), self.next_id) catch unreachable;
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

            if (t.subclass(Extra.Cfg)) |c| {
                late_scheds[c.base.id] = if (isBasicBlockStart(c.base.kind)) c else c.base.cfg0();
            } else if (t.kind == .Phi) {
                late_scheds[t.id] = t.cfg0().?;
            } else if (isPinned(t.kind)) {} else {
                todo(.Proj, "pin projs to the parent");

                for (t.outputs()) |o| {
                    if (late_scheds[o.id] == null) continue :task;
                }

                if (t.kind == .Load) {
                    for (t.mem().outputs()) |p| {
                        if (p.kind == .Store) continue :task;
                    }
                }

                schedule_late: {
                    const early = t.cfg0() orelse unreachable;

                    var lca: ?*CfgNode = null;
                    for (t.outputs()) |o| {
                        const other = t.useBlock(o, late_scheds);
                        lca = if (lca) |l| l.findLca(other) else other;
                    }

                    var best = lca.?;
                    var cursor = best.base.cfg0().?;
                    while (cursor != early.idom()) : (cursor = cursor.idom()) {
                        if (cursor.better(best)) best = cursor;
                    }

                    if (isBasicBlockEnd(best.base.kind)) {
                        best = best.idom();
                    }

                    if (t.kind == .Load) add_antideps: {
                        var cur = best;
                        while (cur != early.idom()) : (cur = cur.idom()) {
                            cur.extra.antidep = t.id;
                        }

                        for (t.mem().outputs()) |o| switch (o.kind) {
                            .Store, .CallEnd => {
                                const sdef = o.cfg0().?;
                                var curr = late_scheds[o.id].?;
                                while (curr != sdef.idom()) : (curr = curr.idom()) {
                                    if (curr.extra.antidep == t.id) {
                                        best = sdef.findLca(best);
                                        if (best == sdef) {
                                            self.addDep(o, t);
                                            self.addUse(t, o);
                                        }
                                    }
                                }
                            },
                            .Load, .Local => {},
                            else => std.debug.panic("{any}", .{o.kind}),
                        };

                        break :add_antideps;
                    }

                    nodes[t.id] = t;
                    late_scheds[t.id] = best;

                    break :schedule_late;
                }
            }

            for (t.inputs()) |odef| if (odef) |def| {
                if (late_scheds[def.id] == null and !visited.isSet(def.id)) {
                    visited.set(def.id);
                    work_list.append(def) catch unreachable;

                    if (def.kind == .Store) for (def.outputs()) |out| {
                        if (out.kind == .Load and !visited.isSet(def.id)) {
                            visited.set(def.id);
                            work_list.append(def) catch unreachable;
                        }
                    };
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

        const postorder = self.collectPostorder(tmp, &stack, &visited);
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
                e.* = .{ .priority = if (isCfg(o.kind)) 0 else if (o.kind == .Phi) 100 else 50 };
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

fn shedEarly(self: *Func, node: *Node, early: *CfgNode, stack: *std.ArrayList(Frame), visited: *std.DynamicBitSet) void {
    std.debug.assert(early.base.kind != .Start);
    if (visited.isSet(node.id)) return;
    visited.set(node.id);

    for (node.inputs()) |i| if (i) |ii| if (ii.kind != .Phi) {
        self.shedEarly(ii, early, stack, visited);
    };

    if (!isPinned(node.kind)) {
        var best = early;
        if (node.inputs()[0]) |n| if (n.subclass(Extra.Cfg)) |cn| {
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

fn logNid(wr: anytype, nid: usize, cc: std.io.tty.Config) void {
    cc.setColor(wr, @enumFromInt(1 + nid % 15)) catch unreachable;
    wr.print("%{d}", .{nid}) catch unreachable;
    cc.setColor(wr, .reset) catch unreachable;
}

pub fn collectPostorder(self: *Func, arena: std.mem.Allocator, stack: *std.ArrayList(Frame), visited: *std.DynamicBitSet) []*CfgNode {
    var postorder = std.ArrayList(*CfgNode).init(arena);

    self.collectPostorder2(self.root, arena, &postorder, visited);

    if (false) {
        stack.append(.{ self.root, self.root.inputs() }) catch unreachable;
        visited.set(self.root.id);

        while (stack.items.len > 0) {
            const frame = &stack.items[stack.items.len - 1];
            if (frame[1].len == 0) {
                _ = stack.pop();
                continue;
            }
            const node = frame[1][0];
            frame[1] = frame[1][1..];
            if (node) |n| if (isCfg(n.kind) and !visited.isSet(n.id)) {
                visited.set(n.id);
                stack.append(.{ n, n.inputs() }) catch unreachable;
            };
        }
    }

    return postorder.items;
}

pub fn collectPostorderAll(self: *Func, node: *Node, arena: std.mem.Allocator, pos: *std.ArrayList(*CfgNode), visited: *std.DynamicBitSet) void {
    switch (node.kind) {
        .Region => {
            if (!visited.isSet(node.id)) {
                visited.set(node.id);
                return;
            }
        },
        else => {
            if (visited.isSet(node.id)) {
                return;
            }
            visited.set(node.id);
        },
    }

    pos.append(node.subclass(Extra.Cfg).?) catch unreachable;
    for (node.outputs()) |o| if (isCfg(o.kind)) self.collectPostorderAll(o, arena, pos, visited);
}

pub fn collectPostorder2(self: *Func, node: *Node, arena: std.mem.Allocator, pos: *std.ArrayList(*CfgNode), visited: *std.DynamicBitSet) void {
    switch (node.kind) {
        .Region => {
            if (!visited.isSet(node.id)) {
                visited.set(node.id);
                return;
            }
        },
        else => {
            if (visited.isSet(node.id)) {
                return;
            }
            visited.set(node.id);
        },
    }

    if (isBasicBlockStart(node.kind)) pos.append(node.subclass(Extra.Cfg).?) catch unreachable;
    for (node.outputs()) |o| if (isCfg(o.kind)) self.collectPostorder2(o, arena, pos, visited);
}

pub fn fmtScheduled(self: *Func, writer: anytype, colors: std.io.tty.Config, comptime Mach: type) void {
    const tmp = self.beginTmpAlloc();

    var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
    var stack = std.ArrayList(Frame).init(tmp);

    self.root.fmt(self.block_count, writer, colors, Mach);
    writer.writeAll("\n") catch unreachable;
    for (self.collectPostorder(tmp, &stack, &visited)) |p| {
        p.base.fmt(self.block_count, writer, colors, Mach);

        writer.writeAll("\n") catch unreachable;
        for (p.base.outputs()) |o| {
            writer.writeAll("  ") catch unreachable;
            o.fmt(self.instr_count, writer, colors, Mach);
            writer.writeAll("\n") catch unreachable;
        }
    }
}

pub fn fmtLog(self: *Func, comptime Mach: type) void {
    self.fmt(std.io.getStdErr().writer(), std.io.tty.detectConfig(std.io.getStdErr()), Mach);
}

pub fn fmt(self: *Func, writer: anytype, colors: std.io.tty.Config, comptime Mach: type) void {
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

    std.mem.reverse(*Node, worklist.list.items);

    for (worklist.list.items) |p| {
        p.fmt(null, writer, colors, Mach);
        writer.writeAll("\n") catch unreachable;
    }
}

fn todo(comptime variant: anytype, comptime message: []const u8) void {
    if (@hasField(Extra, @tagName(variant))) @compileError(message);
}
