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

pub const Node = extern struct {
    kind: NodeKind,
    id: u16,
    schedule: u16 = undefined,

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

    fn fmt(
        self: *Node,
        scheduled: ?u16,
        writer: anytype,
        colors: std.io.tty.Config,
        comptime Mach: type,
    ) void {
        logNid(writer, self.id, colors);
        const name = switch (splitKind(self.kind, Mach)) {
            inline else => |t| @tagName(t),
        };

        if (scheduled) |_| {
            writer.print(" ={d} {s}", .{ self.schedule, name }) catch unreachable;
        } else {
            writer.print(" = {s}", .{name}) catch unreachable;
        }

        var add_colon_space = false;

        switch (splitKind(self.kind, Mach)) {
            .Builtin => |b| switch (b) {
                inline else => |t| {
                    const ext = self.extra(t);
                    if (@TypeOf(ext.*) != void) {
                        if (!add_colon_space) {
                            writer.writeAll(": ") catch unreachable;
                            add_colon_space = true;
                        }
                        writer.print("{any}", .{ext.*}) catch unreachable;
                    }
                },
            },
            .Specific => |s| switch (s) {
                inline else => |t| {
                    const ext = self.machExtra(Mach, t);
                    if (@TypeOf(ext.*) != void) {
                        if (!add_colon_space) {
                            writer.writeAll(": ") catch unreachable;
                            add_colon_space = true;
                        }
                        writer.print("{any}", .{ext.*}) catch unreachable;
                    }
                },
            },
        }

        for (self.inputs()[@min(@intFromBool(!isCfg(self.kind) or !isBasicBlockStart(self.kind)), self.inputs().len)..]) |oo| if (oo) |o| {
            if (!add_colon_space) {
                writer.writeAll(": ") catch unreachable;
                add_colon_space = true;
            } else {
                writer.writeAll(", ") catch unreachable;
            }
            logNid(writer, o.id, colors);
        };

        writer.writeAll("\n") catch unreachable;
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
        _ = self; // autofix
        todo(.Phi, "phis need to be forwarded to a block depending which use this is");
        return scheds[use.id].?;
    }
};

pub const CfgNode = SubclassFor(Extra.Cfg);

pub const Extra = union(enum(u16)) {
    Start: Cfg,
    // [Start]
    Arg: usize,
    // [Start]
    Entry: Cfg,
    // [Cfg, ret]
    Return: Cfg,
    // [?Cfg]
    CInt: i64,
    // [?Cfg, lhs, rhs]
    BinOp: Lexer.Lexeme,
    // [Cfg, ..args]
    Call: extern struct {
        base: Cfg = .{},
        id: Types.Func,

        pub fn format(self: *const @This(), comptime _: anytype, _: anytype, writer: anytype) !void {
            try writer.print("{}, {}", .{ self.id, self.base });
        }
    },
    CallEnd: Cfg,
    Ret: void,

    pub const Cfg = extern struct {
        idepth: u16 = 0,

        pub fn format(self: *const Cfg, comptime _: anytype, _: anytype, writer: anytype) !void {
            try writer.print("idpth: {}", .{self.idepth});
        }
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
    return isCfg(k) or k == .Ret;
}

pub fn isCfg(k: NodeKind) bool {
    return switch (k) {
        .Return, .Entry, .Start, .Call, .CallEnd => true,
        else => false,
    };
}

pub fn isBasicBlockStart(k: NodeKind) bool {
    std.debug.assert(isCfg(k));
    return switch (k) {
        .Entry, .CallEnd => true,
        else => false,
    };
}

pub fn isBasicBlockEnd(k: NodeKind) bool {
    std.debug.assert(isCfg(k));
    return switch (k) {
        .Return, .Call => true,
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
                else => cfg.base.cfg0().?.idepth() + 1,
            };
            return extra.idepth;
        }

        fn findLce(left: *@This(), right: *@This()) *@This() {
            var lc, var rc = .{ left, right };
            while (lc != rc) {
                if (lc.idepth() >= rc.idepth()) lc = lc.base.cfg0().?;
                if (rc.idepth() >= lc.idepth()) rc = rc.base.cfg0().?;
            }
            return lc;
        }

        fn idom(cfg: *@This()) *@This() {
            return switch (cfg.base.kind) {
                else => cfg.base.cfg0().?,
            };
        }

        fn better(cfg: *@This(), best: *@This()) bool {
            return cfg.idepth() > best.idepth() or isBasicBlockEnd(best.base.kind);
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

    for (owned_inputs) |on| if (on) |def| {
        self.addUse(def, &node.base);
    };

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
    self.next_id += 1;

    return &node.base;
}

pub fn iterPeeps(self: *Func, comptime Mach: type) void {
    const tmp = self.beginTmpAlloc();

    var worklist = std.ArrayList(*Node).initCapacity(tmp, self.next_id) catch unreachable;
    var in_worklist = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
    worklist.appendAssumeCapacity(self.end);
    var i: usize = 0;
    while (i < worklist.items.len) : (i += 1) {
        for (worklist.items[i].inputs()) |oi| if (oi) |o| {
            if (in_worklist.isSet(o.id)) continue;
            in_worklist.set(o.id);
            worklist.appendAssumeCapacity(o);
        };
    }

    while (worklist.popOrNull()) |t| {
        if (t.outputs().len == 0 and t != self.end) {
            t.kill();
            continue;
        }

        if (Mach.idealize(self, t)) |nt| {
            self.subsume(nt, t);
        }
    }
}

pub fn subsume(self: *Func, this: *Node, target: *Node) void {
    for (target.outputs()) |use| {
        const index = std.mem.indexOfScalar(?*Node, use.inputs(), target).?;
        self.setInput(use, index, this);
    }

    target.kill();
}

pub fn setInput(self: *Func, use: *Node, idx: usize, def: *Node) void {
    if (use.inputs()[idx] == def) return;
    if (use.inputs()[idx]) |n| {
        n.removeUse(use);
    }

    use.inputs()[idx] = def;
    self.addUse(def, use);
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

        break :cfg_rpo rpo.items;
    };

    sched_early: {
        var iter = std.mem.reverseIterator(cfg_rpo);
        while (iter.next()) |cfg| {
            self.shedEarly(cfg, cfg_rpo[1], &stack, &visited);

            todo(.Phi, "phis need to be traversed");
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
            } else if (isPinned(t.kind)) {} else {
                todo(.Phi, "pin phys to the region");

                todo(.Proj, "pin projs to the parent");

                for (t.outputs()) |o| {
                    if (late_scheds[o.id] == null) continue :task;
                }

                schedule_late: {
                    const early = t.cfg0() orelse unreachable;

                    var lca: ?*CfgNode = null;
                    for (t.outputs()) |o| {
                        const other = t.useBlock(o, late_scheds);
                        lca = if (lca) |l| l.findLce(other) else other;
                    }

                    todo(.Load, "handle loads being defered");

                    var best = lca.?;
                    var cursor = best.base.cfg0().?;
                    while (cursor != early.idom()) {
                        if (cursor.better(best)) best = cursor;
                        cursor = early.idom();
                    }

                    std.debug.assert(!isBasicBlockEnd(best.base.kind));

                    nodes[t.id] = t;
                    late_scheds[t.id] = best;
                    break :schedule_late;
                }
            }

            for (t.inputs()) |odef| if (odef) |def| {
                if (late_scheds[def.id] == null and !visited.isSet(def.id)) {
                    visited.set(def.id);
                    work_list.append(def) catch unreachable;

                    todo(.Load, "smh appent loads smh");
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

        todo(.Loop, "loops need to be handled differently due to cycles");
        traversePostorder(struct {
            func: *Func,
            const dir = "outputs";
            fn each(ctx: @This(), node: *Func.Node) void {
                if (!isBasicBlockStart(node.kind)) return;

                node.schedule = ctx.func.block_count;
                ctx.func.block_count += 1;

                for (node.outputs()) |o| if (!isCfg(o.kind)) {
                    o.schedule = 0;
                } else {
                    o.schedule = node.output_len;
                };
                var changed = true;
                while (changed) {
                    changed = false;
                    for (node.outputs()) |o| if (!isCfg(o.kind)) {
                        var max_depth: u16 = 0;
                        for (o.inputs()[1..]) |oi| if (oi) |i| if (i.inputs()[0] == o.inputs()[0]) {
                            max_depth = @max(max_depth, i.schedule + 1);
                        };
                        changed = changed or max_depth != o.schedule;
                        o.schedule = max_depth;
                    };
                }

                std.sort.pdq(*Node, node.outputs(), {}, struct {
                    fn lt(_: void, a: *Node, b: *Node) bool {
                        return a.schedule < b.schedule;
                    }
                }.lt);

                var iter = std.mem.reverseIterator(node.outputs());
                while (iter.next()) |o| if (!isCfg(o.kind)) {
                    o.schedule = ctx.func.instr_count;
                    ctx.func.instr_count += 1;
                };
            }

            fn filter(_: @This(), node: *Func.Node) bool {
                return Func.isCfg(node.kind);
            }
        }{ .func = self }, self.root, &stack, &visited);

        break :compact_ids;
    }
}

fn shedEarly(self: *Func, cfg: *CfgNode, early: *CfgNode, stack: *std.ArrayList(Frame), visited: *std.DynamicBitSet) void {
    for (cfg.base.inputs()) |oinp| if (oinp) |inp| {
        traversePostorder(struct {
            early: *CfgNode,
            func: *Func,
            const dir = "inputs";
            fn each(ctx: @This(), node: *Node) void {
                if (isPinned(node.kind)) return;

                var best = ctx.early;
                if (node.inputs()[0]) |n| if (n.subclass(Extra.Cfg)) |cn| {
                    best = cn;
                };

                for (node.inputs()) |oin| if (oin) |in| {
                    if (in.cfg0().?.idepth() > best.idepth()) {
                        best = in.cfg0().?;
                    }
                };

                ctx.func.setInput(node, 0, &best.base);
            }
        }{ .early = early, .func = self }, inp, stack, visited);
    };
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
    traversePostorder(struct {
        rpo: *std.ArrayList(*CfgNode),
        const dir = "inputs";
        fn each(ctx: @This(), node: *Node) void {
            if (isBasicBlockStart(node.kind))
                ctx.rpo.append(node.subclass(Extra.Cfg).?) catch unreachable;
        }
        fn filter(_: @This(), node: *Node) bool {
            return isCfg(node.kind);
        }
    }{ .rpo = &postorder }, self.end, stack, visited);
    return postorder.items;
}

pub fn fmtScheduled(self: *Func, writer: anytype, colors: std.io.tty.Config, comptime Mach: type) void {
    const tmp = self.beginTmpAlloc();

    var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
    var stack = std.ArrayList(Frame).init(tmp);

    self.root.fmt(self.block_count, writer, colors, Mach);
    for (self.collectPostorder(tmp, &stack, &visited)) |p| {
        p.base.fmt(self.block_count, writer, colors, Mach);
        for (p.base.outputs()) |o| {
            writer.writeAll("  ") catch unreachable;
            o.fmt(self.instr_count, writer, colors, Mach);
        }
    }
}

pub fn fmt(self: *Func, writer: anytype, colors: std.io.tty.Config, comptime Mach: type) void {
    const tmp = self.beginTmpAlloc();

    var seen = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
    var postorder = std.ArrayList(*Node).init(tmp);
    postorder.append(self.end) catch unreachable;

    var i: usize = 0;
    while (i < postorder.items.len) {
        defer i += 1;
        const node = postorder.items[i];

        const pre_len = postorder.items.len;
        for (node.inputs()) |on| if (on) |n| {
            if (!seen.isSet(n.id)) {
                seen.set(n.id);
                postorder.append(n) catch unreachable;
            }
        };

        std.mem.reverse(*Node, postorder.items[pre_len..]);
    }

    std.mem.reverse(*Node, postorder.items);

    for (postorder.items) |p| p.fmt(null, writer, colors, Mach);
}

fn todo(comptime variant: anytype, comptime message: []const u8) void {
    if (@hasField(Extra, @tagName(variant))) @compileError(message);
}
