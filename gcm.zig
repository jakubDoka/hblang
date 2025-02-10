const std = @import("std");
const Func = @import("Func.zig");
const Node = Func.Node;
const CfgNode = Func.CfgNode;
const Frame = Func.Frame;
const Extra = Func.Extra;
const NodeKind = Func.NodeKind;
const BuiltinNodeKind = Func.BuiltinNodeKind;
const ExtFor = Func.ExtFor;
const toBuiltinKind = Func.toBuiltinKind;
const todo = Func.todo;

pub fn Utils(comptime Mach: type) type {
    return @TypeOf(_Utils(Mach));
}

fn _Utils(comptime Mach: type) struct {
    pub fn dataDeps(self: *Node) []?*Node {
        if (self.kind == .Phi and self.data_type == .mem) return &.{};
        const start: usize = @intFromBool(isMemOp(self.kind));
        return self.input_base[1 + start .. self.input_ordered_len];
    }

    fn LayoutFor(comptime kind: std.meta.Tag(Mach)) type {
        return extern struct {
            base: Node,
            extra: @typeInfo(Mach).@"union".fields[@intFromEnum(kind) - @typeInfo(BuiltinNodeKind).@"enum".fields.len].type,
        };
    }

    pub fn idepth(cfg: *CfgNode) u16 {
        const extra: *Extra.Cfg = &cfg.extra;

        if (extra.idepth != 0) return extra.idepth;
        extra.idepth = switch (cfg.base.kind) {
            .Start => return 0,
            .Region => idepth(idom(cfg)),
            else => idepth(cfg0(&cfg.base).?) + 1,
        };
        return extra.idepth;
    }

    fn findLca(left: *CfgNode, right: *CfgNode) *CfgNode {
        var lc, var rc = .{ left, right };
        while (lc != rc) {
            if (!isCfg(lc.base.kind)) std.debug.panic("{}", .{lc.base});
            if (!isCfg(rc.base.kind)) std.debug.panic("{}", .{rc.base});
            const diff = @as(i64, idepth(lc)) - idepth(rc);
            if (diff >= 0) lc = cfg0(&lc.base).?;
            if (diff <= 0) rc = cfg0(&rc.base).?;
        }
        return lc;
    }

    fn idom(cfg: *CfgNode) *CfgNode {
        return switch (cfg.base.kind) {
            .Region => findLca(subclass(cfg.base.inputs()[0].?, Extra.Cfg).?, subclass(cfg.base.inputs()[1].?, Extra.Cfg).?),
            else => cfg0(&cfg.base).?,
        };
    }

    fn better(cfg: *CfgNode, best: *CfgNode) bool {
        return idepth(cfg) > idepth(best) or
            (cfg.base.kind == .Jmp and cfg.base.outputs()[0].kind == .Loop) or
            isBasicBlockEnd(best.base.kind);
    }

    pub fn collectPostorder(self: *Func, arena: std.mem.Allocator, stack: *std.ArrayList(Frame), visited: *std.DynamicBitSet) []*CfgNode {
        var postorder = std.ArrayList(*CfgNode).init(arena);

        collectPostorder2(self, self.root, arena, &postorder, visited, true);

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
        self.collectPostorder2(node, arena, pos, visited, false);
    }

    pub fn collectPostorder2(
        self: *Func,
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

        if (!only_basic or isBasicBlockStart(node.kind)) pos.append(subclass(node, Extra.Cfg).?) catch unreachable;
        if (isSwapped(node)) {
            var iter = std.mem.reverseIterator(node.outputs());
            while (iter.next()) |o| if (isCfg(o.kind)) collectPostorder2(self, o, arena, pos, visited, only_basic);
        } else {
            for (node.outputs()) |o| if (isCfg(o.kind)) collectPostorder2(self, o, arena, pos, visited, only_basic);
        }
    }

    pub fn fmtScheduled(self: *Func, writer: anytype, colors: std.io.tty.Config) void {
        const tmp = self.beginTmpAlloc();

        var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
        var stack = std.ArrayList(Frame).init(tmp);

        fmt(self.root, self.block_count, writer, colors);
        writer.writeAll("\n") catch unreachable;
        for (collectPostorder(self, tmp, &stack, &visited)) |p| {
            fmt(&p.base, self.block_count, writer, colors);

            writer.writeAll("\n") catch unreachable;
            for (p.base.outputs()) |o| {
                writer.writeAll("  ") catch unreachable;
                fmt(o, self.instr_count, writer, colors);
                writer.writeAll("\n") catch unreachable;
            }
        }
    }

    pub fn fmtLog(self: *Func) void {
        self.fmt(std.io.getStdErr().writer(), std.io.tty.detectConfig(std.io.getStdErr()));
    }

    pub fn fmtUnscheduled(self: *Func, writer: anytype, colors: std.io.tty.Config) void {
        const tmp = self.beginTmpAlloc();

        var worklist = Func.WorkList.init(tmp, self.next_id) catch unreachable;

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
            fmt(p, null, writer, colors);
            writer.writeAll("\n") catch unreachable;
        }
    }

    pub fn iterPeeps(self: *Func) void {
        const tmp = self.beginTmpAlloc();

        var worklist = Func.WorkList.init(tmp, self.next_id) catch unreachable;
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

    fn idealize(self: *Func, node: *Node, worklist: *Func.WorkList) ?*Node {
        const inps = node.inputs();

        var is_dead = node.kind == .Region and Func.isDead(inps[0]) and Func.isDead(inps[1]);
        is_dead = is_dead or (node.kind != .Start and node.kind != .Region and
            isCfg(node.kind) and Func.isDead(inps[0]));

        if (is_dead) {
            node.data_type = .dead;
            for (node.outputs()) |o| worklist.add(o);
            return null;
        }

        if (node.kind == .Region) b: {
            std.debug.assert(node.inputs().len == 2);
            const idx = for (node.inputs(), 0..) |in, i| {
                if (Func.isDead(in)) break i;
            } else break :b;

            var iter = std.mem.reverseIterator(node.outputs());
            while (iter.next()) |o| if (o.kind == .Phi) {
                for (o.outputs()) |oo| worklist.add(oo);
                self.subsume(o.inputs()[(1 - idx) + 1].?, o);
            };

            return node.inputs()[1 - idx].?.inputs()[0];
        }

        if (node.kind == .Loop) b: {
            if (!Func.isDead(node.inputs()[1])) break :b;

            var iter = std.mem.reverseIterator(node.outputs());
            while (iter.next()) |o| if (o.kind == .Phi) {
                for (o.outputs()) |oo| worklist.add(oo);
                self.subsume(o.inputs()[1].?, o);
            };

            return node.inputs()[0].?.inputs()[0];
        }

        if (node.kind == .Store) {
            if (node.base().kind == .Local and cfg0(node) != null) {
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

            if (node.base().kind == .Local and cfg0(node) != null) {
                const ld = self.addNode(.Load, &.{ null, inps[1], inps[2] }, {});
                worklist.add(ld);
                return ld;
            }

            while (earlier.kind == .Store and
                (cfg0(earlier) == cfg0(node) or cfg0(node) == null) and
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
                    (cfg0(l) == cfg0(node) or cfg0(node) == null) and
                    noAlias(l.base(), node.base()))
                {
                    l = l.mem();
                }

                while (r.kind == .Store and
                    (cfg0(r) == cfg0(node) or cfg0(node) == null) and
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
                //std.debug.assert(node.id == 31);
                return self.addNode(.Load, &.{ inps[0], earlier, inps[2] }, {});
            }
        }

        if (node.kind == .Phi) {
            const region, const l, const r = .{ inps[0].?, inps[1].?, inps[2].? };

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
        return false;
    }

    pub fn fmt(
        self: *const Node,
        scheduled: ?u16,
        writer: anytype,
        colors: std.io.tty.Config,
    ) void {
        Func.logNid(writer, self.id, colors);
        const name = switch (splitKind(self.kind)) {
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

        switch (splitKind(self.kind)) {
            inline else => |b, tg| switch (b) {
                inline else => |t| {
                    const ext = switch (tg) {
                        .Builtin => self.extraConst(t),
                        .Specific => machExtraConst(self, t),
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
            Func.logNid(writer, o.id, colors);
        };

        if (scheduled == null) {
            writer.writeAll(" [") catch unreachable;
            for (self.output_base[0..self.output_len]) |o| {
                writer.writeAll(", ") catch unreachable;
                Func.logNid(writer, o.id, colors);
            }
            writer.writeAll("]") catch unreachable;
        }
    }

    pub fn machExtra(self: *Node, comptime kind: std.meta.Tag(Mach)) *std.meta.TagPayload(Mach, kind) {
        std.debug.assert(splitKind(self.kind).Specific == kind);
        const ptr: *LayoutFor(kind) = @ptrCast(self);
        return &ptr.extra;
    }

    pub fn machExtraConst(self: *const Node, comptime kind: std.meta.Tag(Mach)) *const std.meta.TagPayload(Mach, kind) {
        std.debug.assert(splitKind(self.kind).Specific == kind);
        const ptr: *const LayoutFor(kind) = @ptrCast(self);
        return &ptr.extra;
    }

    fn splitKind(kind: NodeKind) union(enum) { Builtin: BuiltinNodeKind, Specific: std.meta.Tag(Mach) } {
        if (@typeInfo(BuiltinNodeKind).@"enum".fields.len > @intFromEnum(kind)) {
            return .{ .Builtin = @enumFromInt(@intFromEnum(kind)) };
        } else {
            return .{ .Specific = @enumFromInt(@intFromEnum(kind)) };
        }
    }

    fn callCheck(comptime name: []const u8, value: anytype) bool {
        return @hasDecl(Mach, name) and @field(Mach, name)(value);
    }

    pub fn isLoad(k: NodeKind) bool {
        return k == .Load or callCheck("isLoad", k);
    }

    pub fn isStore(k: NodeKind) bool {
        return k == .Store or callCheck("isStore", k);
    }

    pub fn isPinned(k: NodeKind) bool {
        return switch (k) {
            .Ret, .Phi, .Mem => true,
            else => isCfg(k) or callCheck("isPinned", k),
        };
    }

    pub fn isMemOp(k: NodeKind) bool {
        return switch (k) {
            .Load, .Local, .Store, .Return, .Call => true,
            else => callCheck("isMemOp", k),
        };
    }

    pub fn isSwapped(node: *Node) bool {
        return callCheck("isSwapped", node);
    }

    pub fn isCfg(k: NodeKind) bool {
        return switch (splitKind(k)) {
            .Builtin => |kt| switch (kt) {
                inline else => |t| return comptime Node.isSubbclass(ExtFor(t), Extra.Cfg),
            },
            .Specific => |kt| switch (kt) {
                inline else => |t| return comptime Node.isSubbclass(std.meta.TagPayload(Mach, t), Extra.Cfg),
            },
        };
    }

    pub fn isBasicBlockStart(k: NodeKind) bool {
        std.debug.assert(isCfg(k));
        return switch (k) {
            .Entry, .CallEnd, .Then, .Else, .Region, .Loop => true,
            else => callCheck("isBasicBlockStart", k),
        };
    }

    pub fn isBasicBlockEnd(k: NodeKind) bool {
        std.debug.assert(isCfg(k));
        return switch (k) {
            .Return, .Call, .If, .Jmp => true,
            else => callCheck("isBasicBlockEnd", k),
        };
    }

    pub fn subclass(self: *Node, comptime Ext: type) ?*Func.SubclassFor(Ext) {
        switch (splitKind(self.kind)) {
            .Builtin => |kt| switch (kt) {
                inline else => |t| if (comptime Node.isSubbclass(ExtFor(t), Ext)) {
                    return @ptrCast(self);
                },
            },
            .Specific => |kt| switch (kt) {
                inline else => |t| if (comptime Node.isSubbclass(std.meta.TagPayload(Mach, t), Ext)) {
                    return @ptrCast(self);
                },
            },
        }
        return null;
    }

    pub fn cfg0(self: *Node) ?*Func.SubclassFor(Extra.Cfg) {
        if (self.kind == .Start) return subclass(self, Extra.Cfg);
        return subclass((self.inputs()[0] orelse return null), Extra.Cfg);
    }

    pub fn useBlock(self: *Node, use: *Node, scheds: []const ?*CfgNode) *CfgNode {
        if (use.kind == .Phi) {
            std.debug.assert(use.inputs()[0].?.kind == .Region or use.inputs()[0].?.kind == .Loop);
            for (use.inputs()[0].?.inputs(), use.inputs()[1..]) |b, u| {
                if (u.? == self) {
                    return subclass(b.?, Extra.Cfg).?;
                }
            }
        }
        return scheds[use.id].?;
    }

    pub fn gcm(self: *Func) void {
        const tmp = self.beginTmpAlloc();

        var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
        var stack = std.ArrayList(Frame).init(tmp);

        const cfg_rpo = cfg_rpo: {
            var rpo = std.ArrayList(*CfgNode).init(tmp);

            Func.traversePostorder(struct {
                rpo: *std.ArrayList(*CfgNode),
                pub const dir = "outputs";
                pub fn each(ctx: @This(), node: *Node) void {
                    ctx.rpo.append(subclass(node, Extra.Cfg).?) catch unreachable;
                }
                pub fn filter(_: @This(), node: *Node) bool {
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

                if (subclass(t, Extra.Cfg)) |c| {
                    late_scheds[c.base.id] = if (isBasicBlockStart(c.base.kind)) c else cfg0(&c.base);
                } else if (isPinned(t.kind)) {
                    late_scheds[t.id] = cfg0(t).?;
                } else {
                    todo(.Proj, "pin projs to the parent");

                    for (t.outputs()) |o| {
                        if (late_scheds[o.id] == null) {
                            continue :task;
                        }
                    }

                    if (isLoad(t.kind)) {
                        for (t.mem().outputs()) |p| {
                            if (p.kind == .Store and late_scheds[p.id] == null) {
                                continue :task;
                            }
                        }
                    }

                    schedule_late: {
                        const early = cfg0(t) orelse unreachable;

                        var olca: ?*CfgNode = null;
                        for (t.outputs()) |o| {
                            const other = useBlock(t, o, late_scheds);
                            olca = if (olca) |l| findLca(l, other) else other;
                        }
                        var lca = olca.?;

                        if (t.id == 31) {
                            std.debug.print("{}\n", .{&lca.base});
                        }

                        if (isLoad(t.kind)) add_antideps: {
                            var cursor = lca;
                            while (cursor != idom(early)) : (cursor = idom(cursor)) {
                                std.debug.assert(cursor.base.kind != .Start);
                                cursor.extra.antidep = t.id;
                            }

                            for (t.mem().outputs()) |o| switch (o.kind) {
                                .Store, .Call => {
                                    const sdef = cfg0(o).?;
                                    var lcar = late_scheds[o.id].?;
                                    while (lcar != idom(sdef)) : (lcar = idom(lcar)) {
                                        if (lcar.extra.antidep == t.id) {
                                            lca = findLca(lcar, lca);
                                            if (lca == sdef) {
                                                self.addDep(o, t);
                                                self.addUse(t, o);
                                            }
                                            break;
                                        }
                                    }
                                },
                                .Phi => {
                                    for (o.inputs()[1..], cfg0(o).?.base.inputs()) |inp, oblk| if (inp.? == t.mem()) {
                                        const sdef = cfg0(t.mem()).?;
                                        var lcar = subclass(oblk.?, Extra.Cfg).?;
                                        while (lcar != idom(sdef)) : (lcar = idom(lcar)) {
                                            if (lcar.extra.antidep == t.id) {
                                                lca = findLca(lcar, lca);
                                            }
                                        }
                                    };
                                },
                                .Local => {},
                                .Return => {},
                                else => if (!isLoad(o.kind)) std.debug.panic("{any}", .{o.kind}),
                            };

                            break :add_antideps;
                        }

                        if (t.id == 31) {
                            std.debug.print("{}\n", .{&lca.base});
                        }

                        var best = lca;
                        var cursor = cfg0(&best.base).?;
                        while (cursor != idom(early)) : (cursor = idom(cursor)) {
                            std.debug.assert(cursor.base.kind != .Start);
                            if (better(cursor, best)) best = cursor;
                        }

                        if (isBasicBlockEnd(best.base.kind)) {
                            best = idom(best);
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
                            if (isLoad(out.kind) and late_scheds[out.id] == null and !visited.isSet(def.id)) {
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

            const postorder = collectPostorder(self, tmp, &stack, &visited);
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
                    e.* = .{ .priority = if (isCfg(o.kind))
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

    fn shedEarly(self: *Func, node: *Node, early: *CfgNode, stack: *std.ArrayList(Frame), visited: *std.DynamicBitSet) void {
        std.debug.assert(early.base.kind != .Start);
        if (visited.isSet(node.id)) return;
        visited.set(node.id);

        for (node.inputs()) |i| if (i) |ii| if (ii.kind != .Phi) {
            shedEarly(self, ii, early, stack, visited);
        };

        if (!isPinned(node.kind)) {
            var best = early;
            if (node.inputs()[0]) |n| if (subclass(n, Extra.Cfg)) |cn| {
                if (n.kind != .Start) best = cn;
            };

            for (node.inputs()[1..]) |oin| if (oin) |in| {
                if (idepth(cfg0(in).?) > idepth(best)) {
                    best = cfg0(in).?;
                }
            };

            std.debug.assert(best.base.kind != .Start);
            self.setInput(node, 0, &best.base);
        }
    }
} {
    return .{};
}
