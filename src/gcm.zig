const graph = @import("graph.zig");
const root = @import("utils.zig");
const std = @import("std");

pub fn gcm(comptime MachNode: type, self: *graph.Func(MachNode)) void {
    const Func = @TypeOf(self.*);
    const CfgNode = Func.CfgNode;
    const Node = Func.Node;

    var tmp = root.Arena.scrath(self.arena);
    defer tmp.deinit();

    var visited = std.DynamicBitSet.initEmpty(tmp.arena.allocator(), self.next_id * 2) catch unreachable;
    var stack = std.ArrayList(Func.Frame).init(tmp.arena.allocator());

    const cfg_rpo = cfg_rpo: {
        var rpo = std.ArrayList(*CfgNode).init(tmp.arena.allocator());

        Func.traversePostorder(struct {
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

    add_mach_moves: {
        for (cfg_rpo) |n| if (n.base.kind == .Loop or n.base.kind == .Region) {
            for (0..2) |i| {
                self.setInputNoIntern(&n.base, i, self.addNode(.Jmp, &.{n.base.inputs()[i].?}, .{}));
            }

            var intmp = root.Arena.scrath(self.arena);
            defer intmp.deinit();
            for (intmp.arena.dupe(*Node, n.base.outputs())) |o| if (o.isDataPhi()) {
                std.debug.assert(o.inputs().len == 3);
                const lhs = self.addNode(.MachMove, &.{ null, o.inputs()[1].? }, {});
                const rhs = self.addNode(.MachMove, &.{ null, o.inputs()[2].? }, {});
                const new_phy = self.addNode(.Phi, &.{ &n.base, lhs, rhs }, {});
                self.subsume(new_phy, o);
            };
        };
        break :add_mach_moves;
    }

    sched_early: {
        for (cfg_rpo) |cfg| {
            for (cfg.base.inputs()) |oinp| if (oinp) |inp| {
                shedEarly(MachNode, self, inp, cfg_rpo[1], &visited);
            };

            if (cfg.base.kind == .Region or cfg.base.kind == .Loop) {
                var intmp = root.Arena.scrath(self.arena);
                defer intmp.deinit();
                for (intmp.arena.dupe(*Node, cfg.base.outputs())) |o| {
                    if (o.kind == .Phi) {
                        shedEarly(MachNode, self, o, cfg_rpo[1], &visited);
                    }
                }
            }
        }

        break :sched_early;
    }

    sched_late: {
        const late_scheds = tmp.arena.alloc(?*CfgNode, self.next_id);
        @memset(late_scheds, null);
        const nodes = tmp.arena.alloc(?*Node, self.next_id);
        @memset(nodes, null);
        var work_list = std.ArrayList(*Node).init(tmp.arena.allocator());
        visited.setRangeValue(.{ .start = 0, .end = visited.capacity() }, false);

        work_list.append(self.end) catch unreachable;
        visited.set(self.end.id);

        task: while (work_list.popOrNull()) |t| {
            visited.unset(t.id);
            std.debug.assert(late_scheds[t.id] == null);

            if (t.asCfg()) |c| {
                late_scheds[c.base.id] = if (c.base.isBasicBlockStart()) c else c.base.cfg0();
            } else if (t.isPinned() or t.kind == .Arg) {
                late_scheds[t.id] = t.cfg0().?;
            } else {
                for (t.outputs()) |o| {
                    if (late_scheds[o.id] == null) {
                        continue :task;
                    }
                }

                if (t.isLoad()) {
                    for (t.mem().outputs()) |p| {
                        if (p.isStore() and late_scheds[p.id] == null) {
                            continue :task;
                        }
                    }
                }

                schedule_late: {
                    const early = t.cfg0() orelse {
                        var frointier = std.ArrayList(*Node).init(tmp.arena.allocator());
                        var seen = std.DynamicBitSet.initEmpty(tmp.arena.allocator(), self.next_id) catch unreachable;
                        frointier.append(t) catch unreachable;
                        seen.set(t.id);
                        var i: usize = 0;
                        while (i < frointier.items.len) : (i += 1) {
                            for (frointier.items[i].inputs()) |oinp| if (oinp) |inp| {
                                if (seen.isSet(inp.id) or inp.cfg0() != null) continue;
                                seen.set(inp.id);
                                frointier.append(inp) catch unreachable;
                            };
                        }
                        unreachable;
                    };

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

                        // TODO: might be dangerosa
                        for (t.mem().outputs()) |o| switch (o.kind) {
                            .Call => {
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
                            else => if (o.isLoad()) {} else if (o.isStore()) {
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
                            } else std.debug.panic("{any}", .{o.kind}),
                        };

                        break :add_antideps;
                    }

                    var best = lca;
                    var cursor = best.base.cfg0().?;
                    while (cursor != early.idom()) : (cursor = cursor.idom()) {
                        std.debug.assert(cursor.base.kind != .Start);
                        if (cursor.better(best, t)) best = cursor;
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
            std.debug.assert(self.setInput(n, 0, &l.?.base) == null);
        };

        break :sched_late;
    }

    compact_ids: {
        visited.setRangeValue(.{ .start = 0, .end = visited.capacity() }, false);
        self.block_count = 0;
        self.instr_count = 0;
        self.root.schedule = 0;

        const postorder = self.collectPostorder(tmp.arena.allocator(), &visited);
        for (postorder) |bb| {
            const node = &bb.base;
            node.schedule = self.block_count;
            self.block_count += 1;

            scheduleBlock(MachNode, tmp.arena.allocator(), node);

            for (node.outputs()) |o| {
                o.schedule = self.instr_count;
                self.instr_count += 1;
            }
        }

        break :compact_ids;
    }
}

pub fn scheduleBlock(comptime MachNode: type, tmp: std.mem.Allocator, node: *graph.Func(MachNode).Node) void {
    const Node = @TypeOf(node.*);
    const NodeMeta = struct {
        unscheduled_deps: u16 = 0,
        ready_unscheduled_deps: u16 = 0,
        priority: u16,
    };

    // init meta
    const extra = tmp.alloc(NodeMeta, node.outputs().len) catch unreachable;
    for (node.outputs(), extra, 0..) |o, *e, i| {
        if (o.schedule != std.math.maxInt(u16) and !o.isCfg()) std.debug.panic("{} {}\n", .{ o, o.schedule });
        o.schedule = @intCast(i);
        e.* = .{ .priority = if (o.isCfg())
            0
        else if (o.kind == .Local)
            20
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
        o.schedule = std.math.maxInt(u16);
    }
}

fn shedEarly(
    comptime MachNode: type,
    self: *graph.Func(MachNode),
    node: *@TypeOf(self.*).Node,
    early: *@TypeOf(self.*).CfgNode,
    visited: *std.DynamicBitSet,
) void {
    std.debug.assert(early.base.kind != .Start);
    if (visited.isSet(node.id)) return;
    visited.set(node.id);

    for (node.inputs()) |i| if (i) |ii| if (ii.kind != .Phi) {
        shedEarly(MachNode, self, ii, early, visited);
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

        std.debug.assert(self.setInput(node, 0, &best.base) == null);
    }
}
