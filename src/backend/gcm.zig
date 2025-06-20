const graph = @import("graph.zig");
const root = graph.utils;
const std = @import("std");

pub fn GcmMixin(comptime Backend: type) type {
    return struct {
        loop_tree_built: std.debug.SafetyLock = .{},
        cfg_built: std.debug.SafetyLock = .{},
        loop_tree: []LoopTree = undefined,
        postorder: []*CfgNode = undefined,
        block_count: u16 = undefined,
        instr_count: u16 = undefined,

        const Func = graph.Func(Backend);
        const Self = @This();
        const CfgNode = Func.CfgNode;
        const Node = Func.Node;

        pub fn loopDepthOf(self: *Self, node: *CfgNode) u16 {
            const slot = &self.loop_tree[node.ext.loop];
            if (slot.depth == 0) slot.depth = self.loopDepthOf(self.loop_tree[slot.par.?].head) + 1;
            return slot.depth;
        }

        pub fn getGraph(self: *Self) *Func {
            return @alignCast(@fieldParentPtr("gcm", self));
        }

        pub const LoopTree = struct {
            head: *CfgNode,
            par: ?u16 = null,
            depth: u16 = 0,
        };

        pub const LoopTreeBuilder = struct {
            post_walked: std.DynamicBitSetUnmanaged,
            pre_levels: []u16,
            tree: std.ArrayList(LoopTree),
        };

        pub fn buildLoopTree(gcm: *Self) void {
            gcm.loop_tree_built.lock();
            const self = gcm.getGraph();

            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            var builder = LoopTreeBuilder{
                .post_walked = std.DynamicBitSetUnmanaged.initEmpty(tmp.arena.allocator(), self.next_id) catch unreachable,
                .pre_levels = tmp.arena.alloc(u16, self.next_id),
                .tree = std.ArrayList(LoopTree).init(tmp.arena.allocator()),
            };
            @memset(builder.pre_levels, 0);

            builder.tree.append(.{ .head = self.root.asCfg().?, .par = 0, .depth = 1 }) catch unreachable;
            self.end.asCfg().?.ext.loop = 0;
            self.root.asCfg().?.ext.loop = 0;

            _ = postwaklBuildLoopTree(self, 2, self.root.asCfg().?, &builder);

            gcm.loop_tree = self.arena.allocator().dupe(LoopTree, builder.tree.items) catch unreachable;
        }

        pub fn postwaklBuildLoopTree(self: *Func, par_preorder: u16, from: *CfgNode, builder: *LoopTreeBuilder) u16 {
            // TODO: make the preorder globaly increase, but after we know why thats actually important

            if (builder.pre_levels[from.base.id] != 0) return par_preorder;
            builder.pre_levels[from.base.id] = par_preorder;
            var postorder = par_preorder + 1;

            for (from.base.outputs()) |o| if (o.asCfg()) |oc| {
                postorder = postwaklBuildLoopTree(self, postorder, oc, builder);
            };

            var inner: ?u16 = null;
            for (from.base.outputs()) |o| if (o.asCfg()) |oc| {
                var ltree: u16 = undefined;
                if (builder.post_walked.isSet(oc.base.id)) {
                    ltree = oc.ext.loop;
                    const tree = &builder.tree.items[ltree];
                    if (tree.head == oc) {
                        ltree = tree.par orelse b: {
                            tree.par = fixLoop(self, oc, self.end).ext.loop;
                            break :b tree.par.?;
                        };
                    }
                } else {
                    std.debug.assert(oc.base.kind == .Loop);
                    const id: u16 = @intCast(builder.tree.items.len);
                    oc.ext.loop = id;
                    ltree = id;
                    builder.tree.append(.{ .head = oc }) catch unreachable;
                }

                const cur = inner orelse {
                    inner = ltree;
                    continue;
                };
                if (cur == ltree) continue;

                std.debug.assert(oc.base.kind != .Loop);
                std.debug.assert(builder.pre_levels[builder.tree.items[cur].head.base.id] != 0);
                std.debug.assert(builder.pre_levels[builder.tree.items[ltree].head.base.id] != 0);

                const inner_greater = builder.pre_levels[builder.tree.items[cur].head.base.id] >
                    builder.pre_levels[builder.tree.items[ltree].head.base.id];
                const outer = if (inner_greater) ltree else cur;
                inner = if (inner_greater) cur else ltree;
                builder.tree.items[inner.?].par = outer;
            };

            if (inner) |in| from.ext.loop = in;
            builder.post_walked.set(from.base.id);

            return postorder;
        }

        pub fn fixLoop(func: *Func, loop: *CfgNode, end: *Node) *CfgNode {
            const dead = func.addNode(.Never, .top, &.{loop.base.inputs()[1].?}, .{});
            const then = func.addNode(.Then, .top, &.{dead}, .{});
            const else_ = func.addNode(.Else, .top, &.{dead}, .{});

            else_.asCfg().?.ext.loop = 0;

            func.setInputNoIntern(&loop.base, 1, else_);

            func.addTrap(then, graph.infinite_loop_trap);

            return end.asCfg().?;
        }

        pub fn buildCfg(gcm: *Self) void {
            _ = gcm.buildLoopTree();

            gcm.loop_tree_built.assertLocked();
            gcm.cfg_built.lock();
            const self = gcm.getGraph();

            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            var visited = std.DynamicBitSet.initEmpty(tmp.arena.allocator(), self.next_id * 2) catch unreachable;
            var stack = std.ArrayList(Func.Frame).init(tmp.arena.allocator());

            const cfg_rpo: []*CfgNode = cfg_rpo: {
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
                        self.setInputNoIntern(&n.base, i, self.addNode(.Jmp, .top, &.{n.base.inputs()[i].?}, .{}));
                    }

                    var intmp = root.Arena.scrath(null);
                    defer intmp.deinit();
                    for (intmp.arena.dupe(*Node, n.base.outputs())) |o| if (o.isDataPhi()) {
                        std.debug.assert(o.inputs().len == 3);
                        const lhs = self.addNode(.MachMove, .top, &.{ null, o.inputs()[1].? }, .{});
                        const rhs = self.addNode(.MachMove, .top, &.{ null, o.inputs()[2].? }, .{});
                        const new_phy = self.addNode(.Phi, o.data_type, &.{ &n.base, lhs, rhs }, .{});
                        self.subsume(new_phy, o);
                    };
                };
                break :add_mach_moves;
            }

            sched_early: {
                for (cfg_rpo) |cfg| {
                    if (cfg.base.kind != .Return or cfg.base.inputs()[0] != null) {
                        _ = cfg.idom();
                    }

                    for (cfg.base.inputs()) |oinp| if (oinp) |inp| {
                        gcm.shedEarly(inp, cfg_rpo[1], &visited);
                    };

                    if (cfg.base.kind == .Region or cfg.base.kind == .Loop) {
                        var intmp = root.Arena.scrath(null);
                        defer intmp.deinit();
                        for (intmp.arena.dupe(*Node, cfg.base.outputs())) |o| {
                            if (o.kind == .Phi) {
                                gcm.shedEarly(o, cfg_rpo[1], &visited);
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

                task: while (work_list.pop()) |t| {
                    visited.unset(t.id);
                    std.debug.assert(late_scheds[t.id] == null);

                    if (t.asCfg()) |c| {
                        late_scheds[c.base.id] = if (c.base.isBasicBlockStart()) c else c.base.tryCfg0();
                    } else if (t.isPinned() or t.isSub(graph.Arg)) {
                        late_scheds[t.id] = t.cfg0();
                    } else {
                        for (t.outputs()) |o| {
                            if (late_scheds[o.id] == null) {
                                continue :task;
                            }
                        }

                        if (t.isLoad()) {
                            for (t.mem().outputs()) |p| {
                                if ((p.isStore() or p.kind == .Call) and late_scheds[p.id] == null) {
                                    continue :task;
                                }
                            }
                        }

                        schedule_late: {
                            const early = t.cfg0();

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
                                        const sdef = o.cfg0();
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
                                        for (o.inputs()[1..], o.cfg0().base.inputs()) |inp, oblk| if (inp.? == t.mem()) {
                                            const sdef = t.mem().cfg0();
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
                                        const sdef = o.cfg0();
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
                                    } else root.panic("{any}", .{o.kind}),
                                };

                                break :add_antideps;
                            }

                            var best = lca;
                            var cursor = best.base.cfg0();
                            while (cursor != early.idom()) : (cursor = cursor.idom()) {
                                std.debug.assert(cursor.base.kind != .Start);
                                if (cursor.better(best, t, self)) best = cursor;
                            }

                            if (best.base.isBasicBlockEnd()) {
                                best = best.idom();
                            }

                            nodes[t.id] = t;
                            late_scheds[t.id] = best;

                            break :schedule_late;
                        }
                    }

                    if (t.kind == .Loop or t.kind == .Region) {
                        for (t.outputs()) |o| if (late_scheds[o.id] == null) {
                            if (!visited.isSet(o.id)) {
                                visited.set(o.id);
                                work_list.append(o) catch unreachable;
                            }
                        };
                    }

                    for (t.inputs()) |odef| if (odef) |def| {
                        if (late_scheds[def.id] == null) {
                            if (!visited.isSet(def.id)) {
                                visited.set(def.id);
                                work_list.append(def) catch unreachable;
                            }

                            for (def.outputs()) |out| {
                                if (out.isLoad() and late_scheds[out.id] == null and !visited.isSet(out.id)) {
                                    visited.set(out.id);
                                    work_list.append(out) catch unreachable;
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
                self.gcm.block_count = 0;
                self.gcm.instr_count = 0;
                self.root.schedule = 0;

                const postorder = self.collectPostorder(tmp.arena.allocator(), &visited);
                for (postorder) |bb| {
                    const node = &bb.base;
                    node.schedule = self.gcm.block_count;
                    self.gcm.block_count += 1;

                    scheduleBlock(node);

                    self.gcm.instr_count += @intCast(node.outputs().len);
                }

                gcm.postorder = self.arena.allocator().dupe(*CfgNode, postorder) catch unreachable;
                break :compact_ids;
            }

            if (std.debug.runtime_safety) validate_ssa: {
                for (cfg_rpo[1..]) |bb| if (bb.base.isBasicBlockStart()) {
                    for (bb.base.outputs()[0 .. bb.base.outputs().len - 1]) |o| {
                        if (o.tryCfg0() == null) {
                            std.debug.assert(o.kind == .Return);
                            continue;
                        }
                        if (o.kind == .Phi) continue;
                        for (o.inputs()[1..]) |i| if (i != null) {
                            var cursor = o.cfg0();
                            while (cursor.idepth() > i.?.cfg0().idepth()) {
                                cursor = cursor.idom();
                            }
                        };
                    }
                };

                break :validate_ssa;
            }
        }

        pub fn scheduleBlock(node: *Func.Node) void {
            const NodeMeta = struct {
                unscheduled_deps: u16 = 0,
                ready_unscheduled_deps: u16 = 0,
                priority: u16,
            };

            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            // init meta
            const extra = tmp.arena.alloc(NodeMeta, node.outputs().len);
            for (node.outputs(), extra, 0..) |o, *e, i| {
                if (o.schedule != std.math.maxInt(u16) and !o.isCfg()) root.panic("{} {}\n", .{ o, o.schedule });
                o.schedule = @intCast(i);
                e.* = .{ .priority = if (o.isCfg())
                    0
                else if (o.kind == .MachMove)
                    10
                else if (o.subclass(graph.Arg)) |arg|
                    @intCast(99 - arg.ext.index)
                else if (o.kind == .Phi or o.kind == .Mem or o.kind == .Ret)
                    100
                else if (o.isStore())
                    75
                else
                    50 };
                if (o.kind != .Phi) {
                    for (o.inputs()[1..]) |j| if (j != null and !j.?.isCfg() and j.?.inputs()[0] == node) {
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
            if (ready != scheduled) while (scheduled < outs.len - 1) {
                if (ready == scheduled) root.panic("{} {} {} {any}", .{ scheduled, outs.len, node, outs[scheduled..] });

                var pick = scheduled;
                for (outs[scheduled + 1 .. ready], scheduled + 1..) |o, i| {
                    if (extra[o.schedule].priority > extra[outs[pick].schedule].priority) {
                        pick = i;
                    } else if (extra[o.schedule].priority == extra[outs[pick].schedule].priority and
                        b: {
                            var sum: usize = 1000;
                            for (o.outputs()) |oo| if (oo.inputs()[0] == node) {
                                sum = @min(sum, extra[oo.schedule].unscheduled_deps);
                            };
                            break :b sum;
                        } < b: {
                            var sum: usize = 1000;
                            for (outs[pick].outputs()) |oo| if (oo.inputs()[0] == node) {
                                sum = @min(sum, extra[oo.schedule].unscheduled_deps);
                            };
                            break :b sum;
                        })
                    {
                        pick = i;
                    }
                }

                const n = outs[pick];
                for (n.outputs()) |def| if (node == def.inputs()[0] and def.kind != .Phi) {
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
            };

            for (node.outputs()) |o| {
                o.schedule = std.math.maxInt(u16);
            }
        }

        fn shedEarly(
            gcm: *Self,
            node: *Func.Node,
            early: *Func.CfgNode,
            visited: *std.DynamicBitSet,
        ) void {
            const self = gcm.getGraph();

            std.debug.assert(early.base.kind != .Start);
            if (visited.isSet(node.id)) return;
            visited.set(node.id);

            for (node.inputs()) |i| if (i) |ii| if (ii.kind != .Phi) {
                gcm.shedEarly(ii, early, visited);
            };

            if (!node.isPinned()) {
                if (node.kind == .Start) {
                    root.panic("{}\n", .{node});
                }

                var best = early;
                if (node.inputs()[0]) |n| if (n.asCfg()) |cn| {
                    if (n.kind != .Start) best = cn;
                };

                for (node.inputs()[1..]) |oin| if (oin) |in| {
                    if (in.cfg0().idepth() > best.idepth()) {
                        best = in.cfg0();
                    }
                };

                std.debug.assert(best.base.kind != .Start);

                _ = self.setInput(node, 0, &best.base);
            }
        }
    };
}
