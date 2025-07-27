const std = @import("std");

const graph = @import("graph.zig");
const utils = graph.utils;

pub fn Mixin(comptime Backend: type) type {
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

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var builder = LoopTreeBuilder{
                .post_walked = std.DynamicBitSetUnmanaged.initEmpty(tmp.arena.allocator(), self.next_id) catch unreachable,
                .pre_levels = tmp.arena.alloc(u16, self.next_id),
                .tree = std.ArrayList(LoopTree).init(tmp.arena.allocator()),
            };
            @memset(builder.pre_levels, 0);

            builder.tree.append(.{ .head = self.start.asCfg().?, .par = 0, .depth = 1 }) catch unreachable;
            self.end.asCfg().?.ext.loop = 0;
            self.start.asCfg().?.ext.loop = 0;

            _ = postwaklBuildLoopTree(self, 2, self.start.asCfg().?, &builder);

            gcm.loop_tree = self.arena.allocator().dupe(LoopTree, builder.tree.items) catch unreachable;
        }

        pub fn postwaklBuildLoopTree(self: *Func, par_preorder: u16, from: *CfgNode, builder: *LoopTreeBuilder) u16 {
            if (builder.pre_levels[from.base.id] != 0) return par_preorder;
            builder.pre_levels[from.base.id] = par_preorder;
            var postorder = par_preorder + 1;

            for (from.base.outputs()) |o| if (o.get().asCfg()) |oc| {
                postorder = postwaklBuildLoopTree(self, postorder, oc, builder);
            };

            var inner: ?u16 = null;
            for (from.base.outputs()) |o| if (o.get().asCfg()) |oc| {
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
            if (loop.base.extra(.Loop).anal_stage == .has_break) {
                loop.base.extra(.Loop).anal_stage = .has_dead_break;
            }

            const dead = func.addNode(.Never, .none, .top, &.{loop.base.inputs()[1].?}, .{});
            const then = func.addNode(.Then, .none, .top, &.{dead}, .{});
            const else_ = func.addNode(.Else, .none, .top, &.{dead}, .{});

            else_.asCfg().?.ext.loop = 0;

            func.setInputIgnoreIntern(&loop.base, 1, else_);

            func.addTrapIgnoreIntern(loop.base.sloc, then, graph.infinite_loop_trap);

            return end.asCfg().?;
        }

        pub fn buildCfg(gcm: *Self) void {
            const self = gcm.getGraph();

            self.stopped_interning.lock();
            _ = gcm.buildLoopTree();
            gcm.loop_tree_built.assertLocked();
            gcm.cfg_built.lock();

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var visited = std.DynamicBitSetUnmanaged.initEmpty(tmp.arena.allocator(), self.next_id) catch unreachable;
            var stack = std.ArrayList(Func.Frame).init(tmp.arena.allocator());

            const cfg_rpo: []*CfgNode = cfg_rpo: {
                var rpo = std.ArrayList(*CfgNode).init(tmp.arena.allocator());

                Func.traversePostorder(struct {
                    rpo: *std.ArrayList(*CfgNode),
                    pub fn each(ctx: @This(), node: *Node) void {
                        ctx.rpo.append(node.asCfg().?) catch unreachable;
                    }
                    pub fn filter(_: @This(), node: *Node) bool {
                        return node.isCfg();
                    }
                }{ .rpo = &rpo }, self.start, &stack, &visited);

                std.mem.reverse(*CfgNode, rpo.items);

                break :cfg_rpo rpo.items;
            };

            add_mach_moves: {
                for (cfg_rpo) |n| if (n.base.kind == .Loop or n.base.kind == .Region) {
                    for (0..2) |i| {
                        self.setInputIgnoreIntern(&n.base, i, self.addNode(.Jmp, n.base.sloc, .top, &.{n.base.inputs()[i].?}, .{}));
                    }

                    visited.resize(tmp.arena.allocator(), self.next_id, true) catch unreachable;
                };
                break :add_mach_moves;
            }

            sched_early: {
                for (cfg_rpo) |cfg| cfg.ext.idepth = 0;
                for (cfg_rpo) |cfg| {
                    if ((cfg.base.kind != .Return or cfg.base.inputs()[0] != null) and
                        cfg.base.kind != .TrapRegion)
                    {
                        _ = cfg.idom();
                    }

                    for (cfg.base.inputs()) |oinp| if (oinp) |inp| {
                        gcm.shedEarly(inp, cfg_rpo[1], &visited);
                    };

                    if (cfg.base.kind == .Region or cfg.base.kind == .Loop) {
                        var intmp = utils.Arena.scrath(null);
                        defer intmp.deinit();
                        for (intmp.arena.dupe(Node.Out, cfg.base.outputs())) |o| {
                            if (o.get().kind == .Phi) {
                                gcm.shedEarly(o.get(), cfg_rpo[1], &visited);
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
                    } else if (t.isFloating()) {} else if (t.isPinned() or t.isSub(graph.Arg)) {
                        late_scheds[t.id] = t.cfg0();
                    } else {
                        for (t.outputs()) |o| {
                            if (late_scheds[o.get().id] == null) {
                                continue :task;
                            }
                        }

                        if (t.isLoad()) {
                            for (t.mem().outputs()) |n| {
                                const p = n.get();
                                if ((p.isStore() or p.kind == .Call) and late_scheds[p.id] == null) {
                                    continue :task;
                                }
                            }
                        }

                        schedule_late: {
                            const early = t.cfg0();

                            var olca: ?*CfgNode = null;
                            for (t.outputs()) |n| {
                                const o = n.get();
                                const other = t.useBlock(o, n.pos(), late_scheds);
                                olca = if (olca) |l| l.findLca(other) else other;
                            }
                            var lca = olca.?;

                            if (t.isLoad()) add_antideps: {
                                lca = findAntideps(self, lca, t, late_scheds);
                                break :add_antideps;
                            }

                            var best = lca;
                            var cursor = best.base.cfg0();
                            while (cursor != early.idom()) : (cursor = cursor.idom()) {
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
                        for (t.outputs()) |n| {
                            const o = n.get();
                            if (late_scheds[o.id] == null) {
                                if (!visited.isSet(o.id)) {
                                    visited.set(o.id);
                                    work_list.append(o) catch unreachable;
                                }
                            }
                        }
                    }

                    for (t.inputs()) |odef| if (odef) |def| {
                        if (late_scheds[def.id] == null) {
                            if (!visited.isSet(def.id)) {
                                visited.set(def.id);
                                work_list.append(def) catch unreachable;
                            }
                        }
                        if (t.isStore() or t.kind == .Call)
                            for (def.outputs()) |ot| {
                                const out = ot.get();
                                if (out.isLoad() and late_scheds[out.id] == null and !visited.isSet(out.id)) {
                                    visited.set(out.id);
                                    work_list.append(out) catch unreachable;
                                }
                            };
                    };
                }

                for (nodes, late_scheds) |on, l| if (on) |n| {
                    std.debug.assert(!n.isFloating());
                    self.setInputIgnoreIntern(n, 0, &l.?.base);
                };

                break :sched_late;
            }

            compact_ids: {
                visited.setRangeValue(.{ .start = 0, .end = visited.capacity() }, false);
                self.gcm.block_count = 0;
                self.gcm.instr_count = 0;
                self.start.schedule = 0;

                const postorder = self.collectPostorder(tmp.arena.allocator(), &visited);
                for (postorder) |bb| {
                    const node = &bb.base;
                    node.schedule = self.gcm.block_count;
                    self.gcm.block_count += 1;

                    scheduleBlock(self, bb);

                    self.gcm.instr_count += @intCast(node.outputs().len);
                }

                gcm.postorder = self.arena.allocator().dupe(*CfgNode, postorder) catch unreachable;
                break :compact_ids;
            }

            if (std.debug.runtime_safety) validate_ssa: {
                for (cfg_rpo[1..]) |bb| if (bb.base.isBasicBlockStart()) {
                    for (bb.base.outputs()[0 .. bb.base.outputs().len - 1]) |n| {
                        const o = n.get();
                        if (o.tryCfg0() == null) {
                            std.debug.assert(o.kind == .Return);
                            continue;
                        }
                        if (o.kind == .Phi) continue;
                        for (o.inputs()[1..]) |i| if (i != null) {
                            if (i.?.isFloating()) continue;
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

        pub fn findAntideps(
            self: *Func,
            lca_: *Func.CfgNode,
            load: *Func.Node,
            late_scheds: []const ?*Func.CfgNode,
        ) *Func.CfgNode {
            var lca = lca_;
            const early = load.cfg0();
            std.debug.assert(load.isLoad());
            var cursor = lca;
            while (cursor != early.idom()) : (cursor = cursor.idom()) {
                std.debug.assert(cursor.base.kind != .Start);
                cursor.ext.antidep = load.id;
            }

            for (load.mem().outputs()) |n| {
                const o = n.get();
                switch (o.kind) {
                    .Call => {
                        const stblck = late_scheds[o.id].?;
                        if (stblck.ext.antidep == load.id) {
                            lca = stblck.findLca(lca);
                            if (lca == stblck) {
                                const idx = self.addDep(o, load);
                                self.addUse(load, idx, o);
                            }
                        }
                    },
                    .Phi => {
                        for (o.inputs()[1..], o.cfg0().base.inputs()) |inp, oblk| if (inp.? == load.mem()) {
                            var stblck = oblk.?.cfg0();
                            if (stblck.ext.antidep == load.id) {
                                lca = stblck.findLca(lca);
                            }
                        };
                    },
                    .Local => {},
                    .Return => {},
                    else => if (o.isLoad() or o.kind == .LocalAlloc) {} else if (o.isStore()) {
                        const stblck = late_scheds[o.id].?;
                        if (stblck.ext.antidep == load.id) {
                            lca = stblck.findLca(lca);
                            if (lca == stblck) {
                                const idx = self.addDep(o, load);
                                self.addUse(load, idx, o);
                            }
                        }
                    } else utils.panic("{any}", .{o.kind}),
                }
            }

            return lca;
        }

        pub fn scheduleBlock(func: *Func, bb: *Func.CfgNode) void {
            const NodeMeta = packed struct(u16) {
                unscheduled_deps: u6 = 0,
                ready_unscheduled_deps: u6 = 0,
                remote_def: bool = false,
                remote_use: bool = false,
                single_def: bool = false,
                padding: u1 = 0,

                pub fn priority(
                    self: @This(),
                    fnc: *Func,
                    b: *Func.CfgNode,
                    n: *Node,
                    meta: []@This(),
                ) usize {
                    if (n.isSub(graph.Arg) or n.kind == .Phi or
                        n.kind == .Mem or n.kind == .Ret) return 1000;
                    if (n.isCfg()) {
                        std.debug.assert(n.isBasicBlockEnd());
                        return 0;
                    }

                    var score: usize = 500;
                    if (!n.isDef()) return score;

                    if (self.remote_def) score = 200;

                    var cnts: [2]usize = @splat(0);
                    const flags = b: {
                        if (n.outputs().len > 1 and n.isClone() or n.isReadonly())
                            break :b false;

                        for (n.outputs()) |o| {
                            if (o.get().cfg0() != b) continue;
                            if (o.get().isCfg()) break :b true;
                            cnts[@intFromBool(self.single_def)] += 1;
                        }

                        break :b false;
                    };
                    score -= @as(usize, @min(cnts[0], 2)) * 10;
                    score -= @as(usize, @min(cnts[1], 2)) * 100;
                    if (flags) return 10;

                    var tmp = utils.Arena.scrath(null);
                    defer tmp.deinit();

                    cnts = @splat(0);
                    for (n.dataDeps(), n.dataDepOffset()..) |def, i| {
                        if (def.cfg0() != b) continue;
                        if (def.outputs().len > 1) continue;
                        cnts[
                            @intFromBool(meta[def.schedule].single_def or
                                n.regMask(fnc, i, tmp.arena).count() == 1)
                        ] += 1;
                    }

                    score += @as(usize, @min(cnts[0], 2)) * 10;
                    score += @as(usize, @min(cnts[1], 2)) * 100;

                    std.debug.assert(10 <= score and score <= 990);
                    return score;
                }
            };

            const bbn = &bb.base;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            // init meta
            const metas: []NodeMeta = tmp.arena.alloc(NodeMeta, bbn.outputs().len);
            for (bbn.outputs(), metas, 0..) |in, *m, i| {
                const instr = in.get();
                instr.schedule = @intCast(i);

                m.* = .{};

                if (instr.kind != .Phi) {
                    for (instr.inputs()[1..]) |def| if (def) |df| {
                        // if instr == df, this is a infinite loop
                        if ((!df.isCfg() and df.tryCfg0() == bb) or instr == df) {
                            m.unscheduled_deps += 1;
                        } else if (df.isDef()) {
                            m.remote_use = true;
                        }
                    };
                }

                if (instr.isDef()) {
                    var rmask = instr.regMask(func, 0, tmp.arena);
                    for (instr.outputs()) |use| {
                        if (!use.get().hasUseFor(use.pos(), instr)) continue;
                        if (use.get().cfg0() != bb) m.remote_def = true;
                        rmask.setIntersection(use.get()
                            .regMask(func, use.pos(), tmp.arena));
                    }

                    m.single_def = rmask.count() == 1;
                }
            }

            for (bbn.outputs(), metas) |in, *m| {
                const instr = in.get();
                if (instr.inPlaceSlot()) |slot| {
                    const def = instr.dataDeps()[slot];
                    if (def.cfg0() == bb) {
                        m.single_def = metas[def.schedule].single_def;
                    }
                }
            }

            const outs = bb.base.outputs();
            var ready: usize = 0;
            for (outs) |*o| {
                if (metas[o.get().schedule].unscheduled_deps == 0) {
                    std.mem.swap(Node.Out, &outs[ready], o);
                    ready += 1;
                }
            }

            var scheduled: usize = 0;
            if (ready != scheduled) while (scheduled < outs.len - 1) {
                if (ready == scheduled) utils.panic("{} {} {} {any}", .{ scheduled, outs.len, bbn, outs[scheduled..] });

                var pick = scheduled;
                var pick_priority = metas[outs[pick].get().schedule]
                    .priority(func, bb, outs[pick].get(), metas);
                for (outs[scheduled + 1 .. ready], scheduled + 1..) |n, i| {
                    const o = n.get();
                    const o_priority = metas[o.schedule].priority(func, bb, o, metas);
                    if (o_priority > pick_priority) {
                        pick = i;
                        pick_priority = o_priority;
                    }
                }

                const n = outs[pick].get();
                for (n.outputs()) |def| if (bb == def.get().tryCfg0() and
                    def.get().kind != .Phi)
                {
                    metas[def.get().schedule].unscheduled_deps -= 1;
                };

                std.mem.swap(Node.Out, &outs[scheduled], &outs[pick]);
                scheduled += 1;

                for (outs[ready..]) |*o| {
                    if (metas[o.get().schedule].unscheduled_deps == 0) {
                        std.debug.assert(o.get().kind != .Phi);
                        std.mem.swap(Node.Out, &outs[ready], o);
                        ready += 1;
                    }
                }
            };
        }

        fn shedEarly(
            gcm: *Self,
            node: *Func.Node,
            early: *Func.CfgNode,
            visited: *std.DynamicBitSetUnmanaged,
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
                    utils.panic("{}\n", .{node});
                }

                var best = early;
                if (node.inputs()[0]) |n| if (n.asCfg()) |cn| {
                    if (n.kind != .Start) best = cn;
                };

                for (node.inputs()[1..]) |oin| if (oin) |in| {
                    if (in.isFloating()) continue;
                    if (in.cfg0().idepth() > best.idepth()) {
                        best = in.cfg0();
                    }
                };

                std.debug.assert(best.base.kind != .Start);

                self.setInputIgnoreIntern(node, 0, &best.base);
            }
        }
    };
}
