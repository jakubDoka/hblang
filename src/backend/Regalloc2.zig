const std = @import("std");
const utils = graph.utils;
const graph = @import("graph.zig");

const indexOfScalar = std.mem.indexOfScalar;
const indexOfScalarPos = std.mem.indexOfScalarPos;

// TODO: use a custom set, we dont need the length with each bitset
const Set = std.DynamicBitSetUnmanaged;
const ArrayList = std.ArrayListUnmanaged;

pub fn getMasks(set: Set) []Set.MaskInt {
    return set.masks[0 .. (set.bit_length + (@bitSizeOf(Set) - 1)) / @bitSizeOf(Set)];
}

pub fn insertAlloc(arena: *utils.Arena, arr: anytype, vl: anytype) bool {
    _ = indexOfScalar(@TypeOf(vl), arr.items, vl) orelse {
        arr.append(arena.allocator(), vl) catch unreachable;
        return true;
    };

    return false;
}

pub fn insert(arr: anytype, vl: anytype) bool {
    _ = indexOfScalar(@TypeOf(vl), arr.items, vl) orelse {
        arr.appendAssumeCapacity(vl);
        return true;
    };

    return false;
}

pub fn ralloc(comptime Mach: type, func: *graph.Func(Mach)) []u16 {
    errdefer unreachable;

    func.gcm.cfg_built.assertLocked();

    const Func = @TypeOf(func.*);

    const failed_reg = std.math.maxInt(usize);

    const LiveRange = struct {
        def: *Func.Node,
        allowed_set: Set,
        parent: ?*LiveRange = null,
        // TODO: we dont need this, it can be computed
        idx: usize,
        // valid during coloring
        reg: usize = failed_reg,
        adjacent: []*LiveRange = &.{},
        active_adjacent: usize = undefined,

        const LiveRange = @This();

        pub fn tryMerge(self: *LiveRange, other: *LiveRange) ?*LiveRange {
            std.debug.assert(self != other);
            if (self.idx > other.idx)
                other.parent = self
            else
                self.parent = other;

            self.allowed_set.setIntersection(other.allowed_set);

            if (self.allowed_set.count() == 0) {
                std.debug.print("wug\n", .{});
                return null;
            }

            return if (self.idx > other.idx) self else other;
        }

        pub fn get(self: *LiveRange) *LiveRange {
            const parent = self.parent orelse return self;
            const parent_parent = parent.parent orelse return parent;

            self.parent = rollup: {
                var root = parent_parent;
                var limit: usize = 100;
                while (root.parent) |p| : (root = p) {
                    limit -= 1;
                }

                var cursor = parent_parent;
                limit = 100;
                while (cursor.parent) |p| : (cursor = p) {
                    cursor.parent = root;
                    limit -= 1;
                }

                break :rollup root;
            };

            return self.parent.?;
        }
    };

    const Block = struct {
        liveouts: std.AutoArrayHashMapUnmanaged(*LiveRange, *Func.Node) = .empty,
    };

    const Conflict = struct {
        in: *LiveRange,
        at: *Func.Node,

        const Conflict = @This();

        fn add(
            its: *std.ArrayListUnmanaged(Conflict),
            active: *std.AutoArrayHashMapUnmanaged(*LiveRange, *Func.Node),
            live_range: *LiveRange,
            node: *Func.Node,
        ) void {
            if (active.get(live_range)) |curr_node| {
                if (curr_node != node) {
                    _ = indexOfScalar(*anyopaque, @ptrCast(its.items), node) orelse {
                        its.appendAssumeCapacity(.{ .in = live_range, .at = node });
                    };
                    _ = indexOfScalar(*anyopaque, @ptrCast(its.items), node) orelse {
                        its.appendAssumeCapacity(.{ .in = live_range, .at = curr_node });
                    };
                }
            }
        }
    };

    //var total_spill_count = 0;
    var limt: usize = 7;
    while (true) {
        limt -= 1;
        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        var live_range_slots = tmp.arena.makeArrayList(LiveRange, func.instr_count);
        var splits = tmp.arena.makeArrayList(*LiveRange, func.instr_count);
        var kills = tmp.arena.makeArrayList(*LiveRange, func.instr_count);
        var conflicts = tmp.arena.makeArrayList(Conflict, func.instr_count);
        var spill_count: usize = 0;

        const live_ranges = build_live_ranges: {
            const slots = tmp.arena.alloc(?*LiveRange, func.instr_count);
            @memset(slots, null);

            // TODO: use the second temp arena here

            for (func.gcm.postorder) |bb| {
                std.debug.assert(bb.base.isBasicBlockStart());
                for (bb.base.outputs()) |instr| {
                    if (instr.isCfg() and !instr.isBasicBlockEnd()) {
                        utils.panic("{} {}", .{ instr, &bb.base });
                    }
                    const slot = &slots[instr.schedule];

                    if (instr.isDataPhi()) {
                        if (instr.inputs()[1].?.schedule == std.math.maxInt(u16)) {
                            std.debug.print("{}\n", .{instr.inputs()[1].?.inputs()[0].?});
                        }
                        slot.* = slots[instr.inputs()[1].?.schedule];
                        std.debug.assert(slot.* != null);

                        for (instr.inputs()[2..]) |def| {
                            const lr = slots[def.?.schedule] orelse {
                                const allowed_set = def.?.allowedRegsFor(0, tmp.arena) orelse {
                                    continue;
                                };
                                slot.*.?.allowed_set.setIntersection(allowed_set);
                                if (slot.*.?.allowed_set.count() == 0) {
                                    _ = insert(&splits, slot.*.?);
                                }

                                slots[def.?.schedule] = slot.*;
                                continue;
                            };
                            slot.* = slot.*.?.tryMerge(lr) orelse {
                                _ = insert(&splits, slot.*.?);
                                break;
                            };
                        }
                    } else if (slot.* == null) {
                        const allowed_set = instr.allowedRegsFor(0, tmp.arena) orelse {
                            continue;
                        };

                        if (instr.inPlaceSlot()) |idx| {
                            const other_liverange = slots[instr.inputs()[idx].?.schedule].?.get();
                            other_liverange.allowed_set.setIntersection(allowed_set);
                            if (allowed_set.count() == 0) {
                                std.debug.print("frn\n", .{});
                                _ = insert(&splits, slot.*.?);
                                continue;
                            }

                            slot.* = other_liverange;
                        } else {
                            slot.* = live_range_slots.addOneAssumeCapacity();
                            slot.*.?.* = .{
                                .def = instr,
                                .allowed_set = allowed_set,
                                .idx = live_range_slots.items.len - 1,
                            };
                        }

                        for (instr.outputs()) |use| {
                            const idx = indexOfScalar(?*Func.Node, use.inputs(), instr) orelse
                                unreachable;
                            const other = use.allowedRegsFor(idx, tmp.arena) orelse
                                continue; // antidep?
                            slot.*.?.allowed_set.setIntersection(other);

                            if (slot.*.?.allowed_set.count() == 0) {
                                std.debug.print("pop {}\n", .{instr});
                                _ = insert(&splits, slot.*.?);
                                break;
                            }
                        }
                    }

                    std.debug.assert(slot.* != null);
                }
            }

            unify: {
                for (slots) |*s| {
                    if (s.*) |*slot| {
                        slot.* = slot.*.get();
                    }
                }

                for (splits.items) |*spill| {
                    spill.* = spill.*.get();
                }

                break :unify;
            }

            break :build_live_ranges slots;
        };

        build_interference: {
            if (spill_count + splits.items.len + kills.items.len != 0) break :build_interference;

            const blocks = tmp.arena.alloc(Block, func.gcm.postorder.len);
            @memset(blocks, .{});

            var work_list = tmp.arena.makeArrayList(*Func.CfgNode, func.gcm.postorder.len);
            work_list.appendSliceAssumeCapacity(func.gcm.postorder);

            // TODO: we can still flatten this
            const interference_matrix = tmp.arena.alloc(Set, live_range_slots.items.len);
            for (interference_matrix) |*slot| slot.* = try Set.initEmpty(tmp.arena.allocator(), live_range_slots.items.len);

            var active_nodes = std.AutoArrayHashMapUnmanaged(*LiveRange, *Func.Node).empty;
            try active_nodes.ensureTotalCapacity(tmp.arena.allocator(), live_range_slots.items.len);
            var limit: usize = 10000;
            while (work_list.pop()) |bb| {
                std.debug.print("{}\n", .{&bb.base});
                limit -= 1;
                active_nodes.clearRetainingCapacity();

                const block = &blocks[bb.base.schedule];

                for (
                    block.liveouts.entries.items(.key),
                    block.liveouts.entries.items(.value),
                ) |k, v| active_nodes.putAssumeCapacity(k, v);

                var iter = std.mem.reverseIterator(bb.base.outputs());
                while (iter.next()) |n| {
                    const node: *Func.Node = n;

                    kills: {
                        var reg_kills = node.regKills(tmp.arena) orelse break :kills;
                        reg_kills.toggleAll();

                        for (active_nodes.entries.items(.key)) |active_node| {
                            // this means its a self conflict so split insead
                            active_node.allowed_set.setIntersection(reg_kills);
                            if (active_node.allowed_set.count() == 0) {
                                std.debug.print("plup\n", .{});
                                _ = insert(&splits, active_node);
                                _ = insert(&kills, active_node);
                            }
                        }

                        break :kills;
                    }

                    if (live_ranges[node.schedule]) |node_live_range| {
                        _ = active_nodes.swapRemove(node_live_range);
                        Conflict.add(&conflicts, &active_nodes, node_live_range, node);

                        if (node_live_range.allowed_set.count() < active_nodes.entries.len and
                            node_live_range.allowed_set.count() != 1)
                        {
                            spill_count += 1;
                        }

                        for (active_nodes.entries.items(.key)) |active_live_range| {
                            std.debug.assert(active_live_range != node_live_range);
                            const node_allow_set_masks = getMasks(node_live_range.allowed_set);
                            const active_allow_set_masks = getMasks(active_live_range.allowed_set);

                            if (node_live_range.allowed_set.count() == 1) {
                                for (active_allow_set_masks, node_allow_set_masks) |*a, b| a.* &= ~b;
                                std.debug.print("wha {} {}\n", .{ node_live_range.def, active_live_range.def });
                                if (active_live_range.allowed_set.count() == 0) {
                                    _ = insert(&splits, active_live_range);
                                }
                            } else if (active_live_range.allowed_set.count() == 1) {
                                for (node_allow_set_masks, active_allow_set_masks) |*a, b| a.* &= ~b;
                                std.debug.print("bha {} {}\n", .{ node_live_range.def, active_live_range.def });
                                if (node_live_range.allowed_set.count() == 0) {
                                    _ = insert(&splits, node_live_range);
                                }
                            } else {
                                interference_matrix[node_live_range.idx].set(active_live_range.idx);
                                interference_matrix[active_live_range.idx].set(node_live_range.idx);
                            }
                        }
                    }

                    if (node.kind == .Phi) {
                        continue;
                    }

                    for (node.dataDeps()) |def| {
                        const def_live_range = live_ranges[def.?.schedule] orelse unreachable;
                        Conflict.add(&conflicts, &active_nodes, def_live_range, def.?);
                        std.debug.print("-- {}\n", .{def.?});
                        active_nodes.putAssumeCapacity(def_live_range, def.?);
                    }
                }

                if (bb.base.kind == .Entry) {
                    std.debug.assert(active_nodes.count() == 0);
                    continue;
                }

                for (bb.base.inputs(), 0..) |pred_block_term, i| {
                    const pred: *Func.CfgNode = pred_block_term.?.inputs()[0].?.asCfg().?;
                    std.debug.print("|| {}\n", .{pred});
                    std.debug.assert(pred.base.isBasicBlockStart());
                    const pred_block = &blocks[pred.base.schedule];
                    if (bb.base.kind == .Loop or bb.base.kind == .Region) {
                        for (bb.base.outputs()) |use| {
                            if (use.kind == .Phi) {
                                const active_node: *Func.Node = use.inputs()[i + 1].?;
                                const active_live_range = live_ranges[use.schedule].?;

                                if (pred_block.liveouts.get(active_live_range) != null) {
                                    Conflict.add(&conflicts, &pred_block.liveouts, active_live_range, active_node);
                                } else {
                                    try pred_block.liveouts.put(tmp.arena.allocator(), active_live_range, active_node);
                                    _ = insert(&work_list, pred);
                                }
                            }
                        }
                    }
                    for (
                        active_nodes.entries.items(.key),
                        active_nodes.entries.items(.value),
                    ) |active_live_range, active| {
                        var active_node: *Func.Node = active;
                        if (active_node.kind == .Phi and active_node.cfg0().? == pred) {
                            active_node = active_node.inputs()[i + 1].?;
                        }

                        if (pred_block.liveouts.get(active_live_range) != null) {
                            Conflict.add(&conflicts, &pred_block.liveouts, active_live_range, active_node);
                        } else {
                            try pred_block.liveouts.put(tmp.arena.allocator(), active_live_range, active_node);
                            _ = insert(&work_list, pred);
                        }
                    }
                }
            }

            for (blocks, func.gcm.postorder) |bl, bb| {
                std.debug.print("{}\n", .{&bb.base});
                for (bl.liveouts.entries.items(.value)) |l| {
                    std.debug.print("-- {}\n", .{l});
                }
            }

            for (live_range_slots.items) |*live_range| {
                const cap = interference_matrix[live_range.idx].count();
                live_range.adjacent = tmp.arena.alloc(*LiveRange, cap);
                live_range.active_adjacent = cap;

                var iter = interference_matrix[live_range.idx].iterator(.{});
                for (live_range.adjacent) |*slot| slot.* = &live_range_slots.items[iter.next().?];
            }

            break :build_interference;
        }

        color: {
            if (spill_count + splits.items.len + kills.items.len +
                conflicts.items.len != 0) break :color;

            var done_frontier: usize = 0;
            var known_frontier: usize = 0;
            var color_stack = tmp.arena.alloc(*LiveRange, live_range_slots.items.len);

            bootstrap: {
                var color_stack_len: usize = 0;

                for (live_range_slots.items) |*live_range| {
                    if (live_range.parent != null) continue;
                    color_stack[color_stack_len] = live_range;
                    if (live_range.allowed_set.count() > live_range.adjacent.len) {
                        std.mem.swap(*LiveRange, &color_stack[color_stack_len], &color_stack[done_frontier]);
                        known_frontier += 1;
                    }
                    color_stack_len += 1;
                }

                color_stack.len = color_stack_len;
                break :bootstrap;
            }

            while (done_frontier < color_stack.len) : (done_frontier += 1) {
                pick_color: {
                    pick_risky: {
                        if (done_frontier < known_frontier) break :pick_risky;

                        const max_score = 10000000;
                        var best_index = color_stack.len;
                        var best_score: usize = 0;

                        for (known_frontier..color_stack.len) |pick_index| {
                            const pick = color_stack[pick_index];
                            _ = pick;

                            const score = risky_score: {
                                // TODO: clonable

                                // TODO: callee saved liverange

                                // TODO: track use and def
                                break :risky_score 1000;
                            };

                            if (score > best_score) {
                                best_score = score;
                                best_index = pick_index;
                                if (best_score == max_score) break;
                            }
                        }

                        std.mem.swap(
                            *LiveRange,
                            &color_stack[best_index],
                            &color_stack[known_frontier],
                        );

                        known_frontier += 1;

                        break :pick_color;
                    }

                    var best_index = done_frontier;
                    var best_live_range = color_stack[best_index];

                    for (done_frontier + 1..known_frontier) |pick_index| {
                        const pick = color_stack[pick_index];
                        const is_better = better: {
                            if ((pick.allowed_set.count() == 1) !=
                                (best_live_range.allowed_set.count() == 1))
                            {
                                break :better best_live_range.allowed_set.count() == 1;
                            }

                            // TODO: has split

                            break :better pick.allowed_set.count() >
                                best_live_range.allowed_set.count();
                        };

                        if (is_better) {
                            best_index = pick_index;
                            best_live_range = pick;
                        }
                    }

                    std.mem.swap(
                        *LiveRange,
                        &color_stack[best_index],
                        &color_stack[done_frontier],
                    );

                    break :pick_color;
                }

                const live_range = color_stack[done_frontier];

                for (live_range.adjacent) |adjacent_lr| {
                    std.debug.assert(adjacent_lr != live_range);
                    // remove but keep the value in the cap
                    const live_range_index =
                        indexOfScalar(*LiveRange, adjacent_lr.adjacent, live_range).?;
                    std.mem.swap(
                        *LiveRange,
                        &adjacent_lr.adjacent[live_range_index],
                        &adjacent_lr.adjacent[adjacent_lr.active_adjacent - 1],
                    );
                    adjacent_lr.active_adjacent -= 1;

                    // if we become trivial, mark as done
                    if (adjacent_lr.allowed_set.count() == adjacent_lr.active_adjacent + 1) {
                        const adjacent_lr_index =
                            indexOfScalarPos(*LiveRange, color_stack, done_frontier, adjacent_lr).?;
                        std.mem.swap(
                            *LiveRange,
                            &color_stack[done_frontier],
                            &color_stack[adjacent_lr_index],
                        );
                        done_frontier += 1;
                    }
                }
            }

            var iter = std.mem.reverseIterator(color_stack);
            while (iter.next()) |c| {
                const to_color: *LiveRange = c;
                std.debug.print("{}\n", .{to_color.def});
                for (to_color.adjacent) |adj| {
                    std.debug.assert(adj.adjacent[adj.active_adjacent] == to_color);
                    adj.active_adjacent += 1;
                    std.debug.print("-- {}\n", .{adj.def});
                    if (adj.reg == failed_reg) {
                        continue;
                    }
                    std.debug.assert(adj.allowed_set.count() != 1 or !to_color.allowed_set.isSet(adj.reg));
                    to_color.allowed_set.unset(adj.reg);
                }

                var it = to_color.allowed_set.iterator(.{});
                while (it.next()) |i| if (i < 10) std.debug.print("{} ", .{i});
                std.debug.print("\n", .{});
                if (to_color.allowed_set.findFirstSet()) |reg| {
                    // TODO: do bias selection
                    to_color.reg = reg;
                } else {
                    to_color.reg = failed_reg;
                    // TODO: fail them somehow
                }
            }

            const allocs = try func.arena.allocator().alloc(u16, func.instr_count);
            for (func.gcm.postorder) |bb| {
                std.debug.print("{}\n", .{bb});
                for (bb.base.outputs()) |instr| {
                    const live_range = live_ranges[instr.schedule] orelse {
                        std.debug.print("      {}\n", .{instr});
                        allocs[instr.schedule] = 0;
                        continue;
                    };
                    std.debug.assert(live_range.parent == null);
                    std.debug.print("  {} {} {}\n", .{ live_range.idx, live_range.reg, instr });
                    allocs[instr.schedule] = @intCast(live_range.reg);
                }
            }

            return allocs;
        }

        insert_splits: {
            for (conflicts.items) |conflict| {
                for (conflict.at.outputs()) |use| {
                    const def_pos = indexOfScalar(?*Func.Node, use.inputs(), conflict.at).?;
                    if ((use.kind == .Phi and
                        !(use.cfg0().?.base.kind == .Loop and def_pos == 2 and
                            conflict.at.cfg0().?.idepth() > use.cfg0().?.idepth())) or
                        use.inPlaceSlot() == def_pos)
                    {
                        func.splitBefore(use, conflict.at);
                    }
                }

                if (conflict.at.kind == .Phi) {
                    func.splitAfterSubsume(conflict.at);
                    func.splitBefore(conflict.at, conflict.at.inputs()[1].?);
                }
            }

            //for (kills.items) |live_range| {
            //    std.debug.assert(!live_range.def.isCfg());

            //    const block = &live_range.def.cfg0().?.base;

            //    const split = func.addSplit(block, live_range.def);

            //    const is_pinned = live_range.def.allowedRegsFor(0, tmp.arena).?.count() == 1;

            //    for (tmp.arena.dupe(*Func.Node, live_range.def.outputs())) |use| {
            //        if (use == split) continue;
            //        const use_idx = indexOfScalar(?*Func.Node, use.inputs(), live_range.def).?;
            //        if (!is_pinned and use.allowedRegsFor(use_idx, tmp.arena).?.count() != 1) continue;
            //        func.setInputNoIntern(use, use_idx, split);
            //    }

            //    const def_pos = indexOfScalar(*Func.Node, block.outputs(), live_range.def).?;
            //    const to_rotate = block.outputs()[def_pos + 1 ..];
            //    std.mem.rotate(*Func.Node, to_rotate, to_rotate.len - 1);
            //}

            //for (splits.items) |live_range| {
            //    var split_at_some_point = false;
            //    for (tmp.arena.dupe(*Func.Node, live_range.def.outputs())) |use| {
            //        //if (live_range.def.kind == .Phi) unreachable;

            //        const block = &use.useBlock(live_range.def, &.{}).base;
            //        const locked = live_range.def.allowedRegsFor(0, tmp.arena).?.count() == 1;

            //        const def_pos = indexOfScalar(?*Func.Node, use.inputs(), live_range.def).?;
            //        if (!locked and use.allowedRegsFor(def_pos, tmp.arena).?.count() != 1) {
            //            continue;
            //        }
            //        split_at_some_point = true;

            //        const split = func.addSplit(block, live_range.def);
            //        func.setInputNoIntern(use, def_pos, split);

            //        if (use.kind != .Phi) {
            //            const use_pos = indexOfScalar(*Func.Node, block.outputs(), use).?;
            //            const to_rotate = block.outputs()[use_pos..];
            //            std.mem.rotate(*Func.Node, to_rotate, to_rotate.len - 1);
            //        } else {
            //            const elems = block.outputs();
            //            std.mem.swap(*Func.Node, &elems[elems.len - 1], &elems[elems.len - 2]);
            //        }
            //    }

            //    if (!split_at_some_point) {
            //        func.fmtScheduled(std.io.getStdErr().writer().any(), std.io.tty.detectConfig(std.io.getStdErr()));
            //        utils.panic("{}", .{live_range.def});
            //    }
            //}

            func.instr_count = 0;
            for (func.gcm.postorder) |bb| {
                for (bb.base.outputs()) |instr| {
                    instr.schedule = func.instr_count;
                    func.instr_count += 1;
                }
            }

            func.fmtScheduled(std.io.getStdErr().writer().any(), std.io.tty.detectConfig(std.io.getStdErr()));
            std.debug.print("================ retry regalloc ================\n", .{});
            std.debug.print("================ splits: {} conflicts: {} kills: {}\n", .{
                splits.items.len,
                conflicts.items.len,
                kills.items.len,
            });

            break :insert_splits;
        }
    }
}
