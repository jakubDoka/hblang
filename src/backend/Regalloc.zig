const std = @import("std");
const utils = graph.utils;
const graph = @import("graph.zig");

pub const use_new_ralloc = @import("options").use_new_ralloc;

const Set = std.DynamicBitSetUnmanaged;
const Map = std.AutoArrayHashMapUnmanaged;
const Arry = std.ArrayListUnmanaged;
const Error = error{RegallocFailed};

pub fn setIntersects(a: Set, b: Set) bool {
    return for (graph.setMasks(a), graph.setMasks(b)) |aa, bb| {
        if (aa & bb != 0) return true;
    } else false;
}

pub inline fn swap(a: anytype, b: @TypeOf(a)) void {
    std.mem.swap(@TypeOf(a.*), a, b);
}

pub const ralloc = newRalloc;

pub fn newRalloc(comptime Backend: type, func: *graph.Func(Backend)) []u16 {
    func.gcm.cfg_built.assertLocked();

    errdefer unreachable;

    for (0..8) |i| {
        return rallocRound(Backend, func, i) catch continue;
    } else unreachable;
}

pub fn rallocRound(comptime Backend: type, func: *graph.Func(Backend), round: usize) Error![]u16 {
    _ = round; // autofix
    const Func = graph.Func(Backend);
    const Node = Func.Node;
    const CfgNode = Func.CfgNode;

    const unresolved_reg = std.math.maxInt(u16);
    const no_def_sentinel = std.math.maxInt(u16);

    const LiveRange = struct {
        parent: ?*LiveRange = null,
        killed_by: ?*Node = null,
        mask: Set,
        def: *Node,
        failed: bool = false,
        reg: u16 = unresolved_reg,

        const LiveRange = @This();

        pub fn format(self: *const LiveRange, comptime a: anytype, b: anytype, writer: anytype) !void {
            try writer.writeAll("def: ");
            try self.def.format(a, b, writer);
            try writer.writeAll(", ");
            try writer.writeAll("mask: ");
            for (graph.setMasks(self.mask)) |m| {
                try writer.print("{x:016} ", .{m});
            }
            if (self.killed_by) |k| {
                try writer.writeAll("\n\tkilled by: ");
                try k.format(a, b, writer);
            }
        }

        pub fn index(self: *LiveRange, live_ranges: []const LiveRange) u16 {
            return @intCast((@intFromPtr(self) - @intFromPtr(live_ranges.ptr)) / @sizeOf(LiveRange));
        }

        pub fn fail(self: *LiveRange, live_ranges: []const LiveRange, failed: *Arry(u16)) void {
            std.debug.assert(self.parent == null);
            if (self.failed) return;
            self.failed = true;
            failed.appendAssumeCapacity(self.index(live_ranges));
        }

        pub fn unify(self: *LiveRange, other: *LiveRange, live_ranges: []const LiveRange) bool {
            if (self == other) return false;

            var s, var o = .{ self, other };
            if (self.index(live_ranges) < other.index(live_ranges)) {
                std.mem.swap(*LiveRange, &s, &o);
            }

            o.parent = s;

            s.mask.setIntersection(o.mask);
            o.mask = .{};

            return s.mask.count() == 0;
        }

        pub fn unionFind(self: *LiveRange) *LiveRange {
            const parent = self.parent orelse return self;
            const parent_parent = parent.parent orelse return parent;

            var fuel: usize = 1000;
            var root = parent_parent;
            while (root.parent) |p| : (root = p) fuel -= 1;

            var cursor = self;
            while (cursor.parent) |p| : (cursor = p) {
                cursor.parent = root;
                fuel -= 1;
            }

            return root;
        }

        pub fn init(buf: *Arry(LiveRange), mask: Set, def: *Node) *LiveRange {
            const lrg = buf.addOneAssumeCapacity();
            lrg.* = .{ .mask = mask, .def = def };
            return lrg;
        }

        const Conflict = struct {
            lrg: *LiveRange,
            instr: *Node,
        };

        pub fn selfConflict(self: *LiveRange, instr: *Node, other: ?*Node, conflicts: *Arry(Conflict)) bool {
            if (other) |o| {
                if (o != other) {
                    conflicts.appendAssumeCapacity(.{ .lrg = self, .instr = instr });
                    conflicts.appendAssumeCapacity(.{ .lrg = self, .instr = o });
                    return true;
                }
            }
            return false;
        }

        pub fn collectMembers(self: *LiveRange, members: *Arry(u16), arena: *utils.Arena) void {
            _ = self; // autofix
            _ = members; // autofix
            _ = arena; // autofix
            unreachable;
        }

        pub fn isSame(self: *LiveRange, other: *Node, lrg_table: []const *LiveRange) bool {
            var cursor = other;
            while (cursor.kind == .MachSplit) {
                cursor = cursor.inputs()[1].?;
            }
            return lrg_table[cursor.schedule] == self;
        }

        pub fn hasDef(self: *LiveRange, def: *Node, lrg_table: []const *LiveRange) bool {
            if (def.schedule == no_def_sentinel) return false;
            return lrg_table[def.schedule] == self;
        }

        pub fn collectLoopDepth(fnc: *Func, member: *Node, cfg: *CfgNode, min: u32, max: u32) struct { u32, u32 } {
            if (member.kind == .MachSplit) return .{ min, max };

            var depth = fnc.loopDepth(&cfg.base);

            if (depth < min) slid_to_loop: {
                const outs = cfg.base.outputs();
                if (outs[outs.len - 1].kind == .Return) break :slid_to_loop;
                const loop = outs[outs.len - 1].outputs()[0];
                if (loop.kind != .Loop or loop.inputs()[0] != outs[outs.len - 1]) {
                    break :slid_to_loop;
                }

                var iter = std.mem.reverseIterator(outs[0 .. outs.len - 1]);
                while (iter.next()) |instr| {
                    if (instr == member) {
                        depth = fnc.loopDepth(loop);
                        break;
                    }

                    if (instr.kind != .MachSplit) break; // TODO: clonable
                }
            }

            return .{ @min(min, depth), @max(max, depth) };
        }

        pub fn isSameBlockNoClobber(node: *Node, lrg_table: []const *LiveRange) bool {
            std.debug.assert(node.kind == .MachSplit);
            const def = node.dataDeps()[0];
            const cfg = node.cfg0();
            if (def.cfg0() != cfg) return false;
            var reg = lrg_table[def.schedule].reg;
            if (reg == unresolved_reg) reg = @intCast(lrg_table[def.schedule].mask.findFirstSet() orelse
                return false);
            var iter = std.mem.reverseIterator(cfg.base.outputs()[0..cfg.base.posOfOutput(node)]);
            while (iter.next()) |instr| {
                if (instr == node) return true;
                if (instr.schedule == no_def_sentinel) continue;
                if (lrg_table[def.schedule] == lrg_table[instr.schedule]) return false;
                if (lrg_table[instr.schedule].reg == reg) return false;
            } else unreachable;
        }
    };

    const LiveMap = Map(*LiveRange, *Node);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    func.gcm.instr_count = 0;
    const shoud_log = false;
    if (shoud_log) std.debug.print("\n", .{});
    for (func.gcm.postorder) |bb| {
        if (shoud_log) std.debug.print("{}\n", .{bb});
        for (bb.base.outputs()) |instr| {
            if (shoud_log) std.debug.print("  {}\n", .{instr});
            if (instr.isDef()) {
                instr.schedule = func.gcm.instr_count;
                func.gcm.instr_count += 1;
            } else {
                instr.schedule = no_def_sentinel;
            }
        }
    }
    if (shoud_log) std.debug.print("\n", .{});

    if (func.gcm.instr_count == 0) return &.{};

    var lrgs = tmp.arena.makeArrayList(LiveRange, func.gcm.instr_count);
    const lrg_table_build = tmp.arena.alloc(?*LiveRange, func.gcm.instr_count);
    @memset(lrg_table_build, null);
    var failed = tmp.arena.makeArrayList(u16, func.gcm.instr_count);

    // # Build live ranges
    //
    for (func.gcm.postorder) |bb| {
        for (bb.base.outputs()) |instr| {
            if (instr.schedule == no_def_sentinel) continue;

            if (instr.kind == .Phi) {
                const lrg = lrg_table_build[instr.schedule] orelse
                    for (instr.dataDeps()) |d| {
                        if (lrg_table_build[d.schedule]) |l| break l;
                    } else LiveRange.init(&lrgs, instr.regMask(0, tmp.arena), instr);

                lrg_table_build[instr.schedule] = lrg;

                for (instr.dataDeps()) |d| {
                    if (lrg_table_build[d.schedule]) |l| {
                        if (lrg.unify(l, lrgs.items)) {
                            lrg.fail(lrgs.items, &failed);
                        }
                    } else {
                        lrg_table_build[d.schedule] = lrg;
                    }
                }
                continue;
            }

            const lrg = lrg_table_build[instr.schedule] orelse
                LiveRange.init(&lrgs, instr.regMask(0, tmp.arena), instr);

            lrg_table_build[instr.schedule] = lrg;

            if (instr.inPlaceSlot()) |idx| {
                const up_lrg = lrg_table_build[instr.dataDeps()[idx].schedule].?;
                if (lrg.unify(up_lrg, lrgs.items)) {
                    lrg.fail(lrgs.items, &failed);
                    continue;
                }
            }

            for (instr.outputs()) |use| {
                const idx = use.posOfInput(instr);
                lrg.mask.setIntersection(use.regMask(idx, tmp.arena));
                if (lrg.mask.count() == 0) {
                    lrg.fail(lrgs.items, &failed);
                    break;
                }
            }
        }
    }

    for (lrg_table_build) |*lrg| {
        lrg.* = lrg.*.?.unionFind();
    }
    const lrg_table: []*LiveRange = @ptrCast(lrg_table_build);

    errdefer {
        for (failed.items) |lrg_idx| {
            const lrg = &lrgs.items[lrg_idx];
            std.debug.assert(lrg.failed);

            if (shoud_log) std.debug.print("{}\n", .{lrg});

            const alc = tmp.arena.allocator();
            var members: Map(*Node, void) = .empty;
            members.put(alc, lrg.def, {}) catch unreachable;

            var i: usize = 0;
            while (i < members.entries.len) : (i += 1) {
                const def: *Node = members.entries.items(.key)[i];
                if (def.schedule == no_def_sentinel) continue;
                if (lrg_table[def.schedule] != lrg) continue;
                for (def.outputs()) |o| {
                    if (o.hasNoUseFor(def)) continue;
                    members.put(alc, o, {}) catch unreachable;
                }
                for (def.dataDeps()) |d| {
                    if (lrg.hasDef(d, lrg_table)) {
                        members.put(alc, d, {}) catch unreachable;
                    }
                }
            }

            if (shoud_log) for (members.entries.items(.key)) |o| {
                const depth = func.loopDepth(o);
                std.debug.print("|- [{}] {}\n", .{ depth, o });
            };

            var min: u32, var max: u32 = .{ 1000, 0 };
            for (@as([]*Node, members.entries.items(.key))) |member| {
                if (lrg.hasDef(member, lrg_table)) {
                    min, max = LiveRange
                        .collectLoopDepth(func, member, member.cfg0(), min, max);
                }

                if (member.kind == .Phi) {
                    for (member.dataDeps(), member.cfg0().base.inputs()) |dep, cfg| {
                        min, max = LiveRange
                            .collectLoopDepth(func, dep, cfg.?.cfg0(), min, max);
                    }
                } else {
                    for (member.dataDeps()) |dep| {
                        if (lrg.isSame(dep, lrg_table)) {
                            min, max = LiveRange
                                .collectLoopDepth(func, dep, dep.cfg0(), min, max);
                        }
                    }
                }
            }

            if (shoud_log) std.debug.print("min {} max {}\n", .{ min, max });

            for (@as([]*Node, members.entries.items(.key))) |member| {
                if (min == max and member.kind == .MachSplit) continue;

                if (lrg.hasDef(member, lrg_table) and
                    (min == max or func.loopDepth(member) <= min) and
                    // TODO: (is clone) and
                    !(member.outputs().len == 1 and member.outputs()[0].kind == .MachSplit and
                        LiveRange.isSameBlockNoClobber(member.outputs()[0], lrg_table)))
                {
                    func.splitAfterSubsume(member, .@"def/loop");
                }

                if (member.kind == .Phi) {
                    for (member.dataDeps(), member.cfg0().base.inputs(), 0..) |dep, cfg, j| {
                        if (dep.kind == .MachSplit) continue;

                        if (min != max and func.loopDepth(cfg.?) > max) continue;

                        if (member.cfg0().base.kind == .Loop and j == 1 and
                            dep.kind == .Phi and dep.cfg0() == member.cfg0()) continue;

                        func.splitBefore(member, j, dep, .@"use/loop/phi");
                    }
                } else {
                    for (member.dataDeps(), member.dataDepOffset()..) |dep, j| {
                        if (!lrg.isSame(dep, lrg_table)) continue;

                        if (min != max and func.loopDepth(member) > max) continue;

                        func.splitBefore(member, j, dep, .@"use/loop/use");
                    }
                }
            }
        }
    }

    if (failed.items.len != 0) {
        return error.RegallocFailed;
    }

    const block_liveouts = tmp.arena.alloc(LiveMap, func.gcm.postorder.len);
    @memset(block_liveouts, LiveMap.empty);
    const interference = tmp.arena.alloc(Set, lrgs.items.len);
    for (interference) |*r| r.* = Set.initEmpty(
        tmp.arena.allocator(),
        lrgs.items.len,
    ) catch unreachable;

    var conflicts = tmp.arena.makeArrayList(LiveRange.Conflict, @max(lrgs.items.len, 16));

    var work_list = tmp.arena.makeArrayList(u16, func.gcm.postorder.len);
    var in_work_list = Set.initFull(
        tmp.arena.allocator(),
        func.gcm.postorder.len,
    ) catch unreachable;
    for (0..func.gcm.postorder.len) |i| {
        work_list.appendAssumeCapacity(@intCast(i));
    }
    var tmp_liveins = LiveMap.empty;
    while (work_list.pop()) |task| {
        in_work_list.unset(task);
        const bb = func.gcm.postorder[task];
        const liveouts = block_liveouts[task];

        tmp_liveins.clearRetainingCapacity();
        tmp_liveins.ensureTotalCapacity(
            tmp.arena.allocator(),
            liveouts.entries.len,
        ) catch unreachable;
        for (
            liveouts.entries.items(.key),
            liveouts.entries.items(.value),
        ) |k, v| tmp_liveins.putAssumeCapacity(k, v);

        var iter = std.mem.reverseIterator(bb.base.outputs());
        while (iter.next()) |in| {
            const instr: *Node = in;
            if (instr.schedule != no_def_sentinel) {
                const instr_lrg = lrg_table[instr.schedule];
                const value = if (tmp_liveins.fetchSwapRemove(instr_lrg)) |v| v.value else null;
                _ = instr_lrg.selfConflict(instr, value, &conflicts);

                if (instr.kind == .Phi) continue;

                for (tmp_liveins.entries.items(.value)) |concu| {
                    const concu_lrg = lrg_table[concu.schedule];
                    const concu_single_reg = concu_lrg.mask.count() == 1;
                    const instr_single_reg = instr_lrg.mask.count() == 1;
                    const first_concu = if (concu_single_reg) concu_lrg.mask.findFirstSet() else null;
                    const first_instr = if (instr_single_reg) instr_lrg.mask.findFirstSet() else null;

                    if (concu_single_reg) {
                        instr_lrg.mask.unset(first_concu.?);
                        if (instr_lrg.mask.count() == 0) {
                            if (shoud_log) {
                                std.debug.print("killed by concu {}\n", .{concu_lrg});
                                std.debug.print("                {}\n", .{instr_lrg});
                            }
                            instr_lrg.fail(lrgs.items, &failed);
                            break;
                        }
                    }

                    if (instr_single_reg) {
                        concu_lrg.mask.unset(first_instr.?);
                        if (concu_lrg.mask.count() == 0) {
                            if (shoud_log) {
                                std.debug.print("killed by instr {}\n", .{instr_lrg});
                                std.debug.print("                {}\n", .{concu_lrg});
                            }
                            concu_lrg.fail(lrgs.items, &failed);
                        }
                    }

                    if (!concu_single_reg and !instr_single_reg and
                        setIntersects(concu_lrg.mask, instr_lrg.mask))
                    {
                        std.debug.assert(instr.schedule != concu.schedule);
                        interference[instr_lrg.index(lrgs.items)].set(concu_lrg.index(lrgs.items));
                        interference[concu_lrg.index(lrgs.items)].set(instr_lrg.index(lrgs.items));
                    }
                }
            }

            const kills = instr.clobbers();
            if (kills != 0) for (tmp_liveins.entries.items(.key)) |al| {
                const active_lrg: *LiveRange = al;
                // we don't skip if killed_by is not null since we are going in reverse
                std.debug.assert(active_lrg.mask.bit_length >= @bitSizeOf(@TypeOf(kills)));
                @as(
                    *align(@alignOf(usize)) @TypeOf(kills),
                    @ptrCast(&graph.setMasks(active_lrg.mask)[0]),
                ).* &= ~kills;

                if (active_lrg.mask.count() == 0) {
                    active_lrg.killed_by = instr;
                    active_lrg.fail(lrgs.items, &failed);
                }
            };

            for (instr.dataDeps()) |def| {
                tmp_liveins.put(
                    tmp.arena.allocator(),
                    lrg_table[def.schedule],
                    def,
                ) catch unreachable;
            }
        }

        if (bb.base.kind == .Entry) continue;

        for (bb.base.inputs(), 0..) |prd, i| {
            const pred: *Node = prd.?.inputs()[0].?;
            const pred_block = &block_liveouts[pred.schedule];

            var dirty: bool = false;

            for (
                tmp_liveins.entries.items(.key),
                tmp_liveins.entries.items(.value),
            ) |k, v| {
                const other = pred_block.fetchPut(tmp.arena.allocator(), k, v) catch unreachable;
                dirty = k.selfConflict(pred, if (other) |o| o.value else null, &conflicts) or dirty;
                dirty = other == null or dirty;
            }

            for (bb.base.outputs()) |out| {
                if (out.kind != .Phi or out.schedule == no_def_sentinel) continue;
                const k, const v = .{ lrg_table[out.schedule], out.dataDeps()[i] };
                const other = pred_block.fetchPut(tmp.arena.allocator(), k, v) catch unreachable;
                dirty = k.selfConflict(pred, if (other) |o| o.value else null, &conflicts) or dirty;
                dirty = other == null or dirty;
            }

            if (dirty and !in_work_list.isSet(pred.schedule)) {
                in_work_list.set(pred.schedule);
                work_list.appendAssumeCapacity(pred.schedule);
            }
        }
    }

    errdefer {
        if (conflicts.items.len != 0) unreachable;
    }

    if (failed.items.len != 0 or conflicts.items.len != 0) {
        return error.RegallocFailed;
    }

    const ifg = tmp.arena.alloc([]u16, lrgs.items.len);
    for (ifg, interference) |*r, in| {
        const count = in.count();
        r.* = tmp.arena.alloc(u16, count);
        var i: usize = 0;
        var iter = in.iterator(.{});
        while (iter.next()) |k| : (i += 1) {
            r.*[i] = @intCast(k);
        }
    }

    var color_stack = tmp.arena.alloc(u16, lrgs.items.len);
    var fill: usize = 0;
    for (lrgs.items, 0..) |lrg, i| {
        if (lrg.parent != null) continue;
        color_stack[fill] = @intCast(i);
        fill += 1;
    }
    color_stack = color_stack[0..fill];

    var done_cursor: usize = 0;
    var known_cursor: usize = 0;

    for (color_stack, 0..) |color, i| {
        const lrg = lrgs.items[color];
        if (lrg.mask.count() > ifg[color].len) {
            swap(&color_stack[known_cursor], &color_stack[i]);
            known_cursor += 1;
        }
    }

    while (done_cursor < color_stack.len) : (done_cursor += 1) {
        if (done_cursor == known_cursor) {
            // TODO: add heuristic
            known_cursor += 1;
        }

        // TODO: add heuristic
        const best = color_stack[done_cursor];

        for (ifg[best]) |adj| {
            std.debug.assert(best != adj);
            const other_adj = ifg[adj];
            const idx = std.mem.indexOfScalar(u16, other_adj, best).?;
            swap(&other_adj[idx], &other_adj[other_adj.len - 1]);
            ifg[adj].len -= 1;

            if (ifg[adj].len + 1 == lrgs.items[adj].mask.count()) {
                const i = std.mem.indexOfScalarPos(u16, color_stack, known_cursor, adj).?;
                swap(&color_stack[known_cursor], &color_stack[i]);
                known_cursor += 1;
            }
        }
    }

    var iter = std.mem.reverseIterator(color_stack);
    while (iter.next()) |c| {
        const color: u16 = c;
        const lrg = &lrgs.items[color];

        for (ifg[color]) |adj| {
            const adj_lrg = &lrgs.items[adj];
            if (adj_lrg.reg != unresolved_reg) {
                lrg.mask.unset(adj_lrg.reg);
            }
            ifg[adj].len += 1;
            std.debug.assert(ifg[adj][ifg[adj].len - 1] == color);
        }

        if (lrg.mask.findFirstSet()) |reg| {
            lrg.reg = @intCast(reg);
        } else {
            lrg.fail(lrgs.items, &failed);
        }
    }

    if (failed.items.len != 0) {
        return error.RegallocFailed;
    }

    // first allocate into tmp since its near in memory
    const alloc = tmp.arena.alloc(u16, func.gcm.instr_count);

    for (func.gcm.postorder) |bb| {
        for (bb.base.outputs()) |instr| {
            if (instr.schedule == no_def_sentinel) continue;
            const instr_lrg = lrg_table[instr.schedule];
            alloc[instr.schedule] = instr_lrg.reg;
        }
    }

    return func.arena.allocator().dupe(u16, alloc) catch unreachable;
}

pub fn oldRalloc(comptime Backend: type, func: *graph.Func(Backend)) []u16 {
    func.gcm.cfg_built.assertLocked();

    errdefer unreachable;

    const Func = graph.Func(Backend);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    // small overcommit is fine
    var instr_table = tmp.arena.alloc(*Func.Node, func.gcm.instr_count);
    var instr_masks = tmp.arena.alloc(Set, func.gcm.instr_count);

    // compress the instruction count, the non defs dont need to be represented
    // in the interference_table
    //
    func.gcm.instr_count = 0;
    for (func.gcm.postorder) |bb| {
        for (bb.base.outputs()) |instr| {
            if (instr.isDef() or instr.kills()) {
                instr.schedule = func.gcm.instr_count;
                instr_table[func.gcm.instr_count] = instr;
                instr_masks[func.gcm.instr_count] = instr.regMask(0, tmp.arena);
                func.gcm.instr_count += 1;
            } else {
                instr.schedule = std.math.maxInt(u16);
            }
        }
    }

    if (func.gcm.instr_count == 0) return &.{};

    instr_table = instr_table[0..func.gcm.instr_count];
    instr_masks = instr_masks[0..func.gcm.instr_count];

    const block_liveouts = tmp.arena.alloc(Set, func.gcm.postorder.len);
    for (block_liveouts) |*b| b.* = try Set.initEmpty(tmp.arena.allocator(), func.gcm.instr_count);

    var in_interference_work = try Set.initFull(tmp.arena.allocator(), func.gcm.postorder.len);
    var interference_work = tmp.arena.makeArrayList(u16, func.gcm.postorder.len);
    for (0..interference_work.capacity) |i| interference_work.appendAssumeCapacity(@intCast(i));

    const interference_table = tmp.arena.alloc(Set, func.gcm.instr_count);
    for (interference_table) |*r| r.* = Set.initEmpty(tmp.arena.allocator(), func.gcm.instr_count) catch unreachable;

    var slider = try Set.initEmpty(tmp.arena.allocator(), func.gcm.instr_count);

    while (interference_work.pop()) |w| {
        in_interference_work.unset(w);
        const bb = func.gcm.postorder[w];
        const liveouts = block_liveouts[w];

        @memcpy(graph.setMasks(slider), graph.setMasks(liveouts));

        var iter = std.mem.reverseIterator(bb.base.outputs());
        while (iter.next()) |n| {
            const node: *Func.Node = n;

            if (node.inPlaceSlot()) |c| {
                for (node.dataDeps(), 0..) |d, k| {
                    if (k != c) {
                        interference_table[node.schedule].set(d.schedule);
                        interference_table[d.schedule].set(node.schedule);
                    }
                }
            }

            if (node.isDef() or node.kills()) {
                slider.unset(node.schedule);
                const node_masks = graph.setMasks(instr_masks[node.schedule]);

                var siter = slider.iterator(.{});
                while (siter.next()) |elem| {
                    std.debug.assert(elem != node.schedule);

                    // backends should ensure incompatible registers dont overlap
                    // this way the type of the register is also encoded
                    //
                    for (graph.setMasks(instr_masks[elem]), node_masks) |a, b| {
                        if (a & b != 0) break;
                    } else continue;

                    interference_table[elem].set(node.schedule);
                    interference_table[node.schedule].set(elem);
                }

                // phi is unified with mach moves
                if (node.kind == .Phi) continue;
            }

            //std.debug.print("{}\n", .{node});
            for (node.dataDeps()) |dd| {
                //std.debug.print("- {}\n", .{dd.?});
                slider.set(dd.schedule);
            }
        }

        if (bb.base.kind == .Entry) {
            std.debug.assert(slider.count() == 0);
            continue;
        }

        for (bb.base.inputs()) |p| {
            const pred = p.?.inputs()[0].?;
            const pred_block = block_liveouts[pred.schedule];

            var dirty: Set.MaskInt = 0;
            for (graph.setMasks(slider), graph.setMasks(pred_block)) |in, *out| {
                dirty |= out.* ^ in;
                out.* |= in;
            }
            if (dirty != 0 and !in_interference_work.isSet(pred.schedule)) {
                in_interference_work.set(pred.schedule);
                interference_work.appendAssumeCapacity(pred.schedule);
            }
        }
    }

    const edge_table = tmp.arena.alloc([]u16, func.gcm.instr_count);
    const lens = tmp.arena.alloc(u16, func.gcm.instr_count);
    for (edge_table, lens, interference_table) |*edges, *len, row| {
        edges.* = tmp.arena.alloc(u16, row.count());
        len.* = @intCast(edges.len);
        var iter = row.iterator(.{});
        var j: usize = 0;
        while (iter.next()) |k| : (j += 1) edges.*[j] = @intCast(k);
    }

    // alocate to the arena and then copy later for sequential access
    //
    const sentinel = 0;
    const outs = tmp.arena.alloc(u16, func.gcm.instr_count);
    @memset(outs, sentinel);
    if (false) {
        var color_stack = tmp.arena.alloc(u16, func.gcm.instr_count);
        for (color_stack, 0..func.gcm.instr_count) |*slt, i| slt.* = @intCast(i);
        var done_cursor: usize = 0;
        var known_cursor: usize = 0;

        // TODO: count range
        const allowed_reg_counts = tmp.arena.alloc(u16, func.gcm.instr_count);
        const loop_scores = tmp.arena.alloc(u16, func.gcm.instr_count);
        var tmp_mask = try Set.initEmpty(tmp.arena.allocator(), instr_masks[0].bit_length);
        for (
            edge_table,
            instr_masks,
            instr_table,
            color_stack,
            allowed_reg_counts,
            loop_scores,
        ) |edges, mask, instr, *slot, *arc, *ls| {
            ls.* = func.loopDepth(instr);
            for (instr.outputs()) |o| ls.* = @max(func.loopDepth(o), ls.*);

            tmp_mask.setRangeValue(.{ .start = 0, .end = Backend.reg_count + 1 }, true);
            tmp_mask.setIntersection(mask);
            arc.* = @intCast(tmp_mask.count());
            if (arc.* > edges.len) {
                swap(&color_stack[known_cursor], slot);
                known_cursor += 1;
            }
        }

        while (done_cursor != color_stack.len) : (done_cursor += 1) {
            if (done_cursor == known_cursor) {
                // TODO: add the heuristic
                //
                //var best = known_cursor;
                //for (color_stack[known_cursor + 1], known_cursor + 1..) |color, i| {
                //    if ()
                //}
                known_cursor += 1;
            }

            var best: usize = done_cursor;
            for (
                color_stack[done_cursor + 1 .. known_cursor],
                done_cursor + 1..known_cursor,
            ) |color, i| {
                if (allowed_reg_counts[color] > allowed_reg_counts[best] or
                    loop_scores[color] < loop_scores[best])
                {
                    best = i;
                }
            }

            swap(&color_stack[done_cursor], &color_stack[best]);
            const instr = color_stack[done_cursor];

            for (edge_table[instr]) |adj| {
                std.debug.assert(instr != adj);
                {
                    const adj_edges = edge_table[adj];
                    const idx = std.mem.indexOfScalar(u16, adj_edges, instr).?;
                    swap(&adj_edges[idx], &adj_edges[adj_edges.len - 1]);
                    edge_table[adj].len -= 1;
                }

                if (edge_table[adj].len + 1 == allowed_reg_counts[adj]) {
                    const idx = std.mem.indexOfScalarPos(u16, color_stack, known_cursor, adj).?;
                    swap(&color_stack[known_cursor], &color_stack[idx]);
                    known_cursor += 1;
                    continue;
                }
            }

            var overlap_set = try Set.initEmpty(tmp.arena.allocator(), func.gcm.instr_count);
            for (color_stack) |c| {
                std.debug.assert(!overlap_set.isSet(c));
                overlap_set.set(c);
            }
        }

        for (edge_table, lens) |*e, l| e.len = l;

        //std.debug.print("coloring {any}\n", .{color_stack});
        var iter = std.mem.reverseIterator(color_stack);
        while (iter.next()) |to_color| {
            const selection_set = &instr_masks[to_color];
            std.debug.assert(!selection_set.isSet(sentinel));
            for (edge_table[to_color]) |adj| {
                std.debug.assert(to_color != adj);
                //std.debug.assert(edge_table[adj].len < interference_table[adj].count());
                //edge_table[adj].len += 1;
                //const adj_edges = edge_table[adj];
                //std.debug.assert(adj_edges[adj_edges.len - 1] == to_color);
                selection_set.unset(outs[adj]);
                @as(*align(@alignOf(usize)) u64, @ptrCast(&graph.setMasks(selection_set.*)[0])).* &=
                    ~(instr_table[adj].clobbers() << 1);
            }

            const out = &outs[to_color];
            const bias = instr_table[to_color].regBias();
            if (bias != null and selection_set.isSet(bias.? + 1)) {
                out.* = bias.? + 1;
            } else {
                var it = selection_set.iterator(.{});
                out.* = @intCast(it.next().?);
            }
            std.debug.assert(out.* != 0);
        }
    } else {
        var j = instr_table.len;
        while (j > 0) {
            j -= 1;
            const row, const out, const selection_set =
                .{ interference_table[j], &outs[j], &instr_masks[j] };
            selection_set.toggleAll();
            std.debug.assert(selection_set.isSet(sentinel));

            var row_iter = row.iterator(.{});
            while (row_iter.next()) |i| {
                selection_set.set(outs[i]);
                @as(*align(@alignOf(usize)) u64, @ptrCast(&graph.setMasks(selection_set.*)[0])).* |=
                    instr_table[i].clobbers() << 1;
            }

            const bias = instr_table[j].regBias();
            if (bias != null and !selection_set.isSet(bias.? + 1)) {
                out.* = bias.? + 1;
            } else {
                var it = selection_set.iterator(.{ .kind = .unset });
                out.* = @intCast(it.next().?);
            }
            std.debug.assert(out.* != 0);
        }
    }

    // TODO: dont do this and instead modify the backends
    for (outs) |*o| o.* -= sentinel + 1;

    return try func.arena.allocator().dupe(u16, outs);
}
