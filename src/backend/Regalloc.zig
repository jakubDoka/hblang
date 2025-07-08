const std = @import("std");
const utils = graph.utils;
const graph = @import("graph.zig");

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

    for (0..10) |_| {
        return rallocRound(Backend, func) catch continue;
    } else unreachable;
}

pub fn rallocRound(comptime Backend: type, func: *graph.Func(Backend)) Error![]u16 {
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

            var root = parent_parent;
            while (root.parent) |p| : (root = p) {}

            var cursor = self;
            while (cursor.parent != root) {
                const next = cursor.parent.?;
                cursor.parent = root;
                cursor = next;
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

        pub fn selfConflict(
            self: *LiveRange,
            instr: *Node,
            other: ?*Node,
            conflicts: *Map(Conflict, void),
            arena: *utils.Arena,
        ) bool {
            errdefer unreachable;
            if (self.failed) return false;
            if (other) |o| {
                if (o != instr) {
                    try conflicts.put(arena.allocator(), .{ .lrg = self, .instr = instr }, {});
                    try conflicts.put(arena.allocator(), .{ .lrg = self, .instr = o }, {});
                    self.failed = true;
                    return true;
                }
            }
            return false;
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

        pub fn splitAfterSubsume(self: *Func, def: *Node, must: bool, lrg_table: []const *LiveRange, dbg: graph.builtin.MachSplit.Dbg) void {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const block = def.cfg0();
            const ins = self.addSplit(block, def, dbg);
            for (tmp.arena.dupe(*Node, def.outputs())) |use| {
                if (use == def) continue;
                if (use == ins) continue;
                if (use.hasNoUseFor(def)) continue;
                if (!must and use.kind == .MachSplit and
                    isSameBlockNoClobber(use, lrg_table)) continue;
                self.setInputNoIntern(use, use.posOfInput(1, def), ins);
            }

            const oidx = block.base.posOfOutput(def);
            const to_rotate = block.base.outputs()[oidx + 1 ..];
            std.mem.rotate(*Node, to_rotate, to_rotate.len - 1);
        }

        pub fn isSameBlockNoClobber(split: *Node, lrg_table: []const *LiveRange) bool {
            std.debug.assert(split.kind == .MachSplit);
            const def = split.dataDeps()[0];
            const cfg = split.cfg0();
            if (def.cfg0() != cfg) return false;
            var reg = lrg_table[def.schedule].reg;
            if (reg == unresolved_reg) reg = @intCast(lrg_table[def.schedule].mask.findFirstSet() orelse
                return false);
            var iter = std.mem.reverseIterator(cfg.base.outputs()[0..cfg.base.posOfOutput(split)]);
            while (iter.next()) |instr| {
                if (instr == split) return true;
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
    const should_log = false;
    if (should_log) std.debug.print("\n", .{});
    for (func.gcm.postorder) |bb| {
        if (should_log) std.debug.print("{}\n", .{bb});
        for (bb.base.outputs()) |instr| {
            if (should_log) std.debug.print("  {}\n", .{instr});
            if (instr.isDef()) {
                instr.schedule = func.gcm.instr_count;
                func.gcm.instr_count += 1;
            } else {
                instr.schedule = no_def_sentinel;
            }
        }
    }
    if (should_log) std.debug.print("\n", .{});

    if (func.gcm.instr_count == 0) return &.{};

    var build_lrgs = tmp.arena.makeArrayList(LiveRange, func.gcm.instr_count);
    const lrg_table_build = tmp.arena.alloc(?*LiveRange, func.gcm.instr_count);
    @memset(lrg_table_build, null);
    var failed = tmp.arena.makeArrayList(u16, func.gcm.instr_count);

    // # Build live ranges
    //
    for (func.gcm.postorder) |bb| {
        for (bb.base.outputs()) |instr| {
            if (instr.schedule == no_def_sentinel) continue;

            var lrg = if (instr.kind == .Phi) lrg: {
                std.debug.assert(instr.isDataPhi());
                var lrg = lrg_table_build[instr.schedule] orelse
                    for (instr.dataDeps()) |d| {
                        if (lrg_table_build[d.schedule]) |l| break l;
                    } else LiveRange.init(&build_lrgs, instr.regMask(func, 0, tmp.arena), instr);

                lrg = lrg.unionFind();

                lrg_table_build[instr.schedule] = lrg;

                for (instr.dataDeps()) |d| {
                    if (lrg_table_build[d.schedule]) |l| {
                        if (lrg.unify(l.unionFind(), build_lrgs.items)) {
                            lrg.unionFind().fail(build_lrgs.items, &failed);
                        }
                        lrg = lrg.unionFind();
                    } else {
                        lrg_table_build[d.schedule] = lrg;
                    }
                }

                break :lrg lrg;
            } else lrg: {
                var lrg = lrg_table_build[instr.schedule] orelse
                    LiveRange.init(&build_lrgs, instr.regMask(func, 0, tmp.arena), instr);

                lrg = lrg.unionFind();
                lrg_table_build[instr.schedule] = lrg;

                if (instr.inPlaceSlot()) |idx| {
                    const up_lrg = lrg_table_build[instr.dataDeps()[idx].schedule].?.unionFind();
                    std.debug.assert(up_lrg.parent == null);
                    if (lrg.unify(up_lrg, build_lrgs.items)) {
                        lrg.unionFind().fail(build_lrgs.items, &failed);
                        continue;
                    }
                }

                break :lrg lrg;
            };

            lrg = lrg.unionFind();

            var seen = Map(*Node, usize).empty;
            seen.ensureTotalCapacity(tmp.arena.allocator(), instr.outputs().len) catch unreachable;
            for (instr.outputs()) |use| {
                if (use.hasNoUseFor(instr)) {
                    continue;
                }
                const idx = use.posOfInput(seen.get(use) orelse 1, instr);
                if (idx >= use.input_ordered_len) continue;
                seen.putAssumeCapacity(use, idx + 1);
                lrg.mask.setIntersection(use.regMask(func, idx, tmp.arena));

                if (lrg.mask.count() == 0) {
                    lrg.fail(build_lrgs.items, &failed);
                    break;
                }
            }
        }
    }

    for (lrg_table_build) |*lrg| {
        lrg.* = lrg.*.?.unionFind();
    }
    const lrg_table: []*LiveRange = @ptrCast(lrg_table_build);
    const lrgs: []LiveRange = build_lrgs.items;

    if (should_log) {
        std.debug.print("\n", .{});
        for (func.gcm.postorder) |bb| {
            std.debug.print("{}\n", .{bb});
            for (bb.base.outputs()) |instr| {
                if (instr.isDef()) {
                    std.debug.print("  [{}] {x} {}\n", .{
                        lrg_table[instr.schedule].index(lrgs),
                        lrg_table[instr.schedule].mask.masks[0],
                        instr,
                    });
                } else {
                    std.debug.print("       {}\n", .{instr});
                }
            }
        }
        std.debug.print("\n", .{});
    }

    errdefer {
        for (failed.items) |lrg_idx| {
            const lrg = &lrgs[lrg_idx];
            std.debug.assert(lrg.failed);

            if (should_log) std.debug.print("{}\n", .{lrg});

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

            if (should_log) for (members.entries.items(.key)) |o| {
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

            if (should_log) std.debug.print("min {} max {}\n", .{ min, max });

            for (@as([]*Node, members.entries.items(.key))) |member| {
                if (min == max and member.kind == .MachSplit) continue;

                if (lrg.hasDef(member, lrg_table) and
                    (min == max or func.loopDepth(member) <= min) and
                    // TODO: (is clone) and
                    !(member.outputs().len == 1 and member.outputs()[0].kind == .MachSplit and
                        LiveRange.isSameBlockNoClobber(member.outputs()[0], lrg_table)))
                {
                    LiveRange.splitAfterSubsume(func, member, true, lrg_table, .@"def/loop");
                }

                if (member.kind == .Phi) {
                    for (member.dataDeps(), member.cfg0().base.inputs(), member.dataDepOffset()..) |dep, c, j| {
                        if (dep.kind == .MachSplit) continue;

                        const cfg = c.?.inputs()[0].?;

                        if (min != max and func.loopDepth(cfg) > max) continue;

                        if (member.cfg0().base.kind == .Loop and j == 2 and
                            dep.kind == .Phi and dep.cfg0() == member.cfg0()) continue;

                        func.splitBefore(member, j, dep, true, .@"use/loop/phi");
                    }
                } else {
                    for (member.dataDeps(), member.dataDepOffset()..) |dep, j| {
                        if (!lrg.isSame(dep, lrg_table)) continue;

                        if (min != max and func.loopDepth(member) > max) continue;

                        func.splitBefore(member, j, dep, false, .@"use/loop/use");
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
    const interference = tmp.arena.alloc(Set, lrgs.len);
    for (interference) |*r| r.* = Set.initEmpty(
        tmp.arena.allocator(),
        lrgs.len,
    ) catch unreachable;

    var conflicts = Map(LiveRange.Conflict, void).empty;

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
                _ = instr_lrg.selfConflict(instr, value, &conflicts, tmp.arena);

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
                            if (should_log) {
                                std.debug.print("killed by concu {}\n", .{concu_lrg});
                                std.debug.print("                {}\n", .{instr_lrg});
                            }
                            instr_lrg.fail(lrgs, &failed);
                        }
                    }

                    if (instr_single_reg) {
                        concu_lrg.mask.unset(first_instr.?);
                        if (concu_lrg.mask.count() == 0) {
                            if (should_log) {
                                std.debug.print("killed by instr {}\n", .{instr_lrg});
                                std.debug.print("                {}\n", .{concu_lrg});
                            }
                            concu_lrg.fail(lrgs, &failed);
                        }
                    }

                    if (!concu_single_reg and !instr_single_reg and
                        setIntersects(concu_lrg.mask, instr_lrg.mask))
                    {
                        std.debug.assert(instr_lrg.index(lrgs) != concu_lrg.index(lrgs));
                        interference[instr_lrg.index(lrgs)].set(concu_lrg.index(lrgs));
                        interference[concu_lrg.index(lrgs)].set(instr_lrg.index(lrgs));
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
                    active_lrg.fail(lrgs, &failed);
                }
            };

            for (instr.dataDeps()) |def| {
                const other = if (tmp_liveins.fetchPut(
                    tmp.arena.allocator(),
                    lrg_table[def.schedule],
                    def,
                ) catch unreachable) |o| o.value else null;

                _ = lrg_table[def.schedule].selfConflict(def, other, &conflicts, tmp.arena);
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
                dirty = k.selfConflict(v, if (other) |o| o.value else null, &conflicts, tmp.arena) or dirty;
                dirty = other == null or dirty;
            }

            for (bb.base.outputs()) |out| {
                if (out.kind != .Phi or out.schedule == no_def_sentinel) continue;
                const k, const v = .{ lrg_table[out.schedule], out.dataDeps()[i] };
                const other = pred_block.fetchPut(tmp.arena.allocator(), k, v) catch unreachable;
                dirty = other == null or dirty;
            }

            if (dirty and !in_work_list.isSet(pred.schedule)) {
                in_work_list.set(pred.schedule);
                work_list.appendAssumeCapacity(pred.schedule);
            }
        }
    }

    errdefer {
        for (@as([]LiveRange.Conflict, conflicts.entries.items(.key))) |conflict| {
            if (should_log) {
                std.debug.print("clrg {}\n", .{conflict.lrg});
                std.debug.print("cdef {}\n", .{conflict.instr});
            }

            const instr = conflict.instr;

            if (false) {
                for (tmp.arena.dupe(*Node, instr.outputs())) |use| {
                    if (use.inPlaceSlot()) |idx| if (use.dataDeps()[idx] == instr) {
                        func.splitBefore(use, idx + 1, instr, true, .@"conflict/in-place-slot/use");
                    };

                    if (use.kind == .Phi and !(use.cfg0().base.kind == .Loop and
                        use.inputs()[2] == instr and instr.cfg0().idepth() > use.cfg0().idepth()))
                    {
                        std.debug.assert(use.inputs()[1] == instr);
                        func.splitBefore(use, 1, instr, true, .@"conflict/phi/use");
                    }
                }

                if (instr.kind == .Phi) {
                    LiveRange.splitAfterSubsume(func, instr, false, lrg_table, .@"conflict/phi/def");

                    func.splitBefore(instr, 1, instr.inputs()[1].?, true, .@"conflict/phi/def");
                }
            }

            if (instr.inPlaceSlot()) |slt| {
                func.splitBefore(instr, slt + 1, instr.dataDeps()[slt], true, .@"conflict/in-place-slot/def");
            }
        }
    }

    if (failed.items.len != 0 or conflicts.entries.len != 0) {
        return error.RegallocFailed;
    }

    const ifg = tmp.arena.alloc([]u16, lrgs.len);
    for (ifg, interference) |*r, in| {
        const count = in.count();
        r.* = tmp.arena.alloc(u16, count);
        var i: usize = 0;
        var iter = in.iterator(.{});
        while (iter.next()) |k| : (i += 1) {
            r.*[i] = @intCast(k);
        }
    }

    var color_stack = tmp.arena.alloc(u16, lrgs.len);
    var fill: usize = 0;
    for (lrgs, 0..) |lrg, i| {
        if (lrg.parent != null) continue;
        color_stack[fill] = @intCast(i);
        fill += 1;
    }
    color_stack = color_stack[0..fill];

    var done_cursor: usize = 0;
    var known_cursor: usize = 0;

    for (color_stack, 0..) |color, i| {
        const lrg = lrgs[color];
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

            if (ifg[adj].len + 1 == lrgs[adj].mask.count()) {
                const i = std.mem.indexOfScalarPos(u16, color_stack, known_cursor, adj).?;
                swap(&color_stack[known_cursor], &color_stack[i]);
                known_cursor += 1;
            }
        }
    }

    var iter = std.mem.reverseIterator(color_stack);
    while (iter.next()) |c| {
        const color: u16 = c;
        const lrg = &lrgs[color];

        for (ifg[color]) |adj| {
            const adj_lrg = &lrgs[adj];
            if (adj_lrg.reg != unresolved_reg) {
                lrg.mask.unset(adj_lrg.reg);
            }
            ifg[adj].len += 1;
            std.debug.assert(ifg[adj][ifg[adj].len - 1] == color);
        }

        if (Func.biased_regs != 0) {
            if (Func.biased_regs & @as(
                *align(@alignOf(usize)) const u64,
                @ptrCast(&graph.setMasks(lrg.mask)[0]),
            ).* != 0) {
                @as(
                    *align(@alignOf(usize)) u64,
                    @ptrCast(&graph.setMasks(lrg.mask)[0]),
                ).* &= Func.biased_regs;
            }
        }

        if (lrg.mask.findFirstSet()) |reg| {
            lrg.reg = @intCast(reg);
        } else {
            lrg.fail(lrgs, &failed);
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
