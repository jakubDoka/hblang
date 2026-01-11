const std = @import("std");
const utils = graph.utils;
const graph = @import("graph.zig");

const Map = std.AutoArrayHashMapUnmanaged;
const Arry = std.ArrayList;
const Error = error{RegallocFailed};
const Regalloc = @This();

// NOTE: so that it does not show up in the grep
const print = (std.debug).print;

max_lrgs: usize = 0,
max_liveouts: usize = 0,
max_blocks: usize = 0,
max_instructions: usize = 0,
inserted_splits: usize = 0,

pub inline fn swap(a: anytype, b: @TypeOf(a)) void {
    std.mem.swap(@TypeOf(a.*), a, b);
}

pub fn rallocIgnoreStats(comptime Backend: type, func: *graph.Func(Backend)) []u16 {
    var slf = Regalloc{};
    return slf.ralloc(Backend, func);
}

pub fn ralloc(slf: *Regalloc, comptime Backend: type, func: *graph.Func(Backend)) []u16 {
    func.gcm.cfg_built.assertLocked();

    //func.keep = true;
    //defer func.keep = false;

    for (0..7) |_| {
        return slf.rallocRound(Backend, func) catch continue;
    } else unreachable;
}

pub fn rallocRound(slf: *Regalloc, comptime Backend: type, func: *graph.Func(Backend)) Error![]u16 {
    const Func = graph.Func(Backend);
    const Node = Func.Node;
    const CfgNode = Func.CfgNode;
    const Set = Backend.Set;
    const setIntersects = Backend.setIntersects;
    const setMasks = Backend.setMasks;

    const unresolved_reg = std.math.maxInt(u16);
    const no_def_sentinel = std.math.maxInt(u16);

    const LiveRange = struct {
        parent: ?*LiveRange = null,
        //killed_by: ?*Node = null,
        mask: Set,
        def: *Node,
        failed: bool = false,
        self_conflict: bool = false,
        reg: u16 = unresolved_reg,

        const LiveRange = @This();

        pub fn format(self: *const LiveRange, writer: *std.Io.Writer) !void {
            try writer.writeAll("def: ");
            try self.def.format(writer);
            try writer.writeAll(", ");
            try writer.writeAll("mask: ");
            var mask = self.mask;
            for (setMasks(&mask)) |m| {
                try writer.print("{x:016} ", .{m});
            }
            // if (self.killed_by) |k| {
            //     try writer.writeAll("\n\tkilled by: ");
            //     try k.format(a, b, writer);
            // }
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
            if (s.index(live_ranges) < o.index(live_ranges)) {
                std.mem.swap(*LiveRange, &s, &o);
            }

            o.parent = s;

            s.mask.setIntersection(o.mask);

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
            if (other) |o| {
                if (o != instr) {
                    try conflicts.put(arena.allocator(), .{ .lrg = self, .instr = instr }, {});
                    try conflicts.put(arena.allocator(), .{ .lrg = self, .instr = o }, {});
                    self.self_conflict = true;
                    return true;
                }
            }
            return false;
        }

        pub fn isSame(self: *LiveRange, other: *Node, lrg_table: []const *LiveRange) bool {
            var cursor = other;
            while (cursor.schedule == no_def_sentinel and cursor.kind == .MachSplit) {
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
                if (outs[outs.len - 1].get().kind == .Return) break :slid_to_loop;
                const loop = outs[outs.len - 1].get().outputs()[0].get();
                if (loop.kind != .Loop or loop.inputs()[0] != outs[outs.len - 1].get()) {
                    break :slid_to_loop;
                }

                var iter = std.mem.reverseIterator(outs[0 .. outs.len - 1]);
                while (iter.next()) |in| {
                    const instr = in.get();
                    if (instr == member) {
                        depth = fnc.loopDepth(loop);
                        break;
                    }

                    if (instr.kind != .MachSplit and !instr.isClone() and !instr.isReadonly()) break;
                }
            }

            return .{ @min(min, depth), @max(max, depth) };
        }

        pub fn splitAfterSubsume(
            self: *Func,
            def: *Node,
            must: bool,
            lrg_table: []const *LiveRange,
            dbg: graph.builtin.MachSplit.Dbg,
            counter: *usize,
        ) void {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const block = def.cfg0();
            const ins = self.addSplit(block, def, dbg, counter);
            self.ensureOutputCapacity(ins, def.outputs().len);

            {
                const lock = def.lock();
                defer lock.unlock();

                for (tmp.arena.dupe(Node.Out, def.outputs())) |us| {
                    const use = us.get();
                    if (use == def) continue;
                    if (!use.hasUseFor(us.pos(), def)) continue;
                    if (!must and use.kind == .MachSplit and
                        isSameBlockNoClobber(use, lrg_table)) continue;

                    std.debug.assert(use.dataDepOffset() <= us.pos());

                    self.setInput(use, us.pos(), .nointern, ins);
                }
            }

            self.setInput(ins, 1, .nointern, def);
            var oidx = block.base.posOfOutput(0, def);
            if (def.kind == .Phi) {
                for (block.base.outputs()[oidx + 1 ..]) |o| {
                    if (o.get().kind == .Phi) {
                        oidx += 1;
                    } else {
                        break;
                    }
                }
            }
            const to_rotate = block.base.outputs()[oidx + 1 ..];
            std.mem.rotate(Node.Out, to_rotate, to_rotate.len - 1);
        }

        pub fn isSameBlockNoClobber(split: *Node, lrg_table: []const *LiveRange) bool {
            std.debug.assert(split.kind == .MachSplit);
            const def = split.dataDeps()[0];
            const cfg = split.cfg0();
            if (def.cfg0() != cfg) return false;
            var reg = lrg_table[def.schedule].reg;
            if (reg == unresolved_reg) reg = @intCast(lrg_table[def.schedule].mask.findFirstSet() orelse
                return false);
            var iter = std.mem.reverseIterator(cfg.base.outputs()[0..cfg.base.posOfOutput(0, split)]);
            while (iter.next()) |in| {
                const instr = in.get();
                if (instr == split) return true;
                if (instr.schedule == no_def_sentinel) continue;
                if (lrg_table[def.schedule] == lrg_table[instr.schedule]) return false;
                if (lrg_table[instr.schedule].reg == reg) return false;
            } else unreachable;
        }

        pub fn easierToColorThen(self: LiveRange, other: LiveRange) bool {
            return self.mask.count() > other.mask.count();
        }
    };

    const LiveMap = Map(u16, *Node);

    slf.max_blocks = @max(slf.max_blocks, func.gcm.postorder.len);

    const scnt = &slf.inserted_splits;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    func.gcm.instr_count = 0;
    const should_log = 1 == 0;
    for (func.gcm.postorder) |bb| {
        for (bb.base.outputs()) |instr| {
            if (instr.get().isDef()) {
                instr.get().schedule = func.gcm.instr_count;
                func.gcm.instr_count += 1;
            } else {
                instr.get().schedule = no_def_sentinel;
            }
        }
    }

    slf.max_instructions = @max(slf.max_instructions, func.gcm.instr_count);

    if (func.gcm.instr_count == 0) return &.{};

    var build_lrgs = tmp.arena.makeArrayList(LiveRange, func.gcm.instr_count);
    const lrg_table_build = tmp.arena.alloc(?*LiveRange, func.gcm.instr_count);
    @memset(lrg_table_build, null);
    var failed = tmp.arena.makeArrayList(u16, func.gcm.instr_count);

    // # Build live ranges
    //
    for (func.gcm.postorder) |bb| {
        for (bb.base.outputs()) |in| {
            const instr = in.get();
            if (instr.schedule == no_def_sentinel) continue;

            var lrg = if (instr.kind == .Phi) lrg: {
                std.debug.assert(instr.isDataPhi());
                var lrg = lrg_table_build[instr.schedule] orelse
                    for (instr.dataDeps()) |d| {
                        if (lrg_table_build[d.schedule]) |*l| {
                            l.* = l.*.unionFind();
                            l.*.mask.setIntersection(instr.regMask(func, 0, tmp.arena));
                            if (l.*.mask.count() == 0) {
                                l.*.fail(build_lrgs.items, &failed);
                            }
                            break l.*;
                        }
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
                var blrg: ?*LiveRange = null;

                blrg = blrg orelse lrg_table_build[instr.schedule];
                if (instr.inPlaceSlot()) |idx| {
                    const next_lrg = lrg_table_build[instr.dataDeps()[idx].schedule].?.unionFind();
                    if (blrg) |l| _ = l.unify(next_lrg, build_lrgs.items);
                    blrg = blrg orelse next_lrg;
                }

                const is_new = blrg == null;
                var lrg = blrg orelse LiveRange.init(&build_lrgs, instr.regMask(func, 0, tmp.arena), instr);

                if (!is_new) {
                    lrg.mask.setIntersection(instr.regMask(func, 0, tmp.arena));
                    if (lrg.mask.count() == 0) {
                        lrg.unionFind().fail(build_lrgs.items, &failed);
                    }
                }

                lrg = lrg.unionFind();
                lrg_table_build[instr.schedule] = lrg;

                break :lrg lrg;
            };

            lrg = lrg.unionFind();

            for (instr.outputs()) |us| {
                const use = us.get();
                if (instr.kind == .Call and use.kind == .StackArgOffset) {
                    continue;
                }
                const idx = us.pos();
                if (idx >= use.input_ordered_len) continue;

                lrg.mask.setIntersection(use.regMask(func, idx, tmp.arena));

                if (lrg.mask.count() == 0) {
                    lrg.fail(build_lrgs.items, &failed);
                    break;
                }
            }
        }
    }

    slf.max_lrgs = @max(slf.max_lrgs, build_lrgs.items.len);

    for (lrg_table_build) |*lrg| {
        lrg.* = lrg.*.?.unionFind();
        std.debug.assert(lrg_table_build[lrg.*.?.def.schedule] == lrg.*);
    }
    const lrg_table: []*LiveRange = @ptrCast(lrg_table_build);
    const lrgs: []LiveRange = build_lrgs.items;

    if (should_log) {
        print("\n", .{});
        for (func.gcm.postorder) |bb| {
            print("{f}\n", .{bb});
            for (bb.base.outputs()) |in| {
                const instr = in.get();
                if (instr.isDef()) {
                    print("  [{}] {x:08} {f}\n", .{
                        lrg_table[instr.schedule].index(lrgs),
                        setMasks(&lrg_table[instr.schedule].mask)[0],
                        instr,
                    });
                } else {
                    print("       {f}\n", .{instr});
                }
            }
        }
        print("\n", .{});
    }

    errdefer {
        for (failed.items) |lrg_idx| {
            const lrg = &lrgs[lrg_idx];
            if (lrg.self_conflict) continue;
            if (lrg.parent != null) continue;
            std.debug.assert(lrg.failed);

            if (should_log) print("{f}\n", .{lrg});

            const alc = tmp.arena.allocator();
            var members: Map(*Node, void) = .empty;
            members.put(alc, lrg.def, {}) catch unreachable;

            var i: usize = 0;
            while (i < members.entries.len) : (i += 1) {
                const def: *Node = members.entries.items(.key)[i];
                if (def.schedule == no_def_sentinel) continue;
                if (lrg_table[def.schedule] != lrg) continue;
                for (def.outputs()) |o| {
                    if (!o.get().hasUseFor(o.pos(), def)) continue;
                    members.put(alc, o.get(), {}) catch unreachable;
                }
                for (def.dataDeps()) |d| {
                    if (lrg.hasDef(d, lrg_table)) {
                        members.put(alc, d, {}) catch unreachable;
                    }
                }
            }

            if (should_log) for (members.entries.items(.key)) |o| {
                const depth = func.loopDepth(o);
                print("|- [{}] {f}\n", .{ depth, o });
            };

            var call_cnt: usize = 0;
            var min: u32, var max: u32 = .{ 1000, 0 };
            for (@as([]*Node, members.entries.items(.key))) |member| {
                if (member.kind == .Call) call_cnt += 1;
                if (lrg.hasDef(member, lrg_table)) {
                    min, max = LiveRange
                        .collectLoopDepth(func, member, member.cfg0(), min, max);
                }

                if (member.kind == .Phi) {
                    for (member.dataDeps(), member.cfg0().base.ordInps()) |dep, cfg| {
                        min, max = LiveRange
                            .collectLoopDepth(func, dep, cfg.?.cfg0(), min, max);
                    }
                } else {
                    for (member.dataDeps()) |dep| {
                        if (lrg.isSame(dep, lrg_table)) {
                            min, max = LiveRange
                                .collectLoopDepth(func, member, member.cfg0(), min, max);
                        }
                    }
                }
            }

            if (should_log) print("min {} max {}\n", .{ min, max });
            if (min == 1000) {
                if (should_log) for (members.entries.items(.key)) |member| {
                    if (member.schedule == no_def_sentinel) {
                        print("<- {f}\n", .{member});
                    } else {
                        print("* {} {f} {f} {any}\n", .{
                            lrg.hasDef(member, lrg_table),
                            member,
                            lrg_table[member.schedule],
                            member.outputs(),
                        });
                    }
                };
                unreachable;
            }

            for (@as([]*Node, members.entries.items(.key))) |member| {
                if (min == max and member.kind == .MachSplit) continue;

                if (lrg.hasDef(member, lrg_table) and
                    (min == max or func.loopDepth(member) <= min) and
                    !member.isClone() and !member.isReadonly() and
                    !(member.outputs().len == 1 and member.outputs()[0].get().kind == .MachSplit and
                        LiveRange.isSameBlockNoClobber(member.outputs()[0].get(), lrg_table)))
                {
                    LiveRange.splitAfterSubsume(func, member, true, lrg_table, .@"def/loop", scnt);
                }

                if (member.kind == .Phi) {
                    for (member.dataDeps(), member.cfg0().base.ordInps(), member.dataDepOffset()..) |dep, c, j| {
                        if (dep.kind == .MachSplit) continue;

                        const cfg = c.?.inputs()[0].?;

                        if (min != max and func.loopDepth(cfg) > min and !dep.isReadonly()) continue;

                        if (member.cfg0().base.kind == .Loop and j == 2 and
                            dep.kind == .Phi and dep.cfg0() == member.cfg0()) continue;

                        func.splitBefore(member, j, dep, true, .@"use/loop/phi", scnt);
                    }
                } else {
                    for (member.dataDeps(), member.dataDepOffset()..) |dep, j| {
                        if (!lrg.isSame(dep, lrg_table)) continue;

                        if (min != max and func.loopDepth(member) > min and
                            !dep.isClone() and !dep.isReadonly() and
                            // NOTE: more then one call, so we absolutely need to split on it
                            // or we get into a split loop
                            (call_cnt < 2 or member.kind != .Call)) continue;

                        func.splitBefore(member, j, dep, false, .@"use/loop/use", scnt);
                    }
                }
            }
        }
    }

    if (failed.items.len != 0) {
        return error.RegallocFailed;
    }

    const BitSet = std.DynamicBitSetUnmanaged;
    const block_liveouts = tmp.arena.alloc(LiveMap, func.gcm.postorder.len);
    @memset(block_liveouts, LiveMap.empty);
    var interference = BitSet.initEmpty(tmp.arena.allocator(), lrgs.len * lrgs.len) catch unreachable;

    var conflicts = Map(LiveRange.Conflict, void).empty;

    var work_list = tmp.arena.makeArrayList(u16, func.gcm.postorder.len);
    var in_work_list = BitSet.initFull(
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
            const instr: *Node = in.get();
            if (instr.schedule != no_def_sentinel) {
                const instr_lrg = lrg_table[instr.schedule];
                const value = if (tmp_liveins.fetchSwapRemove(instr_lrg.index(lrgs))) |v| v.value else null;
                _ = instr_lrg.selfConflict(instr, value, &conflicts, tmp.arena);
            }

            if (instr.kind == .Phi) continue;

            const kills = instr.clobbers();
            if (kills != 0) for (tmp_liveins.entries.items(.key)) |al| {
                const active_lrg: *LiveRange = &lrgs[al];
                // we don't skip if killed_by is not null since we are going in reverse
                std.debug.assert(active_lrg.mask.bit_length >= @bitSizeOf(@TypeOf(kills)));

                @as(
                    *align(@alignOf(usize)) @TypeOf(kills),
                    @ptrCast(&setMasks(&active_lrg.mask)[0]),
                ).* &= ~kills;

                if (active_lrg.mask.count() == 0 and !active_lrg.failed) {
                    //active_lrg.killed_by = instr;
                    active_lrg.fail(lrgs, &failed);
                }
            };

            if (instr.schedule != no_def_sentinel) {
                const instr_lrg = lrg_table[instr.schedule];
                for (tmp_liveins.entries.items(.key)) |id| {
                    const concu_lrg = &lrgs[id];
                    std.debug.assert(concu_lrg != instr_lrg);

                    if (!setIntersects(concu_lrg.mask, instr_lrg.mask)) continue;

                    if (instr_lrg.mask.count() != 1) {
                        std.debug.assert(instr_lrg.index(lrgs) != concu_lrg.index(lrgs));
                        interference.set(concu_lrg.index(lrgs) + instr_lrg.index(lrgs) * lrgs.len);
                        interference.set(instr_lrg.index(lrgs) + concu_lrg.index(lrgs) * lrgs.len);
                        continue;
                    }

                    concu_lrg.mask.unset(instr_lrg.mask.findFirstSet().?);
                    if (concu_lrg.mask.count() == 0) {
                        concu_lrg.fail(lrgs, &failed);
                    }
                }
            }

            for (instr.dataDeps(), instr.dataDepOffset()..) |def, i| {
                //std.debug.assert(def.isDef());

                if (!instr.hasUseFor(i, def)) continue;

                const out = instr.regMask(func, i, tmp.arena);
                if (out.count() == 1) {
                    for (
                        tmp_liveins.entries.items(.key),
                        @as([]*Node, tmp_liveins.entries.items(.value)),
                    ) |concu, nd| {
                        const concu_lrg = &lrgs[concu];

                        if (nd == def) continue;
                        if (!setIntersects(out, nd.regMask(func, 0, tmp.arena))) continue;

                        concu_lrg.mask.unset(out.findFirstSet().?);
                        if (concu_lrg.mask.count() == 0) {
                            concu_lrg.fail(lrgs, &failed);
                        }
                    }
                }

                const other = if (tmp_liveins.fetchPut(
                    tmp.arena.allocator(),
                    lrg_table[def.schedule].index(lrgs),
                    def,
                ) catch unreachable) |o| o.value else null;

                _ = lrg_table[def.schedule].selfConflict(def, other, &conflicts, tmp.arena);
            }
        }

        if (bb.base.kind == .Entry) continue;

        for (bb.base.ordInps(), 0..) |prd, i| {
            const pred: *Node = prd.?.inputs()[0].?;
            if (should_log and pred.schedule == no_def_sentinel) {
                func.fmtScheduledLog();
            }
            const pred_block = &block_liveouts[pred.schedule];

            var dirty: bool = false;

            for (
                tmp_liveins.entries.items(.key),
                tmp_liveins.entries.items(.value),
            ) |k, v| {
                const other = pred_block.fetchPut(tmp.arena.allocator(), k, v) catch unreachable;
                _ = lrgs[k].selfConflict(v, if (other) |o| o.value else null, &conflicts, tmp.arena);
                dirty = other == null or dirty;
            }

            for (bb.base.outputs(), 0..) |ot, j| {
                const out = ot.get();
                if (out.schedule == no_def_sentinel) continue;
                if (out.kind != .Phi) {
                    std.debug.assert(for (bb.base.outputs()[j + 1 ..]) |o| {
                        if (o.get().kind == .Phi) break false;
                    } else true);
                    break;
                }
                const k, const v = .{ lrg_table[out.schedule].index(lrgs), out.dataDeps()[i] };
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
                print("clrg {f}\n", .{conflict.lrg});
                print("cdef {f}\n", .{conflict.instr});
            }

            const instr = conflict.instr;

            for (tmp.arena.dupe(Node.Out, instr.outputs())) |us| {
                const use = us.get();
                if (use.inPlaceSlot()) |idx| if (use.dataDeps()[idx] == instr) {
                    func.splitBefore(
                        use,
                        idx + use.dataDepOffset(),
                        instr,
                        true,
                        .@"conflict/in-place-slot/use",
                        scnt,
                    );
                };

                if (use.kind == .Phi and !(use.cfg0().base.kind == .Loop and
                    use.inputs()[2] == instr and instr.cfg0().idepth() > use.cfg0().idepth()))
                {
                    func.splitBefore(use, us.pos(), instr, true, .@"conflict/phi/use", scnt);
                }
            }

            if (instr.kind == .Phi) {
                LiveRange.splitAfterSubsume(
                    func,
                    instr,
                    false,
                    lrg_table,
                    .@"conflict/phi/def",
                    scnt,
                );
                func.splitBefore(
                    instr,
                    1,
                    instr.inputs()[1].?,
                    true,
                    .@"conflict/phi/def",
                    scnt,
                );
                for (instr.inputs()[2].?.outputs()) |o| {
                    // another phi has same liverange, split or we get stuck
                    if (o.get() != instr and o.get().kind == .Phi) {
                        func.splitBefore(
                            instr,
                            2,
                            instr.inputs()[2].?,
                            true,
                            .@"conflict/phi/def",
                            scnt,
                        );
                        break;
                    }
                }
            }

            if (instr.inPlaceSlot()) |slt| {
                func.splitBefore(
                    instr,
                    slt + instr.dataDepOffset(),
                    instr.dataDeps()[slt],
                    true,
                    .@"conflict/in-place-slot/def",
                    scnt,
                );
            }
        }
    }

    if (failed.items.len != 0 or conflicts.entries.len != 0) {
        return error.RegallocFailed;
    }

    const ifg = tmp.arena.alloc([]u16, lrgs.len);
    {
        const buff = tmp.arena.alloc(u16, interference.count());
        var idx: usize = 0;
        var cursor: usize = 0;
        var last_idx: usize = 0;
        var i: usize = 0;
        var iter = interference.iterator(.{});
        while (iter.next()) |k| : (idx += 1) {
            while (k >= cursor + lrgs.len) {
                cursor += lrgs.len;
                ifg[i] = buff[last_idx..idx];
                last_idx = idx;
                i += 1;
            }

            buff[idx] = @intCast(k - cursor);
        }

        std.debug.assert(idx == buff.len);
        while (cursor < lrgs.len * lrgs.len) {
            cursor += lrgs.len;
            ifg[i] = buff[last_idx..idx];
            last_idx = idx;
            i += 1;
        }

        std.debug.assert(cursor == lrgs.len * lrgs.len);
        std.debug.assert(i == lrgs.len);

        for (buff) |v| {
            std.debug.assert(v < lrgs.len);
        }
    }

    // coalsce
    //
    var coalesced = false;
    for (func.gcm.postorder, 0..) |bb, j| {
        slf.max_liveouts = @max(slf.max_liveouts, block_liveouts[j].entries.len);

        var removed: usize = 0;
        coalesce: for (tmp.arena.dupe(Node.Out, bb.base.outputs()), 0..) |in, i| {
            const instr = in.get();
            if (instr.kind != .MachSplit) continue;
            if (instr.dataDeps().len != 1) continue;

            const splitLrg = lrg_table[instr.schedule].unionFind();
            const defLrg = lrg_table[instr.dataDeps()[0].schedule].unionFind();
            if (splitLrg != defLrg) {
                const lhs, const rhs = if (ifg[splitLrg.index(lrgs)].len >
                    ifg[defLrg.index(lrgs)].len)
                    .{ defLrg, splitLrg }
                else
                    .{ splitLrg, defLrg };

                if (!setIntersects(lhs.mask, rhs.mask)) continue :coalesce;

                // we suffle the edges around to then be joined in bulk
                var to_move: usize = 0;
                for (ifg[lhs.index(lrgs)]) |*other| {
                    if (other.* == rhs.index(lrgs)) {
                        continue :coalesce;
                    }

                    if (std.mem.indexOfScalar(u16, ifg[rhs.index(lrgs)], other.*) ==
                        null)
                    {
                        swap(other, &ifg[lhs.index(lrgs)][to_move]);
                        to_move += 1;
                    }
                }

                var set: Set = lhs.mask.clone(tmp.arena.allocator()) catch unreachable;
                set.setIntersection(rhs.mask);

                if (ifg[rhs.index(lrgs)].len + to_move >= set.count()) {
                    continue :coalesce;
                }

                const final_adj = std.mem.concat(tmp.arena.allocator(), u16, &.{
                    ifg[rhs.index(lrgs)],
                    ifg[lhs.index(lrgs)][0..to_move],
                }) catch unreachable;

                std.debug.assert(!rhs.unify(lhs, lrgs));
                const winner = rhs.unionFind();
                const looser = if (rhs == winner) lhs else rhs;
                ifg[winner.index(lrgs)] = final_adj;

                if (winner.def == instr) {
                    winner.def = looser.def;
                } else {
                    looser.def = winner.def;
                }

                for (ifg[looser.index(lrgs)]) |adj| {
                    const other_adj = ifg[adj];
                    const idx = std.mem.indexOfScalar(
                        u16,
                        other_adj,
                        looser.index(lrgs),
                    ).?;
                    if (std.mem.indexOfScalar(
                        u16,
                        other_adj,
                        winner.index(lrgs),
                    ) != null) {
                        swap(&other_adj[idx], &other_adj[other_adj.len - 1]);
                        ifg[adj].len -= 1;
                    } else {
                        other_adj[idx] = winner.index(lrgs);
                    }
                }
            }

            coalesced = true;

            if (false and should_log) {
                print("coalesce: {f} + {f}\n", .{ instr, instr.dataDeps()[0] });
                print("lrg:      {f}\n", .{splitLrg});
                print("drg:      {f}\n", .{defLrg});
            }

            // TODO: could we actuially retain here?
            // maybe not
            std.mem.rotate(Node.Out, bb.base.outputs()[i - removed ..], 1);
            bb.base.output_len -= 1;
            instr.inputs()[0] = null;
            removed += 1;

            func.subsume(instr.dataDeps()[0], instr, .nointern);
        }
    }

    if (coalesced) for (lrg_table) |*lrg| {
        lrg.* = lrg.*.unionFind();
    };

    // coloring
    //
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
        var best = color_stack[done_cursor];
        if (false) {
            var bidx: usize = done_cursor;

            for (done_cursor + 1..known_cursor) |idx| {
                if (lrgs[color_stack[idx]].easierToColorThen(lrgs[best])) {
                    best = color_stack[idx];
                    bidx = idx;
                }
            }

            if (bidx != done_cursor) {
                swap(&color_stack[done_cursor], &color_stack[bidx]);
            }
        }

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
                @ptrCast(&setMasks(&lrg.mask)[0]),
            ).* != 0) {
                @as(
                    *align(@alignOf(usize)) u64,
                    @ptrCast(&setMasks(&lrg.mask)[0]),
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
    var alloc = std.ArrayList(u16).initCapacity(
        func.arena.allocator(),
        func.gcm.instr_count,
    ) catch unreachable;

    for (func.gcm.postorder) |bb| {
        for (bb.base.outputs()) |in| {
            const instr = in.get();
            if (instr.schedule == no_def_sentinel) continue;
            const instr_lrg = lrg_table[instr.schedule];
            instr.schedule = @intCast(alloc.items.len);
            alloc.appendAssumeCapacity(instr_lrg.reg);
        }
    }

    if (std.debug.runtime_safety) {
        const util = struct {
            pub fn logCollision(fnc: *Func, block: *CfgNode, def: *Node, clobber: *Node, use: *Node, allc: []u16) void {
                if (utils.freestanding) return;
                for (fnc.gcm.postorder) |bb| {
                    print("{f}\n", .{bb});
                    for (bb.base.outputs()) |in| {
                        const instr = in.get();
                        if (instr.schedule != no_def_sentinel) {
                            print("  {} {f}\n", .{ allc[instr.schedule], instr });
                        } else {
                            print("    {f}\n", .{instr});
                        }
                    }
                }
                utils.panic(
                    \\
                    \\block:   {any}
                    \\hef:     {} {any}
                    \\clobber: {} {any}
                    \\use:        {any}
                , .{
                    block,
                    allc[def.schedule],
                    def,
                    allc[clobber.schedule],
                    clobber,
                    use,
                });
            }
        };

        const loop_switches = tmp.arena.alloc(bool, func.gcm.loop_tree.len);
        for (func.gcm.postorder) |bb| {
            for (bb.base.outputs()) |in| {
                const instr = in.get();
                if (instr.schedule == no_def_sentinel) continue;
                const alc = alloc.items[instr.schedule];
                const root_block = instr.cfg0();
                std.debug.assert(root_block.base.kind != .Start);
                const root_idx = root_block.base.posOfOutput(0, instr);

                for (instr.outputs()) |us| {
                    @memset(loop_switches, false);

                    const use = us.get();
                    if (!use.hasUseFor(us.pos(), instr)) continue;
                    var block = use.cfg0();
                    var idx: usize = undefined;
                    if (use.kind == .Phi) {
                        block = block.base.inputs()[us.pos() - 1].?.cfg0();
                        std.debug.assert(block.base.isBasicBlockStart());
                        idx = block.base.outputs().len;
                    } else {
                        idx = block.base.posOfOutput(0, use);
                    }

                    if (block == root_block) {
                        for (block.base.outputs()[root_idx + 1 .. idx]) |o| {
                            const other = o.get();
                            if (other.schedule == no_def_sentinel) continue;
                            if (alc == alloc.items[other.schedule]) {
                                util.logCollision(func, block, instr, other, use, alloc.items);
                            }
                        }
                        continue;
                    } else {
                        for (block.base.outputs()[0..idx]) |o| {
                            const other = o.get();
                            if (other.schedule == no_def_sentinel) continue;
                            if (alc == alloc.items[other.schedule]) {
                                util.logCollision(func, block, instr, other, use, alloc.items);
                            }
                        }
                        block = block.idom().idom();
                    }

                    while (block != root_block) {
                        std.debug.assert(block.base.kind != .Start);
                        if (!block.base.isBasicBlockStart()) {
                            utils.panic("{f}", .{block});
                        }
                        for (block.base.outputs()) |o| {
                            const other = o.get();
                            if (other == use) continue;
                            if (other.schedule == no_def_sentinel) continue;
                            if (alc == alloc.items[other.schedule]) {
                                util.logCollision(func, block, instr, other, use, alloc.items);
                            }
                        }

                        if (block.base.kind == .Loop and
                            func.loopDepth(&block.base) > func.loopDepth(&root_block.base))
                        {
                            // take the backedge first
                            if (!loop_switches[block.ext.loop]) {
                                loop_switches[block.ext.loop] = true;
                                block = block.base.inputs()[1].?.cfg0();
                                continue;
                            }
                        }
                        block = block.idom().idom();
                    }
                }
            }
        }
    }

    return alloc.items;
}
