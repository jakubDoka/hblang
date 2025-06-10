const std = @import("std");
const utils = graph.utils;
const graph = @import("graph.zig");

const Set = std.DynamicBitSetUnmanaged;
const Arry = std.ArrayListUnmanaged;
pub fn setMasks(s: Set) []Set.MaskInt {
    return s.masks[0 .. (s.bit_length + @bitSizeOf(Set.MaskInt) - 1) / @bitSizeOf(Set.MaskInt)];
}

pub fn ralloc(comptime Mach: type, func: *graph.Func(Mach)) []u16 {
    func.gcm.cfg_built.assertLocked();

    errdefer unreachable;

    const Func = graph.Func(Mach);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    // small overcommit is fine
    const instr_table = tmp.arena.alloc(*Func.Node, func.instr_count);

    // compress the instruction count, the non defs dont need to be represented
    // in the interference_table
    //
    func.instr_count = 0;
    for (func.gcm.postorder) |bb| {
        for (bb.base.outputs()) |instr| {
            if (instr.isDef() or instr.kills()) {
                instr.schedule = func.instr_count;
                instr_table[func.instr_count] = instr;
                func.instr_count += 1;
            } else {
                instr.schedule = std.math.maxInt(u16);
            }
        }
    }

    const block_liveouts = tmp.arena.alloc(Set, func.gcm.postorder.len);
    for (block_liveouts) |*b| b.* = try Set.initEmpty(tmp.arena.allocator(), func.instr_count);

    var in_interference_work = try Set.initFull(tmp.arena.allocator(), func.gcm.postorder.len);
    var interference_work = tmp.arena.makeArrayList(u16, func.gcm.postorder.len);
    for (0..interference_work.capacity) |i| interference_work.appendAssumeCapacity(@intCast(i));

    const interference_table = tmp.arena.alloc(Set, func.instr_count);
    for (interference_table) |*r| r.* = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable;

    var slider = try Set.initEmpty(tmp.arena.allocator(), func.instr_count);

    while (interference_work.pop()) |w| {
        in_interference_work.unset(w);
        const bb = func.gcm.postorder[w];
        const liveouts = block_liveouts[w];

        @memcpy(setMasks(slider), setMasks(liveouts));

        var iter = std.mem.reverseIterator(bb.base.outputs());
        while (iter.next()) |n| {
            const node: *Func.Node = n;

            if (node.isDef() or node.kills()) {
                slider.unset(node.schedule);

                var siter = slider.iterator(.{});
                while (siter.next()) |elem| {
                    std.debug.assert(elem != node.schedule);
                    interference_table[elem].set(node.schedule);
                    interference_table[node.schedule].set(elem);
                }

                // phi is unified with mach moves
                if (node.kind == .Phi) continue;
            }

            for (node.dataDeps()) |dd| {
                slider.set(dd.?.schedule);
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
            for (setMasks(slider), setMasks(pred_block)) |in, *out| {
                dirty |= out.* ^ in;
                out.* |= in;
            }
            if (dirty != 0 and !in_interference_work.isSet(pred.schedule)) {
                in_interference_work.set(pred.schedule);
                interference_work.appendAssumeCapacity(pred.schedule);
            }
        }
    }

    const sentinel = 0;
    // alocate to the arena and then copy later for sequential access
    const outs = tmp.arena.alloc(u16, func.instr_count);
    @memset(outs, sentinel);
    var selection_set = try Set.initEmpty(tmp.arena.allocator(), @max(func.instr_count + 1, 256));
    for (interference_table, outs, 0..) |row, *slot, j| {
        selection_set.unsetAll();
        selection_set.set(sentinel);

        @as(*align(@alignOf(usize)) u64, @ptrCast(&setMasks(selection_set)[0])).* |=
            if (@hasDecl(Mach, "reserved_regs")) Mach.reserved_regs << 1 else 0;

        var row_iter = row.iterator(.{});
        while (row_iter.next()) |i| {
            selection_set.set(outs[i]);
            @as(*align(@alignOf(usize)) u64, @ptrCast(&setMasks(selection_set)[0])).* |=
                instr_table[i].clobbers() << 1;
        }

        if (instr_table[j].carried()) |c| {
            for (instr_table[j].dataDeps(), 0..) |d, k| {
                if (k != c) {
                    selection_set.set(outs[d.?.schedule]);
                }
            }
        }

        const bias = instr_table[j].regBias();
        if (bias != null and !selection_set.isSet(bias.?)) {
            slot.* = bias.?;
        } else {
            var it = selection_set.iterator(.{ .kind = .unset });
            slot.* = @intCast(it.next().?);
        }
    }

    // TODO: dont do this and instead modify the backends
    for (outs) |*o| o.* -= sentinel + 1;

    return try func.arena.allocator().dupe(u16, outs);
}
