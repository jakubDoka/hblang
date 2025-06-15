const std = @import("std");
const utils = graph.utils;
const graph = @import("graph.zig");

const Set = std.DynamicBitSetUnmanaged;
const Arry = std.ArrayListUnmanaged;
pub fn setMasks(s: Set) []Set.MaskInt {
    return s.masks[0 .. (s.bit_length + @bitSizeOf(Set.MaskInt) - 1) / @bitSizeOf(Set.MaskInt)];
}

pub inline fn swap(a: anytype, b: @TypeOf(a)) void {
    std.mem.swap(@TypeOf(a.*), a, b);
}

pub fn ralloc(comptime Backend: type, func: *graph.Func(Backend)) []u16 {
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
                instr_masks[func.gcm.instr_count] = instr.allowedRegsFor(0, tmp.arena).?;
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

        @memcpy(setMasks(slider), setMasks(liveouts));

        var iter = std.mem.reverseIterator(bb.base.outputs());
        while (iter.next()) |n| {
            const node: *Func.Node = n;

            if (node.carried()) |c| {
                for (node.dataDeps(), 0..) |d, k| {
                    if (k != c) {
                        interference_table[node.schedule].set(d.?.schedule);
                        interference_table[d.?.schedule].set(node.schedule);
                    }
                }
            }

            if (node.isDef() or node.kills()) {
                slider.unset(node.schedule);
                const node_masks = setMasks(instr_masks[node.schedule]);

                var siter = slider.iterator(.{});
                while (siter.next()) |elem| {
                    std.debug.assert(elem != node.schedule);

                    // backends should ensure incompatible registers dont overlap
                    // this way the type of the register is also encoded
                    //
                    for (setMasks(instr_masks[elem]), node_masks) |a, b| {
                        if (a & b != 0) break;
                    } else continue;

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
                @as(*align(@alignOf(usize)) u64, @ptrCast(&setMasks(selection_set.*)[0])).* &=
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
            const row, const out, const selection_set = .{ interference_table[j], &outs[j], &instr_masks[j] };
            selection_set.toggleAll();
            std.debug.assert(selection_set.isSet(sentinel));

            var row_iter = row.iterator(.{});
            while (row_iter.next()) |i| {
                selection_set.set(outs[i]);
                @as(*align(@alignOf(usize)) u64, @ptrCast(&setMasks(selection_set.*)[0])).* |=
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
