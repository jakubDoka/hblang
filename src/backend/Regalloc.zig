const std = @import("std");
const utils = graph.utils;
const graph = @import("graph.zig");

pub fn ralloc(comptime Mach: type, func: *graph.Func(Mach)) []u16 {
    const Fn = graph.Func(Mach);

    const Set = std.DynamicBitSetUnmanaged;
    const Block = struct {
        start: *Fn.Node = undefined,
        end: *Fn.Node = undefined,
        liveins: Set,
        liveouts: Set,
        defs: Set,
        uses: Set,

        pub fn setMasks(s: Set) []Set.MaskInt {
            return s.masks[0 .. (s.bit_length + @bitSizeOf(Set.MaskInt) - 1) / @bitSizeOf(Set.MaskInt)];
        }
    };

    const Instr = struct {
        def: *Fn.Node = undefined,
        preds: []const *Fn.Node = undefined,
        succ: []const *Fn.Node = undefined,
        liveins: Set,
        liveouts: Set,
        defs: Set,
        uses: Set,

        pub fn isBasicBlock(k: Fn.NodeKind) bool {
            std.debug.assert(Fn.isCfg(k));
            return switch (k) {
                .Entry => true,
                else => false,
            };
        }

        pub fn setMasks(s: Set) []Set.MaskInt {
            return s.masks[0 .. (s.bit_length + @bitSizeOf(Set.MaskInt) - 1) / @bitSizeOf(Set.MaskInt)];
        }
    };

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const instrs = tmp.arena.alloc(Instr, func.instr_count);

    //var work_list = std.ArrayListUnmanaged(u16).initBuffer(tmp.arena.alloc(u16, instrs.len));
    //var in_work_list = std.DynamicBitSetUnmanaged.initEmpty(tmp.arena.allocator(), instrs.len) catch unreachable;

    // TODO: we can clean this up: arena should contruct the bitset
    for (instrs) |*b| {
        //   work_list.appendAssumeCapacity(@intCast(instrs.len - i - 1));
        b.* = .{
            .liveins = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
            .liveouts = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
            .defs = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
            .uses = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
        };
    }

    var visited = std.DynamicBitSet.initEmpty(tmp.arena.allocator(), func.next_id) catch unreachable;
    const postorder = func.collectPostorder(tmp.arena.allocator(), &visited);
    for (postorder) |bb| {
        const node = &bb.base;
        for (node.outputs(), 0..) |c, i| {
            instrs[c.schedule].def = c;

            if (i + 1 < node.outputs().len) {
                instrs[c.schedule].succ = node.outputs()[i + 1 ..][0..1];
            } else if (c.kind != .Trap) {
                instrs[c.schedule].succ = c.outputs();
            } else {
                instrs[c.schedule].succ = &.{};
            }

            if (i == 0) {
                instrs[c.schedule].preds = @ptrCast(bb.base.inputs());
            } else {
                instrs[c.schedule].preds = node.outputs()[i - 1 ..][0..1];
            }
        }
    }

    for (instrs, 0..) |*instr, i| {
        if (instr.def.outputs().len != 0 and instr.def.kind != .MachMove and (!instr.def.isStore() or instr.def.kind == .MemCpy) and
            instr.def.kind != .Mem and !instr.def.isCfg() and (instr.def.kind != .Phi or instr.def.isDataPhi()))
        {
            instr.defs.set(i);
        }

        if (instr.def.kind == .Call) {
            instr.liveouts.set(i);
        }

        if (instr.def.kind == .Phi) continue;
        for (instr.def.dataDeps()) |use| if (use) |uuse| {
            instrs[instr.def.schedule].uses.set(uuse.schedule);
        };
    }

    // compute liveins and liveouts

    //    while (work_list.pop()) |task| {
    //        const i = instrs[task];
    //        var changed: usize = 0;
    //        for (
    //            Block.setMasks(i.liveins),
    //            Block.setMasks(i.liveouts),
    //            Block.setMasks(i.uses),
    //            Block.setMasks(i.defs),
    //        ) |*lin, *lot, us, df| {
    //            const previ = lin.*;
    //            lin.* = us | (lot.* & ~df);
    //
    //            changed |= (previ ^ lin.*);
    //        }
    //
    //        if (changed != 0) {
    //            for (i.preds) |p| {
    //                if (!in_work_list.isSet(p.schedule)) {
    //                    in_work_list.set(p.schedule);
    //                    work_list.appendAssumeCapacity(p.schedule);
    //                }
    //            }
    //        }
    //
    //        for (i.succ) |bo| {
    //            changed = 0;
    //            for (
    //                Block.setMasks(i.liveouts),
    //                Block.setMasks(instrs[if (bo.isCfg() and bo.isBasicBlockStart()) bo.outputs()[0].schedule else bo.schedule].liveins),
    //            ) |*lot, sin| {
    //                const prevo = lot.*;
    //                lot.* |= sin;
    //                changed |= (prevo ^ lot.*);
    //            }
    //
    //            if (changed != 0) {
    //                if (!in_work_list.isSet(bo.schedule)) {
    //                    in_work_list.set(bo.schedule);
    //                    work_list.appendAssumeCapacity(bo.schedule);
    //                }
    //            }
    //        }
    //    }
    //

    var changed: Set.MaskInt = 1;
    while (changed != 0) {
        changed = 0;

        var ite = std.mem.reverseIterator(instrs);
        while (ite.next()) |i| {
            for (
                Block.setMasks(i.liveins),
                Block.setMasks(i.liveouts),
                Block.setMasks(i.uses),
                Block.setMasks(i.defs),
            ) |*lin, *lot, us, df| {
                const previ = lin.*;
                lin.* = us | (lot.* & ~df);

                changed |= (previ ^ lin.*);
            }

            for (i.succ) |bo| {
                for (
                    Block.setMasks(i.liveouts),
                    Block.setMasks(instrs[if (bo.isCfg() and bo.isBasicBlockStart()) bo.outputs()[0].schedule else bo.schedule].liveins),
                ) |*lot, sin| {
                    const prevo = lot.*;
                    lot.* |= sin;
                    changed |= (prevo ^ lot.*);
                }
            }
        }
    }

    for (instrs) |*i| {
        for (Block.setMasks(i.liveins), Block.setMasks(i.uses)) |a, b| {
            std.debug.assert(b & ~a == 0);
        }
    }

    for (postorder) |bb| {
        for (bb.base.outputs()) |o| {
            if (o.kind == .Phi) continue;
            for (o.dataDeps()) |i| if (i) |ii| {
                std.debug.assert(instrs[o.schedule].liveins.isSet(ii.schedule));
            };
        }
    }

    // build interference => very wastefull
    const interference_table = tmp.arena.alloc(Set, func.instr_count);
    for (interference_table) |*r| r.* = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable;

    for (instrs) |*ins| {
        var iter = ins.defs.iterator(.{});
        while (iter.next()) |i| {
            interference_table[i].setUnion(ins.liveouts);
        }
    }

    for (interference_table, 0..) |it_row, j| {
        var iter = it_row.iterator(.{});
        while (iter.next()) |i| {
            interference_table[i].set(j);
        }
    }

    const sentinel = std.math.maxInt(u16);

    const colors = func.arena.allocator().alloc(u16, func.instr_count) catch unreachable;
    @memset(colors, sentinel);

    var selection_set = Set.initEmpty(tmp.arena.allocator(), func.instr_count + 64) catch unreachable;
    for (interference_table, colors, instrs, 0..) |it_row, *color, instr, i| {
        @memset(Block.setMasks(selection_set), 0);

        @as(*align(@alignOf(usize)) u64, @ptrCast(&Block.setMasks(selection_set)[0])).* |=
            if (@hasDecl(Mach, "reserved_regs")) Mach.reserved_regs else 0;

        var iter = it_row.iterator(.{});
        //std.debug.print("| {}\n", .{instrs[i].def});
        while (iter.next()) |e| if (i != e) {
            //std.debug.print("|  {}\n", .{instrs[e].def});
            if (colors[e] != sentinel) selection_set.set(colors[e]);
            @as(*align(@alignOf(usize)) u64, @ptrCast(&Block.setMasks(selection_set)[0])).* |=
                instrs[e].def.clobbers();
        };

        if (instrs[i].def.carried()) |c| {
            for (instrs[i].def.dataDeps(), 0..) |d, k| {
                if (k != c) {
                    selection_set.set(colors[d.?.schedule]);
                }
            }
        }

        const bias = instr.def.regBias();
        if (bias != null and !selection_set.isSet(bias.?)) {
            color.* = bias.?;
        } else {
            var it = selection_set.iterator(.{ .kind = .unset });
            color.* = @intCast(it.next().?);
        }
    }

    return colors;
}
