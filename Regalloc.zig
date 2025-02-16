const std = @import("std");
const graph = @import("graph.zig");

pub fn ralloc(comptime Mach: type, func: *graph.Func(Mach)) []u8 {
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
        prev: *Fn.Node = undefined,
        def: *Fn.Node = undefined,
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

    const tmp, const lock = func.beginTmpAlloc();
    defer lock.unlock();

    const instrs = tmp.alloc(Instr, func.instr_count) catch unreachable;

    for (instrs) |*b| b.* = .{
        .liveins = Set.initEmpty(tmp, func.instr_count) catch unreachable,
        .liveouts = Set.initEmpty(tmp, func.instr_count) catch unreachable,
        .defs = Set.initEmpty(tmp, func.instr_count) catch unreachable,
        .uses = Set.initEmpty(tmp, func.instr_count) catch unreachable,
    };

    var visited = std.DynamicBitSet.initEmpty(tmp, func.next_id) catch unreachable;
    const postorder = func.collectPostorder(tmp, &visited);
    for (postorder) |bb| {
        const node = &bb.base;
        for (node.outputs(), 0..) |c, i| {
            instrs[c.schedule].def = c;
            if (i + 1 < node.outputs().len) {
                instrs[c.schedule].succ = node.outputs()[i + 1 ..][0..1];
            } else {
                instrs[c.schedule].succ = c.outputs();
            }
        }
    }

    for (instrs, 0..) |*instr, i| {
        if (instr.def.outputs().len != 0 and instr.def.kind != .MachMove and !instr.def.isStore() and
            instr.def.kind != .Mem and !instr.def.isCfg())
        {
            instr.defs.set(i);
        }
        if (instr.def.kind == .Phi) continue;
        for (instr.def.dataDeps()) |use| if (use) |uuse| {
            instrs[instr.def.schedule].uses.set(uuse.schedule);
        };
    }

    // compute liveins and liveouts
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
    const interference_table = tmp.alloc(Set, func.instr_count) catch unreachable;
    for (interference_table) |*r| r.* = Set.initEmpty(tmp, func.instr_count) catch unreachable;

    for (instrs) |*ins| {
        var iter = ins.defs.iterator(.{});
        while (iter.next()) |i| {
            interference_table[i].setUnion(ins.liveouts);
        }
    }

    const tight_interference_table = tmp.alloc([]u16, func.instr_count) catch unreachable;
    for (interference_table, tight_interference_table, 0..) |r, *tr, j| {
        tr.* = tmp.alloc(u16, r.count() -| 1) catch unreachable;
        var i: usize = 0;
        var iter = r.iterator(.{});
        while (iter.next()) |e| if (j != e) {
            //std.debug.print("{} {}\n", .{ instrs[j].def, instrs[e].def });
            tr.*[i] = @intCast(e);
            i += 1;
        };
    }

    // color => inefficient
    const colors = func.arena.allocator().alloc(u8, func.instr_count) catch unreachable;
    @memset(colors, 0);
    for (tight_interference_table, colors) |slc, *c| {
        // we set the bits of occupied colors
        var selection_set: usize = 0;
        for (slc) |e| {
            if (colors[e] != 0) {
                selection_set |= @as(usize, 1) << @intCast(colors[e] - 1);
            }
        }
        // select the closest free bit as a new color
        c.* = @ctz(~selection_set) + 1;
    }

    return colors;
}
