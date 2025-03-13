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

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const instrs = tmp.arena.alloc(Instr, func.instr_count);

    // TODO: we can clean this up: arena should contruct the bitset
    for (instrs) |*b| b.* = .{
        .liveins = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
        .liveouts = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
        .defs = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
        .uses = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
    };

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
        }
    }

    for (instrs, 0..) |*instr, i| {
        if (instr.def.outputs().len != 0 and instr.def.kind != .MachMove and !instr.def.isStore() and
            instr.def.kind != .Mem and !instr.def.isCfg() and (instr.def.kind != .Phi or instr.def.isDataPhi()))
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
    const interference_table = tmp.arena.alloc(Set, func.instr_count);
    for (interference_table) |*r| r.* = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable;

    for (instrs) |*ins| {
        var iter = ins.defs.iterator(.{});
        while (iter.next()) |i| {
            interference_table[i].setUnion(ins.liveouts);
        }
    }

    const colors = func.arena.allocator().alloc(u16, func.instr_count) catch unreachable;
    @memset(colors, 0);
    for (interference_table, colors, 0..) |r, *c, j| {
        var selection_set: u256 = 0;
        var iter = r.iterator(.{});
        while (iter.next()) |e| if (j != e) {
            if (colors[e] != 0) {
                selection_set |= @as(u256, 1) << @intCast(colors[e] - 1);
            }
        };
        c.* = @ctz(~selection_set) + 1;
    }

    return colors;
}
