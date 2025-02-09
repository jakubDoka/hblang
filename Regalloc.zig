const std = @import("std");
const Func = @import("Func.zig");

const Set = std.DynamicBitSetUnmanaged;
pub const Block = struct {
    start: *Func.Node = undefined,
    end: *Func.Node = undefined,
    liveins: Set,
    liveouts: Set,
    defs: Set,
    uses: Set,

    pub fn setMasks(s: Set) []Set.MaskInt {
        return s.masks[0 .. (s.bit_length + @bitSizeOf(Set.MaskInt) - 1) / @bitSizeOf(Set.MaskInt)];
    }
};

pub const Instr = struct {
    prev: *Func.Node = undefined,
    def: *Func.Node = undefined,
    succ: []const *Func.Node = undefined,
    liveins: Set,
    liveouts: Set,
    defs: Set,
    uses: Set,

    pub fn isBasicBlock(k: Func.NodeKind) bool {
        std.debug.assert(Func.isCfg(k));
        return switch (k) {
            .Entry => true,
            else => false,
        };
    }

    pub fn setMasks(s: Set) []Set.MaskInt {
        return s.masks[0 .. (s.bit_length + @bitSizeOf(Set.MaskInt) - 1) / @bitSizeOf(Set.MaskInt)];
    }
};

pub fn ralloc(func: *Func, comptime Mach: type) []u8 {
    const gcm = @import("gcm.zig").Utils(Mach);
    const tmp = func.beginTmpAlloc();

    const instrs = tmp.alloc(Instr, func.instr_count) catch unreachable;
    //const blocks = tmp.alloc(Block, func.block_count) catch unreachable;

    for (instrs) |*b| b.* = .{
        .liveins = Set.initEmpty(tmp, func.instr_count) catch unreachable,
        .liveouts = Set.initEmpty(tmp, func.instr_count) catch unreachable,
        .defs = Set.initEmpty(tmp, func.instr_count) catch unreachable,
        .uses = Set.initEmpty(tmp, func.instr_count) catch unreachable,
    };

    var visited = std.DynamicBitSet.initEmpty(tmp, func.next_id) catch unreachable;
    var stack = std.ArrayList(Func.Frame).init(tmp);
    const postorder = gcm.collectPostorder(func, tmp, &stack, &visited);
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
        if (instr.def.outputs().len != 0 and !gcm.isCfg(instr.def.kind)) {
            instr.defs.set(i);
        }
        for (gcm.dataDeps(instr.def)) |use| if (use) |uuse| {
            instrs[instr.def.schedule].uses.set(uuse.schedule);
        };
    }

    // compute liveins and liveouts
    var changed: Set.MaskInt = 1;
    while (changed != 0) {
        changed = 0;

        for (instrs) |*i| {
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
                    Block.setMasks(instrs[if (gcm.isCfg(bo.kind) and gcm.isBasicBlockStart(bo.kind)) bo.outputs()[0].schedule else bo.schedule].liveins),
                ) |*lot, sin| {
                    const prevo = lot.*;
                    lot.* |= sin;
                    changed |= (prevo ^ lot.*);
                }
            }
        }
    }

    for (postorder) |bb| {
        for (bb.base.outputs()) |o| {
            for (gcm.dataDeps(o)) |i| if (i) |ii| {
                std.debug.assert(instrs[o.schedule].liveins.isSet(ii.schedule));
            };
        }
    }

    // build interference => very wastefull
    const interference_table = tmp.alloc(Set, func.instr_count) catch unreachable;
    for (interference_table) |*r| r.* = Set.initEmpty(tmp, func.instr_count) catch unreachable;

    for (instrs) |ins| {
        var iter = ins.liveins.iterator(.{});
        while (iter.next()) |i| {
            interference_table[i].setUnion(ins.liveins);
        }
        iter = ins.liveouts.iterator(.{});
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
