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

pub fn ralloc(func: *Func) []u8 {
    const tmp = func.beginTmpAlloc();

    // init blocks
    const blocks = tmp.alloc(Block, func.block_count) catch unreachable;

    for (blocks) |*b| b.* = .{
        .liveins = Set.initEmpty(tmp, func.instr_count) catch unreachable,
        .liveouts = Set.initEmpty(tmp, func.instr_count) catch unreachable,
        .defs = Set.initEmpty(tmp, func.instr_count) catch unreachable,
        .uses = Set.initEmpty(tmp, func.instr_count) catch unreachable,
    };

    var visited = std.DynamicBitSet.initEmpty(tmp, func.next_id) catch unreachable;
    var stack = std.ArrayList(Func.Frame).init(tmp);
    Func.traversePostorder(struct {
        blocks: []Block,
        pub const dir = "outputs";
        pub fn each(ctx: @This(), node: *Func.Node) void {
            if (Block.isBasicBlock(node.kind)) {
                ctx.blocks[node.schedule].start = node;
            } else if (Func.isBasicBlockEnd(node.kind)) {
                ctx.blocks[node.schedule].end = node;
            }
        }

        pub fn filter(_: @This(), node: *Func.Node) bool {
            return Func.isCfg(node.kind);
        }
    }{ .blocks = blocks }, func.root, &stack, &visited);

    // compute def and uses
    for (blocks) |*b| {
        for (b.start.outputs()) |def| if (!Func.isCfg(def.kind)) {
            if (def.outputs().len != 0) b.defs.set(def.schedule);
            for (def.outputs()) |use| {
                if (use.inputs()[0] != def.inputs()[0])
                    blocks[use.inputs()[0].?.schedule].uses.set(def.schedule);
            }
        };
    }

    // compute liveins and liveouts
    var changed: Set.MaskInt = 0;
    while (changed != 0) {
        changed = 0;

        // the blocks are already in the reverse order
        for (blocks) |*b| {
            for (
                Block.setMasks(b.liveins),
                Block.setMasks(b.liveouts),
                Block.setMasks(b.uses),
                Block.setMasks(b.defs),
            ) |*lin, *lot, us, df| {
                const previ = lin.*;
                lin.* = us | (lot.* & ~df);

                changed |= (previ ^ lin.*);
            }

            for (b.end.outputs()) |bo| if (Func.isCfg(bo.kind)) {
                for (
                    Block.setMasks(b.liveouts),
                    Block.setMasks(blocks[bo.schedule].liveins),
                ) |*lot, sin| {
                    const prevo = lot.*;
                    lot.* |= sin;
                    changed |= (prevo ^ lot.*);
                }
            };
        }
    }

    // build interference => very wastefull
    const interference_table = tmp.alloc(Set, func.instr_count) catch unreachable;
    for (interference_table) |*r| r.* = Set.initEmpty(tmp, func.instr_count) catch unreachable;

    for (blocks) |b| {
        var iter = b.liveins.iterator(.{});
        while (iter.next()) |i| {
            interference_table[i].setUnion(b.liveins);
        }
        iter = b.liveouts.iterator(.{});
        while (iter.next()) |i| {
            interference_table[i].setUnion(b.liveouts);
        }
    }

    const tight_interference_table = tmp.alloc([]u16, func.instr_count) catch unreachable;
    for (interference_table, tight_interference_table) |r, *tr| {
        tr.* = tmp.alloc(u16, r.count()) catch unreachable;
        var i: usize = 0;
        var iter = r.iterator(.{});
        while (iter.next()) |e| : (i += 1) {
            tr.*[i] = @intCast(e);
        }
    }

    // color => inefficient
    const colors = func.arena.allocator().alloc(u8, func.instr_count) catch unreachable;
    @memset(colors, 0);
    for (tight_interference_table, colors) |slc, *c| {
        // we set the bits of occupied colors
        var selection_set: usize = 0;
        for (slc) |e| if (colors[e] != 0) {
            selection_set |= @as(usize, 1) << @intCast(e - 1);
        };
        // select the closest free bit as a new color
        c.* = @ctz(~selection_set) + 1;
    }

    return colors;
}
