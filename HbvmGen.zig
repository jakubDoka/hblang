const std = @import("std");
const isa = @import("isa.zig");
const Func = @import("Func.zig");
const Regalloc = @import("Regalloc.zig");

pub fn gen(func: *Func, allocs: []u8, out: *std.ArrayList(u8)) void {
    const Reloc = struct {
        dest_block: u16,
        offset: i32,
        sub_offset: u8,
    };

    const tmp = func.beginTmpAlloc();

    const block_offsets = tmp.alloc(i32, func.block_count) catch unreachable;
    var relocs = std.ArrayList(Reloc).init(tmp);

    var visited = std.DynamicBitSet.initEmpty(tmp, func.next_id) catch unreachable;
    var stack = std.ArrayList(Func.Frame).init(tmp);
    Func.traversePostorder(struct {
        out: *std.ArrayList(u8),
        relocs: *std.ArrayList(Reloc),
        block_offsets: []i32,
        allocs: []u8,

        pub const dir = "inputs";
        pub fn each(ctx: @This(), node: *Func.Node) void {
            if (Regalloc.Block.isBasicBlock(node.kind)) {
                ctx.block_offsets[node.schedule] = @intCast(ctx.relocs.items.len);

                for (node.outputs()) |no| {
                    const alloc: isa.Reg = @enumFromInt(ctx.allocs[no.schedule]);
                    switch (no.kind) {
                        .CInt => {
                            const extra = no.extra(.CInt);
                            ctx.out.appendSlice(&isa.pack(.li64, .{ alloc, @as(u64, @intCast(extra.*)) })) catch unreachable;
                        },
                        .Return => {
                            ctx.out.appendSlice(&isa.pack(.cp, .{ .ret, alloc })) catch unreachable;
                        },
                        else => std.debug.panic("{any}", .{no.kind}),
                    }
                }
            }
        }

        pub fn filter(_: @This(), node: *Func.Node) bool {
            return Func.isCfg(node.kind);
        }
    }{
        .out = out,
        .relocs = &relocs,
        .block_offsets = block_offsets,
        .allocs = allocs,
    }, func.end, &stack, &visited);

    out.appendSlice(&isa.pack(.tx, .{})) catch unreachable;
}
