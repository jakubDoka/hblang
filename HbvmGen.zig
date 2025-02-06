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
                    const alloc = ctx.reg(no);
                    const inps = no.inputs();
                    switch (no.kind) {
                        .CInt => {
                            const extra = no.extra(.CInt);
                            ctx.emit(.li64, .{ alloc, @as(u64, @intCast(extra.*)) });
                        },
                        .Return => {
                            ctx.emit(.cp, .{ .ret, alloc });
                        },
                        .BinOp => {
                            const extra = no.extra(.BinOp);
                            switch (extra.*) {
                                .@"+" => ctx.binop(.add64, no),
                                .@"-" => ctx.binop(.sub64, no),
                                .@"*" => ctx.binop(.mul64, no),
                                .@"/" => ctx.emit(.dirs64, .{ alloc, .null, ctx.reg(inps[1]), ctx.reg(inps[2]) }),
                                else => std.debug.panic("{any}", .{extra.*}),
                            }
                        },
                        else => std.debug.panic("{any}", .{no.kind}),
                    }
                }
            }
        }

        fn binop(ctx: @This(), comptime op: isa.Op, n: *Func.Node) void {
            ctx.emit(op, .{ ctx.reg(n), ctx.reg(n.inputs()[1]), ctx.reg(n.inputs()[2]) });
        }

        fn reg(ctx: @This(), n: ?*Func.Node) isa.Reg {
            return @enumFromInt(ctx.allocs[n.?.schedule]);
        }

        fn emit(ctx: @This(), comptime op: isa.Op, args: anytype) void {
            ctx.out.appendSlice(&isa.pack(op, args)) catch unreachable;
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
