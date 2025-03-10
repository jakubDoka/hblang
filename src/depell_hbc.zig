const hb = @import("root.zig");
const std = @import("std");
const Arena = hb.utils.Arena;

export fn compile(ptr: [*c]u8, len: usize) void {
    const source = ptr[0..len :0];

    Arena.initScratch(1024 * 1024 * 10);
    defer Arena.deinitScratch();

    var gpa_impl = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_impl.deinit();

    const gpa = gpa_impl.allocator();

    const diagnostics = std.io.null_writer.any();

    var ast_arena = std.heap.ArenaAllocator.init(gpa);
    defer ast_arena.deinit();

    const asts = &.{hb.Ast.init(ast_arena.allocator(), .{ .code = source, .path = "" }) catch unreachable};

    var types = hb.Types.init(gpa, asts, diagnostics);
    defer types.deinit();

    var codegen = hb.Codegen.init(gpa, Arena.scrath(null).arena, &types, .runtime);
    defer codegen.deinit();

    var hbg = hb.HbvmGen{ .gpa = gpa };
    defer hbg.deinit();

    const backend = hb.Mach.init(&hbg);

    var syms = std.heap.ArenaAllocator.init(gpa);
    defer syms.deinit();

    const entry = codegen.getEntry(.root, "main") catch {
        diagnostics.writeAll(
            \\...you can define the `main` in the mentioned file:
            \\main := fn(): uint {
            \\    return 0
            \\}
        ) catch unreachable;

        return;
    };

    codegen.queue(.{ .Func = entry });

    var errored = false;
    while (codegen.nextTask()) |tsk| switch (tsk) {
        .Func => |func| {
            defer codegen.bl.func.reset();

            codegen.build(func) catch {
                errored = true;
                continue;
            };

            backend.emitFunc(&codegen.bl.func, .{
                .id = func.id,
                .name = hb.Types.Id.init(.{ .Func = func }).fmt(&types)
                    .toString(syms.allocator()) catch unreachable,
                .entry = func.id == entry.id,
            });
        },
        .Global => |global| {
            backend.emitData(.{
                .id = global.id,
                .name = hb.Types.Id.init(.{ .Global = global }).fmt(&types)
                    .toString(syms.allocator()) catch unreachable,
                .value = .{ .init = global.data },
            });
        },
    };

    if (errored) {
        diagnostics.print("failed due to previous errors\n", .{}) catch unreachable;
        return;
    }

    var out = backend.finalize();
    defer out.deinit(gpa);
}
