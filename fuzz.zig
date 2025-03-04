const std = @import("std");
const root = @import("src/utils.zig");
const isa = @import("src/isa.zig");
pub const Ast = @import("src/Ast.zig");
pub const Vm = @import("src/Vm.zig");
pub const Builder = @import("src/Builder.zig");
pub const Codegen = @import("src/Codegen.zig");
pub const HbvmGen = @import("src/HbvmGen.zig");
pub const Types = @import("src/Types.zig");
pub const Regalloc = @import("src/Regalloc.zig");
pub const graph = @import("src/graph.zig");
pub const Mach = @import("src/Mach.zig");
pub const tests = @import("src/test_util.zig");

comptime {
    @export(&fuzz, .{ .name = "main", .linkage = .strong });
}

fn fuzz() callconv(.c) void {
    root.Arena.initScratch(1024 * 1024);
    var arena = root.Arena.init(1024 * 1024 * 4);
    const input = std.io.getStdIn().readToEndAlloc(arena.allocator(), 1024 * 1024) catch unreachable;
    fuzzRun("fuzz", input, arena.allocator(), std.io.null_writer.any()) catch |err| switch (err) {
        error.UnexpectedToken, error.ParsingFailed, error.NoMain, error.Never => {},
        else => @panic(""),
    };
}

pub fn main() void {
    fuzz();
}

pub fn fuzzRun(
    name: []const u8,
    code: []const u8,
    gpa: std.mem.Allocator,
    output: std.io.AnyWriter,
) !void {
    const asts = try tests.parseExample(gpa, name, code, output);
    const ast = asts[0];

    defer {
        for (asts) |*a| a.deinit(gpa);
        gpa.free(asts);
    }

    const main_fn = ast.findDecl(ast.items, "main") orelse return error.NoMain;
    const fn_ast = ast.exprs.get(main_fn).BinOp.rhs;

    var types = Types.init(gpa, asts, output);
    defer types.deinit();

    var func_arena = root.Arena.scrath(null);
    defer func_arena.deinit();

    var cg = Codegen.init(gpa, func_arena.arena, &types, .runtime);
    defer cg.deinit();

    cg.parent_scope = .{ .Perm = types.getScope(.root) };
    const entry_ty = (try cg.resolveTy("main", fn_ast));
    if (entry_ty.data() != .Func) return error.Never;
    const entry = entry_ty.data().Func;
    cg.work_list.appendAssumeCapacity(.{ .Func = entry });

    var finalized = false;
    var hbgen = HbvmGen.init(gpa);
    errdefer if (!finalized) hbgen.deinit();
    errdefer if (!finalized) hbgen.out.deinit();
    var gen = Mach.init(&hbgen);

    var errored = false;
    while (cg.nextTask()) |task| switch (task) {
        .Func => |func| {
            defer cg.bl.func.reset();

            cg.build(func) catch {
                errored = true;
                continue;
            };

            gen.emitFunc(&cg.bl.func, .{
                .id = func.id,
                .entry = func.id == entry.id,
            });
        },
        .Global => |g| {
            gen.emitData(.{
                .id = g.id,
                .value = .{ .init = g.data },
            });
        },
    };

    if (errored) return error.Never;

    finalized = true;
    var out = gen.finalize();
    defer out.deinit();
}
