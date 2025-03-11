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
    fuzzRun("fuzz", input, &arena, std.io.null_writer.any()) catch |err| switch (err) {
        error.UnexpectedToken, error.ParsingFailed, error.Never => {},
        else => @panic(""),
    };
}

pub fn main() void {
    fuzz();
}

pub fn fuzzRun(
    name: []const u8,
    code: []const u8,
    arena: *root.Arena,
    output: std.io.AnyWriter,
) !void {
    const asts = try tests.parseExample(arena, name, code, output);

    const gpa = arena.allocator();

    var types = Types.init(gpa, asts, output);
    defer types.deinit();

    var func_arena = root.Arena.scrath(null);
    defer func_arena.deinit();

    var cg = Codegen.init(gpa, func_arena.arena, &types, .runtime);
    defer cg.deinit();

    const entry = try cg.getEntry(.root, "main");

    cg.work_list.appendAssumeCapacity(.{ .Func = entry });

    var hbgen = HbvmGen{ .gpa = gpa };
    defer hbgen.deinit();
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

    var out = gen.finalize();
    defer out.deinit(gpa);
}
