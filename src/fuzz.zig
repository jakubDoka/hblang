const std = @import("std");

const root = @import("root.zig");
const isa = root.hbvm.isa;
const Types = root.frontend.Types;
const Builder = root.backend.Builder;
const Node = Builder.BuildNode;
const graph = root.backend.graph;
const utils = root.utils;
const static_anal = root.backend.static_anal;
const Mach = root.backend.Mach;
const Ast = root.frontend.Ast;
const Arena = utils.Arena;
const Codegen = root.frontend.Codegen;
const Comptime = root.frontend.Comptime;
const Lexer = root.frontend.Lexer;
const HbvmGen = root.hbvm.HbvmGen;
const Vm = root.hbvm.Vm;
const tests = @import("test_util.zig");

comptime {
    if (@import("root") == @This()) @export(&fuzz, .{ .name = "main", .linkage = .strong });
}

fn fuzz() callconv(.c) void {
    utils.Arena.initScratch(1024 * 1024);
    defer utils.Arena.deinitScratch();
    var arena = utils.Arena.init(1024 * 1024 * 4);
    defer arena.deinit();
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
    arena: *utils.Arena,
    output: std.io.AnyWriter,
) !void {
    const asts = try tests.parseExample(arena, name, code, output);

    const gpa = arena.allocator();

    var types = Types.init(gpa, asts, output);
    defer types.deinit();

    var func_arena = utils.Arena.scrath(null);
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
