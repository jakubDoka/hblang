const std = @import("std");

const root = @import("hb");
const isa = root.hbvm.isa;
const Types = root.frontend.Types;
const Builder = root.backend.Builder;
const Node = Builder.BuildNode;
const graph = root.backend.graph;
const utils = root.utils;
const static_anal = root.backend.static_anal;
const Mach = root.backend.Machine;
const Ast = root.frontend.Ast;
const Arena = utils.Arena;
const Codegen = root.frontend.Codegen;
const Comptime = root.frontend.Comptime;
const Lexer = root.frontend.Lexer;
const HbvmGen = root.hbvm.HbvmGen;
const Vm = root.hbvm.Vm;
const tests = root.test_utils;

comptime {
    if (@import("root") == @This()) @export(&fuzz, .{ .name = "main", .linkage = .strong });
}

fn fuzz() callconv(.c) void {
    utils.Arena.initScratch(1024 * 1024);
    var arena = utils.Arena.init(1024 * 1024 * 4);
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
    if (false) {
        const asts = try tests.parseExample(arena, name, code, output);

        const gpa = arena.allocator();

        var types = Types.init(asts, output);
        defer types.deinit();

        var func_arena = utils.Arena.scrath(null);
        defer func_arena.deinit();

        const cg = Codegen.init(func_arena.arena, types, .runtime, .ableos);
        defer cg.deinit();

        const entry = try cg.getEntry(.root, "main");

        types.queue(.runtime, .init(.{ .Func = entry }));

        var hbgen = HbvmGen{ .gpa = gpa };
        defer hbgen.deinit();
        var gen = Mach.init("hbvm-ableos", &hbgen);

        const errored = root.frontend.Codegen.emitReachable(func_arena.arena, types, .ableos, gen, .{});

        if (errored) return error.Never;

        gen.finalize(std.io.null_writer.any());
    }
}
