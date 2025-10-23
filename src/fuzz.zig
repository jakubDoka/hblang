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

var glob_arena: Arena = undefined;

export fn zig_fuzz_init() void {
    glob_arena = Arena.init(1024 * 1024 * 128);
    Arena.initScratch(1024 * 1024 * 32);
}

export fn zig_fuzz_test(buf: [*]u8, len: isize) void {
    const src = buf[0..@intCast(len)];
    fuzzRun("fuzz", src, &glob_arena, null) catch |err| switch (err) {
        error.UnexpectedToken, error.ParsingFailed, error.Never => {},
        else => @panic(""),
    };
}

pub fn fuzzRun(
    name: []const u8,
    code: []const u8,
    arena: *Arena,
    output: ?*std.Io.Writer,
) !void {
    var point = arena.checkpoint();
    defer point.deinit();

    const asts = try tests.parseExample(arena, name, code, output);

    if (asts.len == 0) return error.Never;

    const gpa = arena.allocator();

    var types = Types.init(arena.subslice(1024 * 1024 * 64), asts, output, gpa);
    defer types.deinit();

    var func_arena = utils.Arena.scrath(null);
    defer func_arena.deinit();

    const cg = Codegen.init(func_arena.arena, types, .runtime, .ableos);
    defer cg.deinit();

    const entry = try cg.getEntry(.root, "main");

    types.queue(.runtime, .init(.{ .Func = entry }));

    var hbgen = HbvmGen{ .gpa = gpa };
    defer hbgen.deinit();

    var threading = root.Threading{ .single = .{ .types = types, .machine = &hbgen.mach } };
    const errored = root.frontend.Codegen.emitReachable(func_arena.arena, &threading, .{
        .abi = .ableos,
        .optimizations = .release,
    });

    if (errored) return error.Never;

    hbgen.finalize(.{
        .output = null,
        .optimizations = .{ .mode = .release },
        .builtins = .{},
        .files = types.line_indexes,
    });
}
