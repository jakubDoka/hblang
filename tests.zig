const std = @import("std");
pub const root = @import("src/utils.zig");
pub const test_util = @import("src/test_util.zig");
pub const hbc = @import("src/hbc.zig");

test {
    _ = @import("zig-out/tests.zig");
    _ = @import("zig-out/vendored_tests.zig");
    //_ = @import("zig-out/fuzz_finding_tests.zig");
    std.testing.refAllDeclsRecursive(@This());
}

pub fn runTest(name: []const u8, code: [:0]const u8) !void {
    root.Arena.initScratch(1024 * 1024);
    defer root.Arena.deinitScratch();

    const gpa = std.testing.allocator;

    try test_util.testFmt(name, name, code);

    var out = std.ArrayList(u8).init(gpa);
    defer out.deinit();

    errdefer {
        const stderr = std.io.getStdErr();
        const colors = std.io.tty.detectConfig(stderr);
        test_util.testBuilder(name, code, gpa, stderr.writer().any(), colors, true) catch unreachable;
    }

    try test_util.testBuilder(name, code, gpa, out.writer().any(), .no_color, false);

    if (!test_util.hasEnv("SKIP_DIFF"))
        try test_util.checkOrUpdatePrintTest(name, out.items);
}

pub fn runFuzzFindingTest(name: []const u8, code: []const u8) !void {
    root.Arena.initScratch(1024 * 1024);
    defer root.Arena.deinitScratch();

    const gpa = std.testing.allocator;

    std.debug.print("{s}\n", .{code});

    //errdefer {
    //    const stderr = std.io.getStdErr();
    //    const colors = std.io.tty.detectConfig(stderr);
    //    test_util.testBuilder(name, code, gpa, stderr.writer().any(), colors, true) catch {};
    //}

    try test_util.testBuilder(name, code, gpa, std.io.null_writer.any(), .no_color, false);
}

pub fn runVendoredTest(path: []const u8) !void {
    root.Arena.initScratch(1024 * 1024);
    defer root.Arena.deinitScratch();

    var bin = std.ArrayListUnmanaged(u8).empty;
    defer bin.deinit(std.testing.allocator);
    var ast = try hbc.compile(.{
        .gpa = std.testing.allocator,
        .diagnostics = std.io.getStdErr().writer().any(),
        .colors = std.io.tty.detectConfig(std.io.getStdErr()),
        .output = bin.writer(std.testing.allocator).any(),
        .mangle_terminal = true,
        .root_file = path,
    });
    defer ast.arena.deinit();

    const HbvmGen = @import("src/HbvmGen.zig");

    const header: HbvmGen.ExecHeader = @bitCast(bin.items[0..@sizeOf(HbvmGen.ExecHeader)].*);
    try test_util.runVm(
        &ast.ast[0],
        ast.arena.allocator(),
        false,
        bin.items[@sizeOf(HbvmGen.ExecHeader)..],
        header.code_length,
        std.io.null_writer.any(),
        .no_color,
    );
}
