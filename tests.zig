const std = @import("std");
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
pub const Fuzz = @import("fuzz.zig");
pub const root = @import("src/utils.zig");
pub const test_util = @import("src/test_util.zig");

test {
    _ = @import("zig-out/tests.zig");
    _ = @import("zig-out/vendored_tests.zig");
    _ = @import("zig-out/fuzz_finding_tests.zig");
    std.testing.refAllDeclsRecursive(@This());
}

pub fn runTest(name: []const u8, code: []const u8) !void {
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

    //errdefer {
    //    const stderr = std.io.getStdErr();
    //    const colors = std.io.tty.detectConfig(stderr);
    //    test_util.testBuilder(name, code, gpa, stderr.writer().any(), colors, true) catch {};
    //}

    try test_util.testBuilder(name, code, gpa, std.io.null_writer.any(), .no_color, false);
}

pub fn runVendoredTest(path: []const u8) !void {
    _ = path;
}
