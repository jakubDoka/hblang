const std = @import("std");
pub const utils = @import("utils.zig");
pub const root = @import("root.zig");
pub const test_util = @import("test_util.zig");
pub const hbc = @import("hbc.zig");
pub const fuzz = @import("fuzz.zig");

comptime {
    @setEvalBranchQuota(2000);
    refAllDeclsRecursive(@This(), 10);
}

pub fn refAllDeclsRecursive(comptime T: type, depth: usize) void {
    if (depth == 0) return;
    inline for (comptime std.meta.declarations(T)) |decl| {
        if (@TypeOf(@field(T, decl.name)) == type) {
            switch (@typeInfo(@field(T, decl.name))) {
                .@"struct", .@"enum", .@"union", .@"opaque" => refAllDeclsRecursive(@field(T, decl.name), depth - 1),
                else => {},
            }
        }
        _ = &@field(T, decl.name);
    }
}

var ran = false;

pub fn runTest(name: []const u8, code: [:0]const u8) !void {
    if (!ran) {
        utils.Arena.initScratch(1024 * 1024);
        ran = true;
    }

    const gpa = std.testing.allocator;

    test_util.testFmt(name, name, code) catch {};

    var out = std.ArrayList(u8).init(gpa);
    defer out.deinit();

    errdefer {
        const stderr = std.io.getStdErr();
        const colors = std.io.tty.detectConfig(stderr);
        test_util.testBuilder(name, code, gpa, stderr.writer().any(), colors, true) catch {};
    }

    try test_util.testBuilder(name, code, gpa, out.writer().any(), .no_color, false);

    if (!test_util.hasEnv("SKIP_DIFF"))
        try test_util.checkOrUpdatePrintTest(name, out.items);
}

pub fn runFuzzFindingTest(name: []const u8, code: []const u8) !void {
    utils.Arena.initScratch(1024 * 1024 * 10);
    defer utils.Arena.deinitScratch();

    const gpa = std.testing.allocator;

    std.debug.print("{s}\n", .{code});

    //errdefer {
    //const stderr = std.io.getStdErr();
    //const colors = std.io.tty.detectConfig(stderr);
    //test_util.testBuilder(name, code, gpa, stderr.writer().any(), colors, true) catch {};
    //}

    try test_util.testBuilder(name, code, gpa, std.io.null_writer.any(), .no_color, false);
}

pub fn runVendoredTest(path: []const u8) !void {
    utils.Arena.initScratch(1024 * 1024);
    defer utils.Arena.deinitScratch();
    try test_util.runVendoredTest(std.testing.allocator, path);
}
