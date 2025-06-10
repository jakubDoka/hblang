const std = @import("std");
pub const utils = root.utils;
pub const root = @import("hb");
pub const test_util = root.test_utils;
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
        utils.Arena.initScratch(1024 * 1024 * 10);
        ran = true;
    }

    const gpa = std.testing.allocator;

    const stderr = std.io.getStdErr();
    const colors = std.io.tty.detectConfig(stderr);

    const failed_fmt = test_util.testFmt(name, name, code, stderr.writer().any(), colors);

    if (true) {
        const target = "hbvm-ableos";
        var hbvm = root.hbvm.HbvmGen{ .gpa = gpa };
        defer hbvm.deinit();
        try runMachineTest(
            name,
            target,
            code,
            .init(target, &hbvm),
            .ableos,
            gpa,
            stderr.writer().any(),
            colors,
        );
    }

    if (true) {
        if (std.mem.indexOf(u8, name, "float") != null) return;

        const target = "x86_64-linux";
        var x86_64 = root.x86_64.X86_64Gen{ .gpa = gpa, .object_format = .elf };
        defer x86_64.deinit();
        try runMachineTest(
            name,
            target,
            code,
            .init(target, &x86_64),
            .systemv,
            gpa,
            stderr.writer().any(),
            colors,
        );
    }

    try failed_fmt;
}

pub fn runMachineTest(
    name: []const u8,
    category: []const u8,
    code: [:0]const u8,
    machine: root.backend.Machine,
    abi: root.frontend.Types.Abi,
    gpa: std.mem.Allocator,
    out: std.io.AnyWriter,
    color: std.io.tty.Config,
) !void {
    var output = std.ArrayList(u8).init(gpa);
    defer output.deinit();

    errdefer {
        test_util.testBuilder(
            name,
            code,
            category,
            gpa,
            out,
            machine,
            abi,
            color,
            true,
        ) catch unreachable;
    }

    try test_util.testBuilder(
        name,
        code,
        category,
        gpa,
        output.writer().any(),
        machine,
        abi,
        .no_color,
        false,
    );

    if (!test_util.hasEnv("SKIP_DIFF"))
        try test_util.checkOrUpdatePrintTest(name, category, output.items, out, color);
}

pub fn runFuzzFindingTest(name: []const u8, code: [:0]const u8) !void {
    utils.Arena.initScratch(1024 * 1024 * 10);
    defer utils.Arena.deinitScratch();

    const gpa = std.testing.allocator;

    var tmp = utils.Arena.scrath(null);
    const ast = try root.frontend.Ast.init(tmp.arena, .{
        .path = name,
        .code = code,
        .diagnostics = std.io.getStdErr().writer().any(),
    });

    var buf = std.ArrayList(u8).init(tmp.arena.allocator());
    try ast.fmt(&buf);

    std.debug.print("{s}\n", .{buf.items});

    //errdefer {
    //const stderr = std.io.getStdErr();
    //const colors = std.io.tty.detectConfig(stderr);
    //test_util.testBuilder(name, code, gpa, stderr.writer().any(), colors, true) catch {};
    //}

    var hbvm = root.hbvm.HbvmGen{ .gpa = gpa };

    try test_util.testBuilder(
        name,
        code,
        "hbvm-ableos",
        gpa,
        std.io.null_writer.any(),
        .init("hbvm-ableos", &hbvm),
        .ableos,
        .no_color,
        false,
    );
}

pub fn runVendoredTest(path: []const u8) !void {
    // TODO: fix
    if (std.mem.indexOf(u8, path, "struct-niches.hb") != null) return;
    if (std.mem.indexOf(u8, path, "float") != null) return;
    if (std.mem.indexOf(u8, path, "inf") != null) return;

    utils.Arena.initScratch(1024 * 1024 * 32);
    defer utils.Arena.deinitScratch();
    try test_util.runVendoredTest(std.testing.allocator, path, "hbvm-ableos");
    //try test_util.runVendoredTest(std.testing.allocator, path, "x86_64-linux");
}
