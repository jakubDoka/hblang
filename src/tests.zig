const std = @import("std");
pub const utils = root.utils;
pub const root = @import("hb");
pub const test_util = root.test_utils;
pub const fuzz = @import("fuzz.zig");
pub const Regalloc = root.backend.Regalloc;

comptime {
    @setEvalBranchQuota(3000);
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
        utils.Arena.initScratch(1024 * 1024 * 16);
        ran = true;
    }

    const gpa = std.testing.allocator;

    const stderr = std.io.getStdErr();
    const colors = std.io.tty.detectConfig(stderr);

    const failed_fmt = test_util.testFmt(name, name, code, stderr.writer().any(), colors);
    var pool = utils.Pool{ .arena = utils.Arena.init(1024 * 1024 * 16) };
    {
        var hbvm = root.hbvm.HbvmGen{ .gpa = &pool };
        var hbvm2 = root.hbvm.HbvmGen{ .gpa = &pool };
        var x86_64 = root.x86_64.X86_64Gen{ .gpa = &pool, .object_format = .elf };
        var x86_642 = root.x86_64.X86_64Gen{ .gpa = &pool, .object_format = .elf };

        const tests = [_]struct {
            []const u8,
            root.backend.Machine,
            root.backend.Machine.OptOptions,
            root.frontend.Types.Abi,
        }{
            .{ "hbvm-ableos", .init("hbvm-ableos", &hbvm), .all, .ableos },
            .{ "hbvm-ableos-no-opts", .init("hbvm-ableos-no-opts", &hbvm2), .none, .ableos },
            .{ "x86_64-linux", .init("x86_64-linux", &x86_64), .all, .systemv },
            .{ "x86_64-linux-no-opts", .init("x86_64-linux-no-opts", &x86_642), .none, .systemv },
        };

        for (tests) |tst| {
            const target, var machine, const opts, const abi = tst;
            defer machine.deinit();
            if (abi.cc == .systemv and std.mem.indexOf(u8, name, "sse") != null) return;
            try runMachineTest(
                name,
                target,
                code,
                machine,
                abi,
                opts,
                gpa,
                stderr.writer().any(),
                colors,
            );
        }
    }

    try failed_fmt;
}

pub fn runMachineTest(
    name: []const u8,
    category: []const u8,
    code: [:0]const u8,
    machine: root.backend.Machine,
    abi: root.frontend.Types.Abi,
    opts: root.backend.Machine.OptOptions,
    gpa: std.mem.Allocator,
    out: std.io.AnyWriter,
    color: std.io.tty.Config,
) !void {
    if (false) std.debug.print("{s}\n", .{category});
    var output = std.ArrayList(u8).init(gpa);
    defer output.deinit();

    errdefer |err| {
        if (err != error.TestFailed)
            test_util.checkOrUpdatePrintTest(name, category, output.items, out, color) catch {};
        test_util.testBuilder(
            name,
            code,
            category,
            gpa,
            out,
            machine,
            opts,
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
        opts,
        abi,
        .no_color,
        false,
    );

    if (!test_util.hasEnv("SKIP_DIFF"))
        try test_util.checkOrUpdatePrintTest(name, category, output.items, out, color);
}

pub fn runFuzzFindingTest(name: []const u8, code: [:0]const u8) !void {
    if (true) return;
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
        .all,
        .ableos,
        .no_color,
        false,
    );
}

pub fn runVendoredTest(path: []const u8) !void {
    if (std.mem.indexOf(u8, path, "inf") != null) return;

    utils.Arena.initScratch(1024 * 1024 * 32);
    defer utils.Arena.deinitScratch();
    try test_util.runVendoredTest(path, "hbvm-ableos", .all);
    try test_util.runVendoredTest(path, "hbvm-ableos-no-opts", .none);
    try test_util.runVendoredTest(path, "x86_64-linux", .all);
    try test_util.runVendoredTest(path, "x86_64-linux-no-opts", .none);
}
