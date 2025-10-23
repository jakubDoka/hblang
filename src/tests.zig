const std = @import("std");
pub const utils = root.utils;
pub const root = @import("hb");
pub const test_util = root.test_utils;
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
        utils.Arena.initScratch(1024 * 1024 * 32);
        ran = true;
    }

    const gpa = std.testing.allocator;

    const stderr = std.fs.File.stderr();
    var stderr_writer = stderr.writer(&.{});
    const colors = std.io.tty.detectConfig(stderr);

    const failed_fmt = test_util.testFmt(name, name, code, &stderr_writer.interface, colors);
    {
        var hbvm = root.hbvm.HbvmGen{ .gpa = gpa };
        var hbvm_no_opt = root.hbvm.HbvmGen{ .gpa = gpa };
        var x86_64 = root.x86_64.X86_64Gen{ .gpa = gpa, .object_format = .elf };
        var x86_64_no_opt = root.x86_64.X86_64Gen{ .gpa = gpa, .object_format = .elf };
        var wasm = root.wasm.WasmGen{ .gpa = gpa };
        var wasm_no_opt = root.wasm.WasmGen{ .gpa = gpa };

        const tests = [_]struct {
            []const u8,
            *root.backend.Machine,
            root.backend.Machine.OptOptions.Mode,
            root.frontend.Types.Abi,
        }{
            .{ "wasm-freestanding", &wasm.mach, .release, .wasm },
            .{ "wasm-freestanding-no-opts", &wasm_no_opt.mach, .debug, .wasm },
            .{ "hbvm-ableos", &hbvm.mach, .release, .ableos },
            .{ "hbvm-ableos-no-opts", &hbvm_no_opt.mach, .debug, .ableos },
            .{ "x86_64-linux", &x86_64.mach, .release, .systemv },
            .{ "x86_64-linux-no-opts", &x86_64_no_opt.mach, .debug, .systemv },
        };

        for (tests[0..]) |tst| {
            const target, var machine, const opts, const abi = tst;
            //std.debug.print("{s}\n", .{target});
            defer machine.deinit();
            //if (std.mem.indexOf(u8, target, "x") != null) continue;
            if (abi.cc == .systemv and std.mem.indexOf(u8, name, "sse") != null) return;
            try runMachineTest(
                name,
                target,
                code,
                machine,
                abi,
                opts,
                gpa,
                &stderr_writer.interface,
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
    machine: *root.backend.Machine,
    abi: root.frontend.Types.Abi,
    opts: root.backend.Machine.OptOptions.Mode,
    gpa: std.mem.Allocator,
    out: *std.Io.Writer,
    color: std.io.tty.Config,
) !void {
    if (false) std.debug.print("{s}\n", .{category});
    var output = std.Io.Writer.Allocating.init(gpa);
    defer output.deinit();

    errdefer |err| {
        if (err != error.TestFailed)
            test_util.checkOrUpdatePrintTest(name, category, output.written(), out, color) catch {};
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
        &output.writer,
        machine,
        opts,
        abi,
        .no_color,
        false,
    );

    if (!test_util.hasEnv("SKIP_DIFF"))
        try test_util.checkOrUpdatePrintTest(name, category, output.written(), out, color);
}

pub fn runFuzzFindingTest(name: []const u8, code: [:0]const u8) !void {
    utils.Arena.initScratch(1024 * 1024 * 10);
    defer utils.Arena.deinitScratch();
    std.debug.print("{s}\n", .{code});

    const gpa = std.testing.allocator;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();
    var diagnostics = std.fs.File.stderr().writer(&.{});
    const ast = try root.frontend.Ast.init(tmp.arena, .{
        .path = name,
        .code = code,
        .diagnostics = &diagnostics.interface,
    });

    try ast.fmt(&diagnostics.interface);

    var hbvm = root.hbvm.HbvmGen{ .gpa = gpa };
    defer hbvm.deinit();

    try test_util.testBuilder(
        name,
        code,
        "hbvm-ableos",
        gpa,
        &diagnostics.interface,
        &hbvm.mach,
        .release,
        .ableos,
        .no_color,
        false,
    );
}

pub fn runVendoredTest(path: []const u8, projs: []const [2][]const u8) !void {
    if (std.mem.indexOf(u8, path, "inf") != null) return;
    if (std.mem.indexOf(u8, path, "struct-niches") != null) return;

    utils.Arena.initScratch(1024 * 1024 * 32);
    defer utils.Arena.deinitScratch();

    if (projs.len == 0) { // for hblsp tests
        _ = try test_util.runVendoredTest(path, projs, "hbvm-ableos", .release);
        _ = try test_util.runVendoredTest(path, projs, "hbvm-ableos-no-opts", .debug);

        if (false and std.mem.indexOf(u8, path, "almighty-ops") == null) {
            _ = try test_util.runVendoredTest(path, projs, "wasm-freestanding", .release);
            _ = try test_util.runVendoredTest(path, projs, "wasm-freestanding-no-opts", .debug);
        }
    }
    if (true) {
        _ = try test_util.runVendoredTest(path, projs, "x86_64-linux", .release);
        _ = try test_util.runVendoredTest(path, projs, "x86_64-linux-no-opts", .debug);
    }
}
