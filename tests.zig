const std = @import("std");
pub const Ast = @import("parser.zig");
pub const Vm = @import("Vm.zig");
pub const Builder = @import("Builder.zig");
pub const Codegen = @import("Codegen.zig");
pub const HbvmGen = @import("HbvmGen.zig");
pub const Types = @import("Types.zig");
pub const Regalloc = @import("Regalloc.zig");
pub const graph = @import("graph.zig");
pub const Mach = @import("Mach.zig");

test {
    _ = @import("zig-out/tests.zig");
    _ = @import("zig-out/vendored_tests.zig");
    _ = @import("fuzz.zig").main;
    std.testing.refAllDeclsRecursive(@This());
}

pub fn runTest(name: []const u8, code: []const u8) !void {
    const gpa = std.testing.allocator;

    try testFmt(name, name, code);

    var out = std.ArrayList(u8).init(gpa);
    defer out.deinit();

    errdefer {
        const stderr = std.io.getStdErr();
        const colors = std.io.tty.detectConfig(stderr);
        testBuilder(name, code, gpa, stderr.writer().any(), colors) catch unreachable;
    }

    try testBuilder(name, code, gpa, out.writer().any(), .no_color);

    try checkOrUpdatePrintTest(name, out.items);
}

pub fn runVendoredTest(path: []const u8) !void {
    _ = path;
}

inline fn header(comptime name: []const u8, writer: anytype, corors: std.io.tty.Config) !void {
    const side = "========";
    const msg = "\n" ++ side ++ " " ++ name ++ " " ++ side ++ "\n";
    try corors.setColor(writer, .dim);
    try writer.writeAll(msg);
    try corors.setColor(writer, .reset);
}

pub fn testBuilder(
    name: []const u8,
    code: []const u8,
    gpa: std.mem.Allocator,
    output: std.io.AnyWriter,
    colors: std.io.tty.Config,
) !void {
    var ast = try Ast.init(name, code, gpa);
    defer ast.deinit(gpa);

    const main = for (ast.decls) |d| {
        if (std.mem.eql(u8, ast.tokenSrc(d.name.index), "main")) break d.expr;
    } else unreachable;
    const fn_ast = ast.exprs.get(main).BinOp.rhs;

    var types = Types.init(gpa, &.{ast});
    defer types.deinit();

    var cg = Codegen.init(gpa, &types, output);
    defer cg.deinit();

    _ = types.addFunc(.root, ast.posOf(main), fn_ast);

    var hbgen = HbvmGen.init(std.ArrayList(u8).init(gpa));
    var gen = Mach.init(&hbgen);

    while (types.func_worklist.popOrNull()) |func| {
        try header("SOURCE", output, colors);
        var out_fmt = std.ArrayList(u8).init(gpa);
        defer out_fmt.deinit();
        try ast.fmtExpr(&out_fmt, types.get(func).ast);
        try output.writeAll(out_fmt.items);

        try header("UNSCHEDULED SON", output, colors);
        try cg.build(.root, func);
        defer cg.bl.func.reset();

        const fnc: *graph.Func(HbvmGen.Node) = @ptrCast(&cg.bl.func);
        fnc.fmtUnscheduled(output, colors);

        try header("OPTIMIZED SON", output, colors);
        fnc.iterPeeps(1000, @TypeOf(fnc.*).idealizeDead);
        fnc.mem2reg();
        fnc.iterPeeps(1000, @TypeOf(fnc.*).idealize);
        fnc.fmtUnscheduled(output, colors);

        try header("SCHEDULED SON", output, colors);

        fnc.gcm();
        fnc.fmtScheduled(output, colors);

        const tf = types.get(func);
        gen.emitFunc(&cg.bl.func, .{
            .id = @intFromEnum(func),
            .name = types.getFile(tf.file).tokenSrc(tf.name.index),
            .optimizations = .none,
        });
    }

    try header("CODEGEN", output, colors);
    gen.disasm(output, colors);
    var out = gen.finalize();
    defer out.deinit();

    var vm = Vm{};
    vm.fuel = 1000;
    vm.ip = 0;

    try header("EXECUTION", output, colors);
    var stack: [1024 * 10]u8 = undefined;
    vm.regs.set(.stack_addr, stack.len);
    var ctx = Vm.SafeContext{
        .writer = output,
        .color_cfg = colors,
        .code = out.items,
        .memory = &stack,
    };
    try std.testing.expectEqual(.tx, vm.run(&ctx));
}

pub fn testFmt(name: []const u8, path: []const u8, code: []const u8) !void {
    const gpa = std.testing.allocator;

    var ast = try Ast.init(path, code, gpa);
    defer ast.deinit(gpa);

    const ast_overhead = @as(f64, @floatFromInt(ast.exprs.store.items.len)) /
        @as(f64, @floatFromInt(ast.source.len));
    if (ast_overhead > 4.0) {
        std.debug.print(
            "\n{s} is too large ({d} bytes, {any} ratio)\n",
            .{ name, ast.source.len, ast_overhead },
        );
    }

    var fmtd = std.ArrayList(u8).init(gpa);
    defer fmtd.deinit();

    try ast.fmt(&fmtd);

    var dir = std.testing.tmpDir(.{});
    defer dir.cleanup();

    const old, const new = .{
        try std.mem.concat(gpa, u8, &.{ name, ".old.txt" }),
        try std.mem.concat(gpa, u8, &.{ name, ".new.txt" }),
    };
    defer gpa.free(old);
    defer gpa.free(new);

    try dir.dir.writeFile(.{ .sub_path = new, .data = std.mem.trim(u8, fmtd.items, "\n") });
    try dir.dir.writeFile(.{ .sub_path = old, .data = std.mem.trim(u8, code, "\n") });
    try runDiff(gpa, dir, old, new);
}

pub fn runDiff(gpa: std.mem.Allocator, tmp: std.testing.TmpDir, old: []const u8, new: []const u8) !void {
    var child = std.process.Child.init(&.{ "diff", "--unified", "--color", old, new }, gpa);
    child.cwd = try tmp.dir.realpathAlloc(gpa, ".");
    defer gpa.free(child.cwd.?);
    child.stdout_behavior = .Pipe;
    child.stderr_behavior = .Pipe;

    try child.spawn();

    const stdout = try child.stderr.?.readToEndAlloc(gpa, 1024 * 100);
    defer gpa.free(stdout);
    const stderr = try child.stdout.?.readToEndAlloc(gpa, 1024 * 100);
    defer gpa.free(stderr);

    const exit = (try child.wait()).Exited;
    if (exit != 0) {
        const new_data = try tmp.dir.readFileAlloc(gpa, new, 1024 * 1024);
        defer gpa.free(new_data);
        const old_data = try tmp.dir.readFileAlloc(gpa, old, 1024 * 1024);
        defer gpa.free(old_data);
        const new_line_count: isize = @intCast(std.mem.count(u8, new_data, "\n"));
        const old_line_count: isize = @intCast(std.mem.count(u8, old_data, "\n"));
        std.debug.print("line count change: {d}\n", .{new_line_count - old_line_count});
        if (stdout.len > 0) std.debug.print("stdout:\n{s}", .{stdout});
        if (stderr.len > 0) std.debug.print("stderr:\n{s}", .{stderr});
    }
    try std.testing.expectEqual(0, exit);
}

fn checkOrUpdatePrintTest(name: []const u8, output: []const u8) !void {
    const gpa = std.testing.allocator;
    var tests = try std.fs.cwd().openDir("tests", .{});
    defer tests.close();
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const old, const new = .{
        try std.mem.concat(gpa, u8, &.{ name, "tmp.txt" }),
        try std.mem.concat(gpa, u8, &.{ name, ".txt" }),
    };
    defer gpa.free(old);
    defer gpa.free(new);

    if (hasEnv("PT_UPDATE")) {
        try tests.writeFile(.{
            .sub_path = new,
            .data = std.mem.trim(u8, output, "\n"),
        });
    } else {
        try tmp.dir.writeFile(.{
            .sub_path = new,
            .data = std.mem.trim(u8, output, "\n"),
        });

        tests.copyFile(new, tmp.dir, old, .{}) catch |err| switch (err) {
            error.FileNotFound => return error.NewTestFound,
            else => return err,
        };

        try runDiff(gpa, tmp, old, new);
    }
}

fn hasEnv(name: []const u8) bool {
    const update = std.process.getEnvVarOwned(std.testing.allocator, name) catch "";
    defer std.testing.allocator.free(update);
    return update.len > 0;
}
