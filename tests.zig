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

test {
    _ = @import("zig-out/tests.zig");
    _ = @import("zig-out/vendored_tests.zig");
    std.testing.refAllDeclsRecursive(@This());
}

pub fn runTest(name: []const u8, code: []const u8) !void {
    root.Arena.initScratch(1024 * 1024);
    defer root.Arena.deinitScratch();

    const gpa = std.testing.allocator;

    try testFmt(name, name, code);

    var out = std.ArrayList(u8).init(gpa);
    defer out.deinit();

    errdefer {
        const stderr = std.io.getStdErr();
        const colors = std.io.tty.detectConfig(stderr);
        testBuilder(name, code, gpa, stderr.writer().any(), colors, true) catch unreachable;
    }

    try testBuilder(name, code, gpa, out.writer().any(), .no_color, false);

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
    verbose: bool,
) !void {
    const FileRecord = struct {
        path: []const u8,
        source: []const u8,
    };

    const KnownLoader = struct {
        files: []const FileRecord,

        pub fn load(self: *@This(), opts: Ast.Loader.LoadOptions) Types.File {
            return for (self.files, 0..) |fr, i| {
                if (std.mem.eql(u8, fr.path, opts.path)) break @enumFromInt(i);
            } else unreachable;
        }
    };

    var files = std.ArrayList(FileRecord).init(gpa);
    defer files.deinit();

    const signifier = "// in: ";
    var prev_name: []const u8 = name;
    var prev_end: usize = 0;
    while (prev_end < code.len) {
        const next_end = if (std.mem.indexOf(u8, code[prev_end..], signifier)) |idx| prev_end + idx else code.len;
        const fr = FileRecord{
            .path = prev_name,
            .source = std.mem.trim(u8, code[prev_end..next_end], "\t \n"),
        };
        try files.append(fr);
        prev_end = next_end + signifier.len;
        if (prev_end < code.len) if (std.mem.indexOf(u8, code[prev_end..], "\n")) |idx| {
            prev_name = code[prev_end..][0..idx];
            prev_end += idx + 1;
        };
    }

    var loader = KnownLoader{ .files = files.items };
    const asts = gpa.alloc(Ast, files.items.len) catch unreachable;
    defer {
        for (asts) |*a| a.deinit(gpa);
        gpa.free(asts);
    }
    for (asts, files.items, 0..) |*ast, fr, i| {
        ast.* = try Ast.init(gpa, @enumFromInt(i), fr.path, fr.source, .init(&loader));
    }

    const ast = asts[0];

    var ret: u64 = 0;
    if (ast.findDecl(ast.items, "expectations")) |d| {
        const decl = ast.exprs.get(d).BinOp.rhs;
        const ctor = ast.exprs.get(decl).Ctor;
        for (ast.exprs.view(ctor.fields)) |f| {
            const field = ast.exprs.get(f).BinOp;
            const value = ast.exprs.get(field.rhs);

            if (std.mem.eql(u8, ast.tokenSrc(ast.exprs.get(field.lhs).Tag.index + 1), "return_value")) {
                ret = @bitCast(try std.fmt.parseInt(i64, ast.tokenSrc(value.Integer.index), 10));
            }
        }
    }

    const main = ast.findDecl(ast.items, "main").?;
    const fn_ast = ast.exprs.get(main).BinOp.rhs;

    var types = Types.init(gpa, asts, output);
    defer types.deinit();

    var func_arena = root.Arena.scrath(null);
    defer func_arena.deinit();

    var cg = Codegen.init(func_arena.arena, func_arena.arena, &types, .runtime);
    defer cg.deinit();

    const entry = cg.resolveTy(.{ .scope = types.getScope(.root), .name = "main" }, fn_ast).data().Func;
    cg.work_list.appendAssumeCapacity(.{ .Func = entry });

    var hbgen = HbvmGen.init(gpa);
    var gen = Mach.init(&hbgen);

    while (cg.nextTask()) |task| switch (task) {
        .Func => |func| {
            var tmp = cg.bl.func.arena.checkpoint();
            defer {
                tmp.deinit();
                cg.bl.func.reset();
            }

            if (verbose) {
                if (verbose) try header("SOURCE", output, colors);
                var out_fmt = std.ArrayList(u8).init(gpa);
                defer out_fmt.deinit();
                try asts[@intFromEnum(func.key.file)].fmtExpr(&out_fmt, func.key.ast);
                try output.writeAll(out_fmt.items);
            }

            if (verbose) try header("UNSCHEDULED SON", output, colors);
            try cg.build(func);

            const fnc: *graph.Func(HbvmGen.Node) = @ptrCast(&cg.bl.func);
            if (verbose) fnc.fmtUnscheduled(output, colors);

            if (verbose) try header("OPTIMIZED SON", output, colors);
            fnc.iterPeeps(10000, @TypeOf(fnc.*).idealizeDead);
            fnc.mem2reg();
            fnc.iterPeeps(10000, @TypeOf(fnc.*).idealize);
            if (verbose) fnc.fmtUnscheduled(output, colors);

            if (verbose) try header("SCHEDULED SON", output, colors);
            fnc.gcm();
            if (verbose) fnc.fmtScheduled(output, colors);

            gen.emitFunc(&cg.bl.func, .{
                .id = func.id,
                .name = func.name,
                .entry = func.id == entry.id,
                .optimizations = .none,
            });
        },
        .Global => |g| {
            gen.emitData(.{
                .name = g.name,
                .id = g.id,
                .value = .{ .init = g.data },
            });
        },
    };

    if (verbose) try header("CODEGEN", output, colors);
    const code_len = hbgen.link(true);
    gen.disasm(output, colors);
    var out = gen.finalize();
    defer out.deinit();

    const stack_size = 1024 * 10;
    const stack_end = stack_size - out.items.len;

    var stack: [stack_size]u8 = undefined;

    @memcpy(stack[stack_end..], out.items);

    var vm = Vm{};
    vm.ip = stack_end;
    vm.fuel = 1024 * 10;
    vm.regs.set(.stack_addr, stack_end);
    var ctx = Vm.SafeContext{
        .writer = if (verbose) output else std.io.null_writer.any(),
        .color_cfg = colors,
        .memory = &stack,
        .code_start = stack_end,
        .code_end = stack_end + code_len,
    };
    if (verbose) try header("EXECUTION", output, colors);

    if (vm.run(&ctx) catch unreachable != isa.Op.tx) return error.TestExpectedEqual;
    if (vm.regs.get(.ret(0)) != ret) return error.TestExpectedEqual;
}

pub fn testFmt(name: []const u8, path: []const u8, code: []const u8) !void {
    const gpa = std.testing.allocator;

    var ast = try Ast.init(gpa, @enumFromInt(0), path, code, .noop);
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
