const std = @import("std");
const isa = @import("isa.zig");
pub const Ast = @import("Ast.zig");
pub const Vm = @import("Vm.zig");
pub const Builder = @import("Builder.zig");
pub const Codegen = @import("Codegen.zig");
pub const HbvmGen = @import("HbvmGen.zig");
pub const Types = @import("Types.zig");
pub const Regalloc = @import("Regalloc.zig");
pub const graph = @import("graph.zig");
pub const Mach = @import("Mach.zig");
pub const root = @import("utils.zig");

inline fn header(comptime name: []const u8, writer: anytype, corors: std.io.tty.Config) !void {
    const side = "========";
    const msg = "\n" ++ side ++ " " ++ name ++ " " ++ side ++ "\n";
    try corors.setColor(writer, .dim);
    try writer.writeAll(msg);
    try corors.setColor(writer, .reset);
}

pub fn parseExample(gpa: std.mem.Allocator, name: []const u8, code: []const u8, output: std.io.AnyWriter) ![]Ast {
    const FileRecord = struct {
        path: []const u8,
        source: [:0]const u8,
    };

    const KnownLoader = struct {
        files: []const FileRecord,

        pub fn load(self: *@This(), opts: Ast.Loader.LoadOptions) ?Types.File {
            return for (self.files, 0..) |fr, i| {
                if (std.mem.eql(u8, fr.path, opts.path)) break @enumFromInt(i);
            } else {
                return null;
            };
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
            .source = gpa.dupeZ(u8, std.mem.trim(u8, code[prev_end..next_end], "\t \n")) catch unreachable,
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
    errdefer gpa.free(asts);
    for (asts, files.items, 0..) |*ast, fr, i| {
        if (std.mem.endsWith(u8, fr.path, ".hb") or i == 0) {
            ast.* = try Ast.init(gpa, .{
                .current = @enumFromInt(i),
                .path = fr.path,
                .code = fr.source,
                .loader = .init(&loader),
                .diagnostics = output,
            });
        } else {
            ast.* = .{
                .path = fr.path,
                .source = fr.source,
                .root_struct = .zeroSized(.Void),
                .items = .{},
                .exprs = .{},
            };
        }
    }

    return asts;
}

pub fn testBuilder(
    name: []const u8,
    code: []const u8,
    gpa: std.mem.Allocator,
    output: std.io.AnyWriter,
    colors: std.io.tty.Config,
    verbose: bool,
) !void {
    const asts = try parseExample(gpa, name, code, output);
    const ast = asts[0];

    defer {
        for (asts) |*a| {
            gpa.free(a.source);
            a.deinit(gpa);
        }
        gpa.free(asts);
    }

    var func_arena = root.Arena.scrath(null);
    defer func_arena.deinit();

    var ret: u64 = 0;
    var should_error: bool = false;
    var times_out: bool = false;
    var unreaches: bool = false;
    var ecalls: []const Ast.Id = &.{};
    if (ast.findDecl(ast.items, "expectations", func_arena.arena.allocator())) |d| {
        const decl = ast.exprs.getTyped(.BinOp, d[0]).?.rhs;
        const ctor = ast.exprs.getTyped(.Ctor, decl).?;
        for (ast.exprs.view(ctor.fields)) |field| {
            const value = ast.exprs.get(field.value);
            const fname = ast.tokenSrc(field.pos.index);

            if (std.mem.eql(u8, fname, "return_value")) {
                ret = @bitCast(try std.fmt.parseInt(i64, ast.tokenSrc(value.Integer.pos.index), 10));
            }

            if (std.mem.eql(u8, fname, "should_error")) {
                should_error = value.Bool.value;
            }

            if (std.mem.eql(u8, fname, "times_out")) {
                times_out = value.Bool.value;
            }

            if (std.mem.eql(u8, fname, "unreaches")) {
                unreaches = value.Bool.value;
            }

            if (std.mem.eql(u8, fname, "ecalls")) {
                ecalls = ast.exprs.view(value.Tupl.fields);
            }
        }
    }

    var types = Types.init(gpa, asts, output);
    defer types.deinit();

    var cg = Codegen.init(gpa, func_arena.arena, &types, .runtime);
    defer cg.deinit();
    cg.scope = .{};

    const entry = try cg.getEntry(.root, "main");
    cg.work_list.appendAssumeCapacity(.{ .Func = entry });

    var hbgen = HbvmGen{ .gpa = gpa };
    defer hbgen.deinit();
    var gen = Mach.init(&hbgen);

    var syms = std.heap.ArenaAllocator.init(gpa);
    defer syms.deinit();

    var errored = false;
    while (cg.nextTask()) |task| switch (task) {
        .Func => |func| {
            defer {
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
            cg.build(func) catch {
                errored = true;
                continue;
            };

            const fnc: *graph.Func(HbvmGen.Node) = @ptrCast(&cg.bl.func);
            if (verbose) fnc.fmtUnscheduled(output, colors);

            if (verbose) try header("OPTIMIZED SON", output, colors);
            fnc.iterPeeps(10000, @TypeOf(fnc.*).idealizeDead);
            fnc.mem2reg.run();
            fnc.iterPeeps(10000, @TypeOf(fnc.*).idealize);
            fnc.iterPeeps(10000, HbvmGen.idealizeMach);
            if (verbose) fnc.fmtUnscheduled(output, colors);

            if (verbose) try header("SCHEDULED SON", output, colors);
            fnc.gcm.buildCfg();
            if (verbose) fnc.fmtScheduled(output, colors);

            gen.emitFunc(&cg.bl.func, .{
                .id = func.id,
                .name = try std.fmt.allocPrint(syms.allocator(), "{test}", .{Types.Id.init(.{ .Func = func }).fmt(&types)}),
                .entry = func.id == entry.id,
                .optimizations = .none,
            });
        },
        .Global => |g| {
            gen.emitData(.{
                .name = try std.fmt.allocPrint(syms.allocator(), "{test}", .{Types.Id.init(.{ .Global = g }).fmt(&types)}),
                .id = g.id,
                .value = .{ .init = g.data },
            });
        },
    };

    try std.testing.expectEqual(should_error, cg.errored);
    if (errored) {
        return;
    }

    if (verbose) try header("CODEGEN", output, colors);
    const code_len = hbgen.link(0, true);
    gen.disasm(output, colors);
    var out = gen.finalize();
    defer out.deinit(gpa);

    const stack_size = 1024 * 10;
    const stack_end = stack_size - out.items.len;

    var stack: [stack_size]u8 = undefined;

    @memcpy(stack[stack_end..], out.items);

    var vm = Vm{};
    vm.ip = stack_end;
    vm.fuel = 1024 * 10;
    @memset(&vm.regs.values, 0);
    vm.regs.set(.stack_addr, stack_end);
    var ctx = Vm.SafeContext{
        .writer = if (verbose) output else std.io.null_writer.any(),
        .color_cfg = colors,
        .memory = &stack,
        .code_start = stack_end,
        .code_end = stack_end + code_len,
    };
    if (verbose) try header("EXECUTION", output, colors);

    var eca_idx: usize = 0;
    while (true) switch (vm.run(&ctx) catch |err| switch (err) {
        error.Timeout => {
            try std.testing.expect(times_out);
            return;
        },
        error.Unreachable => {
            try std.testing.expect(unreaches);
            return;
        },
        else => unreachable,
    }) {
        .tx => break,
        .eca => {
            try std.testing.expect(eca_idx < ecalls.len);
            const curr_eca = ast.exprs.getTyped(.BinOp, ecalls[eca_idx]).?;

            for (ast.exprs.view(ast.exprs.getTyped(.Tupl, curr_eca.lhs).?.fields), 0..) |vl, i| {
                const value = try std.fmt.parseInt(u64, ast.tokenSrc(ast.exprs.getTyped(.Integer, vl).?.pos.index), 10);
                try std.testing.expectEqual(value, vm.regs.get(.arg(i)));
            }

            const ret_value = try std.fmt.parseInt(u64, ast.tokenSrc(ast.exprs.getTyped(.Integer, curr_eca.rhs).?.pos.index), 10);
            vm.regs.set(.ret(0), ret_value);

            eca_idx += 1;
        },
        else => unreachable,
    };

    if (vm.regs.get(.ret(0)) != ret) return error.TestExpectedEqual;
}

pub fn testFmt(name: []const u8, path: []const u8, code: [:0]const u8) !void {
    const gpa = std.testing.allocator;

    var ast = try Ast.init(gpa, .{ .path = path, .code = code });
    defer ast.deinit(gpa);

    const ast_overhead = @as(f64, @floatFromInt(ast.exprs.store.items.len)) /
        @as(f64, @floatFromInt(ast.source.len));
    if (ast_overhead > 5.0) {
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

pub fn checkOrUpdatePrintTest(name: []const u8, output: []const u8) !void {
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

pub fn hasEnv(name: []const u8) bool {
    const update = std.process.getEnvVarOwned(std.testing.allocator, name) catch "";
    defer std.testing.allocator.free(update);
    return update.len > 0;
}
