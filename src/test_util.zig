const std = @import("std");
const Vm = root.hbvm.Vm;
const HbvmGen = root.hbvm.HbvmGen;
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Ast = root.frontend.Ast;
const Codegen = root.frontend.Codegen;
const Types = root.frontend.Types;
const root = @import("hb");
const diff = root.diff;
const utils = root.utils;
pub const static_anal = root.backend.static_anal;

pub const Expectations = struct {
    return_value: u64 = 0,
    should_error: bool = false,
    times_out: bool = false,
    unreaches: bool = false,

    pub fn init(ast: *const Ast, gpa: std.mem.Allocator) Expectations {
        errdefer unreachable;

        var slf: Expectations = .{};

        const idx = Ast.Index.build(ast, ast.items, gpa);

        if (idx.search(@as([]const u8, "expectations"))) |d| {
            const decl = ast.exprs.getTyped(.Decl, d[0]).?.value;
            const ctor = ast.exprs.getTyped(.Ctor, decl).?;
            for (ast.exprs.view(ctor.fields)) |field| {
                const value = ast.exprs.get(field.value);
                const fname = ast.tokenSrc(field.pos.index);

                inline for (std.meta.fields(Expectations)) |f| {
                    if (std.mem.eql(u8, fname, f.name)) @field(slf, f.name) =
                        switch (f.type) {
                            u64 => @bitCast(try std.fmt.parseInt(
                                i64,
                                ast.tokenSrc(value.Integer.pos.index),
                                10,
                            )),
                            bool => value.Bool.value,
                            []const Ast.Id => ast.exprs.view(value.Tupl.fields),
                            else => comptime unreachable,
                        };
                }
            }
        }

        return slf;
    }

    pub fn assert(expectations: Expectations, res: anyerror!usize) !void {
        const ret = res catch |err| switch (err) {
            error.Timeout => {
                try std.testing.expect(expectations.times_out);
                return;
            },
            error.Unreachable => {
                try std.testing.expect(expectations.unreaches);
                return;
            },
            else => return err,
        };

        try std.testing.expectEqual(expectations.return_value, ret);
    }
};

pub fn runVendoredTest(path: []const u8, target: []const u8, optimizations: Mach.OptOptions) !void {
    var ast = try root.compile(.{
        .diagnostics = std.io.getStdErr().writer().any(),
        .colors = std.io.tty.detectConfig(std.io.getStdErr()),
        .output = std.io.null_writer.any(),
        .mangle_terminal = true,
        .vendored_test = true,
        .root_file = path,
        .target = target,
        .optimizations = optimizations,
    });
    defer ast.arena.deinit();
}

pub inline fn header(comptime name: []const u8, writer: anytype, corors: std.io.tty.Config) !void {
    const side = "========";
    const msg = "\n" ++ side ++ " " ++ name ++ " " ++ side ++ "\n";
    try corors.setColor(writer, .dim);
    try writer.writeAll(msg);
    try corors.setColor(writer, .reset);
}

pub fn parseExample(arena: *utils.Arena, name: []const u8, code: []const u8, output: std.io.AnyWriter) ![]Ast {
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

    var tmp = utils.Arena.scrath(arena);
    defer tmp.deinit();
    var files = std.ArrayList(FileRecord).init(tmp.arena.allocator());
    defer files.deinit();

    const signifier = "// in: ";
    var prev_name: []const u8 = name;
    var prev_end: usize = 0;
    while (prev_end < code.len) {
        const next_end = if (std.mem.indexOf(u8, code[prev_end..], signifier)) |idx| prev_end + idx else code.len;
        const fr = FileRecord{
            .path = prev_name,
            .source = arena.allocator().dupeZ(u8, std.mem.trim(u8, code[prev_end..next_end], "\t \n")) catch unreachable,
        };
        try files.append(fr);
        prev_end = next_end + signifier.len;
        if (prev_end < code.len) if (std.mem.indexOf(u8, code[prev_end..], "\n")) |idx| {
            prev_name = code[prev_end..][0..idx];
            prev_end += idx + 1;
        };
    }

    var loader = KnownLoader{ .files = files.items };
    const asts = arena.alloc(Ast, files.items.len);
    for (asts, files.items, 0..) |*ast, fr, i| {
        if (std.mem.endsWith(u8, fr.path, ".hb") or i == 0) {
            ast.* = try Ast.init(arena, .{
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
    target: []const u8,
    gpa: std.mem.Allocator,
    output: std.io.AnyWriter,
    gen: root.backend.Machine,
    opts: root.backend.Machine.OptOptions,
    abi: root.frontend.Types.Abi,
    colors: std.io.tty.Config,
    verbose: bool,
) !void {
    var type_system_arena = utils.Arena.init(1024 * 1024);

    const asts = parseExample(&type_system_arena, name, code, output) catch return;
    const ast = asts[0];

    var func_arena = utils.Arena.scrath(null);
    defer func_arena.deinit();

    const types = Types.init(type_system_arena, asts, output);
    types.target = target;
    defer types.deinit();

    const errored = Codegen.emitReachable(
        func_arena.arena,
        types,
        abi,
        gen,
        opts,
        true,
        .{ .verbose = verbose, .colors = colors, .output = output },
    );

    const expectations: Expectations = .init(&ast, func_arena.arena.allocator());

    if (std.mem.endsWith(u8, target, "no-opts") and expectations.should_error) {
        return;
    }

    if (errored) {
        try std.testing.expect(expectations.should_error);
        return;
    }

    var anal_errors = std.ArrayListUnmanaged(root.backend.static_anal.Error){};
    var optimizations = opts;
    optimizations.verbose = verbose;
    optimizations.arena = func_arena.arena;
    optimizations.error_buf = &anal_errors;

    if (verbose) try header("CODEGEN", output, colors);
    var out = gen.finalizeBytes(.{
        .gpa = gpa,
        .optimizations = optimizations,
    });
    defer out.deinit(gpa);

    if (types.dumpAnalErrors(&anal_errors)) {
        try std.testing.expect(expectations.should_error);
        return;
    }

    gen.disasm(.{
        .name = name,
        .bin = out.items,
        .out = output,
        .colors = colors,
    });

    if (std.mem.indexOf(u8, name, "infinite") != null) return;

    try expectations.assert(gen.run(.{
        .name = name,
        .code = out.items,
        .colors = colors,
        .output = if (verbose) output else std.io.null_writer.any(),
    }));
}

pub const stack_size = 1024 * 10;

pub fn testFmt(
    name: []const u8,
    path: []const u8,
    code: [:0]const u8,
    out: std.io.AnyWriter,
    color: std.io.tty.Config,
) !void {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const gpa = tmp.arena.allocator();

    var ast = try Ast.init(tmp.arena, .{ .path = path, .code = code, .ignore_errors = true });

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

    if (!std.mem.eql(
        u8,
        std.mem.trim(u8, code, "\n"),
        std.mem.trim(u8, fmtd.items, "\n"),
    )) {
        try diff.printDiff(fmtd.items, code, gpa, out, color);
        return error.TestFailed;
    }
}

pub fn checkOrUpdatePrintTest(
    name: []const u8,
    category: []const u8,
    output: []const u8,
    out: std.io.AnyWriter,
    color: std.io.tty.Config,
) !void {
    var tests_root = try std.fs.cwd().openDir("tests", .{});
    defer tests_root.close();

    var tests = try tests_root.openDir(category, .{});
    defer tests.close();

    var scrath = utils.Arena.scrath(null);
    defer scrath.deinit();
    const gpa = scrath.arena.allocator();

    const new = try std.mem.concat(gpa, u8, &.{ name, ".txt" });

    if (hasEnv("PT_UPDATE")) {
        try tests.writeFile(.{
            .sub_path = new,
            .data = std.mem.trim(u8, output, "\n"),
        });
    } else {
        const old = tests.readFileAlloc(gpa, new, 1024 * 1024) catch |err| switch (err) {
            error.FileNotFound => return error.NewTestFound,
            else => return err,
        };

        if (!std.mem.eql(
            u8,
            std.mem.trim(u8, output, "\n"),
            std.mem.trim(u8, old, "\n"),
        )) {
            try diff.printDiff(old, output, gpa, out, color);
            return error.TestFailed;
        }
    }
}

pub fn hasEnv(name: []const u8) bool {
    const update = std.process.getEnvVarOwned(std.testing.allocator, name) catch "";
    defer std.testing.allocator.free(update);
    return update.len > 0;
}
