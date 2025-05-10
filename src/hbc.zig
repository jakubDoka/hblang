const std = @import("std");

const hb = @import("root.zig");
const static_anal = hb.backend.static_anal;
const Arena = hb.utils.Arena;

const max_file_len = std.math.maxInt(u31);

pub const CompileOptions = struct {
    gpa: std.mem.Allocator,
    diagnostics: std.io.AnyWriter = std.io.null_writer.any(),
    colors: std.io.tty.Config = .no_color,
    output: std.io.AnyWriter,
    raw_binary: bool = false,

    // #CLI start
    // #ARGS (main.hb)
    root_file: []const u8 = "main.hb",
    // #FLAGS (--help)
    help: bool = false, // print this help message
    fmt: bool = false, // format all files reachable from the root_file
    fmt_stdout: bool = false, // format only the root file and print it to stdout
    dump_asm: bool = false, // dump assembly of the program
    mangle_terminal: bool = false, // dump the executable even if colors are supported
    vendored_test: bool = false,
    // #OPTIONS (--target ableos)
    target: []const u8 = "ableos", // target triple to compile to (not used yet since we have only one target)
    extra_threads: usize = 0, // extra threads used for the compilation (not used yet)
    path_projections: std.StringHashMapUnmanaged([]const u8) = .{}, // can be specified multiple times
    // as `--path-projection name path`, when the `@use("name")` is encountered, its projected to `@use("path")`
    // #CLI end

    pub fn deinit(self: *CompileOptions) void {
        self.path_projections.deinit(self.gpa);
    }

    pub fn loadCli(self: *CompileOptions, arena: std.mem.Allocator) !void {
        var args = try std.process.ArgIterator.initWithAllocator(arena);
        _ = args.next();

        var i: usize = 0;
        while (args.next()) |a| {
            var arg: []const u8 = a[0..];
            if (!std.mem.startsWith(u8, arg, "--")) {
                switch (i) {
                    0 => self.root_file = arg,
                    else => {},
                }
                i += 1;
                continue;
            }

            arg = arg[2..];

            self.help = self.help or std.mem.eql(u8, arg, "help");
            self.fmt = self.fmt or std.mem.eql(u8, arg, "fmt");
            self.fmt_stdout = self.fmt_stdout or std.mem.eql(u8, arg, "fmt-stdout");
            self.dump_asm = self.dump_asm or std.mem.eql(u8, arg, "dump-asm");
            self.mangle_terminal = self.mangle_terminal or std.mem.eql(u8, arg, "mangle-terminal");
            self.vendored_test = self.vendored_test or std.mem.eql(u8, arg, "vendored-test");

            if (std.mem.eql(u8, arg, "target")) self.target = args.next() orelse {
                try self.diagnostics.writeAll("--target takes an argument");
                return;
            };

            if (std.mem.eql(u8, arg, "extra-threads")) {
                arg = args.next() orelse {
                    try self.diagnostics.writeAll("--extra-threads takes an integer argument");
                    return;
                };
                self.extra_threads = std.fmt.parseInt(usize, arg, 10) catch |err| {
                    try self.diagnostics.print("failed to parse --extra-threads argument: {s}", .{@errorName(err)});
                    return;
                };
            }

            if (std.mem.eql(u8, arg, "path-projection")) {
                const msg = "--path-projection takes two argumens: <key> <value>";
                const key = args.next() orelse {
                    try self.diagnostics.writeAll(msg);
                    return;
                };
                const value = args.next() orelse {
                    try self.diagnostics.writeAll(msg);
                    return;
                };
                try self.path_projections.put(self.gpa, key, value);
            }
        }
    }
};

pub fn compile(opts: CompileOptions) anyerror!struct {
    arena: Arena,
    ast: []const hb.frontend.Ast,
} {
    if (opts.help) {
        const help_str = comptime b: {
            const source = @embedFile("hbc.zig");
            const start_pat = "// #CLI start";
            const end_pat = "// #CLI end";
            const start = std.mem.indexOf(u8, source, start_pat).? + start_pat.len;
            const end = std.mem.indexOfPos(u8, source, start, end_pat).?;
            break :b std.mem.trimRight(u8, source[start..end], "\n\t\r ") ++ "";
        };

        try opts.diagnostics.writeAll(help_str);
        return error.Failed;
    }

    var ast_arena = Arena.init(1024 * 1024 * 20);
    errdefer ast_arena.deinit();

    if (opts.fmt_stdout) {
        const source = try std.fs.cwd().readFileAllocOptions(ast_arena.allocator(), opts.root_file, max_file_len, null, @alignOf(u8), 0);
        const ast = try hb.frontend.Ast.init(&ast_arena, .{
            .path = opts.root_file,
            .code = source,
            .diagnostics = opts.diagnostics,
        });

        var buf = std.ArrayList(u8).init(ast_arena.allocator());
        try ast.fmt(&buf);

        try opts.output.writeAll(buf.items);
        return error.Failed;
    }

    const asts, const base = try Loader.loadAll(&ast_arena, opts.path_projections, opts.root_file, opts.diagnostics) orelse {
        try opts.diagnostics.print("failed due to previous errors (codegen skipped)\n", .{});
        return error.Failed;
    };

    if (opts.fmt) {
        for (asts) |ast| {
            var tmp = Arena.scrath(null);
            defer tmp.deinit();

            var buf = std.ArrayList(u8).init(tmp.arena.allocator());
            try ast.fmt(&buf);

            const path = try std.fs.path.join(tmp.arena.allocator(), &.{ base, ast.path });
            try std.fs.cwd().writeFile(.{ .sub_path = path, .data = buf.items });
        }
        return .{ .ast = asts, .arena = ast_arena };
    }

    var types = hb.frontend.Types.init(opts.gpa, asts, opts.diagnostics);
    defer types.deinit();

    var codegen = hb.frontend.Codegen.init(opts.gpa, Arena.scrath(null).arena, &types, .runtime);
    defer codegen.deinit();

    var backend = if (std.mem.eql(u8, opts.target, "ableos")) backend: {
        const slot = ast_arena.create(hb.hbvm.HbvmGen);
        slot.* = hb.hbvm.HbvmGen{ .gpa = opts.gpa, .emit_header = !opts.dump_asm and !opts.raw_binary };
        break :backend hb.backend.Mach.init(slot);
    } else if (std.mem.eql(u8, opts.target, "x86_64-windows")) backend: {
        const slot = ast_arena.create(hb.x86_64.X86_64Gen);
        slot.* = hb.x86_64.X86_64Gen{ .gpa = opts.gpa, .builder = hb.Object.init(.windows, .x86_64) };
        break :backend hb.backend.Mach.init(slot);
    } else if (std.mem.eql(u8, opts.target, "x86_64-linux")) backend: {
        const slot = ast_arena.create(hb.x86_64.X86_64Gen);
        slot.* = hb.x86_64.X86_64Gen{ .gpa = opts.gpa, .builder = hb.Object.init(.linux, .x86_64) };
        break :backend hb.backend.Mach.init(slot);
    } else {
        try opts.diagnostics.print(
            "{s} is unsupported target, only `x86_64-windows` and `ableos` are supported",
            .{opts.target},
        );
        return error.Failed;
    };
    defer backend.deinit();

    var syms = std.heap.ArenaAllocator.init(opts.gpa);
    defer syms.deinit();

    const entry = codegen.getEntry(.root, "main") catch {
        try opts.diagnostics.writeAll(
            \\...you can define the `main` in the mentioned file:
            \\main := fn(): uint {
            \\    return 0
            \\}
        );

        return error.Failed;
    };

    codegen.queue(.{ .Func = entry });

    var errored = false;
    while (codegen.nextTask()) |tsk| switch (tsk) {
        .Func => |func| {
            defer codegen.bl.func.reset();

            codegen.build(func) catch {
                errored = true;
                continue;
            };

            var tmp = Arena.scrath(null);
            defer tmp.deinit();

            //var out_fmt = std.ArrayList(u8).init(tmp.arena.allocator());
            //defer out_fmt.deinit();
            //try asts[@intFromEnum(func.key.file)].fmtExpr(&out_fmt, func.key.ast);
            //try std.io.getStdErr().writeAll(out_fmt.items);

            var errors = std.ArrayListUnmanaged(static_anal.Error){};

            backend.emitFunc(&codegen.bl.func, .{
                .id = @intFromEnum(func),
                .name = try hb.frontend.Types.Id.init(.{ .Func = func })
                    .fmt(&types).toString(syms.allocator()),
                .entry = func == entry,
                .optimizations = .{
                    .arena = tmp.arena,
                    .error_buf = &errors,
                },
            });

            errored = types.dumpAnalErrors(&errors) or errored;
        },
        .Global => |global| {
            backend.emitData(.{
                .id = @intFromEnum(global),
                .name = try hb.frontend.Types.Id.init(.{ .Global = global })
                    .fmt(&types).toString(syms.allocator()),
                .value = .{ .init = types.store.get(global).data },
            });
        },
    };

    if (errored) {
        try opts.diagnostics.print("failed due to previous errors\n", .{});
        return error.Failed;
    }

    if (opts.dump_asm) {
        backend.disasm(opts.output, opts.colors);
        return .{ .ast = asts, .arena = ast_arena };
    }

    var out = backend.finalize();
    defer out.deinit(opts.gpa);

    if (opts.vendored_test) {
        const test_utils = @import("test_util.zig");

        const head: hb.hbvm.HbvmGen.ExecHeader = @bitCast(out.items[0..@sizeOf(hb.hbvm.HbvmGen.ExecHeader)].*);

        errdefer {
            const symbols = backend.downcast(hb.hbvm.HbvmGen).makeSymMap(@sizeOf(hb.hbvm.HbvmGen.ExecHeader), ast_arena.allocator());
            test_utils.runVm(
                &asts[0],
                false,
                out.items[@sizeOf(hb.hbvm.HbvmGen.ExecHeader)..],
                head.code_length,
                std.io.getStdErr().writer().any(),
                std.io.tty.detectConfig(std.io.getStdErr()),
                symbols,
            ) catch {};
        }

        try test_utils.runVm(
            &asts[0],
            false,
            out.items[@sizeOf(hb.hbvm.HbvmGen.ExecHeader)..],
            head.code_length,
            std.io.null_writer.any(),
            .no_color,
            .{},
        );

        return .{ .arena = ast_arena, .ast = asts };
    }

    if (opts.colors == .no_color or opts.mangle_terminal) {
        try opts.output.writeAll(out.items);
        return .{ .ast = asts, .arena = ast_arena };
    } else {
        try opts.diagnostics.writeAll("can't dump the executable to the stdout since it" ++
            " supports colors (pass --mangle-terminal if you dont care)");
        return error.Failed;
    }
}

pub fn main() !void {
    Arena.initScratch(1024 * 1024 * 10);
    defer Arena.deinitScratch();

    var gpa_impl = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_impl.deinit();

    var opts = CompileOptions{
        .gpa = gpa_impl.allocator(),
        .diagnostics = std.io.getStdErr().writer().any(),
        .colors = std.io.tty.detectConfig(std.io.getStdOut()),
        .output = std.io.getStdOut().writer().any(),
    };
    defer opts.deinit();

    var cli_buff: [1024 * 8]u8 = undefined;
    var cli_scratch = std.heap.FixedBufferAllocator.init(&cli_buff);

    try opts.loadCli(cli_scratch.allocator());

    var arena = (try compile(opts)).arena;
    arena.deinit();
}

pub fn makeRelative(arena: std.mem.Allocator, path: []const u8, base: []const u8) ![]const u8 {
    if (std.mem.startsWith(u8, path, base)) return path[base.len + 1 ..];

    var base_segments = std.fs.path.componentIterator(base) catch return path;
    var path_segments = std.fs.path.componentIterator(path) catch return path;

    while (true) {
        if (std.mem.eql(
            u8,
            (base_segments.peekNext() orelse break).path,
            (path_segments.peekNext() orelse break).path,
        )) {
            _ = base_segments.next();
            _ = path_segments.next();
        } else break;
    }

    const rem = path_segments.path[path_segments.end_index + 1 ..];
    var dd_count: usize = 0;
    while (base_segments.next() != null) dd_count += 1;

    const buf = try arena.alloc(u8, dd_count * 3 + rem.len);
    for (0..dd_count) |i| {
        @memcpy(buf[i * 3 ..][0..3], "../");
    }
    @memcpy(buf[dd_count * 3 ..], rem);

    return buf;
}

const Loader = struct {
    arena: *Arena,
    base: []const u8,
    path_projections: std.StringHashMapUnmanaged([]const u8),
    files: std.ArrayListUnmanaged(hb.frontend.Ast) = .{},

    pub fn load(self: *Loader, opts: hb.frontend.Ast.Loader.LoadOptions) ?hb.frontend.Types.File {
        var tmp = Arena.scrath(null);
        defer tmp.deinit();

        const arena = self.arena.allocator();

        const base = self.base;
        const file = self.files.items[@intFromEnum(opts.from)];
        const rel_base = std.fs.path.dirname(file.path) orelse "";
        const mangled_path = self.path_projections.get(opts.path) orelse
            std.fs.path.join(tmp.arena.allocator(), &.{ base, rel_base, opts.path }) catch return null;
        const path = std.fs.cwd().realpathAlloc(tmp.arena.allocator(), mangled_path) catch mangled_path;

        const canon = makeRelative(tmp.arena.allocator(), path, base) catch return null;

        for (self.files.items, 0..) |fl, i| {
            if (std.mem.eql(u8, fl.path, canon)) return @enumFromInt(i);
        }

        const slot = self.files.addOne(arena) catch return null;
        slot.path = self.arena.dupe(u8, canon);
        slot.source = std.fs.cwd().readFileAllocOptions(arena, path, max_file_len, null, @alignOf(u8), 0) catch |err| {
            hb.frontend.Ast.report(
                file.path,
                file.source,
                opts.pos,
                "can't open used file: {s}: {s}",
                .{ path, @errorName(err) },
                opts.diagnostics,
            );
            return null;
        };

        return @enumFromInt(self.files.items.len - 1);
    }

    fn loadAll(
        arena: *Arena,
        path_projections: std.StringHashMapUnmanaged([]const u8),
        root: []const u8,
        diagnostics: std.io.AnyWriter,
    ) !?struct { []const hb.frontend.Ast, []const u8 } {
        const real_root = std.fs.cwd().realpathAlloc(arena.allocator(), root) catch root;

        var self = Loader{
            .arena = arena,
            .base = std.fs.path.dirname(real_root) orelse "",
            .path_projections = path_projections,
        };

        const slot = try self.files.addOne(self.arena.allocator());
        slot.path = std.fs.path.basename(root);
        slot.source = std.fs.cwd().readFileAllocOptions(arena.allocator(), root, max_file_len, null, @alignOf(u8), 0) catch {
            try diagnostics.print("could not read the root file: {s}\n", .{root});
            return null;
        };

        var failed = false;
        var i: usize = 0;
        while (i < self.files.items.len) : (i += 1) {
            var tmp = Arena.scrath(arena);
            defer tmp.deinit();

            const file = self.files.items[i];
            const fid: hb.frontend.Types.File = @enumFromInt(i);

            const ast_res = hb.frontend.Ast.init(tmp.arena, .{
                .current = fid,
                .path = file.path,
                .code = file.source,
                .loader = .init(&self),
                .diagnostics = diagnostics,
            });

            if (ast_res) |ast| {
                self.files.items[i] = ast;
                self.files.items[i].exprs = try self.files.items[i].exprs.dupe(self.arena.allocator());
            } else |err| {
                switch (err) {
                    error.ParsingFailed => {
                        failed = true;
                        continue;
                    },
                    else => return err,
                }
            }
        }

        if (failed) return null;

        return .{ self.files.items, self.base };
    }
};
