pub const backend = enum {
    pub const Builder = @import("backend/Builder.zig");
    pub const Machine = @import("backend/Machine.zig");
    pub const Regalloc = @import("backend/Regalloc.zig");
    pub const Regalloc2 = @import("backend/Regalloc2.zig");
    pub const mem2reg = @import("backend/mem2reg.zig");
    pub const gcm = @import("backend/gcm.zig");
    pub const static_anal = @import("backend/static_anal.zig");
    pub const graph = @import("backend/graph.zig");
};

pub const hbvm = enum {
    pub const Vm = @import("hbvm/Vm.zig");
    pub const isa = @import("hbvm/isa.zig");
    pub const HbvmGen = @import("hbvm/HbvmGen.zig");
    pub const object = @import("hbvm/object.zig");
};

pub const x86_64 = enum {
    pub const X86_64Gen = @import("x86_64/X86_64Gen.zig");
};

pub const object = @import("object.zig");

pub const frontend = enum {
    pub const Lexer = @import("frontend/Lexer.zig");
    pub const Ast = @import("frontend/Ast.zig");
    pub const Parser = @import("frontend/Parser.zig");
    pub const Fmt = @import("frontend/Fmt.zig");
    pub const Types = @import("frontend/TypeStore.zig");
    pub const types = @import("frontend/types.zig");
    pub const Codegen = @import("frontend/Codegen.zig");
    pub const Comptime = @import("frontend/Comptime.zig");
};

pub const utils = @import("utils.zig");
pub const test_utils = @import("test_util.zig");
pub const diff = @import("diff.zig");

const std = @import("std");
const hb = @import("hb");
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
    parser_mode: hb.frontend.Ast.InitOptions.Mode = .latest, // or "legacy" for migrating code
    help: bool = false, // print this help message
    fmt: bool = false, // format all files reachable from the root_file
    fmt_stdout: bool = false, // format only the root file and print it to stdout
    dump_asm: bool = false, // dump assembly of the program
    mangle_terminal: bool = false, // dump the executable even if colors are supported
    vendored_test: bool = false,
    // #OPTIONS (--target ableos)
    target: []const u8 = "hbvm-ableos", // target triple to compile to (not used yet since we have only one target)
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
                try self.diagnostics.writeAll("--target <triple>");
                return;
            };

            if (std.mem.eql(u8, arg, "parser-mode")) {
                self.parser_mode = std.meta.stringToEnum(@TypeOf(self.parser_mode), args.next() orelse {
                    try self.diagnostics.writeAll("--parser-mode <mode>");
                    return;
                }) orelse {
                    try self.diagnostics.writeAll("--parser-mode <latest/legacy>");
                    return;
                };
            }

            if (std.mem.eql(u8, arg, "extra-threads")) {
                arg = args.next() orelse {
                    try self.diagnostics.writeAll("--extra-threads <integer>");
                    return;
                };
                self.extra_threads = std.fmt.parseInt(usize, arg, 10) catch |err| {
                    try self.diagnostics.print("--extra-threads <1..>: {s}", .{@errorName(err)});
                    return;
                };
            }

            if (std.mem.eql(u8, arg, "path-projection")) {
                const msg = "--path-projection <key> <value>";
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
            @setEvalBranchQuota(2000);
            const source = @embedFile("root.zig");
            const start_pat = "// #CLI start";
            const end_pat = "// #CLI end";
            const start = std.mem.indexOf(u8, source, start_pat).? + start_pat.len;
            const end = std.mem.indexOfPos(u8, source, start, end_pat).?;
            break :b std.mem.trimRight(u8, source[start..end], "\n\t\r ") ++ "";
        };

        try opts.diagnostics.writeAll(help_str);
        return error.Failed;
    }

    var ast_arena = Arena.init(1024 * 1024 * 128);
    errdefer ast_arena.deinit();

    if (opts.fmt_stdout) {
        const source = try std.fs.cwd().readFileAllocOptions(ast_arena.allocator(), opts.root_file, max_file_len, null, @alignOf(u8), 0);
        const ast = try hb.frontend.Ast.init(&ast_arena, .{
            .path = opts.root_file,
            .code = source,
            .diagnostics = opts.diagnostics,
            .mode = opts.parser_mode,
        });

        var buf = std.ArrayList(u8).init(ast_arena.allocator());
        try ast.fmt(&buf);

        try opts.output.writeAll(buf.items);
        return error.Failed;
    }

    const asts, const base = try Loader.loadAll(
        &ast_arena,
        opts.path_projections,
        opts.root_file,
        opts.diagnostics,
        opts.parser_mode,
    ) orelse {
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

    var bckend, const abi: hb.frontend.Types.Abi = if (std.mem.eql(u8, opts.target, "hbvm-ableos")) backend: {
        const slot = ast_arena.create(hb.hbvm.HbvmGen);
        slot.* = hb.hbvm.HbvmGen{ .gpa = opts.gpa };
        break :backend .{ hb.backend.Machine.init(opts.target, slot), .ableos };
    } else if (std.mem.eql(u8, opts.target, "x86_64-windows")) backend: {
        const slot = ast_arena.create(hb.x86_64.X86_64Gen);
        slot.* = hb.x86_64.X86_64Gen{ .gpa = opts.gpa, .object_format = .coff };
        break :backend .{ hb.backend.Machine.init(opts.target, slot), .fastcall };
    } else if (std.mem.eql(u8, opts.target, "x86_64-linux")) backend: {
        const slot = ast_arena.create(hb.x86_64.X86_64Gen);
        slot.* = hb.x86_64.X86_64Gen{ .gpa = opts.gpa, .object_format = .elf };
        break :backend .{ hb.backend.Machine.init(opts.target, slot), .systemv };
    } else {
        try opts.diagnostics.print(
            "{s} is unsupported target, only `x86_64-(windows|linux)` and `hbvm-ableos` are supported",
            .{opts.target},
        );
        return error.Failed;
    };
    defer bckend.deinit();

    const types = hb.frontend.Types.init(opts.gpa, asts, opts.diagnostics);
    types.target = opts.target;
    defer types.deinit();

    var root_tmp = utils.Arena.scrath(null);
    defer root_tmp.deinit();

    const errored = hb.frontend.Codegen.emitReachable(opts.gpa, root_tmp.arena, types, abi, bckend, .{});
    if (errored) {
        try opts.diagnostics.print("failed due to previous errors\n", .{});
        return error.Failed;
    }

    const name = try std.mem.replaceOwned(u8, ast_arena.allocator(), opts.root_file, "/", "_");

    if (opts.dump_asm) {
        const out = bckend.finalizeBytes(ast_arena.allocator());

        bckend.disasm(.{
            .name = name,
            .bin = out.items,
            .out = opts.output,
            .colors = opts.colors,
        });
        return .{ .ast = asts, .arena = ast_arena };
    }

    if (opts.vendored_test) {
        const expectations: test_utils.Expectations = .init(&asts[0], ast_arena.allocator());

        const out = bckend.finalizeBytes(ast_arena.allocator());

        errdefer {
            bckend.disasm(.{
                .name = name,
                .bin = out.items,
                .out = std.io.getStdErr().writer().any(),
                .colors = std.io.tty.detectConfig(std.io.getStdErr()),
            });

            expectations.assert(bckend.run(.{
                .name = name,
                .code = out.items,
                .output = std.io.getStdErr().writer().any(),
                .colors = std.io.tty.detectConfig(std.io.getStdErr()),
            })) catch {};
        }

        try expectations.assert(bckend.run(.{
            .name = name,
            .code = out.items,
        }));

        return .{ .arena = ast_arena, .ast = asts };
    }

    if (opts.colors == .no_color or opts.mangle_terminal) {
        bckend.finalize(opts.output);
        return .{ .ast = asts, .arena = ast_arena };
    } else {
        try opts.diagnostics.writeAll("can't dump the executable to the stdout since it" ++
            " supports colors (pass --mangle-terminal if you dont care)");
        return error.Failed;
    }
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

    pub fn loadAll(
        arena: *Arena,
        path_projections: std.StringHashMapUnmanaged([]const u8),
        root: []const u8,
        diagnostics: std.io.AnyWriter,
        parser_mode: hb.frontend.Ast.InitOptions.Mode,
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
                .mode = parser_mode,
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
