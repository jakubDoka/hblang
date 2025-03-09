const std = @import("std");
const hb = @import("root.zig");

const Arena = hb.utils.Arena;

const max_file_len = std.math.maxInt(u31);

pub fn main() !void {
    Arena.initScratch(1024 * 1024 * 10);
    defer Arena.deinitScratch();

    var gpa_impl = std.heap.GeneralPurposeAllocator(.{}){};
    const gpa = gpa_impl.allocator();

    const diagnostics = std.io.getStdErr().writer().any();

    var args = std.process.args();
    _ = args.next();

    // #CLI start
    // #ARGS (main.hb)
    var root_file: []const u8 = "main.hb";
    // #FLAGS (--help)
    var help = false; // print this help message
    var fmt = false; // format all files reachable from the root_file
    var fmt_stdout = false; // format only the root file and print it to stdout
    var dump_asm = false; // dump assembly of the program
    // #OPTIONS (--target ableos)
    var target: []const u8 = "ableos"; // target triple to compile to (not used yet since we have only one target)
    var extra_threads: usize = 0; // extra threads used for the compilation (not used yet)
    var path_projections = std.StringHashMap([]const u8).init(gpa); // can be specified multiple times
    // as `--path-projection name path`, when the `@use("name")` is encountered, its projected to `@use("path")`
    // #CLI end

    defer path_projections.deinit();

    var i: usize = 0;
    while (args.next()) |a| {
        var arg: []const u8 = a[0..];
        if (!std.mem.startsWith(u8, arg, "--")) {
            switch (i) {
                0 => root_file = arg,
                else => {},
            }
            i += 1;
            continue;
        }

        arg = arg[2..];

        help = help or std.mem.eql(u8, arg, "help");
        fmt = fmt or std.mem.eql(u8, arg, "fmt");
        fmt_stdout = fmt_stdout or std.mem.eql(u8, arg, "fmt-stdout");
        dump_asm = dump_asm or std.mem.eql(u8, arg, "dump-asm");

        if (std.mem.eql(u8, arg, "target")) target = args.next() orelse {
            try diagnostics.writeAll("--target takes an argument");
            return;
        };
        if (std.mem.eql(u8, arg, "extra-threads")) {
            arg = args.next() orelse {
                try diagnostics.writeAll("--extra-threads takes an integer argument");
                return;
            };
            extra_threads = std.fmt.parseInt(usize, arg, 10) catch |err| {
                try diagnostics.print("failed to parse --extra-threads argument: {s}", .{@errorName(err)});
                return;
            };
        }
        if (std.mem.eql(u8, arg, "path-projection")) {
            const msg = "--path-projection takes two argumens: <key> <value>";
            const key = args.next() orelse {
                try diagnostics.writeAll(msg);
                return;
            };
            const value = args.next() orelse {
                try diagnostics.writeAll(msg);
                return;
            };
            try path_projections.put(key, value);
        }
    }

    if (help) {
        const help_str = comptime b: {
            const source = @embedFile("main.zig");
            const start_pat = "// #CLI start\n";
            const end_pat = "// #CLI end\n";
            const start = std.mem.indexOf(u8, source, start_pat).? + start_pat.len;
            const end = std.mem.indexOfPos(u8, source, start, end_pat).?;
            break :b std.mem.trimRight(u8, source[start..end], "\n\t ") ++ "";
        };

        try diagnostics.writeAll(help_str);
        return;
    }

    var ast_arena = std.heap.ArenaAllocator.init(gpa);
    defer ast_arena.deinit();

    if (fmt_stdout) {
        const source = try std.fs.cwd().readFileAlloc(ast_arena.allocator(), root_file, max_file_len);
        const ast = try hb.Ast.init(ast_arena.allocator(), .root, root_file, source, .noop, diagnostics);

        var buf = std.ArrayList(u8).init(ast_arena.allocator());
        try ast.fmt(&buf);

        try std.io.getStdOut().writeAll(buf.items);
        return;
    }

    const asts, const base = try Loader.loadAll(ast_arena.allocator(), path_projections, root_file, diagnostics) orelse return;

    if (fmt) {
        for (asts) |ast| {
            var tmp = Arena.scrath(null);
            defer tmp.deinit();

            var buf = std.ArrayList(u8).init(tmp.arena.allocator());
            try ast.fmt(&buf);

            const path = try std.fs.path.join(tmp.arena.allocator(), &.{ base, ast.path });
            try std.fs.cwd().writeFile(.{ .sub_path = path, .data = buf.items });
        }
        return;
    }

    var types = hb.Types.init(gpa, asts, diagnostics);
    defer types.deinit();

    var codegen = hb.Codegen.init(gpa, Arena.scrath(null).arena, &types, .runtime);
    defer codegen.deinit();

    var hbg = hb.HbvmGen{ .gpa = gpa, .emit_header = !dump_asm };
    const backend = hb.Mach.init(&hbg);

    var syms = std.heap.ArenaAllocator.init(gpa);
    defer syms.deinit();

    const entry = codegen.getEntry(.root, "main") catch {
        try diagnostics.writeAll(
            \\...you can define the `main` in the mentioned file:
            \\main := fn(): uint {
            \\    return 0
            \\}
        );

        return;
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

            backend.emitFunc(&codegen.bl.func, .{
                .id = func.id,
                .name = try hb.Types.Id.init(.{ .Func = func }).fmt(&types)
                    .toString(syms.allocator()),
                .entry = func.id == entry.id,
            });
        },
        .Global => |global| {
            backend.emitData(.{
                .id = global.id,
                .name = try hb.Types.Id.init(.{ .Global = global }).fmt(&types)
                    .toString(syms.allocator()),
                .value = .{ .init = global.data },
            });
        },
    };

    if (errored) {
        try diagnostics.print("failed due to previous errors\n", .{});
        return;
    }

    if (dump_asm) {
        backend.disasm(std.io.getStdOut().writer().any(), std.io.tty.detectConfig(std.io.getStdOut()));
        return;
    }

    var out = backend.finalize();
    defer out.deinit(gpa);

    try std.io.getStdOut().writeAll(out.items);
}

const Loader = struct {
    gpa: std.mem.Allocator,
    base: []const u8,
    path_projections: std.StringHashMap([]const u8),
    files: std.ArrayListUnmanaged(hb.Ast) = .{},

    pub fn load(self: *Loader, opts: hb.Ast.Loader.LoadOptions) ?hb.Types.File {
        const base = self.base;
        const file = self.files.items[@intFromEnum(opts.from)];
        const rel_base = std.fs.path.dirname(file.path) orelse "";
        const mangled_path = self.path_projections.get(opts.path) orelse
            std.fs.path.join(self.gpa, &.{ base, rel_base, opts.path }) catch return null;
        const path = std.fs.cwd().realpathAlloc(self.gpa, mangled_path) catch mangled_path;

        const canon = if (std.mem.startsWith(u8, path, base)) path[base.len + 1 ..] else b: {
            var base_segments = std.fs.path.componentIterator(base) catch break :b path;
            var path_segments = std.fs.path.componentIterator(path) catch break :b path;

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

            const buf = self.gpa.alloc(u8, dd_count * 3 + rem.len) catch break :b path;
            for (0..dd_count) |i| {
                @memcpy(buf[i * 3 ..][0..3], "../");
            }
            @memcpy(buf[dd_count * 3 ..], rem);

            break :b buf;
        };

        for (self.files.items, 0..) |fl, i| {
            if (std.mem.eql(u8, fl.path, canon)) return @enumFromInt(i);
        }

        const slot = self.files.addOne(self.gpa) catch return null;
        slot.path = canon;
        slot.source = std.fs.cwd().readFileAlloc(self.gpa, path, max_file_len) catch |err| {
            hb.Ast.report(
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
        gpa: std.mem.Allocator,
        path_projections: std.StringHashMap([]const u8),
        root: []const u8,
        diagnostics: std.io.AnyWriter,
    ) !?struct { []const hb.Ast, []const u8 } {
        const real_root = std.fs.cwd().realpathAlloc(gpa, root) catch root;

        var self = Loader{
            .gpa = gpa,
            .base = std.fs.path.dirname(real_root) orelse "",
            .path_projections = path_projections,
        };

        const slot = try self.files.addOne(self.gpa);
        slot.path = std.fs.path.basename(root);
        slot.source = std.fs.cwd().readFileAlloc(self.gpa, root, max_file_len) catch {
            try diagnostics.print("could not read the root file: {s}", .{root});
            return null;
        };

        var failed = false;
        var i: usize = 0;
        while (i < self.files.items.len) : (i += 1) {
            const file = self.files.items[i];
            const fid: hb.Types.File = @enumFromInt(i);

            const ast_res = hb.Ast.init(self.gpa, fid, file.path, file.source, .init(&self), diagnostics);
            if (ast_res) |ast| {
                self.files.items[i] = ast;
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
