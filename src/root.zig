const frontend2 = opaque {
    pub const Lexer = @import("frontend2/Lexer.zig");
    pub const Ast = @import("frontend2/Ast.zig");
    pub const Abi = @import("frontend2/Abi.zig");
    pub const Parser = @import("frontend2/Parser.zig");
    pub const Fmt = @import("frontend2/Fmt.zig");
    pub const Types = @import("frontend2/TypeStore.zig");
    pub const types = @import("frontend2/types.zig");
    pub const Codegen = @import("frontend2/Codegen.zig");
    pub const Comptime = @import("frontend2/Comptime.zig");
    pub const test_utils = @import("frontend2/test_util.zig");
};

pub const frontend = opaque {
    pub const Lexer = @import("frontend/Lexer.zig");
    pub const Codegen = @import("frontend/Codegen.zig");
    pub const Abi = @import("frontend/Abi.zig");
    pub const Types = @import("frontend/TypeStore.zig");
    pub const DeclIndex = @import("frontend/DeclIndex.zig");
};

pub const backend = opaque {
    pub const Builder = @import("backend/Builder.zig");
    pub const Machine = @import("backend/Machine.zig");
    pub const Regalloc = @import("backend/Regalloc.zig");
    pub const mem2reg = @import("backend/mem2reg.zig");
    pub const mem2reg2 = @import("backend/mem2reg2.zig");
    pub const gcm = @import("backend/gcm.zig");
    pub const static_anal = @import("backend/static_anal.zig");
    pub const inliner = @import("backend/inliner.zig");
    pub const graph = @import("backend/graph.zig");
};

pub const hbvm = opaque {
    pub const Vm = @import("hbvm/Vm.zig");
    pub const isa = @import("hbvm/isa.zig");
    pub const HbvmGen = @import("hbvm/HbvmGen.zig");
    pub const object = @import("hbvm/object.zig");
};

pub const x86_64 = opaque {
    pub const X86_64Gen = @import("x86_64/X86_64Gen.zig");
};

pub const wasm = opaque {
    pub const WasmGen = @import("wasm/WasmGen.zig");
    pub const object = @import("wasm/object.zig");
};

pub const object = opaque {
    pub const elf = @import("object/elf.zig");
    pub const coff = @import("object/coff.zig");

    pub const Arch = enum {
        x86_64,
    };
};

pub const dwarf = @import("dwarf.zig");
pub const utils = @import("utils-lib");
pub const diff = @import("diff.zig");
pub const lane = utils.lane;
pub const runTest = frontend.Codegen.runTest;

test {
    std.testing.refAllDeclsRecursive(@This());
}

const std = @import("std");
const hb = @import("hb");
const static_anal = hb.backend.static_anal;
const Arena = hb.utils.Arena;

const max_file_len = std.math.maxInt(u31);

var alloc = std.heap.GeneralPurposeAllocator(.{}).init;

const CompileOptions = struct {
    diagnostics: ?*std.Io.Writer = null,
    error_colors: std.io.tty.Config = .no_color,
    colors: std.io.tty.Config = .no_color,
    output: ?*std.Io.Writer = null,
    raw_binary: bool = false,
    gpa: std.mem.Allocator = if (utils.lane.single_threaded) alloc.allocator() else std.heap.smp_allocator,

    arg_start: void = {},

    root_file: []const u8 = "main.hb",

    flag_start: void = {},

    parser_mode: hb.frontend2.Ast.InitOptions.Mode = .latest,
    help: bool = false,
    fmt: bool = false,
    fmt_stdout: bool = false,
    dump_asm: bool = false,
    mangle_terminal: bool = false,
    vendored_test: bool = false,
    log_stats: bool = false,
    type_system_memory: usize = 1024 * 1024 * 256,
    scratch_memory: usize = 1024 * 1024 * 128,
    target: hb.backend.Machine.SupportedTarget = .@"hbvm-ableos",
    no_entry: bool = false,
    extra_threads: usize = 127,
    path_projection: std.StringHashMapUnmanaged([]const u8) = .{},
    optimizations: backend.Machine.OptOptions.Mode = .debug,
    benchmark_rounds: usize = 1,

    const option_docs = .{
        .root_file = "the root file to compile from",

        .parser_mode = "use `legacy` for migrating code",
        .help = "print this help message",
        .fmt = "format from the root file",
        .fmt_stdout = "format only the root file and print it to stdout",
        .dump_asm = "dump assembly of the program",
        .mangle_terminal = "dump the executable even if colors are supported",
        .vendored_test = "run the file in a vendored test setting",
        .log_stats = "log stats about the compilation",
        .type_system_memory = "how much memory can type system use, this is per thread",
        .scratch_memory = "how much memory can each scratch arena use, there are 2 per thread",
        .target = "target triple to compile to",
        .no_entry = "wether compiler should look for main function",
        .extra_threads = "extra threads used for the compilation, the value will" ++
            " be truncated to the number of cpus",
        .path_projection = "can be specified multiple times as" ++
            "`--path-projection name path`, when the `@use(\"name\")`" ++
            " is encountered, its projected to `@use(\"path\")`",
        .optimizations = "or release for optimizations",
        .benchmark_rounds = "run the compiler in succesion in order to" ++
            " collect more samples for profiling",
    };

    fn typeToArgHint(comptime T: type, default: T) []const u8 {
        return switch (T) {
            bool => "",
            []const u8 => "<string> =" ++ default,
            usize => "<integer> =" ++ std.fmt.comptimePrint("{d}", .{default}),
            backend.Machine.OptOptions.Mode,
            frontend2.Ast.InitOptions.Mode,
            hb.backend.Machine.SupportedTarget,
            => {
                var value: []const u8 = "[";
                inline for (std.meta.fields(T)) |f| {
                    if (f.name[0] == '@') continue;
                    value = value ++ f.name ++ "|";
                }
                value = value[0 .. value.len - 1] ++ "] =" ++ @tagName(default);

                return value;
            },
            std.StringHashMapUnmanaged([]const u8) => "<name> <path>",
            else => @compileError("unsupported type: " ++ @typeName(T)),
        };
    }

    pub const help_str = b: {
        var msg: []const u8 = "";

        msg = msg ++ "hbc - the hblang compiler\n";
        msg = msg ++ "usage: hbc [root-file] [--flags [vlaues...]]\n";
        msg = msg ++ "\n";

        var arg_offset: usize = 0;
        var flag_offset: usize = 0;
        for (std.meta.fields(CompileOptions), 0..) |f, i| {
            if (std.mem.eql(u8, f.name, "arg_start")) {
                arg_offset = i + 1;
            }

            if (std.mem.eql(u8, f.name, "flag_start")) {
                flag_offset = i + 1;
            }
        }
        std.debug.assert(arg_offset != 0);
        std.debug.assert(flag_offset != 0);

        msg = msg ++ "arguments:\n";
        for (std.meta.fields(CompileOptions)[arg_offset .. flag_offset - 1]) |f| {
            msg = msg ++ "  " ++ f.name ++ "" ++ " - " ++ @field(option_docs, f.name) ++ "\n";
        }

        const too_long_trigger = 20;

        var max_flag_len: usize = 0;
        var max_arg_len: usize = 0;
        var args: [std.meta.fields(CompileOptions).len][]const u8 = undefined;
        for (std.meta.fields(CompileOptions)[flag_offset..], 0..) |f, i| {
            max_flag_len = @max(max_flag_len, f.name.len);
            args[i] = typeToArgHint(f.type, f.defaultValue().?);
            if (args[i].len > too_long_trigger) {
                continue;
            }
            max_arg_len = @max(max_arg_len, args[i].len);
        }

        const arg_padding = " " ** max_arg_len;
        const flag_padding = " " ** max_flag_len;

        msg = msg ++ "flags:\n";
        for (std.meta.fields(CompileOptions)[flag_offset..], 0..) |f, i| {
            const name = p: {
                var mem = f.name[0..f.name.len].*;
                for (&mem) |*c| if (c.* == '_') {
                    c.* = '-';
                };
                break :p mem ++ "";
            };

            msg = msg ++ "  --" ++ name ++ flag_padding[f.name.len..];
            msg = msg ++ " " ++ args[i];
            if (args[i].len > too_long_trigger) {
                msg = msg ++ "\n" ++ " " ** (2 + 2 + flag_padding.len + 1 + arg_padding.len);
            } else {
                msg = msg ++ arg_padding[args[i].len..];
            }
            msg = msg ++ " - " ++ @field(option_docs, f.name) ++ "\n";
        }

        break :b msg;
    };

    pub fn logDiag(self: CompileOptions, comptime fmt: []const u8, args: anytype) void {
        if (lane.isRoot()) {
            if (self.diagnostics) |d| d.print(fmt, args) catch unreachable;
        }
    }

    pub fn loadCli(self: *CompileOptions, arena: std.mem.Allocator) std.mem.Allocator.Error!void {
        var args = try std.process.ArgIterator.initWithAllocator(arena);
        _ = args.next();

        var i: usize = 0;
        parse: while (args.next()) |a| {
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

            inline for (std.meta.fields(CompileOptions)[6..]) |f| flag: {
                if (f.type == void) continue;

                const name = comptime b: {
                    var mem = f.name[0..f.name.len].*;
                    for (&mem) |*c| if (c.* == '_') {
                        c.* = '-';
                    };
                    break :b mem ++ "";
                };

                if (!std.mem.eql(u8, arg, name)) break :flag;

                const val = &@field(self, f.name);

                var failed = true;
                defer if (failed) {
                    self.logDiag("--{s} {s}\n", .{
                        f.name,
                        comptime typeToArgHint(f.type, f.defaultValue().?),
                    });
                    if (self.diagnostics) |d| d.flush() catch unreachable;
                    self.help = true;
                };

                switch (f.type) {
                    bool => val.* = true,
                    backend.Machine.OptOptions.Mode,
                    frontend2.Ast.InitOptions.Mode,
                    hb.backend.Machine.SupportedTarget,
                    => {
                        const str_value = args.next() orelse continue :parse;
                        const value = if (@hasDecl(f.type, "fromStr"))
                            f.type.fromStr(str_value)
                        else
                            std.meta.stringToEnum(f.type, str_value);

                        val.* = value orelse continue :parse;
                    },
                    []const u8 => val.* = args.next() orelse continue :parse,
                    usize => {
                        const str_value = args.next() orelse continue :parse;
                        val.* = std.fmt.parseInt(usize, str_value, 10) catch continue :parse;
                    },
                    std.StringHashMapUnmanaged([]const u8) => {
                        const key = args.next() orelse continue :parse;
                        const value = args.next() orelse continue :parse;
                        try val.put(arena, key, value);
                    },
                    else => @compileError(@typeName(f.type)),
                }

                failed = false;
                continue :parse;
            }

            self.logDiag("unknown flag: --{s}\n", .{arg});
            self.help = true;
        }
    }
};

fn compile(opts: CompileOptions) error{ WriteFailed, Failed, OutOfMemory }!void {
    if (opts.help) {
        if (lane.isRoot()) if (opts.diagnostics) |d|
            try d.writeAll(CompileOptions.help_str);
        return error.Failed;
    }

    errdefer {
        opts.logDiag("failed due to previous errors\n", .{});
    }

    var type_system_memory = Arena.init(opts.type_system_memory);
    defer if (std.debug.runtime_safety) {
        type_system_memory.deinit();
    };

    if (opts.fmt_stdout) {
        if (lane.isRoot()) {
            const source = std.fs.cwd().readFileAllocOptions(
                type_system_memory.allocator(),
                opts.root_file,
                max_file_len,
                null,
                .of(u8),
                0,
            ) catch {
                opts.logDiag("cant find root file: {s}", .{opts.root_file});
                return error.Failed;
            };

            const ast = hb.frontend2.Ast.init(
                &type_system_memory,
                type_system_memory.allocator(),
                .{
                    .path = opts.root_file,
                    .code = source,
                    .diagnostics = opts.diagnostics,
                    .mode = opts.parser_mode,
                    .colors = opts.error_colors,
                },
            ) catch |err| switch (err) {
                error.ParsingFailed => {
                    return error.Failed;
                },
                else => unreachable,
            };

            if (opts.output) |o| {
                try ast.fmt(o);
                try o.flush();
            }
        }

        return;
    }

    const asts, const base = try Loader.loadAll(
        &type_system_memory,
        opts.gpa,
        opts.path_projection,
        opts.root_file,
        opts.diagnostics,
        opts.error_colors,
        opts.parser_mode,
    ) orelse {
        return error.Failed;
    };

    if (opts.fmt) {
        var tmp = Arena.scrath(null);
        defer tmp.deinit();

        const queue = lane.share(tmp.arena, lane.FixedQueue{});
        while (queue.next(asts.len)) |i| {
            const ast = asts[i];

            var frame = tmp.arena.checkpoint();
            defer frame.deinit();

            const path = try std.fs.path.join(
                frame.arena.allocator(),
                &.{ base, ast.path },
            );
            var buf: [4096]u8 = undefined;
            const file = std.fs.cwd().openFile(
                path,
                .{ .mode = .write_only },
            ) catch {
                opts.logDiag("cant open file: {s}", .{path});
                continue;
            };

            var writer = file.writer(&buf);

            try ast.fmt(&writer.interface);
            try writer.interface.flush();

            file.setEndPos(writer.pos) catch {
                opts.logDiag("cant truncate file: {s}", .{path});
            };
        }

        lane.sync(.{});

        return;
    }

    const abi = opts.target.toCallConv();

    const types = hb.frontend2.Types.init(
        type_system_memory,
        asts,
        opts.diagnostics,
        opts.gpa,
    );
    types.target = @tagName(opts.target);
    types.colors = opts.error_colors;

    var root_tmp = utils.Arena.scrath(null);
    defer root_tmp.deinit();

    const logs = if (opts.log_stats) opts.diagnostics else null;

    defer lane.sync(.{});

    const bckend = opts.target.toMachine(&types.pool.arena, opts.gpa);

    const errored = hb.frontend2.Codegen.emitReachable(
        types,
        bckend,
        .{
            .abi = .{ .cc = abi },
            .has_main = !opts.no_entry,
            .optimizations = opts.optimizations,
            .logs = logs,
        },
    );

    if (errored or types.errored) {
        return error.Failed;
    }

    const backends = lane.productBroadcast(root_tmp.arena, bckend);

    if (lane.isRoot()) {
        if (opts.log_stats) b: {
            const diags = opts.diagnostics orelse break :b;

            try diags.writeAll("type system:\n");
            inline for (std.meta.fields(@TypeOf(types.store.rpr))) |field| {
                try diags.print(
                    "  {s:<8}: {}\n",
                    .{ field.name, @field(types.store.rpr, field.name).meta.len },
                );
            }
            try diags.print("  arena   : {}\n", .{types.pool.arena.consumed()});

            inline for (std.meta.fields(@TypeOf(types.stats))) |field| {
                try diags.print("  {s:<8}: {}\n", .{ field.name, @field(types.stats, field.name) });
            }

            var runtim_functions: usize = 0;
            var comptime_functions: usize = 0;
            var dead_functions: usize = 0;

            for (0..types.store.rpr.Func.meta.len) |i| {
                const f: *frontend2.types.Func = types.store.rpr.Func.at(i);
                if (f.completion.get(.@"comptime") == .compiled) comptime_functions += 1;
                if (f.completion.get(.runtime) == .compiled) runtim_functions += 1;

                if (f.completion.get(.@"comptime") == .queued and
                    f.completion.get(.runtime) == .queued)
                {
                    dead_functions += 1;
                }
            }

            try diags.print("  runtime functions:  {}\n", .{runtim_functions});
            try diags.print("  comptime functions: {}\n", .{comptime_functions});
            try diags.print("  dead functions:     {}\n", .{dead_functions});
            try diags.print("  stale pool memory:  {}\n", .{types.pool.staleMemory()});

            types.metrics.logStats(diags);
        }
    }

    var anal_errors = std.ArrayList(backend.static_anal.Error){};

    const options = backend.Machine.FinalizeOptionsInterface{
        .optimizations = .{
            .mode = opts.optimizations,
            .error_buf = &anal_errors,
            .arena = root_tmp.arena,
        },
        .builtins = types.getBuiltins(),
        .files = types.line_indexes,
        .others = backends,
    };

    const name = try std.mem.replaceOwned(
        u8,
        root_tmp.arena.allocator(),
        opts.root_file,
        "/",
        "_",
    );

    if (opts.dump_asm) {
        const out = bckend.finalizeBytes(types.pool.arena.allocator(), options);
        if (types.dumpAnalErrors(&anal_errors)) return error.Failed;

        if (lane.isRoot()) {
            bckend.disasm(.{
                .name = name,
                .bin = out.items,
                .out = opts.output,
                .colors = opts.colors,
            });

            if (opts.output) |o| try o.flush();
        }

        return;
    }

    if (opts.vendored_test and !@import("options").dont_simulate) {
        const expectations: frontend2.test_utils.Expectations = .init(&asts[0], &types.pool.arena);

        const out = bckend.finalizeBytes(types.pool.arena.allocator(), options);
        if (types.dumpAnalErrors(&anal_errors)) return error.Failed;

        if (lane.isRoot()) {
            errdefer {
                bckend.disasm(.{
                    .name = name,
                    .bin = out.items,
                    .out = opts.diagnostics,
                    .colors = opts.colors,
                });

                expectations.assert(bckend.run(.{
                    .name = name,
                    .code = out.items,
                    .output = opts.diagnostics,
                    .colors = opts.colors,
                })) catch unreachable;
            }

            expectations.assert(bckend.run(.{
                .name = name,
                .code = out.items,
            })) catch |err| {
                opts.logDiag("failed to run the test: {s}", .{@errorName(err)});
                return error.Failed;
            };

            bckend.disasm(.{
                .name = name,
                .bin = out.items,
                .out = opts.output,
                .colors = .no_color,
            });
        }

        return;
    }

    if (opts.colors == .no_color or opts.mangle_terminal) {
        bckend.finalize(opts.output, options);
        if (types.dumpAnalErrors(&anal_errors)) return error.Failed;
    } else {
        bckend.finalize(null, options);
        if (types.dumpAnalErrors(&anal_errors)) return error.Failed;

        opts.logDiag("can't dump the executable to the stdout since it" ++
            " supports colors (pass --mangle-terminal if you dont care)", .{});
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
    gpa: std.mem.Allocator,
    shared: *Shared,

    pub const Shared = struct {
        base: []const u8,
        path_projections: std.StringHashMapUnmanaged([]const u8),
        files: std.ArrayList(hb.frontend2.Ast) = .{},
        in_progress: usize = 0,
        completed: usize = 0,
        failed: std.atomic.Value(bool) = .init(false),
        state_lock: std.Thread.Mutex = .{},
        lobby: utils.lane.Lobby = .{},
    };

    pub fn load(self: *Loader, opts: hb.frontend2.Ast.Loader.LoadOptions) ?hb.frontend2.Types.File {
        var tmp = Arena.scrath(null);
        defer tmp.deinit();

        const base = self.shared.base;
        self.shared.state_lock.lock();
        const file = self.shared.files.items[@intFromEnum(opts.from)];
        self.shared.state_lock.unlock();
        const rel_base = std.fs.path.dirname(file.path) orelse "";
        const mangled_path = self.shared.path_projections.get(opts.path) orelse
            std.fs.path.join(tmp.arena.allocator(), &.{ base, rel_base, opts.path }) catch return null;
        const path = std.fs.cwd().realpathAlloc(tmp.arena.allocator(), mangled_path) catch mangled_path;

        const canon = makeRelative(tmp.arena.allocator(), path, base) catch return null;

        _ = std.fs.cwd().statFile(path) catch |err| {
            file.report(opts, opts.pos, "can't stat used file: {}: {}", .{ path, @errorName(err) });
        };

        {
            defer self.shared.lobby.signal();

            const arena = self.arena;

            self.shared.state_lock.lock();
            defer self.shared.state_lock.unlock();

            // This search might be too slow, but we want such problems
            for (self.shared.files.items, 0..) |fl, i| {
                if (std.mem.eql(u8, fl.path, canon)) return @enumFromInt(i);
            }

            const slot = self.shared.files.addOne(arena.allocator()) catch unreachable;
            slot.path = self.arena.dupe(u8, canon);

            return @enumFromInt(self.shared.files.items.len - 1);
        }
    }

    pub const Options = struct {};

    pub const Error = error{ OutOfMemory, WriteFailed };

    pub fn loadAll(
        scratch: *Arena,
        gpa: std.mem.Allocator,
        path_projections: std.StringHashMapUnmanaged([]const u8),
        root: []const u8,
        diagnostics: ?*std.Io.Writer,
        colors: std.io.tty.Config,
        parser_mode: hb.frontend2.Ast.InitOptions.Mode,
    ) Error!?struct { []const hb.frontend2.Ast, []const u8 } {
        var root_tmp = utils.Arena.scrath(scratch);
        defer root_tmp.deinit();

        var shared: *Shared = undefined;
        if (lane.isRoot()) {
            const arena = scratch.allocator();

            const real_root = std.fs.cwd().realpathAlloc(arena, root) catch root;

            shared = root_tmp.arena.create(Shared);
            shared.* = Shared{
                .base = std.fs.path.dirname(real_root) orelse "",
                .path_projections = path_projections,
            };

            const slot = try shared.files.addOne(arena);
            slot.path = std.fs.path.basename(root);
            _ = std.fs.cwd().statFile(root) catch |err| {
                if (diagnostics) |d| try d.print("could not stat the root file ({s}): {s}\n", .{ root, @errorName(err) });
                return null;
            };
        }
        lane.broadcast(&shared, .{});

        var self = Loader{ .arena = scratch, .shared = shared, .gpa = gpa };

        while (true) {
            var tmp = root_tmp.arena.checkpoint();
            defer tmp.deinit();

            self.shared.state_lock.lock();

            // we are done
            if (self.shared.completed == self.shared.files.items.len) {
                self.shared.state_lock.unlock();
                self.shared.lobby.done();
                break;
            }

            // all available taks are taken, go to lobby
            if (self.shared.in_progress == self.shared.files.items.len) {
                self.shared.state_lock.unlock();
                self.shared.lobby.wait();
                continue;
            }

            std.debug.assert(self.shared.in_progress < self.shared.files.items.len);

            // steal a task
            const i = self.shared.in_progress;
            self.shared.in_progress += 1;
            const slot_path = self.shared.files.items[i].path;

            self.shared.state_lock.unlock();

            var failed = true;
            defer {
                self.shared.failed.store(failed, .unordered);
                self.shared.state_lock.lock();
                self.shared.completed += 1;
                self.shared.state_lock.unlock();
            }

            const fid: hb.frontend2.Types.File = @enumFromInt(i);

            const path = try std.fs.path.join(
                tmp.arena.allocator(),
                &.{ self.shared.base, slot_path },
            );

            const source = std.fs.cwd().readFileAllocOptions(
                self.arena.allocator(),
                path,
                1024 * 1024 * 1024,
                null,
                .of(u8),
                0,
            ) catch |err| {
                if (diagnostics) |d| try d.print("could not read the file ({s}) ({s})," ++
                    " did it get deleted in the mean itme?\n", .{ slot_path, @errorName(err) });
                continue;
            };

            var ast_res = hb.frontend2.Ast.init(self.arena, self.gpa, .{
                .current = fid,
                .path = slot_path,
                .code = source,
                .loader = .init(&self),
                .diagnostics = diagnostics,
                .mode = parser_mode,
                .colors = colors,
            });

            if (ast_res) |*ast| {
                self.shared.state_lock.lock();
                self.shared.files.items[i] = ast.*;
                self.shared.state_lock.unlock();
            } else |err| {
                switch (err) {
                    error.ParsingFailed => {
                        continue;
                    },
                    else => |e| return e,
                }
            }

            failed = self.shared.failed.load(.unordered);
        }

        lane.sync(.{});

        const base = self.shared.base;
        const files = self.shared.files.items;
        if (self.shared.failed.raw) return null;

        lane.sync(.spinning);

        return .{ files, base };
    }
};

pub const LineIndex = struct {
    nlines: []const u32,

    pub fn lineCol(self: LineIndex, pos: u32) struct { u32, u32 } {
        var start: usize, var end = .{ 0, self.nlines.len };

        while (start < end) {
            const mid = (start + end) / 2;
            if (pos < self.nlines[mid]) {
                end = mid;
            } else {
                start = mid + 1;
            }
        }

        return .{ @intCast(start), pos - self.nlines[start - 1] };
    }

    pub fn init(file_content: []const u8, arena: *Arena) LineIndex {
        var line_count: usize = 1;
        for (file_content) |c| {
            if (c == '\n') line_count += 1;
        }

        var nlines = arena.alloc(u32, line_count);
        nlines[0] = 0;

        line_count = 1;
        for (file_content, 0..) |c, i| {
            if (c == '\n') {
                nlines[line_count] = @intCast(i + 1);
                line_count += 1;
            }
        }

        return .{ .nlines = nlines };
    }
};

test LineIndex {
    const file_content =
        \\akjdshkdfj
        \\ksjdhks
        \\akjdsk
        \\akjdshkdfj
        \\ksjdhks
        \\akjdsk
    ;

    var arena = Arena.init(4096);
    defer arena.deinit();

    const line_index = LineIndex.init(file_content, &arena);

    var line: u32 = 1;
    var last_nl: usize = 0;
    for (file_content, 0..) |c, i| {
        const lin, const col = line_index.lineCol(@intCast(i));
        try std.testing.expectEqual(line, lin);
        try std.testing.expectEqual(i - last_nl, col);
        if (c == '\n') {
            line += 1;
            last_nl = i + 1;
        }
    }
}
