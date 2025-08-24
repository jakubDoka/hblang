pub const backend = enum {
    pub const Builder = @import("backend/Builder.zig");
    pub const Machine = @import("backend/Machine.zig");
    pub const Regalloc = @import("backend/Regalloc.zig");
    pub const mem2reg = @import("backend/mem2reg.zig");
    pub const gcm = @import("backend/gcm.zig");
    pub const static_anal = @import("backend/static_anal.zig");
    pub const inliner = @import("backend/inliner.zig");
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
pub const dwarf = @import("dwarf.zig");

pub const frontend = enum {
    pub const Lexer = @import("frontend/Lexer.zig");
    pub const Ast = @import("frontend/Ast.zig");
    pub const Abi = @import("frontend/Abi.zig");
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

test {
    _ = &utils;
}

const max_file_len = std.math.maxInt(u31);

pub const CompileOptions = struct {
    diagnostics: ?*std.Io.Writer = null,
    error_colors: std.io.tty.Config = .no_color,
    colors: std.io.tty.Config = .no_color,
    output: ?*std.Io.Writer = null,
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
    vendored_test: bool = false, // run the file in a vendored test setting
    log_stats: bool = false, // log stats about the compilation (memory)
    type_system_memory: usize = 1024 * 1024 * 256, // how much memory can type system use
    scratch_memory: usize = 1024 * 1024 * 128, // how much memory can each scratch arena use (there are 2)
    shared_queue_capacity: usize = 1024 * 256, // estimated queue capacity
    target: []const u8 = "hbvm-ableos", // target triple to compile to (not
    // used yet since we have only one target)
    no_entry: bool = false, // wether compiler should look for main function
    extra_threads: usize = 0, // extra threads used for the compilation (not used yet)
    path_projection: std.StringHashMapUnmanaged([]const u8) = .{}, // can be
    // specified multiple times as `--path-projection name path`, when the
    // `@use("name")` is encountered, its projected to `@use("path")` #CLI end
    optimizations: backend.Machine.OptOptions.Mode = .debug,
    // run the compiler in succesion in order to collect more samples for
    // profiling
    benchmark_rounds: usize = 1,
    // #CLI end

    pub fn logDiag(self: CompileOptions, comptime fmt: []const u8, args: anytype) void {
        if (self.diagnostics) |d| d.print(fmt, args) catch unreachable;
    }

    pub fn loadCli(self: *CompileOptions, arena: std.mem.Allocator) !void {
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

            inline for (std.meta.fields(CompileOptions)[5..]) |f| flag: {
                const name = comptime b: {
                    var mem = f.name[0..f.name.len].*;
                    for (&mem) |*c| if (c.* == '_') {
                        c.* = '-';
                    };
                    break :b mem ++ "";
                };

                if (!std.mem.eql(u8, arg, name)) break :flag;

                const val = &@field(self, f.name);

                errdefer |err| {
                    self.logDiag("--{s} <{s}>", .{ f.name, @errorName(err) });
                    std.process.exit(1);
                }

                switch (f.type) {
                    bool => val.* = true,
                    backend.Machine.OptOptions.Mode => val.* = std.meta.stringToEnum(
                        @TypeOf(@field(self, f.name)),
                        args.next() orelse return error.mode,
                    ) orelse return error.@"debug/release",
                    frontend.Ast.InitOptions.Mode => val.* = std.meta.stringToEnum(
                        @TypeOf(@field(self, f.name)),
                        args.next() orelse return error.mode,
                    ) orelse return error.@"legacy/latest",
                    []const u8 => val.* = args.next() orelse return error.target,
                    usize => val.* = try std.fmt.parseInt(usize, args.next() orelse return error.integer, 10),
                    std.StringHashMapUnmanaged([]const u8) => {
                        const key = args.next() orelse return error.@"key> <value";
                        const value = args.next() orelse return error.@"key> <value";
                        try val.put(arena, key, value);
                    },
                    else => @compileError(@typeName(f.type)),
                }

                continue :parse;
            }

            self.logDiag("unknown flag: --{s}", .{arg});
            std.process.exit(1);
        }
    }
};

pub const Task = struct {
    id: utils.EntId(frontend.types.Func),
    thread: u32,
    from: *frontend.Types,

    pub fn fronFn(types: *frontend.Types, thread: usize, func: utils.EntId(frontend.types.Func)) Task {
        return Task{ .id = func, .from = types, .thread = @intCast(thread) };
    }

    pub fn intoFunc(self: Task, dest: *frontend.Types) ?utils.EntId(frontend.types.Func) {
        if (self.from == dest) return self.id;
        const id, const new = dest.cloneFrom(self.from, .init(.{ .Func = self.id }));
        if (!new) return null;

        dest.remote_ids.append(dest.pool.allocator(), .{
            .remote = self.id,
            .from_thread = self.thread,
            .local = id.data().Func,
        }) catch unreachable;

        return id.data().Func;
    }
};

pub const Queue = utils.SharedQueue(Task);

pub const Threading = union(enum) {
    single: struct {
        types: *frontend.Types,
        machine: backend.Machine,
    },
    multi: Multi,

    pub const Multi = struct {
        queue: Queue,
        types: []*frontend.Types,
        para: backend.Machine.Parallelism,
        machine: backend.Machine,

        pub fn buildMapping(self: *Multi, scratch: *utils.Arena) backend.Machine.GlobalMapping {
            var global_table_size: usize = 0;
            const local_bases = scratch.alloc(u32, self.types.len);
            for (self.types, local_bases) |t, *gt| {
                gt.* = @intCast(global_table_size);
                global_table_size += t.remote_ids.items.len;
            }

            // Build a trivial table
            //
            var global_table = scratch.alloc(backend.Machine.LocalId, global_table_size);
            for (self.types, local_bases, 0..) |t, lb, tid| {
                for (0..t.store.rpr.Func.meta.len) |func_idx| {
                    global_table[lb + func_idx] = .{
                        .thread = @intCast(tid),
                        .index = @intCast(func_idx),
                    };
                }
            }

            // Patch up remotes
            //
            for (self.types, 0..) |t, tid| {
                for (t.remote_ids.items) |ri| {
                    // make the remote point to outr function since they don't
                    // have the compiled graph
                    global_table[local_bases[ri.from_thread] + @intFromEnum(ri.remote)] = .{
                        .thread = @intCast(tid),
                        .index = @intCast(@intFromEnum(ri.local)),
                    };
                }
            }

            return .{
                .global_table = global_table,
                .local_bases = local_bases,
            };
        }
    };

    pub fn singleBackend(self: *Threading) backend.Machine {
        return switch (self.*) {
            .single => |s| s.machine,
            .multi => |m| m.machine,
        };
    }

    pub fn ast(self: *Threading) []const hb.frontend.Ast {
        return switch (self.*) {
            .single => |s| s.types.files,
            .multi => |m| m.types[0].files,
        };
    }

    pub fn dumpAsm(
        self: *Threading,
        name: []const u8,
        out: *std.Io.Writer,
        colors: std.io.tty.Config,
        optimizations: backend.Machine.OptOptions.Mode,
    ) void {
        errdefer unreachable;

        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        var output = std.Io.Writer.Allocating.init(tmp.arena.allocator());
        self.finalize(&output.writer, tmp.arena, null, optimizations);

        self.singleBackend().disasm(.{
            .name = name,
            .bin = output.written(),
            .out = out,
            .colors = colors,
        });
    }

    pub fn runVendoredTest(
        self: *Threading,
        name: []const u8,
        out: *std.Io.Writer,
        colors: std.io.tty.Config,
        optimizations: backend.Machine.OptOptions.Mode,
    ) !void {
        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        var output = std.Io.Writer.Allocating.init(tmp.arena.allocator());
        self.finalize(&output.writer, tmp.arena, null, optimizations);

        const expectations: test_utils.Expectations = .init(&self.ast()[0], tmp.arena);

        errdefer {
            self.singleBackend().disasm(.{
                .name = name,
                .bin = output.written(),
                .out = out,
                .colors = colors,
            });

            _ = self.singleBackend().run(.{
                .name = name,
                .code = output.written(),
                .output = out,
                .logs = out,
                .colors = colors,
            }) catch {};
        }

        try expectations.assert(self.singleBackend().run(.{
            .name = name,
            .code = output.written(),
            .output = out,
            .colors = colors,
        }));
    }

    pub fn finalize(
        self: *Threading,
        out: *std.Io.Writer,
        out_scratch: ?*utils.Arena,
        logs: ?*std.Io.Writer,
        optimizations: backend.Machine.OptOptions.Mode,
    ) void {
        switch (self.*) {
            .single => |s| {
                s.machine.finalize(.{
                    .optimizations = .{ .mode = optimizations },
                    .builtins = s.types.getBuiltins(),
                    .output = out,
                    .output_scratch = out_scratch,
                    .logs = logs,
                });
            },
            .multi => |*m| {
                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();
                m.para.mapping = m.buildMapping(tmp.arena);

                m.machine.finalize(.{
                    .optimizations = .{ .mode = optimizations },
                    .builtins = m.types[0].getBuiltins(),
                    .output = out,
                    .output_scratch = out_scratch,
                    .parallelism = &m.para,
                    .logs = logs,
                });
            },
        }
    }

    pub fn logStats(self: *Threading, out: *std.Io.Writer) void {
        _ = self; // autofix
        _ = out; // autofix
    }
};

pub fn compile(opts: CompileOptions) anyerror!void {
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

        if (opts.diagnostics) |d| try d.writeAll(help_str);
        return error.Failed;
    }

    var type_system_memory = Arena.init(opts.type_system_memory);
    defer if (std.debug.runtime_safety) type_system_memory.deinit();

    if (opts.fmt_stdout) {
        const source = try std.fs.cwd().readFileAllocOptions(
            type_system_memory.allocator(),
            opts.root_file,
            max_file_len,
            null,
            .of(u8),
            0,
        );
        const ast = try hb.frontend.Ast.init(&type_system_memory, .{
            .path = opts.root_file,
            .code = source,
            .diagnostics = opts.diagnostics,
            .mode = opts.parser_mode,
            .colors = opts.error_colors,
        });

        if (opts.output) |o| {
            try ast.fmt(o);
            try o.flush();
        }

        return;
    }

    const asts, const base = try Loader.loadAll(
        &type_system_memory,
        opts.path_projection,
        opts.root_file,
        opts.diagnostics,
        opts.error_colors,
        opts.parser_mode,
    ) orelse {
        opts.logDiag("failed due to previous errors (codegen skipped)\n", .{});
        return error.Failed;
    };

    if (opts.fmt) {
        for (asts) |ast| {
            var tmp = Arena.scrath(null);
            defer tmp.deinit();

            const path = try std.fs.path.join(tmp.arena.allocator(), &.{ base, ast.path });
            var buf: [4096]u8 = undefined;
            var writer = (try std.fs.cwd().openFile(path, .{ .mode = .write_only })).writer(&buf);
            try ast.fmt(&writer.interface);
            try writer.interface.flush();
        }

        return;
    }

    const target = hb.backend.Machine.SupportedTarget.fromStr(opts.target) orelse {
        opts.logDiag("unknown target: {s}\n", .{opts.target});
        opts.logDiag("supported targets are:\n", .{});
        inline for (std.meta.fields(hb.backend.Machine.SupportedTarget)) |t| {
            opts.logDiag("  {s}\n", .{t.name});
        }
        return error.Failed;
    };

    const abi = target.toCallConv();

    var shared_arena: Arena = undefined;
    var threading: Threading = undefined;
    if (@import("builtin").single_threaded or opts.extra_threads == 0) {
        threading = .{ .single = .{
            .types = b: {
                const types = hb.frontend.Types.init(
                    type_system_memory,
                    asts,
                    opts.diagnostics,
                );
                types.target = opts.target;
                types.colors = opts.error_colors;
                break :b types;
            },
            .machine = undefined,
        } };
        threading.single.machine = target.toMachine(&threading.single.types.pool);
    } else {
        const thread_count = opts.extra_threads + 1;

        shared_arena = Arena.init(
            Queue.size_of(
                thread_count,
                opts.shared_queue_capacity,
            ) + @sizeOf(Queue) * thread_count + 4096,
        );

        threading = .{ .multi = undefined };
        const ref = &threading.multi;

        try std.Thread.Pool.init(&ref.para.pool, .{
            .allocator = shared_arena.allocator(),
            .n_jobs = thread_count,
        });

        const types = type_system_memory.alloc(*hb.frontend.Types, thread_count);
        const chunk_size = (opts.type_system_memory - type_system_memory.consumed()) / thread_count;
        for (types) |*t| {
            // TODO: diagnostics need to be agregated somehow in a sync manner
            t.* = hb.frontend.Types.init(type_system_memory.subslice(chunk_size), asts, opts.diagnostics);
            t.*.target = opts.target;
            t.*.colors = opts.error_colors;
        }

        ref.queue = .init(
            &shared_arena,
            opts.extra_threads + 1,
            opts.shared_queue_capacity / thread_count * 2,
        );
        ref.types = types;
        ref.para.shards = shared_arena.alloc(backend.Machine.Shard, thread_count);
        for (ref.para.shards, types) |*s, t| {
            s.* = .{ .gpa = &t.pool };
        }
    }

    var root_tmp = utils.Arena.scrath(null);
    defer root_tmp.deinit();

    const logs = if (opts.log_stats) opts.diagnostics else null;

    const errored = hb.frontend.Codegen.emitReachable(
        root_tmp.arena,
        &threading,
        .{
            .abi = .{ .cc = abi },
            .has_main = !opts.no_entry,
            .optimizations = opts.optimizations,
            .logs = logs,
        },
    );
    if (errored) {
        opts.logDiag("failed due to previous errors\n", .{});
        return error.Failed;
    }

    const name = try std.mem.replaceOwned(u8, root_tmp.arena.allocator(), opts.root_file, "/", "_");

    var anal_errors = std.ArrayListUnmanaged(backend.static_anal.Error){};

    const optimizations = backend.Machine.OptOptions{
        .mode = opts.optimizations,
        .error_buf = &anal_errors,
        .arena = root_tmp.arena,
    };

    if (threading == .multi) {
        if (opts.benchmark_rounds == 1) {
            opts.logDiag("multi threading code emmision is not yet supported\n", .{});
        }
        return;
    }

    const types = threading.single.types;
    const bckend = threading.single.machine;

    if (opts.dump_asm) {
        const out = bckend.finalizeBytes(.{
            .gpa = types.pool.arena.allocator(),
            .optimizations = optimizations,
            .builtins = types.getBuiltins(),
        });

        if (types.dumpAnalErrors(&anal_errors)) {
            opts.logDiag("failed due to previous errors\n", .{});
            return error.Failed;
        }

        bckend.disasm(.{
            .name = name,
            .bin = out.items,
            .out = opts.output,
            .colors = opts.colors,
        });

        if (opts.output) |o| try o.flush();

        return;
    }

    if (opts.vendored_test and !@import("options").dont_simulate) {
        const expectations: test_utils.Expectations = .init(&asts[0], &types.pool.arena);

        const out = bckend.finalizeBytes(.{
            .gpa = types.pool.arena.allocator(),
            .optimizations = optimizations,
            .builtins = types.getBuiltins(),
        });

        if (types.dumpAnalErrors(&anal_errors)) {
            opts.logDiag("failed due to previous errors\n", .{});
            return error.Failed;
        }

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

        try expectations.assert(bckend.run(.{
            .name = name,
            .code = out.items,
        }));

        bckend.disasm(.{
            .name = name,
            .bin = out.items,
            .out = opts.output,
            .colors = .no_color,
        });

        return;
    }

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

        if (false) {
            var runtim_functions: usize = 0;
            var comptime_functions: usize = 0;
            var dead_functions: usize = 0;

            for (@as([]const frontend.types.Func, types.store.rpr.Func.items)) |f| {
                if (f.completion.get(.@"comptime") == .compiled) comptime_functions += 1;
                if (f.completion.get(.runtime) == .compiled) runtim_functions += 1;

                if (f.completion.get(.@"comptime") == .queued and
                    f.completion.get(.runtime) == .queued)
                {
                    dead_functions += 1;
                }
            }

            try diags.print("  runtime functions: {}\n", .{runtim_functions});
            try diags.print("  comptime functions: {}\n", .{comptime_functions});
            try diags.print("  dead functions: {}\n", .{dead_functions});
        }
        try diags.print("  stale pool memory: {}\n", .{types.pool.staleMemory()});

        types.metrics.logStats(diags);
    }

    if (opts.colors == .no_color or opts.mangle_terminal) {
        bckend.finalize(.{
            .output = opts.output,
            .optimizations = optimizations,
            .builtins = types.getBuiltins(),
            .logs = logs,
        });

        if (types.dumpAnalErrors(&anal_errors)) {
            opts.logDiag("failed due to previous errors\n", .{});
            return error.Failed;
        }

        return;
    } else {
        bckend.finalize(.{
            .output = null,
            .optimizations = optimizations,
            .builtins = types.getBuiltins(),
            .logs = logs,
        });

        if (types.dumpAnalErrors(&anal_errors)) {
            opts.logDiag("failed due to previous errors\n", .{});
            return error.Failed;
        }

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
        slot.source = std.fs.cwd().readFileAllocOptions(arena, path, max_file_len, null, .of(u8), 0) catch |err| {
            file.report(
                opts,
                opts.pos,
                "can't open used file: {}: {}",
                .{ path, @errorName(err) },
            );

            slot.source = "";
            return null;
        };

        return @enumFromInt(self.files.items.len - 1);
    }

    pub fn loadAll(
        arena: *Arena,
        path_projections: std.StringHashMapUnmanaged([]const u8),
        root: []const u8,
        diagnostics: ?*std.Io.Writer,
        colors: std.io.tty.Config,
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
        slot.source = std.fs.cwd().readFileAllocOptions(arena.allocator(), root, max_file_len, null, .of(u8), 0) catch {
            if (diagnostics) |d| try d.print("could not read the root file: {s}\n", .{root});
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
                .colors = colors,
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
