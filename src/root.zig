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

const max_file_len = std.math.maxInt(u31);

pub const CompileOptions = struct {
    diagnostics: std.io.AnyWriter = std.io.null_writer.any(),
    error_colors: std.io.tty.Config = .no_color,
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
                    self.diagnostics.print("--{s} <{s}>", .{ f.name, @errorName(err) }) catch unreachable;
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

            try self.diagnostics.print("unknown flag: --{s}", .{arg});
            std.process.exit(1);
        }
    }
};

pub fn SharedQueue(comptime T: type) type {
    return struct {
        shards: []Shard,
        progress: usize = 0,
        cached_counter: usize = 0,
        self_id: usize = std.math.maxInt(usize),
        tasks: []const []T,

        const Self = @This();

        pub const Shard = struct {
            reserved: std.atomic.Value(usize) align(std.atomic.cache_line),
            available: std.atomic.Value(usize) align(std.atomic.cache_line),
        };

        pub fn size_of(thread_count: usize, capacity: usize) usize {
            return @sizeOf(T) * capacity * thread_count +
                @sizeOf(Shard) * thread_count +
                @sizeOf([]T) * thread_count;
        }

        pub fn init(arena: *Arena, thread_count: usize, capacity: usize) Self {
            const tasks = arena.alloc([]T, thread_count);
            const shards = arena.alloc(Shard, thread_count);
            for (shards, tasks) |*s, *t| {
                s.reserved.store(0, .unordered);
                s.available.store(0, .unordered);
                t.* = arena.alloc(T, capacity);
            }

            return .{ .shards = shards, .tasks = tasks };
        }

        pub fn enque(self: *Self, tasks: []const T) void {
            const push_to = (if (!std.meta.hasMethod(T, "hash") and std.meta.hasUniqueRepresentation(T))
                std.hash.Wyhash.hash(0, @ptrCast(tasks))
            else
                T.hash(tasks)) & self.shards.len - 1;

            const idx = self.shards[push_to].reserved.fetchAdd(tasks.len, .monotonic);
            @memcpy(self.tasks[push_to][idx..][0..tasks.len], tasks);
            while (self.shards[push_to].available.cmpxchgWeak(idx, idx + tasks.len, .release, .monotonic) != null) {}
        }

        pub fn dequeue(self: *Self) ?T {
            const shard = self.shards[self.self_id];
            if (self.progress == self.cached_counter) {
                self.cached_counter = shard.available.load(.acquire);
                if (self.cached_counter == self.progress) return null;
            }
            self.progress += 1;
            return self.tasks[self.self_id][self.progress - 1];
        }
    };
}

test "queue shard" {
    const tasks_per_thread = 1024 * 1024;

    const thread = struct {
        fn runShardThread(ashard: SharedQueue(u64)) void {
            var shard = ashard;
            for (0..tasks_per_thread) |i| {
                var tasks: u64 = i + shard.self_id * tasks_per_thread;
                shard.enque((&tasks)[0..1]);
                _ = shard.dequeue();
            }
        }
    };

    const thread_count = 8;

    var arena = Arena.init(SharedQueue(u64).size_of(thread_count, tasks_per_thread * thread_count));
    var shard = SharedQueue(u64).init(&arena, thread_count, tasks_per_thread * thread_count);

    const Thrd = struct {
        thread: std.Thread,
    };

    const tsrgs = std.testing.allocator.alloc(Thrd, thread_count) catch unreachable;
    defer std.testing.allocator.free(tsrgs);
    for (tsrgs, 0..) |*thrd, i| {
        shard.self_id = i;
        thrd.* = .{ .thread = try std.Thread.spawn(.{}, thread.runShardThread, .{shard}) };
    }

    for (tsrgs) |thrd| {
        thrd.thread.join();
    }

    var bitset = try std.DynamicBitSetUnmanaged.initEmpty(std.testing.allocator, thread_count * tasks_per_thread);
    defer bitset.deinit(std.testing.allocator);

    for (shard.tasks, shard.shards) |thrd, shrd| {
        for (thrd[0..shrd.available.load(.unordered)]) |task| {
            bitset.set(@bitCast(task));
        }
    }

    std.debug.assert(bitset.count() == thread_count * tasks_per_thread);
}

pub const Task = struct {
    id: struct {
        file: frontend.Types.File,
        captures_len: u16,
        ast: frontend.Ast.Id,
    },
    captures: [*]const frontend.types.Builtin,

    pub fn hash(tasks: []const Task) u64 {
        var hasher = std.hash.Wyhash.init(0);
        for (tasks) |task| {
            hasher.update(std.mem.asBytes(&task.id));
            hasher.update(@ptrCast(task.captures[0..task.id.captures_len]));
        }
        return hasher.final();
    }

    pub fn tryFronFn(types: *frontend.Types, func: utils.EntId(frontend.types.Func)) !Task {
        const fnc: *frontend.types.Func = types.store.get(func);

        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        const captures = tmp.arena.alloc(frontend.types.Builtin, fnc.key.captures().len);
        for (fnc.key.captures(), captures) |cap, *c| {
            if (cap.ty != .type) return error.TooComplex;
            const vty: frontend.Types.Id = @enumFromInt(cap.value);
            if (vty.data() != .Builtin) return error.TooComplex;
            c.* = vty.data().Builtin;
        }

        return Task{
            .id = .{
                .file = fnc.key.loc.file,
                .captures_len = @intCast(captures.len),
                .ast = fnc.key.loc.ast,
            },
            .captures = types.pool.arena.dupe(frontend.types.Builtin, captures).ptr,
        };
    }

    pub fn intoFunc(self: Task, types: *frontend.Types) ?utils.EntId(frontend.types.Func) {
        _ = self; // autofix
        _ = types; // autofix

        // const slot, const alloc = self.types.intern(.Func, .{
        //     .loc = .{
        //         .scope = typ,
        //         .file = tmpl.key.loc.file,
        //         .ast = tmpl.key.loc.ast,
        //     },
        //     .name = "-",
        //     .captures = captures[0..capture_idx],
        // });

        // if (!slot.found_existing) {
        //     const alc = self.types.store.get(alloc);
        //     alc.* = .{
        //         .key = alc.key,
        //         .args = self.types.pool.arena.dupe(Types.Id, arg_tys),
        //         .ret = ret,
        //     };
        //     alc.key.captures =
        //         self.types.pool.arena.dupe(Types.Scope.Capture, alc.key.captures);
        //     alc.is_inline = tmpl.is_inline;
        // }
        unreachable;
    }
};

pub const Queue = SharedQueue(Task);

pub const Threading = union(enum) {
    single: struct {
        types: *frontend.Types,
    },
    multi: Multi,

    pub const Multi = struct {
        pool: std.Thread.Pool,
        queue: SharedQueue(Task),
        types: []*frontend.Types,
    };
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

    var type_system_memory = Arena.init(opts.type_system_memory);
    errdefer type_system_memory.deinit();

    if (opts.fmt_stdout) {
        const source = try std.fs.cwd().readFileAllocOptions(
            type_system_memory.allocator(),
            opts.root_file,
            max_file_len,
            null,
            @alignOf(u8),
            0,
        );
        const ast = try hb.frontend.Ast.init(&type_system_memory, .{
            .path = opts.root_file,
            .code = source,
            .diagnostics = opts.diagnostics,
            .mode = opts.parser_mode,
            .colors = opts.error_colors,
        });

        var buf = std.ArrayList(u8).init(type_system_memory.allocator());
        try ast.fmt(&buf);

        try opts.output.writeAll(buf.items);
        return .{ .ast = &.{}, .arena = type_system_memory };
    }

    const asts, const base = try Loader.loadAll(
        &type_system_memory,
        opts.path_projection,
        opts.root_file,
        opts.diagnostics,
        opts.error_colors,
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
        return .{ .ast = asts, .arena = type_system_memory };
    }

    var shared_arena: Arena = undefined;
    var threading: Threading = if (opts.extra_threads == 0) .{ .single = .{
        .types = b: {
            const types = hb.frontend.Types.init(type_system_memory, asts, opts.diagnostics);
            types.target = opts.target;
            types.colors = opts.error_colors;
            break :b types;
        },
    } } else b: {
        const thread_count = opts.extra_threads + 1;

        shared_arena = Arena.init(
            Queue.size_of(
                thread_count,
                opts.shared_queue_capacity,
            ) + @sizeOf(Queue) * thread_count + 4096,
        );

        var pool: std.Thread.Pool = undefined;
        try std.Thread.Pool.init(&pool, .{
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

        break :b .{
            .multi = .{
                .pool = pool,
                .queue = .init(
                    &shared_arena,
                    opts.extra_threads + 1,
                    opts.shared_queue_capacity / (opts.extra_threads + 1) * 2,
                ),
                .types = types,
            },
        };
    };

    var bckend, const abi: hb.backend.graph.CallConv = if (std.mem.startsWith(u8, opts.target, "hbvm-ableos")) backend: {
        const slot = threading.single.types.pool.arena.create(hb.hbvm.HbvmGen);
        slot.* = hb.hbvm.HbvmGen{ .gpa = &threading.single.types.pool };
        break :backend .{ hb.backend.Machine.init(slot), .ablecall };
    } else if (std.mem.startsWith(u8, opts.target, "x86_64-windows")) backend: {
        const slot = threading.single.types.pool.arena.create(hb.x86_64.X86_64Gen);
        slot.* = hb.x86_64.X86_64Gen{ .gpa = &threading.single.types.pool, .object_format = .coff };
        break :backend .{ hb.backend.Machine.init(slot), .fastcall };
    } else if (std.mem.startsWith(u8, opts.target, "x86_64-linux")) backend: {
        const slot = threading.single.types.pool.arena.create(hb.x86_64.X86_64Gen);
        slot.* = hb.x86_64.X86_64Gen{ .gpa = &threading.single.types.pool, .object_format = .elf };
        break :backend .{ hb.backend.Machine.init(slot), .systemv };
    } else if (std.mem.startsWith(u8, opts.target, "null")) backend: {
        var value = hb.backend.Machine.Null{};
        switch (threading) {
            .single => |s| s.types.target = "x86_64-linux",
            .multi => |m| for (m.types) |t| {
                t.target = "x86_64-linux";
            },
        }
        break :backend .{ hb.backend.Machine.init(&value), .systemv };
    } else {
        try opts.diagnostics.print(
            "{s} is unsupported target, only `x86_64-(windows|linux)` and `hbvm-ableos` are supported",
            .{opts.target},
        );
        return error.Failed;
    };
    defer bckend.deinit();

    var root_tmp = utils.Arena.scrath(null);
    defer root_tmp.deinit();

    const errored = hb.frontend.Codegen.emitReachable(
        root_tmp.arena,
        &threading,
        .{ .cc = abi },
        bckend,
        opts.optimizations,
        !opts.no_entry,
        .{},
    );
    if (errored) {
        try opts.diagnostics.print("failed due to previous errors\n", .{});
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
        try opts.diagnostics.print("multi threading code emmision is not yet supported\n", .{});
        return error.Failed;
    }

    const types = threading.single.types;

    if (opts.dump_asm) {
        const out = bckend.finalizeBytes(.{
            .gpa = root_tmp.arena.allocator(),
            .optimizations = optimizations,
            .builtins = types.getBuiltins(),
        });

        if (types.dumpAnalErrors(&anal_errors)) {
            try opts.diagnostics.print("failed due to previous errors\n", .{});
            return error.Failed;
        }

        bckend.disasm(.{
            .name = name,
            .bin = out.items,
            .out = opts.output,
            .colors = opts.colors,
        });
        return .{ .ast = asts, .arena = types.pool.arena };
    }

    if (opts.vendored_test and !@import("options").dont_simulate) {
        const expectations: test_utils.Expectations = .init(&asts[0], &types.pool.arena);

        const out = bckend.finalizeBytes(.{
            .gpa = types.pool.arena.allocator(),
            .optimizations = optimizations,
            .builtins = types.getBuiltins(),
        });

        if (types.dumpAnalErrors(&anal_errors)) {
            try opts.diagnostics.print("failed due to previous errors\n", .{});
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

        return .{ .arena = types.pool.arena, .ast = asts };
    }

    if (opts.log_stats) {
        try opts.diagnostics.writeAll("type system:\n");
        inline for (std.meta.fields(@TypeOf(types.store.rpr))) |field| {
            try opts.diagnostics.print(
                "  {s:<8}: {}\n",
                .{ field.name, @field(types.store.rpr, field.name).items.len },
            );
        }
        try opts.diagnostics.print("  arena   : {}\n", .{types.pool.arena.consumed()});

        inline for (std.meta.fields(@TypeOf(types.stats))) |field| {
            try opts.diagnostics.print("  {s:<8}: {}\n", .{ field.name, @field(types.stats, field.name) });
        }

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

        try opts.diagnostics.print("  runtime functions: {}\n", .{runtim_functions});
        try opts.diagnostics.print("  comptime functions: {}\n", .{comptime_functions});
        try opts.diagnostics.print("  dead functions: {}\n", .{dead_functions});
        try opts.diagnostics.print("  stale pool memory: {}\n", .{types.pool.staleMemory()});
    }

    const logs = if (opts.log_stats) opts.diagnostics else null;

    if (opts.colors == .no_color or opts.mangle_terminal) {
        bckend.finalize(.{
            .output = opts.output,
            .optimizations = optimizations,
            .builtins = types.getBuiltins(),
            .logs = logs,
        });

        if (types.dumpAnalErrors(&anal_errors)) {
            try opts.diagnostics.print("failed due to previous errors\n", .{});
            return error.Failed;
        }

        return .{ .ast = asts, .arena = types.pool.arena };
    } else {
        bckend.finalize(.{
            .output = std.io.null_writer.any(),
            .optimizations = optimizations,
            .builtins = types.getBuiltins(),
            .logs = logs,
        });

        if (types.dumpAnalErrors(&anal_errors)) {
            try opts.diagnostics.print("failed due to previous errors\n", .{});
            return error.Failed;
        }

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
        diagnostics: std.io.AnyWriter,
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
