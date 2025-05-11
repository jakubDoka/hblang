test init {
    const ExampleMachine = struct {
        const Func = graph.Func(Node);

        pub const Node = union(enum) {
            CustomNode: bool,

            pub const is_basic_block_start: []const Func.Kind = &.{};
            pub const is_mem_op: []const Func.Kind = &.{};
            pub const is_basic_block_end: []const Func.Kind = &.{.CustomNode};
            pub const is_pinned: []const Func.Kind = &.{.CustomNode};

            pub fn isInterned(kind: Func.Kind) bool {
                // this is not a good idea since its supposed to be a control flow
                return kind == .CustomNode;
            }

            pub fn isSwapped(node: *Func.Node) bool {
                // means the output basic blocks should be reversed for reducing jumps
                return node.kind == .CustomNode and node.extra(.CustomNode).*;
            }

            pub fn idealize(func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
                _ = worklist;
                // relpace node whih the return value
                if (node.kind == .Start)
                    return func.addNode(.CustomNode, .top, &.{}, false);

                return null;
            }
        };

        pub fn emitFunc(self: *@This(), func: *Func, opts: EmitOptions) void {
            opts.optimizations.execute(Node, func);
            _ = self;
            unreachable;
        }

        pub fn emitData(self: *@This(), opts: DataOptions) void {
            _ = self;
            _ = opts;
            unreachable;
        }

        pub fn finalize(self: *@This()) std.ArrayListUnmanaged(u8) {
            _ = self;
            unreachable;
        }

        pub fn disasm(self: *@This(), opts: DisasmOpts) void {
            _ = self;
            _ = opts;
            unreachable;
        }

        pub fn run(self: *@This(), env: RunEnv) !usize {
            _ = self;
            _ = env;
            return 0;
        }

        pub fn deinit(self: *@This()) void {
            _ = self;
        }
    };

    var em = ExampleMachine{};
    _ = init(&em);
}

data: *anyopaque,
_emitFunc: *const fn (self: *anyopaque, func: *BuilderFunc, opts: EmitOptions) void,
_emitData: *const fn (self: *anyopaque, opts: DataOptions) void,
_finalize: *const fn (self: *anyopaque) std.ArrayListUnmanaged(u8),
_disasm: *const fn (self: *anyopaque, opts: DisasmOpts) void,
_run: *const fn (self: *anyopaque, env: RunEnv) anyerror!usize,
_deinit: *const fn (self: *anyopaque) void,

const std = @import("std");
const graph = @import("graph.zig");
const static_anal = @import("static_anal.zig");
const Builder = @import("Builder.zig");
const BuilderFunc = Builder.Func;
const Machine = @This();
const root = @import("../utils.zig");

pub const RunEnv = struct {
    name: []const u8,
    code: []const u8,
    output: std.io.AnyWriter = std.io.null_writer.any(),
    colors: std.io.tty.Config = .no_color,
};

pub const DataOptions = struct {
    id: u32,
    name: []const u8 = &.{},
    value: ValueSpec,

    pub const ValueSpec = union(enum) { init: []const u8, uninit: usize };
};

pub const EmitOptions = struct {
    id: u32,
    name: []const u8 = &.{},
    entry: bool = false,
    optimizations: struct {
        verbose: bool = false,
        dead_code_fuel: usize = 10000,
        mem2reg: bool = true,
        peephole_fuel: usize = 10000,
        do_gcm: bool = true,
        arena: ?*root.Arena = null,
        error_buf: ?*std.ArrayListUnmanaged(static_anal.Error) = null,

        pub const none = @This(){
            .mem2reg = false,
            .peephole_fuel = 0,
            .do_gcm = false,
        };

        pub fn execute(self: @This(), comptime MachNode: type, func: *graph.Func(MachNode)) void {
            const freestanding = @import("builtin").target.os.tag != .freestanding;

            if (self.peephole_fuel != 0) {
                func.iterPeeps(self.peephole_fuel, @TypeOf(func.*).idealizeDead);
            }

            if (self.mem2reg) {
                func.mem2reg.run();
            }

            if (self.peephole_fuel != 0) {
                func.iterPeeps(self.peephole_fuel, @TypeOf(func.*).idealize);
            }

            if (self.peephole_fuel != 0 and @hasDecl(MachNode, "idealizeMach")) {
                func.iterPeeps(self.peephole_fuel, MachNode.idealizeMach);
            }

            if (self.do_gcm) {
                func.gcm.buildCfg();
            }

            if (freestanding and self.verbose)
                func.fmtScheduled(
                    std.io.getStdErr().writer().any(),
                    std.io.tty.detectConfig(std.io.getStdErr()),
                );

            if (self.error_buf) |eb| {
                func.static_anal.analize(self.arena.?, eb);
            }
        }
    } = .{},
};

pub const DisasmOpts = struct {
    name: []const u8,
    bin: []const u8,
    out: std.io.AnyWriter = std.io.null_writer.any(),
    colors: std.io.tty.Config = .no_color,
};

pub fn init(data: anytype) Machine {
    const Type = @TypeOf(data.*);
    if (!@hasDecl(Type, "Node")) @compileError("expected `pub const Node = enum(union) { ... }` to be present");

    const fns = struct {
        fn emitFunc(self: *anyopaque, func: *BuilderFunc, opts: EmitOptions) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            const fnc: *graph.Func(Type.Node) = @alignCast(@ptrCast(func));
            slf.emitFunc(fnc, opts);
        }
        fn emitData(self: *anyopaque, opts: DataOptions) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            slf.emitData(opts);
        }
        fn finalize(self: *anyopaque) std.ArrayListUnmanaged(u8) {
            const slf: *Type = @alignCast(@ptrCast(self));
            return slf.finalize();
        }
        fn disasm(self: *anyopaque, opts: DisasmOpts) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            return slf.disasm(opts);
        }
        fn run(self: *anyopaque, env: RunEnv) !usize {
            const slf: *Type = @alignCast(@ptrCast(self));
            return slf.run(env);
        }
        fn deinit(self: *anyopaque) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            slf.deinit();
        }
    };

    return .{
        .data = data,
        ._emitFunc = fns.emitFunc,
        ._emitData = fns.emitData,
        ._finalize = fns.finalize,
        ._disasm = fns.disasm,
        ._run = fns.run,
        ._deinit = fns.deinit,
    };
}

/// generate apropriate final output for a function
///
/// this also runs optimization passes
pub fn emitFunc(self: Machine, func: *BuilderFunc, opts: EmitOptions) void {
    self._emitFunc(self.data, func, opts);
}

pub fn emitData(self: Machine, opts: DataOptions) void {
    self._emitData(self.data, opts);
}

/// package the final output (.eg object file)
/// this function should also restart the state for next emmiting
pub fn finalize(self: Machine) std.ArrayListUnmanaged(u8) {
    return self._finalize(self.data);
}

/// visualize already compiled code, its best to include different colors
/// for registers for better readability
pub fn disasm(self: Machine, opts: DisasmOpts) void {
    self._disasm(self.data, opts);
}

pub fn run(self: Machine, env: RunEnv) !usize {
    return self._run(self.data, env);
}

/// frees the internal resources
pub fn deinit(self: *Machine) void {
    self._deinit(self.data);
    self.* = undefined;
}
