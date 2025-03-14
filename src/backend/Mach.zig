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

        pub fn disasm(self: *@This(), out: std.io.AnyWriter, colors: std.io.tty.Config) void {
            _ = self;
            _ = out;
            _ = colors;
            unreachable;
        }
    };

    var em = ExampleMachine{};
    _ = init(&em);
}

data: *anyopaque,
_emitFunc: *const fn (self: *anyopaque, func: *BuilderFunc, opts: EmitOptions) void,
_emitData: *const fn (self: *anyopaque, opts: DataOptions) void,
_finalize: *const fn (self: *anyopaque) std.ArrayListUnmanaged(u8),
_disasm: *const fn (self: *anyopaque, out: std.io.AnyWriter, colors: std.io.tty.Config) void,

const std = @import("std");
const graph = @import("graph.zig");
const static_anal = @import("static_anal.zig");
const Builder = @import("Builder.zig");
const BuilderFunc = Builder.Func;
const Mach = @This();
const root = @import("../utils.zig");

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
        dead_code_fuel: usize = 1000,
        mem2reg: bool = true,
        peephole_fuel: usize = 1000,
        do_gcm: bool = true,
        arena: ?*root.Arena = null,
        error_buf: ?*std.ArrayListUnmanaged(static_anal.Error) = null,

        pub const none = @This(){
            .mem2reg = false,
            .peephole_fuel = 0,
            .do_gcm = false,
        };

        pub fn execute(self: @This(), comptime MachNode: type, func: *graph.Func(MachNode)) void {
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

            if (self.error_buf) |eb| {
                func.static_anal.analize(self.arena.?, eb);
            }
        }
    } = .{},
};

pub fn init(data: anytype) Mach {
    const Type = @TypeOf(data.*);
    if (!@hasDecl(Type, "Node")) @compileError("expected `pub const Node = enum(union) { ... }` to be present");

    return .{
        .data = data,
        ._emitFunc = struct {
            fn emitFunc(self: *anyopaque, func: *BuilderFunc, opts: EmitOptions) void {
                const slf: *Type = @alignCast(@ptrCast(self));
                const fnc: *graph.Func(Type.Node) = @alignCast(@ptrCast(func));
                slf.emitFunc(fnc, opts);
            }
        }.emitFunc,
        ._emitData = struct {
            fn emitData(self: *anyopaque, opts: DataOptions) void {
                const slf: *Type = @alignCast(@ptrCast(self));
                slf.emitData(opts);
            }
        }.emitData,
        ._finalize = struct {
            fn finalize(self: *anyopaque) std.ArrayListUnmanaged(u8) {
                const slf: *Type = @alignCast(@ptrCast(self));
                return slf.finalize();
            }
        }.finalize,
        ._disasm = struct {
            fn disasm(self: *anyopaque, out: std.io.AnyWriter, colors: std.io.tty.Config) void {
                const slf: *Type = @alignCast(@ptrCast(self));
                return slf.disasm(out, colors);
            }
        }.disasm,
    };
}

/// generate apropriate final output for a function
///
/// this also runs optimization passes
pub fn emitFunc(self: Mach, func: *BuilderFunc, opts: EmitOptions) void {
    self._emitFunc(self.data, func, opts);
}

pub fn emitData(self: Mach, opts: DataOptions) void {
    self._emitData(self.data, opts);
}

/// package the final output (.eg object file)
pub fn finalize(self: Mach) std.ArrayListUnmanaged(u8) {
    return self._finalize(self.data);
}

/// visualize already compiled code, its best to include different colors
/// for registers for better readability
pub fn disasm(self: Mach, out: std.io.AnyWriter, colors: std.io.tty.Config) void {
    self._disasm(self.data, out, colors);
}
