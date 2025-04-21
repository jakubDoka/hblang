const std = @import("std");
const object = @import("../object.zig");
const root = @import("../root.zig");
const graph = root.backend.graph;
const Func = graph.Func(Node);
const Mach = root.backend.Mach;

builder: object.Coff.Builder = .{},

pub const Node = union(enum) {
    pub const is_basic_block_start: []const Func.Kind = &.{};
    pub const is_mem_op: []const Func.Kind = &.{};
    pub const is_basic_block_end: []const Func.Kind = &.{};
    pub const is_pinned: []const Func.Kind = &.{};

    pub fn isInterned(kind: Func.Kind) bool {
        _ = kind;
        return false;
    }

    pub fn isSwapped(node: *Func.Node) bool {
        _ = node;
        return false;
    }

    pub fn idealize(func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
        _ = func;
        _ = node;
        _ = worklist;
        return null;
    }
};

pub fn emitFunc(self: *@This(), func: *Func, opts: Mach.EmitOptions) void {
    opts.optimizations.execute(Node, func);
    _ = self;
    unreachable;
}

pub fn emitData(self: *@This(), opts: Mach.DataOptions) void {
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
