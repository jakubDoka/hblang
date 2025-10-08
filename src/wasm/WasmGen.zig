const std = @import("std");
pub const Set = std.DynamicBitSetUnmanaged;

const root = @import("hb");
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Regalloc = root.backend.Regalloc;
const utils = root.utils;

const WasmGen = @This();
const Func = graph.Func(WasmGen);

gpa: std.mem.Allocator,
mach: Mach = .init(WasmGen),

pub const classes = enum {};

pub fn emitFunc(self: *WasmGen, func: *Func, opts: Mach.EmitOptions) void {
    _ = func;
    _ = opts;
    _ = self;
    unreachable;
}

pub fn emitData(self: *WasmGen, opts: Mach.DataOptions) void {
    _ = opts;
    _ = self;
    unreachable;
}

pub fn finalize(self: *WasmGen, opts: Mach.FinalizeOptions) void {
    root.wasm.object.flush(
        self.mach.out,
        opts.output orelse return,
    ) catch unreachable;
}

pub fn disasm(self: *WasmGen, opts: Mach.DisasmOpts) void {
    _ = opts;
    _ = self;
    unreachable;
}

pub fn run(self: *WasmGen, opts: Mach.RunEnv) !usize {
    _ = opts;
    _ = self;
    unreachable;
}

pub fn deinit(self: *WasmGen) void {
    _ = self;
    unreachable;
}
