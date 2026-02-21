const std = @import("std");
const hb = @import("hb");
const graph = hb.backend.graph;
const Func = graph.Func(hb.backend.Builder);
const Node = Func.Node;
const Regalloc = hb.backend.Regalloc;

emit_: *const fn (*Machine, *Func, *Opts) void,

const Machine = @This();

pub const DisasmOpts = struct {
    name: []const u8,
    bin: []const u8,
    out: ?*std.Io.Writer,
    colors: std.io.tty.Config = .no_color,

    pub fn print(self: DisasmOpts, comptime fmt: []const u8, args: anytype) void {
        if (self.colors == .no_color) {
            if (self.out) |o| o.print(fmt, args) catch unreachable;
        } else {
            (std.debug).print(fmt, args);
        }
    }
};

pub const RunError = error{
    Timeout,
    Unreachable,
    OutOfMemory,
    MalformedBinary,
    SegmentationFault,
    InvalidCall,
    InvalidInstruction,
};

pub const RunEnv = struct {
    name: []const u8,
    code: []const u8,
    output: ?*std.Io.Writer = null,
    logs: ?*std.Io.Writer = null,
    colors: std.io.tty.Config = .no_color,
};

pub const Opts = struct {
    gpa: std.mem.Allocator,
    out: std.ArrayList(u8),
    big_constants: std.ArrayList(u8),
    relocs: std.ArrayList(FuncReloc),
    line_info: std.ArrayList(NodeLineInfo),
    builtins: Builtins,
    regalloc: Regalloc,
    spec: FuncSpec,

    pub fn addReloc(self: *Opts, reloc: FuncReloc) void {
        const slot = self.relocs.addOne(self.gpa) catch unreachable;
        slot.* = reloc;
        slot.offset = @intCast(self.out.items.len - slot.offset);
    }
};

pub const FuncSpec = struct {
    stack_size: u32,
};

pub const NodeLineInfo = struct {
    offset: u32,
    sloc: graph.Sloc align(4),
};

pub const Sym = enum(u32) { invalid = std.math.maxInt(u32), _ };

pub const Builtins = std.EnumArray(Builtin, Sym);

pub const Builtin = enum {
    memcpy,
};

pub const FuncReloc = extern struct {
    offset: u32 = undefined,
    target: Sym,
    meta: packed struct(u32) {
        addend: i29,
        size: RelocSize,
        kind: Kind,
    },

    const RelocSize = enum(u1) { @"4", @"8" };
    const Kind = enum(u2) { text, data, big_constant };
};

pub fn init(comptime T: type) Machine {
    const fns = struct {
        pub fn emit(self: *Machine, func: *Func, opts: *Opts) void {
            const slf: *T = @fieldParentPtr("mach", self);
            const fnc: *graph.Func(T) = @ptrCast(func);
            return slf.emit(fnc, opts);
        }
    };

    return .{ .emit_ = fns.emit };
}

pub fn emit(self: *Machine, func: *Func, opts: Opts) void {
    return self.emit(func, opts);
}
