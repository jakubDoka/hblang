const std = @import("std");
const hb = @import("hb");
const graph = hb.backend.graph;
const Func = graph.Func(hb.backend.Builder);
const Node = Func.Node;

emit_: *const fn (*Machine, *Func, Opts) void,

const Machine = @This();

pub const Opts = struct {
    out: *std.Io.Writer,
};

pub fn init(comptime T: type) Machine {
    const fns = struct {
        pub fn emit(self: *T, func: *Func, opts: Opts) void {
            const fnc: *graph.Func(T) = @ptrCast(func);
            return self.emit(fnc, opts);
        }
    };

    return .{
        .emit_ = fns.emit,
    };
}

pub fn emit(self: *Machine, func: *Func, opts: Opts) void {
    return self.emit(func, opts);
}
