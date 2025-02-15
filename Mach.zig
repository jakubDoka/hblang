data: *anyopaque,
_emitFunc: *const fn (self: *anyopaque, func: *Func, opts: EmitOptions) void,
_finalize: *const fn (self: *anyopaque) std.ArrayList(u8),
_disasm: *const fn (self: *anyopaque, out: std.io.AnyWriter, colors: std.io.tty.Config) void,

const std = @import("std");
const graph = @import("Func.zig");
const Builder = @import("Builder.zig");
const Func = Builder.Func;
const Mach = @This();

pub fn init(data: anytype) Mach {
    const Type = @TypeOf(data.*);

    return .{
        .data = data,
        ._emitFunc = struct {
            fn emitFunc(self: *anyopaque, func: *Func, opts: EmitOptions) void {
                const slf: *Type = @alignCast(@ptrCast(self));
                const fnc: *graph.Func(Type.Node) = @alignCast(@ptrCast(func));
                slf.emitFunc(fnc, opts);
            }
        }.emitFunc,
        ._finalize = struct {
            fn finalize(self: *anyopaque) std.ArrayList(u8) {
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

pub const EmitOptions = struct {
    id: u32,
    name: []const u8 = &.{},
    optimizations: struct {
        dead_code_fuel: usize = 1000,
        mem2reg: bool = true,
        peephole_fuel: usize = 1000,

        pub const none = @This(){ .dead_code_fuel = 0, .mem2reg = false, .peephole_fuel = 0 };

        pub fn execute(self: @This(), comptime MachNode: type, func: *graph.Func(MachNode)) void {
            if (self.dead_code_fuel != 0) {
                func.iterPeeps(self.dead_code_fuel, @TypeOf(func.*).idealizeDead);
            }

            if (self.mem2reg) {
                func.mem2reg();
            }

            if (self.peephole_fuel != 0) {
                func.iterPeeps(self.peephole_fuel, @TypeOf(func.*).idealize);
            }
        }
    } = .{},
};

/// Translates the function into machine code and ideally alos relocations
///  - func: functions has `gcm()`
pub fn emitFunc(self: Mach, func: *Func, opts: EmitOptions) void {
    self._emitFunc(self.data, func, opts);
}

pub fn finalize(self: Mach) std.ArrayList(u8) {
    return self._finalize(self.data);
}

pub fn disasm(self: Mach, out: std.io.AnyWriter, colors: std.io.tty.Config) void {
    self._disasm(self.data, out, colors);
}
