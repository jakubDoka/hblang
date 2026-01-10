regs: std.EnumArray(isa.Reg, u64) = .{ .values = [_]u64{0} ++ [_]u64{undefined} ** 255 },
ip: usize = undefined,
fuel: usize = 0,

const std = @import("std");
const isa = @import("isa.zig");
const utils = @import("utils-lib");
const Vm = @This();
const debug = @import("builtin").mode == .Debug;

const one: u64 = 1;

pub const Error = error{
    MemOob,
    InvalidOp,
    Unreachable,
    DivideByZero,
    Timeout,
};

pub const SafeContext = struct {
    color_cfg: std.io.tty.Config = .no_color,
    writer: ?*std.Io.Writer = null,
    symbols: std.AutoHashMapUnmanaged(u32, []const u8) = .{},
    memory: []u8,
    code_start: usize,
    code_end: usize,

    const check_ops = true;
    const assume_no_div_by_zero = false;
    const Self = @This();

    fn read(self: *Self, src: usize, dst: []u8) !void {
        try self.assertOutsideCode(src);
        @memcpy(dst, self.memory[src..][0..dst.len]);
    }

    fn write(self: *Self, src: []u8, dst: usize) !void {
        try self.assertOutsideCode(dst);
        @memcpy(self.memory[dst..][0..src.len], src);
    }

    fn setColor(self: *Self, color: std.io.tty.Color) !void {
        try utils.setColor(self.color_cfg, self.writer.?, color);
    }

    fn memmove(self: *Self, dst: usize, src: usize, len: usize) !void {
        try self.assertOutsideCode(src);
        try self.assertOutsideCode(dst);
        const srcp = self.memory[src..];
        const dstp = self.memory[dst..];
        if (dst + len <= src or src + len <= dst) {
            @memcpy(dstp[0..len], srcp[0..len]);
        } else if (dst <= src) {
            std.mem.copyForwards(u8, dstp[0..len], srcp[0..len]);
        } else {
            std.mem.copyBackwards(u8, dstp[0..len], srcp[0..len]);
        }
    }

    fn assertOutsideCode(self: *const Self, pos: usize) !void {
        if (self.code_start <= pos and pos < self.code_end) return error.MemOob;
        if (self.memory.len <= pos) return error.MemOob;
    }

    fn progRead(self: *Self, comptime T: type, src: usize) !*align(1) const T {
        if (self.code_start != self.code_end) {
            if (self.code_start > src or src + @sizeOf(T) > self.code_end) {
                return error.MemOob;
            }
        } else {
            if (self.memory.len < src + @sizeOf(T)) {
                return error.MemOob;
            }
        }
        const mem = self.memory[src..][0..@sizeOf(T)];
        return @ptrCast(mem.ptr);
    }
};

pub fn run(self: *Vm, ctx: anytype) Error!isa.Op {
    @setEvalBranchQuota(3000);
    while (self.fuel > 0) : (self.fuel -= 1) switch (try self.readOp(ctx)) {
        .un => return error.Unreachable,
        .nop => {},
        .tx, .eca, .ebp => |op| return op,
        .cp => {
            const args = try self.readArgs(.cp, ctx);
            self.writeReg(args.arg0, self.regs.get(args.arg1));
        },
        .swa => {
            const args = try self.readArgs(.swa, ctx);
            std.mem.swap(u64, self.regs.getPtr(args.arg0), self.regs.getPtr(args.arg1));
        },
        inline .@"and", .@"or", .xor, .cmpu, .cmps, .andi, .ori, .xori, .cmpui, .cmpsi => |op| {
            const args = try self.readArgs(op, ctx);
            const lhs = self.regs.get(args.arg1);
            const rhs = if (@TypeOf(args.arg2) != isa.Reg) args.arg2 else self.regs.get(args.arg2);
            const res = switch (op) {
                .@"and", .andi => lhs & rhs,
                .@"or", .ori => lhs | rhs,
                .xor, .xori => lhs ^ rhs,
                .cmpu, .cmpui => b: {
                    if (lhs < rhs) break :b toUnsigned(64, -1);
                    if (lhs == rhs) break :b 0;
                    break :b 1;
                },
                .cmps, .cmpsi => b: {
                    const slhs = toSigned(64, lhs);
                    const srhs = toSigned(64, rhs);
                    if (slhs < srhs) break :b toUnsigned(64, -1);
                    if (slhs == srhs) break :b 0;
                    break :b 1;
                },
                else => @compileError("what"),
            };
            self.writeReg(args.arg0, res);
        },
        inline .add8, .add16, .add32, .add64 => |op| try self.ibinOp(.add8, op, ctx),
        inline .addi8, .addi16, .addi32, .addi64 => |op| try self.ibinOp(.addi8, op, ctx),
        inline .sub8, .sub16, .sub32, .sub64 => |op| try self.ibinOp(.sub8, op, ctx),
        inline .mul8, .mul16, .mul32, .mul64 => |op| try self.ibinOp(.mul8, op, ctx),
        inline .muli8, .muli16, .muli32, .muli64 => |op| try self.ibinOp(.muli8, op, ctx),
        inline .slu8, .slu16, .slu32, .slu64 => |op| try self.ibinOp(.slu8, op, ctx),
        inline .slui8, .slui16, .slui32, .slui64 => |op| try self.ibinOp(.slui8, op, ctx),
        inline .sru8, .sru16, .sru32, .sru64 => |op| try self.ibinOp(.sru8, op, ctx),
        inline .srui8, .srui16, .srui32, .srui64 => |op| try self.ibinOp(.srui8, op, ctx),
        inline .srs8, .srs16, .srs32, .srs64 => |op| try self.ibinOp(.srs8, op, ctx),
        inline .srsi8, .srsi16, .srsi32, .srsi64 => |op| try self.ibinOp(.srsi8, op, ctx),
        inline .diru8, .diru16, .diru32, .diru64 => |op| try self.idivOp(.diru8, op, ctx),
        inline .dirs8, .dirs16, .dirs32, .dirs64 => |op| try self.idivOp(.dirs8, op, ctx),
        inline .sxt8, .sxt16, .sxt32 => |op| {
            const mask = comptime OpInteger(.sxt8, op);
            const width = @bitSizeOf(mask);
            const args = try self.readArgs(op, ctx);
            const opera: mask = @truncate(self.regs.get(args.arg1));
            self.writeReg(args.arg0, toUnsigned(64, toSigned(width, opera)));
        },
        inline .not, .neg, .itf32, .itf64 => |op| {
            const args = try self.readArgs(op, ctx);
            const opera = self.regs.get(args.arg1);
            const res = switch (op) {
                .not => @intFromBool(opera == 0),
                .neg => -%opera,
                .itf32 => @as(u32, @bitCast(@as(f32, @floatFromInt(toSigned(64, @truncate(opera)))))),
                .itf64 => @as(u64, @bitCast(@as(f64, @floatFromInt(toSigned(64, opera))))),
                else => @compileError("baka"),
            };
            self.writeReg(args.arg0, res);
        },
        inline .st, .ld, .str, .ldr, .str16, .ldr16 => |op| {
            const addPc = op != .ld and op != .st;
            const args = try self.readArgs(op, ctx);
            const ptr = (if (addPc) self.ip -% isa.instrSize(op) else 0) +%
                self.regs.get(args.arg1) +% toUnsigned(64, args.arg2);
            const regp: [*]u8 = @ptrCast(@alignCast(self.regs.getPtr(args.arg0)));
            switch (op) {
                .st, .str, .str16 => try ctx.write(regp[0..args.arg3], @truncate(ptr)),
                .ld, .ldr, .ldr16 => try ctx.read(@truncate(ptr), regp[0..args.arg3]),
                else => @compileError("co"),
            }
        },
        inline .li8, .li16, .li32, .li64 => |op| {
            const args = try self.readArgs(op, ctx);
            self.writeReg(args.arg0, args.arg1);
        },
        inline .lra, .lra16 => |op| {
            const args = try self.readArgs(op, ctx);
            const addr = self.ip -% isa.instrSize(op) +% self.regs.get(args.arg1) +% @as(usize, @bitCast(@as(isize, args.arg2)));
            self.writeReg(args.arg0, addr);
        },
        .bmc => {
            const args = try self.readArgs(.bmc, ctx);
            // yep, retarded
            try ctx.memmove(@truncate(self.regs.get(args.arg1)), @truncate(self.regs.get(args.arg0)), args.arg2);
        },
        .brc => {
            const args = try self.readArgs(.brc, ctx);
            const dst = self.regs.values[@intFromEnum(args.arg0)..][0..args.arg2];
            const src = self.regs.values[@intFromEnum(args.arg1)..][0..args.arg2];
            if (@intFromEnum(args.arg0) <= @intFromEnum(args.arg1)) {
                std.mem.copyForwards(u64, dst, src);
            } else {
                std.mem.copyBackwards(u64, dst, src);
            }
        },
        inline .jmp, .jmp16 => |op| {
            const args = try self.readArgs(op, ctx);
            self.ip +%= @as(usize, @truncate(toUnsigned(64, args.arg0))) -% isa.instrSize(op);
        },
        inline .jal, .jala => |op| {
            const args = try self.readArgs(op, ctx);
            self.writeReg(args.arg0, self.ip);
            self.ip = (if (op == .jal) self.ip -% isa.instrSize(op) else 0);
            self.ip +%= @as(usize, @truncate(self.regs.get(args.arg1))) +% @as(usize, @truncate(toUnsigned(64, args.arg2)));
        },
        inline .jltu, .jgtu, .jlts, .jgts, .jeq, .jne => |op| {
            const args = try self.readArgs(op, ctx);
            const lhs = self.regs.get(args.arg0);
            const rhs = self.regs.get(args.arg1);
            if (switch (op) {
                .jltu => lhs < rhs,
                .jgtu => lhs > rhs,
                .jlts => toSigned(64, lhs) < toSigned(64, rhs),
                .jgts => toSigned(64, lhs) > toSigned(64, rhs),
                .jeq => lhs == rhs,
                .jne => lhs != rhs,
                else => @compileError("ke"),
            }) {
                self.ip +%= @as(usize, @truncate(toUnsigned(64, args.arg2))) -% isa.instrSize(op);
            }
        },
        inline .fadd32, .fadd64 => |op| try self.fbinOp(.fadd32, op, ctx),
        inline .fsub32, .fsub64 => |op| try self.fbinOp(.fsub32, op, ctx),
        inline .fmul32, .fmul64 => |op| try self.fbinOp(.fmul32, op, ctx),
        inline .fdiv32, .fdiv64 => |op| try self.fbinOp(.fdiv32, op, ctx),
        inline .fma32, .fma64 => |op| try self.fbinOp(.fma32, op, ctx),
        inline .finv32, .finv64 => |op| try self.fbinOp(.finv32, op, ctx),
        inline .fcmplt32, .fcmplt64 => |op| try self.fbinOp(.fcmplt32, op, ctx),
        inline .fcmpgt32, .fcmpgt64 => |op| try self.fbinOp(.fcmpgt32, op, ctx),
        inline .fti32, .fti64 => |op| try self.fbinOp(.fti32, op, ctx),
        inline .fc32t64, .fc64t32 => |op| try self.fbinOp(.fc32t64, op, ctx),
    };
    return error.Timeout;
}

inline fn fbinOp(self: *Vm, comptime base: isa.Op, comptime op: isa.Op, ctx: anytype) !void {
    const Repr = OpFloat(base, op);
    const args = try self.readArgs(op, ctx);
    const Args = @TypeOf(args);
    const lhs = self.readFloatReg(Repr, args.arg1);
    const rhs = if (@hasField(Args, "arg2") and @TypeOf(args.arg2) == isa.Reg) self.readFloatReg(Repr, args.arg2);
    const rhs2 = if (@hasField(Args, "arg3")) self.readFloatReg(Repr, args.arg3);
    const res = switch (base) {
        .fadd32 => lhs + rhs,
        .fsub32 => lhs - rhs,
        .fmul32 => lhs * rhs,
        .fdiv32 => lhs / rhs,
        .fma32 => lhs * rhs + rhs2,
        .finv32 => 1.0 / lhs,
        .fcmplt32 => lhs < rhs,
        .fcmpgt32 => lhs > rhs,
        .fc32t64 => @as(f64, @floatCast(lhs)),
        .fc64t32 => @as(f32, @floatCast(lhs)),
        .fti32 => b: {
            const ty = if (Repr == f32) i32 else i64;
            break :b @as(ty, @intFromFloat(lhs));
        },
        else => |t| @compileError(std.fmt.comptimePrint("unspupported op {any}", .{t})),
    };
    self.writeReg(args.arg0, switch (@TypeOf(res)) {
        bool => @intFromBool(res),
        f32 => @as(u32, @bitCast(res)),
        f64 => @as(u64, @bitCast(res)),
        i32, i64 => toUnsigned(64, res),
        else => @compileError("wat"),
    });
}

inline fn readFloatReg(self: *Vm, comptime Repr: type, src: isa.Reg) Repr {
    if (src == .null) return 0;
    const IntRepr = if (Repr == f32) u32 else u64;
    return @bitCast(@as(IntRepr, @truncate(self.regs.get(src))));
}

inline fn ibinOp(self: *Vm, comptime base: isa.Op, comptime op: isa.Op, ctx: anytype) !void {
    const Repr = OpInteger(base, op);
    const width = @bitSizeOf(Repr);
    const args = try self.readArgs(op, ctx);
    const lhs: Repr = @truncate(self.regs.get(args.arg1));
    const rhs: Repr = if (@TypeOf(args.arg2) != isa.Reg) args.arg2 else @truncate(self.regs.get(args.arg2));
    const res = switch (base) {
        .add8, .addi8 => lhs +% rhs,
        .sub8 => lhs -% rhs,
        .mul8, .muli8 => lhs *% rhs,
        .slu8, .slui8 => @shlWithOverflow(lhs, @as(std.math.Log2Int(@TypeOf(rhs)), @truncate(rhs)))[0],
        .sru8, .srui8 => lhs >> @truncate(rhs),
        .srs8, .srsi8 => toUnsigned(width, toSigned(width, lhs) >> @truncate(rhs)),
        else => |t| @compileError(std.fmt.comptimePrint("unspupported op {any}", .{t})),
    };
    self.writeReg(args.arg0, res);
}

inline fn idivOp(self: *Vm, comptime base: isa.Op, comptime op: isa.Op, ctx: anytype) !void {
    const Ctx = std.meta.Child(@TypeOf(ctx));
    const Repr = OpInteger(base, op);
    const width = @bitSizeOf(Repr);
    const args = try self.readArgs(op, ctx);
    const lhs: Repr = @truncate(self.regs.get(args.arg2));
    const rhs: Repr = @truncate(self.regs.get(args.arg3));
    if (!Ctx.assume_no_div_by_zero and rhs == 0) return error.DivideByZero;
    switch (base) {
        .diru8 => {
            self.writeReg(args.arg0, lhs / rhs);
            self.writeReg(args.arg1, lhs % rhs);
        },
        .dirs8 => {
            const slhs = toSigned(width, lhs);
            const srhs = toSigned(width, rhs);
            self.writeReg(args.arg0, toUnsigned(width, @divTrunc(slhs, srhs)));
            self.writeReg(args.arg1, toUnsigned(width, @mod(slhs, srhs)));
        },
        else => |t| @compileError(std.fmt.comptimePrint("unspupported op {any}", .{t})),
    }
}

pub inline fn toSigned(comptime width: u16, value: std.meta.Int(.unsigned, width)) std.meta.Int(.signed, width) {
    return @bitCast(value);
}

pub inline fn toUnsigned(comptime width: u16, value: std.meta.Int(.signed, width)) std.meta.Int(.unsigned, width) {
    return @bitCast(value);
}

fn OpInteger(base: isa.Op, offset: isa.Op) type {
    return .{ u8, u16, u32, u64 }[@as(u8, @intFromEnum(offset)) - @as(u8, @intFromEnum(base))];
}

fn OpFloat(base: isa.Op, offset: isa.Op) type {
    return .{ f32, f64 }[@as(u8, @intFromEnum(offset)) - @as(u8, @intFromEnum(base))];
}

inline fn writeReg(self: *Vm, dst: isa.Reg, value: u64) void {
    if (dst == .null) return;
    self.regs.set(dst, value);
}

fn readOp(self: *Vm, ctx: anytype) !isa.Op {
    const byte = try self.progRead(u8, ctx);
    self.ip += 1;
    if (std.meta.Child(@TypeOf(ctx)).check_ops and byte > isa.instr_count) {
        return error.InvalidOp;
    }

    if (ctx.writer) |wrt| {
        errdefer unreachable;

        const prev_ip = self.ip;
        const instr = @as(isa.Op, @enumFromInt(byte));
        const instr_name = @tagName(instr);
        for (instr_name.len..isa.max_instr_len) |_| try wrt.writeAll(" ");
        try wrt.writeAll(instr_name);
        const argTys = isa.spec[byte][1];
        try self.readOpArgs(instr, argTys, ctx, wrt);
        try wrt.writeAll("\n");
        self.ip = prev_ip;
    }

    return @enumFromInt(byte);
}

fn readOpArgs(self: *Vm, op: isa.Op, argTys: []const u8, ctx: anytype, wrt: *std.Io.Writer) !void {
    const prev_ip = self.ip - 1;
    var seen_regs = std.EnumSet(isa.Reg){};
    for (argTys, 0..) |argTy, i| {
        const argt = isa.Arg.fromChar(argTy);
        if (i > 0) try wrt.writeAll(", ") else try wrt.writeAll(" ");
        try self.displayArg(prev_ip, argt, ctx, &seen_regs, switch (op) {
            .fadd64, .fsub64, .fmul64, .fdiv64, .fti64 => .f64,
            .fadd32, .fsub32, .fmul32, .fdiv32, .fti32 => .f32,
            else => .int,
        }, wrt);
    }
}

fn displayArg(
    self: *Vm,
    prev_ip: usize,
    arg: isa.Arg,
    ctx: anytype,
    seen_regs: *std.EnumSet(isa.Reg),
    ty: enum { int, f32, f64 },
    wrt: *std.Io.Writer,
) error{ WriteFailed, MemOob }!void {
    switch (arg) {
        inline .reg => |t| {
            const value = try self.progRead(isa.ArgType(t), ctx);
            self.ip += @sizeOf(isa.ArgType(t));

            const col: std.io.tty.Color = @enumFromInt(3 + @intFromEnum(value) % 12);
            try ctx.setColor(col);
            try wrt.print("${d}", .{@intFromEnum(value)});
            try ctx.setColor(.reset);

            if (!seen_regs.contains(value)) {
                seen_regs.insert(value);

                try ctx.setColor(.dim);
                try wrt.writeAll("=");

                switch (ty) {
                    .int => try wrt.print("{d}", .{@as(i64, @bitCast(self.regs.get(value)))}),
                    .f32 => try wrt.print("{d}", .{@as(f32, @bitCast(@as(u32, @truncate(self.regs.get(value)))))}),
                    .f64 => try wrt.print("{d}", .{@as(f64, @bitCast(self.regs.get(value)))}),
                }
                try ctx.setColor(.reset);
            }
        },
        inline else => |t| {
            const value = try self.progRead(isa.ArgType(t), ctx);
            self.ip += @sizeOf(isa.ArgType(t));
            try ctx.setColor(arg.color());
            const pos = if (t == .rel32) @as(i32, @intCast(prev_ip)) + value - @as(i32, @intCast(ctx.code_start)) else 0;
            if (t == .rel32 and pos > 0 and ctx.symbols.get(@intCast(pos)) != null) {
                try wrt.print("{s}", .{ctx.symbols.get(@intCast(pos)).?});
            } else if (@typeInfo(@TypeOf(value)).int.signedness == .unsigned) {
                try wrt.print("{any}", .{@as(std.meta.Int(.signed, @bitSizeOf(@TypeOf(value))), @bitCast(value))});
            } else {
                try wrt.print("{any}", .{value});
            }
            try ctx.setColor(.reset);
        },
    }
}

fn readArgs(self: *Vm, comptime op: isa.Op, ctx: anytype) !isa.ArgsOf(op) {
    defer self.ip += @sizeOf(isa.ArgsOf(op));
    return try self.progRead(isa.ArgsOf(op), ctx);
}

fn progRead(self: *Vm, comptime T: type, ctx: anytype) !T {
    return (try ctx.progRead(T, self.ip)).*;
}
