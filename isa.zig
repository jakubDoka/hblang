const std = @import("std");

pub const instr_count = spec.len;
pub const max_instr_len = blk: {
    var max_len: usize = 0;
    for (spec) |instr| {
        max_len = @max(max_len, instr.name.len);
    }
    break :blk max_len;
};

pub const Arg = enum { reg, imm8, imm16, imm32, imm64, rel16, rel32, abs64 };
const InstrSpec = struct { name: [:0]const u8, args: []const Arg, desc: []const u8 };

pub fn ArgType(comptime arg: Arg) type {
    return .{ u8, u8, u16, u32, u64, i16, i32, i64 }[@intFromEnum(arg)];
}

pub const Op = b: {
    var values: [spec.len]std.builtin.Type.EnumField = undefined;
    for (spec, &values, 0..) |instr, *value, i|
        value.* = .{ .name = instr.name, .value = i };
    break :b @Type(.{ .@"enum" = .{
        .tag_type = u8,
        .fields = &values,
        .decls = &.{},
        .is_exhaustive = true,
    } });
};

pub fn hasImm(op: Op) bool {
    return for (spec[@intFromEnum(op)].args) |arg| {
        if (arg != .reg) return true;
    } else false;
}

pub fn ArgsOf(comptime op: Op) type {
    const args = spec[@intFromEnum(op)].args;
    var fields: [args.len]std.builtin.Type.StructField = undefined;
    for (args, &fields, 0..) |arg, *field, i| field.* = .{
        .name = &[_:0]u8{ 'a', 'r', 'g', '0' + i },
        .type = ArgType(arg),
        .default_value_ptr = null,
        .alignment = 0,
        .is_comptime = false,
    };
    return @Type(.{ .@"struct" = .{
        .fields = &fields,
        .decls = &.{},
        .is_tuple = false,
        .layout = .@"packed",
    } });
}

pub fn instrSize(comptime op: Op) comptime_int {
    const args = spec[@intFromEnum(op)].args;
    var size = 1;
    for (args) |arg| size += @sizeOf(ArgType(arg));
    return size;
}

pub fn pack(comptime op: Op, args: anytype) [instrSize(op)]u8 {
    var out: [instrSize(op)]u8 = undefined;
    out[0] = @intFromEnum(op);
    comptime var i: usize = 1;
    inline for (std.meta.fields(ArgsOf(op)), 0..) |field, j| {
        if (std.meta.fields(@TypeOf(args)).len <= j)
            @compileError("too few args " ++ @tagName(op));
        @as(*align(1) field.type, @ptrCast(&out[i])).* =
            if (@sizeOf(@TypeOf(args[j])) > @sizeOf(field.type)) @truncate(args[j]) else args[j];
        i += @sizeOf(field.type);
    }
    return out;
}

pub fn packMany(comptime instrs: anytype) []const u8 {
    comptime var cursor = 0;
    inline for (instrs) |instr| cursor += instrSize(instr[0]);

    comptime var out: [cursor]u8 = undefined;
    cursor = 0;
    inline for (instrs) |instr| {
        const op: Op = instr[0];
        out[cursor] = @intFromEnum(op);
        cursor += 1;
        inline for (std.meta.fields(ArgsOf(op)), 1..) |name, i| {
            @as(*align(1) name.type, @ptrCast(&out[cursor])).* = @truncate(instr[i]);
            cursor += @sizeOf(name.type);
        }
    }

    const outa = out;
    return &outa;
}

pub fn disasmOne(full_code: []const u8, cursor: usize, labelMap: *const std.AutoHashMap(u32, u32), out: *std.ArrayList(u8), write_offset: bool) !usize {
    if (write_offset) try out.writer().print("{d:4} ", .{cursor});
    const padding = if (labelMap.count() != 0)
        2 + @max(std.math.log2_int_ceil(usize, labelMap.count()) / 4, 1)
    else
        0;
    if (labelMap.get(@intCast(cursor))) |l| {
        try out.writer().print("{x}: ", .{l});
    } else {
        for (0..padding) |_| try out.append(' ');
    }

    const code = full_code[cursor..];

    const op: Op = @enumFromInt(code[0]);
    switch (op) {
        inline else => |v| {
            try out.appendSlice(@tagName(v));
            const argTys = spec[@intFromEnum(v)].args;
            if (argTys.len > 0) for (@tagName(v).len..max_instr_len) |_| try out.append(' ');
            comptime var i: usize = 1;
            inline for (argTys) |argTy| {
                if (i > 1) try out.appendSlice(", ") else try out.appendSlice(" ");
                const arg: *align(1) const ArgType(argTy) = @ptrCast(@alignCast(&code[i]));
                try disasmArg(argTy, arg.*, @intCast(cursor), labelMap, out);
                i += @sizeOf(@TypeOf(arg.*));
            }
            try out.appendSlice("\n");
            return i;
        },
    }
}

fn disasmArg(
    comptime arg: Arg,
    value: ArgType(arg),
    cursor: i32,
    labelMap: *const std.AutoHashMap(u32, u32),
    out: *std.ArrayList(u8),
) !void {
    switch (arg) {
        .rel16, .rel32 => {
            const pos: u32 = @intCast(cursor + value);
            const label = labelMap.get(pos).?;
            try out.writer().print(":{x}", .{label});
        },
        .reg => try out.writer().print("${d}", .{value}),
        else => try out.writer().print("{any}", .{value}),
    }
}

pub fn disasm(code: []const u8, out: *std.ArrayList(u8), write_offset: bool) !void {
    var labelMap = try makeLabelMap(code, out.allocator);
    defer labelMap.deinit();
    var cursor: usize = 0;
    while (code.len > cursor) {
        cursor += try disasmOne(code, cursor, &labelMap, out, write_offset);
    }
}

fn makeLabelMap(code: []const u8, gpa: std.mem.Allocator) !std.AutoHashMap(u32, u32) {
    var map = std.AutoHashMap(u32, u32).init(gpa);
    var cursor: i32 = 0;
    while (code.len > cursor) {
        const cursor_snap = cursor;
        const op: Op = @enumFromInt(code[@intCast(cursor)]);
        cursor += 1;
        const args = spec[@intFromEnum(op)].args;
        for (args) |argTy| {
            switch (argTy) {
                inline .rel16, .rel32 => |ty| {
                    const arg: *align(1) const ArgType(ty) =
                        @ptrCast(@alignCast(&code[@intCast(cursor)]));
                    const pos: u32 = @intCast(cursor_snap + arg.*);
                    std.debug.assert(code[pos] < instr_count);
                    if (map.get(pos) == null) try map.put(pos, map.count());
                    cursor += @sizeOf(@TypeOf(arg.*));
                },
                inline else => |ty| cursor += @sizeOf(ArgType(ty)),
            }
        }
    }
    return map;
}

fn ni(name: [:0]const u8, args: anytype, desc: []const u8) InstrSpec {
    return .{ .name = name, .args = &args, .desc = desc };
}

fn nsi(name: [:0]const u8, args: anytype, attach_imm: bool, desc: []const u8) [4]InstrSpec {
    var ret: [4]InstrSpec = undefined;
    const names = .{ "8", "16", "32", "64" };
    for (&ret, names, 1..) |*r, nm, i|
        r.* = ni(
            name ++ nm,
            if (attach_imm) args ++ .{@as(Arg, @enumFromInt(i))} else args,
            desc,
        );
    return ret;
}

fn nfsi(name: [:0]const u8, args: anytype, attach_imm: bool, desc: []const u8) [2]InstrSpec {
    return nsi(name, args, attach_imm, desc)[2..].*;
}

const breg = .{ .reg, .reg, .reg };
const bregm = .{ .reg, .reg, .imm64 };

fn bdesc(op: []const u8) []const u8 {
    return std.fmt.comptimePrint("$0 = $1 {s} $2", .{op});
}

fn bdescm(op: []const u8) []const u8 {
    return std.fmt.comptimePrint("$0 = $1 {s} #2", .{op});
}

fn nsiop(name: [:0]const u8, op: []const u8) [4]InstrSpec {
    return nsi(name, breg, false, bdesc(op));
}

fn nsimop(name: [:0]const u8, op: []const u8) [4]InstrSpec {
    return nsi(name, .{ .reg, .reg }, true, bdescm(op));
}

fn nfsiop(name: [:0]const u8, op: []const u8) [2]InstrSpec {
    return nfsi(name, breg, false, bdesc(op ++ "(floating point)"));
}

const cmp_mapping = " < => -1 : = => 0 : > => 1";

pub const spec = .{
    ni("un", .{}, "unreachable code reached"),
    ni("tx", .{}, "gracefully end execution"),
    ni("nop", .{}, "no operation"),
} ++
    nsiop("add", "+") ++
    nsiop("sub", "-") ++
    nsiop("mul", "*") ++ .{
    ni("and", breg, bdesc("&")),
    ni("or", breg, bdesc("|")),
    ni("xor", breg, bdesc("^")),
} ++
    nsiop("slu", "<<") ++
    nsiop("sru", ">>") ++
    nsiop("srs", ">> (signed)") ++ .{
    ni("cmpu", breg, "unsigned coimparison" ++ cmp_mapping),
    ni("cmps", breg, "signed coimparison" ++ cmp_mapping),
} ++
    nsi("diru", .{ .reg, .reg, .reg, .reg }, false, "$0 / $1 = $2, $3 % $1 = $4") ++
    nsi("dirs", .{ .reg, .reg, .reg, .reg }, false, "(signed) $0 / $1 = $2, $3 % $1 = $4") ++ .{
    ni("neg", .{ .reg, .reg }, "$0 = -$1"),
    ni("not", .{ .reg, .reg }, "$0 = !$1"),
    ni("sxt8", .{ .reg, .reg }, "$0 = (signextend) $1"),
    ni("sxt16", .{ .reg, .reg }, "$0 = (signextend) $1"),
    ni("sxt32", .{ .reg, .reg }, "$0 = (signextend) $1"),
} ++
    nsimop("addi", "+") ++
    nsimop("muli", "-") ++ .{
    ni("andi", bregm, bdesc("&")),
    ni("ori", bregm, bdesc("|")),
    ni("xori", bregm, bdesc("^")),
} ++
    nsi("slui", .{ .reg, .reg, .imm8 }, false, bdescm("<<")) ++
    nsi("srui", .{ .reg, .reg, .imm8 }, false, bdescm(">>")) ++
    nsi("srsi", .{ .reg, .reg, .imm8 }, false, bdescm(">> (signed)")) ++ .{
    ni("cmpui", bregm, "unsigned coimparison" ++ cmp_mapping),
    ni("cmpsi", bregm, "signed coimparison" ++ cmp_mapping),
    ni("cp", .{ .reg, .reg }, "$0 = $1"),
    ni("swa", .{ .reg, .reg }, "$0 = $1"),
} ++
    nsi("li", .{.reg}, true, "$0 = #1") ++ .{
    ni("lra", .{ .reg, .reg, .imm32 }, "$0 = ip + $1 + #2"),
    ni("ld", .{ .reg, .reg, .abs64, .imm16 }, "$0[#3] = ($1 + #2)[#3]"),
    ni("st", .{ .reg, .reg, .abs64, .imm16 }, "($1 + #2)[#3] = $0[#3]"),
    ni("ldr", .{ .reg, .reg, .rel32, .imm16 }, "$0[#3] = (pc + $1 + #2)[#3]"),
    ni("str", .{ .reg, .reg, .rel32, .imm16 }, "(pc + $1 + #2)[#3] = $0[#3]"),
    ni("bmc", .{ .reg, .reg, .imm16 }, "$0[#2] = $1[#2]"),
    ni("brc", .{ .reg, .reg, .imm16 }, "$0 = $1[#2]"),
    ni("jmp", .{.rel32}, "pc += #1"),
    ni("jal", .{ .reg, .reg, .rel32 }, "pc += #1"),
    ni("jala", .{ .reg, .reg, .abs64 }, "pc += #1"),
    ni("jeq", .{ .reg, .reg, .rel16 }, "Branch on equal"),
    ni("jne", .{ .reg, .reg, .rel16 }, "Branch on not equal"),
    ni("jltu", .{ .reg, .reg, .rel16 }, "Branch on lesser-than (unsigned)"),
    ni("jgtu", .{ .reg, .reg, .rel16 }, "Branch on greater-than (unsigned)"),
    ni("jlts", .{ .reg, .reg, .rel16 }, "Branch on lesser-than (signed)"),
    ni("jgts", .{ .reg, .reg, .rel16 }, "Branch on greater-than (signed)"),
    ni("eca", .{}, "interrupt"),
    ni("ebp", .{}, "breakpoint"),
} ++
    nfsiop("fadd", "+") ++
    nfsiop("fsub", "-") ++
    nfsiop("fmul", "*") ++
    nfsiop("fdiv", "/") ++
    nfsi("fma", .{ .reg, .reg, .reg, .reg }, false, "$0 = $1 * $2 + $3") ++
    nfsi("finv", .{ .reg, .reg }, false, "$0 = 1.0 / $1") ++
    nfsiop("fcmplt", "<") ++
    nfsiop("fcmpgt", ">") ++
    nfsi("itf", .{ .reg, .reg }, false, "$0 = (F<width>)$1") ++
    nfsi("fti", .{ .reg, .reg }, false, "$0 = (I<width>)$1") ++ .{
    ni("fc32t64", .{ .reg, .reg }, "$0 = (F64)$1"),
    ni("fc64t32", .{ .reg, .reg }, "$0 = (F32)$1"),
    ni("lra16", .{ .reg, .reg, .imm16 }, "$0 = ip + $1 + #2"),
    ni("ldr16", .{ .reg, .reg, .rel16, .imm16 }, "$0[#3] = (pc + $1 + #2)[#3]"),
    ni("str16", .{ .reg, .reg, .rel16, .imm16 }, "(pc + $1 + #2)[#3] = $0[#3]"),
    ni("jmp16", .{.rel16}, "pc += #1"),
};
