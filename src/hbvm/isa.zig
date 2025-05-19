const std = @import("std");
const utils = @import("../utils.zig");

pub const Reg = enum(u8) {
    null,
    ret_addr = 31,
    stack_addr = 254,
    max = 255,
    _,

    pub fn arg(index: usize) Reg {
        return @enumFromInt(1 + index);
    }

    pub fn ret(index: usize) Reg {
        std.debug.assert(index < 2);
        return @enumFromInt(1 + index);
    }
};

pub const instr_count = spec.len;
pub const max_instr_len = blk: {
    var max_len: usize = 0;
    for (spec) |instr| {
        max_len = @max(max_len, instr[0].len);
    }
    break :blk max_len;
};

pub const Arg = enum {
    reg,
    imm8,
    imm16,
    imm32,
    imm64,
    rel16,
    rel32,
    abs64,

    const valid_chars = "RBHWDPOA";
    const min_char = std.mem.min(u8, valid_chars);
    const char_to_self = b: {
        const max_char = std.mem.max(u8, valid_chars) + 1;

        var table: [max_char - min_char]Arg = undefined;
        for (valid_chars, 0..) |c, i| {
            table[c - min_char] = @enumFromInt(i);
        }

        const t = table;
        break :b &t;
    };

    const colors: []const std.io.tty.Color = &.{
        .red,
        .green,
        .green,
        .green,
        .green,
        .red,
        .red,
        .red,
    };

    pub fn color(self: Arg) std.io.tty.Color {
        return colors[@intFromEnum(self)];
    }

    pub fn fromChar(char: u8) Arg {
        return char_to_self[char - min_char];
    }
};
const InstrSpec = struct { [:0]const u8, []const u8, []const u8 };

pub fn ArgType(comptime arg: Arg) type {
    return .{ Reg, u8, u16, u32, u64, i16, i32, i64 }[@intFromEnum(arg)];
}

pub const Op = b: {
    var values: [spec.len]std.builtin.Type.EnumField = undefined;
    for (spec, &values, 0..) |instr, *value, i|
        value.* = .{ .name = instr[0], .value = i };
    break :b @Type(.{ .@"enum" = .{
        .tag_type = u8,
        .fields = &values,
        .decls = &.{},
        .is_exhaustive = true,
    } });
};

pub fn ArgsOf(comptime op: Op) type {
    return ArgsOfStr(spec[@intFromEnum(op)][1]);
}

pub fn ArgsOfStr(comptime args: []const u8) type {
    var fields: [args.len]std.builtin.Type.StructField = undefined;
    for (args, &fields, 0..) |arg, *field, i| field.* = .{
        .name = &[_:0]u8{ 'a', 'r', 'g', '0' + i },
        .type = ArgType(Arg.fromChar(arg)),
        .default_value_ptr = null,
        .alignment = 1,
        .is_comptime = false,
    };
    return @Type(.{ .@"struct" = .{
        .fields = &fields,
        .decls = &.{},
        .is_tuple = false,
        .layout = .@"extern",
    } });
}

pub fn TupleOf(comptime Struct: type) type {
    const field_info = std.meta.fields(Struct);
    var fields: [field_info.len]type = undefined;
    for (field_info, &fields) |arg, *field| field.* = arg.type;
    return std.meta.Tuple(&fields);
}

pub fn packTo(comptime Args: type, args: TupleOf(Args)) Args {
    var val: Args = undefined;
    inline for (std.meta.fields(Args), std.meta.fields(@TypeOf(args))) |af, tf| {
        @field(val, af.name) = @field(args, tf.name);
    }
    return val;
}

pub fn instrSize(comptime op: Op) comptime_int {
    return @sizeOf(ArgsOf(op)) + 1;
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
    if (out.len != i) @compileError("wut");
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
            if (name.type == Reg) {
                if (@TypeOf(instr[i]) == comptime_int) {
                    @as(*align(1) name.type, @ptrCast(&out[cursor])).* = @enumFromInt(instr[i]);
                } else {
                    @as(*align(1) name.type, @ptrCast(&out[cursor])).* = instr[i];
                }
            } else {
                @as(*align(1) name.type, @ptrCast(&out[cursor])).* = @truncate(instr[i]);
            }
            cursor += @sizeOf(name.type);
        }
    }

    const outa = out;
    return &outa;
}

pub const ExecHeader = extern struct {
    magic_number: [3]u8 = .{ 0x15, 0x91, 0xD2 },
    executable_version: u32 align(1) = 0,

    code_length: u64 align(1) = 0,
    data_length: u64 align(1) = 0,
    debug_length: u64 align(1) = 0,
    symbol_count: u64 align(1) = 0,
    config_length: u64 align(1) = 0,
    metadata_length: u64 align(1) = 0,
};

pub const Symbol = extern struct {
    name: u32,
    kind: enum(u32) { func, data },
    offset: u64,
};

pub fn loadSymMap(arena: std.mem.Allocator, code: []const u8) !std.AutoHashMapUnmanaged(u32, []const u8) {
    const header: ExecHeader = @bitCast(code[0..@sizeOf(ExecHeader)].*);
    const sym_start: usize = @intCast(@sizeOf(ExecHeader) + header.code_length + header.data_length);
    const sym_end: usize = @intCast(header.symbol_count * @sizeOf(Symbol));
    const syms: []align(1) const Symbol =
        @ptrCast(code[sym_start..][0..sym_end]);

    const string_table = code[sym_start..][sym_end..@intCast(header.debug_length)];

    var symbols = std.AutoHashMapUnmanaged(u32, []const u8){};
    for (syms) |sym| {
        const len = std.mem.indexOfScalar(u8, string_table[sym.name..], 0).?;
        try symbols.put(
            arena,
            @intCast(sym.offset - @sizeOf(ExecHeader)),
            string_table[sym.name..][0..len],
        );
    }

    return symbols;
}

pub fn disasm(
    code: []const u8,
    arena: std.mem.Allocator,
    writer: anytype,
    colors: std.io.tty.Config,
) !void {
    const header: ExecHeader = @bitCast(code[0..@sizeOf(ExecHeader)].*);

    const symbols = try loadSymMap(arena, code);

    var labelMap = try makeLabelMap(
        code[@sizeOf(ExecHeader)..][0..header.code_length],
        &symbols,
        arena,
    );
    defer labelMap.deinit();
    var cursor: usize = 0;

    const code_section = code[@sizeOf(ExecHeader)..][0..header.code_length];
    while (code_section.len > cursor) {
        cursor += try disasmOne(code_section, cursor, &labelMap, &symbols, writer, colors);
    }
}

pub fn disasmOne(
    full_code: []const u8,
    cursor: usize,
    labelMap: *const std.AutoHashMap(u32, u32),
    symbols: *const std.AutoHashMapUnmanaged(u32, []const u8),
    writer: anytype,
    color: std.io.tty.Config,
) !usize {
    const padding = if (labelMap.count() != 0)
        2 + @max(std.math.log2_int_ceil(usize, labelMap.count()) / 4, 1)
    else
        0;
    if (symbols.get(@intCast(cursor))) |s| {
        try writer.print("{s}:\n", .{s});
        for (0..padding) |_| try writer.writeAll(" ");
    } else if (labelMap.get(@intCast(cursor))) |l| {
        try writer.print("{x}: ", .{l});
    } else {
        for (0..padding) |_| try writer.writeAll(" ");
    }

    const code = full_code[cursor..];

    const op: Op = @enumFromInt(code[0]);
    const name = @tagName(op);
    const argTys = spec[code[0]][1];
    for (name.len..max_instr_len) |_| try writer.writeAll(" ");
    try writer.writeAll(name);
    var i: usize = 1;
    for (argTys) |argTy| {
        const argt = Arg.fromChar(argTy);
        if (i > 1) try writer.writeAll(", ") else try writer.writeAll(" ");
        i += try disasmArg(argt, @intCast(cursor), @ptrCast(&code[i]), labelMap, symbols, writer, color);
    }
    try writer.writeAll("\n");
    return i;
}

fn disasmArg(
    arg: Arg,
    cursor: i32,
    ptr: [*]const u8,
    labelMap: *const std.AutoHashMap(u32, u32),
    symbols: *const std.AutoHashMapUnmanaged(u32, []const u8),
    writer: anytype,
    colors: std.io.tty.Config,
) !usize {
    try utils.setColor(colors, writer, arg.color());
    var size: usize = 0;
    switch (arg) {
        inline else => |t| {
            const value: *align(1) const ArgType(t) = @ptrCast(@alignCast(ptr));
            size = @sizeOf(@TypeOf(value.*));

            switch (t) {
                .rel16, .rel32 => {
                    if (cursor < -value.*) {
                        try writer.print(":!{x}", .{value.*});
                    } else {
                        const pos: u32 = @intCast(cursor + value.*);
                        if (symbols.get(pos)) |s| {
                            try writer.print(":{s}", .{s});
                        } else {
                            const label = labelMap.get(pos) orelse 42069;
                            try writer.print(":{x}", .{label});
                        }
                    }
                },
                .reg => {
                    const col: std.io.tty.Color = @enumFromInt(3 + @intFromEnum(value.*) % 12);
                    try utils.setColor(colors, writer, col);
                    try writer.print("${d}", .{@intFromEnum(value.*)});
                },
                else => try writer.print("{any}", .{@as(std.meta.Int(.signed, @bitSizeOf(@TypeOf(value.*))), @bitCast(value.*))}),
            }
        },
    }
    try utils.setColor(colors, writer, .reset);
    return size;
}

fn makeLabelMap(code: []const u8, syms: *const std.AutoHashMapUnmanaged(u32, []const u8), gpa: std.mem.Allocator) !std.AutoHashMap(u32, u32) {
    var map = std.AutoHashMap(u32, u32).init(gpa);
    var cursor: i32 = 0;
    while (code.len > cursor) {
        const cursor_snap = cursor;

        if (code[@intCast(cursor)] > instr_count) {
            cursor += 1;
            continue;
        }
        const op: Op = @enumFromInt(code[@intCast(cursor)]);
        cursor += 1;
        const args = spec[@intFromEnum(op)][1];
        for (args) |argTy| {
            switch (Arg.fromChar(argTy)) {
                inline .rel16, .rel32 => |ty| {
                    const arg: *align(1) const ArgType(ty) =
                        @ptrCast(@alignCast(&code[@intCast(cursor)]));
                    if (cursor_snap < -arg.*) {
                        continue;
                    }
                    const pos: u32 = @intCast(cursor_snap + arg.*);
                    if (!syms.contains(pos)) {
                        std.debug.assert(code[pos] < instr_count);
                    }
                    if (map.get(pos) == null) try map.put(pos, map.count());
                    cursor += @sizeOf(@TypeOf(arg.*));
                },
                inline else => |ty| cursor += @sizeOf(ArgType(ty)),
            }
        }
    }
    return map;
}

pub const spec = [_]InstrSpec{
    .{ "un", "", "Cause an unreachable code trap" },
    .{ "tx", "", "Termiante execution" },
    .{ "nop", "", "Do nothing" },
    .{ "add8", "RRR", "Addition (8b)" },
    .{ "add16", "RRR", "Addition (16b)" },
    .{ "add32", "RRR", "Addition (32b)" },
    .{ "add64", "RRR", "Addition (64b)" },
    .{ "sub8", "RRR", "Subtraction (8b)" },
    .{ "sub16", "RRR", "Subtraction (16b)" },
    .{ "sub32", "RRR", "Subtraction (32b)" },
    .{ "sub64", "RRR", "Subtraction (64b)" },
    .{ "mul8", "RRR", "Multiplication (8b)" },
    .{ "mul16", "RRR", "Multiplication (16b)" },
    .{ "mul32", "RRR", "Multiplication (32b)" },
    .{ "mul64", "RRR", "Multiplication (64b)" },
    .{ "and", "RRR", "Bitand" },
    .{ "or", "RRR", "Bitor" },
    .{ "xor", "RRR", "Bitxor" },
    .{ "slu8", "RRR", "Unsigned left bitshift (8b)" },
    .{ "slu16", "RRR", "Unsigned left bitshift (16b)" },
    .{ "slu32", "RRR", "Unsigned left bitshift (32b)" },
    .{ "slu64", "RRR", "Unsigned left bitshift (64b)" },
    .{ "sru8", "RRR", "Unsigned right bitshift (8b)" },
    .{ "sru16", "RRR", "Unsigned right bitshift (16b)" },
    .{ "sru32", "RRR", "Unsigned right bitshift (32b)" },
    .{ "sru64", "RRR", "Unsigned right bitshift (64b)" },
    .{ "srs8", "RRR", "Signed right bitshift (8b)" },
    .{ "srs16", "RRR", "Signed right bitshift (16b)" },
    .{ "srs32", "RRR", "Signed right bitshift (32b)" },
    .{ "srs64", "RRR", "Signed right bitshift (64b)" },
    .{ "cmpu", "RRR", "Unsigned comparsion" },
    .{ "cmps", "RRR", "Signed comparsion" },
    .{ "diru8", "RRRR", "Merged divide-remainder (unsigned 8b)" },
    .{ "diru16", "RRRR", "Merged divide-remainder (unsigned 16b)" },
    .{ "diru32", "RRRR", "Merged divide-remainder (unsigned 32b)" },
    .{ "diru64", "RRRR", "Merged divide-remainder (unsigned 64b)" },
    .{ "dirs8", "RRRR", "Merged divide-remainder (signed 8b)" },
    .{ "dirs16", "RRRR", "Merged divide-remainder (signed 16b)" },
    .{ "dirs32", "RRRR", "Merged divide-remainder (signed 32b)" },
    .{ "dirs64", "RRRR", "Merged divide-remainder (signed 64b)" },
    .{ "neg", "RR", "Bit negation" },
    .{ "not", "RR", "Logical negation" },
    .{ "sxt8", "RR", "Sign extend 8b to 64b" },
    .{ "sxt16", "RR", "Sign extend 16b to 64b" },
    .{ "sxt32", "RR", "Sign extend 32b to 64b" },
    .{ "addi8", "RRB", "Addition with immediate (8b)" },
    .{ "addi16", "RRH", "Addition with immediate (16b)" },
    .{ "addi32", "RRW", "Addition with immediate (32b)" },
    .{ "addi64", "RRD", "Addition with immediate (64b)" },
    .{ "muli8", "RRB", "Multiplication with immediate (8b)" },
    .{ "muli16", "RRH", "Multiplication with immediate (16b)" },
    .{ "muli32", "RRW", "Multiplication with immediate (32b)" },
    .{ "muli64", "RRD", "Multiplication with immediate (64b)" },
    .{ "andi", "RRD", "Bitand with immediate" },
    .{ "ori", "RRD", "Bitor with immediate" },
    .{ "xori", "RRD", "Bitxor with immediate" },
    .{ "slui8", "RRB", "Unsigned left bitshift with immedidate (8b)" },
    .{ "slui16", "RRB", "Unsigned left bitshift with immedidate (16b)" },
    .{ "slui32", "RRB", "Unsigned left bitshift with immedidate (32b)" },
    .{ "slui64", "RRB", "Unsigned left bitshift with immedidate (64b)" },
    .{ "srui8", "RRB", "Unsigned right bitshift with immediate (8b)" },
    .{ "srui16", "RRB", "Unsigned right bitshift with immediate (16b)" },
    .{ "srui32", "RRB", "Unsigned right bitshift with immediate (32b)" },
    .{ "srui64", "RRB", "Unsigned right bitshift with immediate (64b)" },
    .{ "srsi8", "RRB", "Signed right bitshift with immediate" },
    .{ "srsi16", "RRB", "Signed right bitshift with immediate" },
    .{ "srsi32", "RRB", "Signed right bitshift with immediate" },
    .{ "srsi64", "RRB", "Signed right bitshift with immediate" },
    .{ "cmpui", "RRD", "Unsigned compare with immediate" },
    .{ "cmpsi", "RRD", "Signed compare with immediate" },
    .{ "cp", "RR", "Copy register" },
    .{ "swa", "RR", "Swap registers" },
    .{ "li8", "RB", "Load immediate (8b)" },
    .{ "li16", "RH", "Load immediate (16b)" },
    .{ "li32", "RW", "Load immediate (32b)" },
    .{ "li64", "RD", "Load immediate (64b)" },
    .{ "lra", "RRO", "Load relative address" },
    .{ "ld", "RRAH", "Load from absolute address" },
    .{ "st", "RRAH", "Store to absolute address" },
    .{ "ldr", "RROH", "Load from relative address" },
    .{ "str", "RROH", "Store to relative address" },
    .{ "bmc", "RRH", "Copy block of memory" },
    .{ "brc", "RRB", "Copy register block" },
    .{ "jmp", "O", "Relative jump" },
    .{ "jal", "RRO", "Linking relative jump" },
    .{ "jala", "RRA", "Linking absolute jump" },
    .{ "jeq", "RRP", "Branch on equal" },
    .{ "jne", "RRP", "Branch on nonequal" },
    .{ "jltu", "RRP", "Branch on lesser-than (unsigned)" },
    .{ "jgtu", "RRP", "Branch on greater-than (unsigned)" },
    .{ "jlts", "RRP", "Branch on lesser-than (signed)" },
    .{ "jgts", "RRP", "Branch on greater-than (signed)" },
    .{ "eca", "", "Environment call trap" },
    .{ "ebp", "", "Environment breakpoint" },
    .{ "fadd32", "RRR", "Floating point addition (32b)" },
    .{ "fadd64", "RRR", "Floating point addition (64b)" },
    .{ "fsub32", "RRR", "Floating point subtraction (32b)" },
    .{ "fsub64", "RRR", "Floating point subtraction (64b)" },
    .{ "fmul32", "RRR", "Floating point multiply (32b)" },
    .{ "fmul64", "RRR", "Floating point multiply (64b)" },
    .{ "fdiv32", "RRR", "Floating point division (32b)" },
    .{ "fdiv64", "RRR", "Floating point division (64b)" },
    .{ "fma32", "RRRR", "Float fused multiply-add (32b)" },
    .{ "fma64", "RRRR", "Float fused multiply-add (64b)" },
    .{ "finv32", "RR", "Float reciprocal (32b)" },
    .{ "finv64", "RR", "Float reciprocal (64b)" },
    .{ "fcmplt32", "RRR", "Flaot compare less than (32b)" },
    .{ "fcmplt64", "RRR", "Flaot compare less than (64b)" },
    .{ "fcmpgt32", "RRR", "Flaot compare greater than (32b)" },
    .{ "fcmpgt64", "RRR", "Flaot compare greater than (64b)" },
    .{ "itf32", "RR", "Int to 32 bit float" },
    .{ "itf64", "RR", "Int to 64 bit float" },
    .{ "fti32", "RRB", "Float 32 to int" },
    .{ "fti64", "RRB", "Float 64 to int" },
    .{ "fc32t64", "RR", "Float 64 to Float 32" },
    .{ "fc64t32", "RRB", "Float 32 to Float 64" },
    .{ "lra16", "RRP", "Load relative immediate (16 bit)" },
    .{ "ldr16", "RRPH", "Load from relative address (16 bit)" },
    .{ "str16", "RRPH", "Store to relative address (16 bit)" },
    .{ "jmp16", "P", "Relative jump (16 bit)" },
};
