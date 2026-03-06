const std = @import("std");
pub const utils = @import("utils-lib");
const Machine = @import("Machine.zig");
const Builder = @import("Builder.zig");
const Regalloc = @import("Regalloc.zig");
pub const is_debug = @import("builtin").mode == .Debug;

const print = (std.debug).print;

fn sext(int: i64, dt: DataType) i64 {
    return if (int & @as(i64, 1) << @intCast(dt.size() * 8 - 1) != 0)
        int | ~dt.mask()
    else
        int;
}

fn tu(int: i64) u64 {
    return @bitCast(int);
}

fn tf(int: i64) f64 {
    return @bitCast(int);
}

fn tf32(int: i64) f32 {
    return @bitCast(@as(u32, @truncate(@as(u64, @bitCast(int)))));
}

pub const Set = std.DynamicBitSetUnmanaged;

pub fn setMasks(s: Set) []Set.MaskInt {
    return s.masks[0 .. (s.bit_length +
        @bitSizeOf(Set.MaskInt) - 1) / @bitSizeOf(Set.MaskInt)];
}

pub const infinite_loop_trap = std.math.maxInt(u64);
pub const unreachable_func_trap = infinite_loop_trap - 1;
pub const indirect_call = Machine.max_func - 100;

pub const Sloc = packed struct(i64) {
    namespace: u32,
    index: u32,

    pub const none: Sloc = .{
        .namespace = std.math.maxInt(u32),
        .index = std.math.maxInt(u32),
    };
};

pub const StackLayout = struct {
    arg_base: u32,
    local_base: u32,
};

pub const BinOp = enum(u8) {
    iadd,
    isub,
    imul,
    udiv,
    umod,
    ishl,
    ushr,
    band,
    bor,
    disjoint_or,
    bxor,

    ne,
    eq,
    ugt,
    ult,
    uge,
    ule,

    sdiv,
    smod,
    sshr,

    sgt,
    slt,
    sge,
    sle,

    fadd,
    fsub,
    fmul,
    fdiv,

    fgt,
    flt,
    fge,
    fle,

    pub fn isCmp(self: BinOp) bool {
        return self.isInRange(.ne, .ule) or
            self.isInRange(.sgt, .sle) or
            self.isInRange(.fgt, .fle);
    }

    pub fn isUnsifned(self: BinOp) bool {
        return self.isInRange(.iadd, .ule);
    }

    pub fn isSigned(self: BinOp) bool {
        return self.isInRange(.sdiv, .sle);
    }

    pub fn isFloat(self: BinOp) bool {
        return self.isInRange(.fadd, .fle);
    }

    pub inline fn isInRange(self: BinOp, min: BinOp, max: BinOp) bool {
        return @intFromEnum(min) <= @intFromEnum(self) and
            @intFromEnum(self) <= @intFromEnum(max);
    }

    pub fn eval(self: BinOp, dt: DataType, lhs: i64, rhs: i64) i64 {
        return @as(i64, switch (self) {
            .iadd => lhs +% rhs,
            .fadd => if (dt == .f64)
                @bitCast(tf(lhs) + tf(rhs))
            else
                @as(u32, @bitCast(tf32(lhs) + tf32(rhs))),
            .isub => lhs -% rhs,
            .fsub => if (dt == .f64)
                @bitCast(tf(lhs) - tf(rhs))
            else
                @as(u32, @bitCast(tf32(lhs) - tf32(rhs))),
            .imul => lhs *% rhs,
            .fmul => if (dt == .f64)
                @bitCast(tf(lhs) * tf(rhs))
            else
                @as(u32, @bitCast(tf32(lhs) * tf32(rhs))),
            .udiv => if (rhs == 0) 0 else @bitCast(tu(lhs) / tu(rhs)),
            // TODO: we can refactor this to not branch, but its questionable
            // since division is expensive
            .sdiv => if (rhs == 0) 0 else switch (dt) {
                .i8 => @divFloor(
                    @as(i8, @truncate(lhs)),
                    @as(i8, @truncate(rhs)),
                ),
                .i16 => @divFloor(
                    @as(i16, @truncate(lhs)),
                    @as(i16, @truncate(rhs)),
                ),
                .i32 => @divFloor(
                    @as(i32, @truncate(lhs)),
                    @as(i32, @truncate(rhs)),
                ),
                .i64 => @divFloor(lhs, rhs),
                else => unreachable,
            },
            .fdiv => if (dt == .f64)
                @bitCast(tf(lhs) / tf(rhs))
            else
                @as(u32, @bitCast(tf32(lhs) / tf32(rhs))),
            .umod => if (rhs == 0) 0 else @bitCast(tu(lhs) % tu(rhs)),
            .smod => if (rhs == 0) 0 else @rem(lhs, rhs),

            .ishl => @shlWithOverflow(lhs, @as(u6, @truncate(tu(rhs))))[0],
            .ushr => @bitCast(tu(lhs) >> @truncate(tu(rhs))),
            .sshr => lhs >> @truncate(tu(rhs)),
            .band => lhs & rhs,
            .bor, .disjoint_or => lhs | rhs,
            .bxor => lhs ^ rhs,

            .ne => @intFromBool(lhs != rhs),
            .eq => @intFromBool(lhs == rhs),

            .ugt => @intFromBool(tu(lhs) > tu(rhs)),
            .ult => @intFromBool(tu(lhs) < tu(rhs)),
            .uge => @intFromBool(tu(lhs) >= tu(rhs)),
            .ule => @intFromBool(tu(lhs) <= tu(rhs)),

            .fgt => if (dt == .f64)
                @intFromBool(tf(lhs) > tf(rhs))
            else
                @intFromBool(tf32(lhs) > tf32(rhs)),
            .flt => if (dt == .f64)
                @intFromBool(tf(lhs) < tf(rhs))
            else
                @intFromBool(tf32(lhs) < tf32(rhs)),
            .fge => if (dt == .f64)
                @intFromBool(tf(lhs) >= tf(rhs))
            else
                @intFromBool(tf32(lhs) >= tf32(rhs)),
            .fle => if (dt == .f64)
                @intFromBool(tf(lhs) <= tf(rhs))
            else
                @intFromBool(tf32(lhs) <= tf32(rhs)),

            .sgt => @intFromBool(sext(lhs, dt) > sext(rhs, dt)),
            .slt => @intFromBool(sext(lhs, dt) < sext(rhs, dt)),
            .sge => @intFromBool(sext(lhs, dt) >= sext(rhs, dt)),
            .sle => @intFromBool(sext(lhs, dt) <= sext(rhs, dt)),
        }) & dt.mask();
    }

    pub fn propagatesPoison(self: BinOp) enum { yes, into_other_value } {
        return switch (self) {
            .bor, .disjoint_or => .into_other_value,
            else => .yes,
        };
    }

    pub fn isComutative(self: BinOp) bool {
        return switch (self) {
            .iadd, .imul, .band, .bor, .disjoint_or, .bxor, .fadd, .fmul, .ne, .eq => true,
            else => false,
        };
    }

    pub fn isAsociative(self: BinOp) bool {
        return switch (self) {
            .iadd, .imul, .band, .bor, .disjoint_or, .bxor, .ne, .eq => true,
            else => false,
        };
    }

    pub fn isDistributive(self: BinOp) bool {
        return switch (self) {
            .imul => true,
            else => false,
        };
    }

    pub fn isRightDistributive(self: BinOp) bool {
        return switch (self) {
            .udiv, .sdiv => true,
            else => false,
        };
    }

    pub fn isDistributing(self: BinOp) bool {
        return switch (self) {
            .iadd, .isub => true,
            else => false,
        };
    }

    pub fn neutralElememnt(self: BinOp, ty: DataType) ?i64 {
        return switch (self) {
            .iadd, .isub, .fsub, .fadd, .bxor, .bor, .ishl, .sshr, .ushr => 0,
            .band => @as(i64, -1) & ty.mask(),
            .imul, .sdiv, .udiv => 1,
            .fmul, .fdiv => if (ty == .f64)
                @bitCast(@as(f64, 1.0))
            else
                @as(u32, @bitCast(@as(f32, 1.0))),
            else => null,
        };
    }

    pub fn killConstant(self: BinOp, c: i64) ?i64 {
        return switch (self) {
            .imul, .band => if (c == 0) 0 else null,
            else => null,
        };
    }

    pub fn symetricConstant(self: BinOp) ?i64 {
        return switch (self) {
            .isub, .bxor, .fsub => 0,
            else => null,
        };
    }
};

pub const UnOp = enum(u8) {
    cast,
    sext,
    uext,
    ired,
    ineg,
    fneg,
    not,
    bnot,
    itf,
    fti,
    fcst,

    pub inline fn propagatesPoison(_: UnOp) bool {
        return true;
    }

    pub fn eval(self: UnOp, src: DataType, dst: DataType, oper: i64) i64 {
        return @as(i64, switch (self) {
            .cast => oper,
            .sext => return switch (src) {
                .i8 => @as(i8, @truncate(oper)),
                .i16 => @as(i16, @truncate(oper)),
                .i32 => @as(i32, @truncate(oper)),
                .i64 => oper,
                else => utils.panic("{f}", .{src}),
            },
            .uext => oper,
            .ired => oper,
            .ineg => -%oper,
            .fneg => return if (src == .f64)
                @bitCast(-tf(oper))
            else
                @as(u32, @bitCast(-tf32(oper))),
            .not => @intFromBool(oper == 0),
            .bnot => ~oper,
            .fti => if (src == .f64)
                @intFromFloat(tf(oper))
            else
                @intFromFloat(tf32(oper)),
            .itf => return if (dst == .f64)
                @bitCast(@as(f64, @floatFromInt(oper)))
            else
                @as(u32, @bitCast(@as(f32, @floatFromInt(oper)))),
            .fcst => return if (src == .f64)
                @as(u32, @bitCast(@as(f32, @floatCast(tf(oper)))))
            else
                @bitCast(@as(f64, @floatCast(tf32(oper)))),
        }) & dst.mask();
    }
};

pub const DataType2 = enum(u8) {
    bot,
    i8,
    i16,
    i32,
    i64,
    f32,
    f64,
    top,
    _,

    pub const Tag = enum(u6) {
        bot,
        i8,
        i16,
        i32,
        i64,
        f32,
        f64,
        top,

        pub fn sizePow(self: Tag) u3 {
            return switch (self) {
                .top, .bot => unreachable,
                .i8 => 0,
                .i16 => 1,
                .i32, .f32 => 2,
                .i64, .f64 => 3,
            };
        }

        pub fn size(self: Tag) u8 {
            return @as(u8, 1) << self.sizePow();
        }
    };

    pub const Size = enum(u2) {
        inferred = std.math.maxInt(u2),
        _,

        pub const max_elem_unit = 8;

        pub fn sizePow(self: Size, tag: Tag) u3 {
            return switch (self) {
                .inferred => tag.sizePow(),
                _ => @intFromEnum(self) + 3,
            };
        }

        pub fn get(self: Size, tag: Tag) u8 {
            return @as(u8, 1) << self.sizePow(tag);
        }
    };

    pub const Repr = packed struct(u8) {
        tag: Tag,
        size: Size,

        pub fn laneCount(self: Repr) u16 {
            return @as(u16, 1) << (self.size.sizePow(self.tag) - self.tag.sizePow());
        }
    };

    pub fn vec(tag: Tag, lane_cont: u16) DataType2 {
        std.debug.assert(std.math.isPowerOfTwo(lane_cont));
        std.debug.assert(tag.size() * lane_cont >= 16);
        return @enumFromInt(@as(u8, @bitCast(Repr{
            .tag = tag,
            .size = @enumFromInt((@ctz(lane_cont) + tag.sizePow()) - 3),
        })));
    }

    pub fn repr(self: DataType2) Repr {
        return @bitCast(@intFromEnum(self));
    }

    pub fn laneCount(self: DataType2) u16 {
        return self.repr().laneCount();
    }

    comptime {
        for (std.meta.fields(DataType2), std.meta.fields(Tag)) |a, b| {
            if (!std.mem.eql(u8, a.name, b.name)) {
                @compileError("mismatched builtin '" ++ a.name ++ "' and '" ++ b.name ++ "'");
            }
        }
    }
};

pub const DataType = enum(u8) {
    bot,
    i8,
    i16,
    i32,
    i64,
    f32,
    f64,
    v128,
    v254,
    v512,
    top,

    pub fn memUnitForAlign(alignment: u64, float: bool) DataType {
        if (float) return @enumFromInt(@intFromEnum(DataType.f32) +
            @min(std.math.log2_int(u64, alignment), 3) - 2);
        return @enumFromInt(@intFromEnum(DataType.i8) +
            @min(std.math.log2_int(u64, alignment), 3));
    }

    pub fn halv(self: DataType) DataType {
        std.debug.assert(self != .i8);
        std.debug.assert(self != .f32);
        return @enumFromInt(@intFromEnum(self) - 1);
    }

    pub fn isSse(self: DataType) bool {
        return switch (self) {
            .v128, .v254, .v512 => true,
            else => false,
        };
    }

    pub fn isInt(self: DataType) bool {
        return switch (self) {
            .i8, .i16, .i32, .i64 => true,
            else => false,
        };
    }

    pub fn meet(self: DataType, other: DataType) DataType {
        if (self == .top) return other;
        if (other == .top) return self;
        if (self == other) return self;

        if (self.isInt() and other.isInt()) {
            return @enumFromInt(@max(@intFromEnum(self), @intFromEnum(other)));
        }

        return .bot;
    }

    pub fn format(self: DataType, writer: *std.Io.Writer) !void {
        try writer.print("{s}", .{@tagName(self)});
    }

    pub fn isFloat(self: DataType) bool {
        return switch (self) {
            .f32, .f64 => true,
            else => false,
        };
    }

    pub fn isXmm(self: DataType) bool {
        return self.isSse() or self.isFloat();
    }

    pub fn sizePow(self: DataType) u3 {
        return switch (self) {
            .top, .bot => unreachable,
            .i8 => 0,
            .i16 => 1,
            .i32, .f32 => 2,
            .i64, .f64 => 3,
            .v128 => 4,
            .v254 => 5,
            .v512 => 6,
        };
    }

    pub fn size(self: DataType) u8 {
        return @as(u8, 1) << self.sizePow();
    }

    pub fn mask(self: DataType) i64 {
        return switch (self) {
            .top, .bot => unreachable,
            .i8 => 0xFF,
            .i16 => 0xFFFF,
            .i32, .f32 => 0xFFFFFFFF,
            .i64, .f64 => -1,
            .v128, .v254, .v512 => unreachable,
        };
    }
};

pub const AbiParam = union(enum) {
    Reg: DataType,
    Stack: StackSpec,

    pub const StackSpec = packed struct(u64) {
        alignment: u6,
        size: u58,

        pub fn fromByteUnits(size: u64, alignment: u64) StackSpec {
            return .{
                .size = @intCast(size),
                .alignment = std.math.log2_int(u64, alignment),
            };
        }

        pub fn alignmentBytes(self: StackSpec) u58 {
            return @intCast(@as(u64, 1) << self.alignment);
        }

        pub fn reg(dt: DataType) StackSpec {
            return fromByteUnits(dt.size(), dt.size());
        }
    };

    pub fn getReg(self: AbiParam) DataType {
        return switch (self) {
            .Reg => |r| r,
            .Stack => .i64,
        };
    }
};

pub const CallConv = enum(u8) {
    systemv,
    syscall,
    ablecall,
    wasmcall,
    @"inline",
};

pub const CcBuilder = struct {
    int_reg_count: usize = 0,
    float_reg_count: usize = 0,

    pub fn handleReg(self: *CcBuilder, cc: CallConv, r: DataType) AbiParam {
        self.int_reg_count += @intFromBool(r.isInt());
        self.float_reg_count += @intFromBool(r.isFloat());

        var spilled = false;
        switch (cc) {
            .systemv => {
                spilled =
                    (self.int_reg_count > 6 and r.isInt()) or
                    (self.float_reg_count > 8 and r.isFloat());
            },
            .ablecall => {
                spilled = self.int_reg_count + self.float_reg_count > 11;
            },
            .syscall => {
                spilled = self.int_reg_count > 7 or r.isFloat();
            },
            .wasmcall => {},
            else => utils.panic("{}", .{cc}),
        }

        if (spilled) return .{ .Stack = .reg(r) };
        return .{ .Reg = r };
    }
};

pub const Signature = extern struct {
    par_base: [*]AbiParam = undefined,
    ret_base: ?[*]AbiParam = undefined,
    call_conv: CallConv = undefined,
    par_count: u8 = 0,
    ret_count: u8 = 0,

    pub const empty = Signature{ .call_conv = .systemv };

    pub fn initBuf(
        call_conv: CallConv,
        pars: []AbiParam,
        rets: ?[]AbiParam,
    ) Signature {
        errdefer unreachable;
        return .{
            .call_conv = call_conv,
            .par_base = pars.ptr,
            .ret_base = if (rets) |r| r.ptr else null,
            .par_count = @intCast(pars.len),
            .ret_count = if (rets) |r| @intCast(r.len) else 0,
        };
    }

    pub fn init(
        call_conv: CallConv,
        pars: []const AbiParam,
        rets: ?[]const AbiParam,
        arena: std.mem.Allocator,
    ) Signature {
        errdefer unreachable;
        return .initBuf(
            call_conv,
            try arena.dupe(AbiParam, pars),
            if (rets) |r| try arena.dupe(AbiParam, r) else null,
        );
    }

    pub fn dupe(self: @This(), arena: std.mem.Allocator) @This() {
        return .init(self.call_conv, self.params(), self.returns(), arena);
    }

    pub fn params(self: @This()) []const AbiParam {
        return self.par_base[0..self.par_count];
    }

    pub fn returns(self: @This()) ?[]const AbiParam {
        return (self.ret_base orelse return null)[0..self.ret_count];
    }

    pub fn stackSize(self: Signature, comptime B: type, call: *Func(B).Node) u64 {
        switch (self.call_conv) {
            .systemv, .ablecall, .wasmcall => {
                var size: u64 = 0;
                const is_indirect = call.extra(.Call).id == indirect_call;
                for (self.params(), call.dataDeps().ptr + @intFromBool(is_indirect)) |par, dp| {
                    if (par == .Stack) {
                        size = std.mem.alignForward(u64, size, par.Stack.alignmentBytes());
                        dp.extra(.LocalAlloc).size = size;
                        size += par.Stack.size;
                    }
                }
                return size;
            },
            else => return 0,
        }
    }
};

pub const builtin = enum {
    // ===== CFG =====
    pub const Start = extern struct {
        base: Cfg = .{},
    };
    pub const FramePointer = extern struct {
        pub const is_readonly = true;
    };
    pub const Entry = extern struct {
        base: Cfg = .{},

        pub const is_basic_block_start = true;
    };
    pub const Never = extern struct {
        base: Cfg = .{},
    };
    pub const Return = extern struct {
        base: Cfg = .{},

        pub const data_dep_offset = 2;
    };
    pub const Trap = extern struct {
        base: Cfg = .{},
        code: u64,
    };
    pub const Call = extern struct {
        base: Cfg = .{},
        signature: Signature,
        id: u32,

        pub const data_dep_offset = 2;
    };
    pub const CallEnd = extern struct {
        base: Cfg = .{},

        pub const is_basic_block_start = true;
    };
    pub const Jmp = extern struct {
        base: Cfg = .{},
    };
    pub const If = mod.If;
    pub const Then = extern struct {
        base: Cfg = .{},

        pub const is_basic_block_start = true;
    };
    pub const Else = extern struct {
        base: Cfg = .{},

        pub const is_basic_block_start = true;
    };
    pub const Region = mod.Region;
    pub const Loop = extern struct {
        base: mod.Cfg = .{},
        anal_stage: enum(u8) { is_infinite, has_break, has_dead_break } =
            .is_infinite,

        pub const is_basic_block_start = true;
    };
    pub const TrapRegion = extern struct {
        base: Cfg = .{},

        pub const is_basic_block_start = true;
    };
    // ===== VALUES ====
    pub const LocalAlloc = extern struct {
        size: u64,
        meta: LocalMeta = undefined,
        debug_ty: u32,

        pub const is_floating = true;
        pub const is_pinned = true;

        pub fn getOffset(self: *LocalAlloc, layout: StackLayout) u31 {
            return @intCast(self.size + switch (self.meta.kind) {
                .variable => layout.local_base,
                .parameter => layout.arg_base,
                .argument => 0,
            });
        }
    };
    pub const Local = extern struct {
        pub const is_clone = true;
        pub const data_dep_offset = 1;
    };
    pub const Phi = extern struct {
        pub const is_pinned = true;
    };
    pub const MachSplit = extern struct {
        dbg: Dbg = .defualt,

        pub const Dbg = enum(u8) {
            defualt,
            @"conflict/phi/def",
            @"conflict/phi/use",
            @"conflict/in-place-slot/def",
            @"conflict/in-place-slot/use",
            @"def/loop",
            @"use/loop/phi",
            @"use/loop/use",
        };
    };
    pub const Arg = mod.Arg;
    pub const BinOp = extern struct {
        op: mod.BinOp,
    };
    pub const UnOp = extern struct {
        op: mod.UnOp,
    };
    pub const Ret = extern struct {
        index: usize,

        pub const is_pinned = true;
    };
    pub const CInt = extern struct {
        value: i64,

        pub const is_clone = true;
    };
    pub const FuncAddr = extern struct {
        id: u32,

        pub const data_dep_offset = 1;
    };
    // ===== MEMORY =====
    pub const Mem = extern struct {
        pub const is_pinned = true;
    };
    pub const MemCpy = mod.MemCpy;
    pub const Load = mod.Load;
    pub const Store = mod.Store;
    pub const GlobalAddr = extern struct {
        id: u32,
        pub const is_clone = true;
        pub const data_dep_offset = 1;
    };
    pub const Dead = extern struct {};
    pub const Poison = extern struct {
        pub const is_clone = true;
    };
    pub const Syms = extern struct {
        pub const is_pinned = true;
    };
    pub const GetLane = extern struct {
        idx: u8,
    };
};

pub const LocalKind = enum(u2) { variable, argument, parameter };
pub const LocalMeta = packed struct(u32) {
    kind: LocalKind,
    index: u30,
};

pub const Arg = extern struct {
    index: usize,
};
pub const MemOp = extern struct {
    pub const data_dep_offset = 1;
};
pub const MemCpy = extern struct {
    base: Store = .{},
};
pub const Load = extern struct {
    base: MemOp = .{},
};
pub const Store = extern struct {
    base: MemOp = .{},
};
pub const If = extern struct {
    base: Cfg = .{},
    id: u32,
    allow_invariance: bool = false,
};
pub const Region = extern struct {
    base: Cfg = .{},
    preserve_identity_phys: bool = false,
    cached_lca: ?*align(8) anyopaque = null,

    pub const is_basic_block_start = true;
};

pub fn UnionOf(comptime mach_classes: type) type {
    const bdecls = @typeInfo(builtin).@"enum".decls;
    const cdecls = @typeInfo(mach_classes).@"enum".decls;
    var fields: [bdecls.len + cdecls.len]std.builtin.Type.UnionField =
        undefined;
    var i: usize = 0;
    for (bdecls) |decl| {
        fields[i] = .{
            .name = decl.name,
            .type = @field(builtin, decl.name),
            .alignment = @alignOf(@field(builtin, decl.name)),
        };
        i += 1;
    }
    for (cdecls) |decl| {
        const value = @field(mach_classes, decl.name);
        fields[i] = .{
            .name = decl.name,
            .type = value,
            .alignment = @alignOf(value),
        };
        i += 1;
    }
    return @Type(.{ .@"union" = .{
        .layout = .auto,
        .tag_type = KindOf(mach_classes),
        .fields = fields[0..i],
        .decls = &.{},
    } });
}

pub fn KindOf(comptime mach_classes: type) type {
    const bdecls = @typeInfo(builtin).@"enum".decls;
    const cdecls = @typeInfo(mach_classes).@"enum".decls;
    var fields: [bdecls.len + cdecls.len]std.builtin.Type.EnumField = undefined;
    var i: usize = 0;
    for (bdecls) |decl| {
        fields[i] = .{
            .name = decl.name,
            .value = i,
        };
        i += 1;
    }
    for (cdecls) |decl| {
        fields[i] = .{
            .name = decl.name,
            .value = i,
        };
        i += 1;
    }
    return @Type(.{ .@"enum" = .{
        .tag_type = u16,
        .fields = fields[0..i],
        .decls = &.{},
        .is_exhaustive = true,
    } });
}

pub const Cfg = extern struct {
    antidep: u32 = 0,
    idepth: u16 = 0,
    loop: u16 = undefined,
};

const mod = @This();
const peeps = @import("peeps.zig");
const mem2reg = @import("mem2reg.zig");
const static_anal = @import("static_anal.zig");
const gcm = @import("gcm.zig");
const inliner = @import("inliner.zig");

pub fn FuncNode(comptime Backend: type) type {
    return Func(Backend).Node;
}

pub fn Func(comptime Backend: type) type {
    return struct {
        name: []const u8 = "",
        arena: std.heap.ArenaAllocator,
        interner: InternMap(Uninserter) = .{},
        signature: Signature = .{},
        node_count: u32 = 0,
        waste: usize = 0,
        cost: u32 = std.math.maxInt(u32),
        start: *Node = undefined,
        end: *Node = undefined,
        peeps: peeps.Mixin(Backend) = .{},
        inliner: inliner.Mixin(Backend) = .{},
        mem2reg: mem2reg.Mixin(Backend) = .{},
        static_anal: static_anal.Mixin(Backend) = .{},
        gcm: gcm.Mixin(Backend) = .{},
        stopped_interning: std.debug.SafetyLock = .{},

        pub const WorkList = peeps.Mixin(Backend).WorkList;
        pub const idealize = peeps.Mixin(Backend).idealize;
        pub const idealizeDead = peeps.Mixin(Backend).idealizeDead;

        pub fn optApi(comptime decl_name: []const u8, comptime Ty: type) bool {
            const prelude = @typeName(Backend) ++
                " requires this unless `pub const i_know_the_api = {}`" ++
                " is declared:";

            const decl = if (@typeInfo(Ty) == .@"fn")
                "pub fn " ++ decl_name ++ @typeName(Ty)[3..]
            else
                "pub const " ++ decl_name ++ ": " ++ @typeName(Ty);

            const known_api = @hasDecl(Backend, "i_know_the_api");
            if (!known_api and !@hasDecl(Backend, decl_name))
                @compileError(prelude ++ " `" ++ decl ++ "`");

            if (@hasDecl(Backend, decl_name) and
                @TypeOf(@field(Backend, decl_name)) != Ty)
            {
                @compileError("expected `" ++ decl ++
                    "` but the type is: " ++
                    @typeName(@TypeOf(@field(Backend, decl_name))));
            }

            return @hasDecl(Backend, decl_name);
        }

        pub fn InternMap(comptime Context: type) type {
            return std.hash_map.HashMapUnmanaged(
                InternedNode,
                void,
                Context,
                std.hash_map.default_max_load_percentage,
            );
        }

        pub const biased_regs = if (optApi("biased_regs", u64))
            Backend.biased_regs
        else
            0;
        pub const all_classes = std.meta.fields(Union);

        const Self = @This();

        pub const InternedNode = struct {
            hash: u64,
            node: *Node,
        };

        pub const CfgNode = LayoutOf(Cfg);

        pub const Kind = KindOf(Backend.classes);
        pub const Union = UnionOf(Backend.classes);

        pub fn ClassFor(comptime kind: Kind) type {
            return all_classes[@intFromEnum(kind)].type;
        }

        pub fn LayoutFor(comptime kind: Kind) type {
            return LayoutOf(ClassFor(kind));
        }

        pub fn LayoutOf(comptime Class: type) type {
            return extern struct {
                base: Node,
                ext: Class,

                pub fn dominates(cfg: *CfgNode, child: *CfgNode) bool {
                    var cursor = child;
                    while (cursor.idepth() > cfg.idepth()) : (cursor = cursor.idom()) {}
                    return cursor == cfg;
                }

                pub fn idepth(cfg: *CfgNode) u16 {
                    const extra: *Cfg = &cfg.ext;

                    if (extra.idepth != 0) return extra.idepth;
                    extra.idepth = switch (cfg.base.kind) {
                        .Start => return 0,
                        .Region => b: {
                            var ideptha: u16 = 0;
                            for (cfg.base.ordInps()) |i| {
                                ideptha = @max(ideptha, i.?.asCfg().?.idepth());
                            }
                            break :b ideptha + 1;
                        },
                        else => idepth(cfg.base.cfg0()) + 1,
                    };
                    return extra.idepth;
                }

                pub fn findLca(left: *CfgNode, right: *CfgNode) *CfgNode {
                    var lc, var rc = .{ left, right };
                    while (lc != rc) {
                        std.debug.assert(lc.base.kind != .Start);
                        std.debug.assert(rc.base.kind != .Start);
                        if (!lc.base.isCfg()) utils.panic("{f}", .{lc.base});
                        if (!rc.base.isCfg()) utils.panic("{f}", .{rc.base});
                        const diff = @as(i64, idepth(lc)) - idepth(rc);
                        if (diff >= 0) lc = lc.idom();
                        if (diff <= 0) rc = rc.idom();
                    }
                    return lc;
                }

                pub fn idom(cfg: *CfgNode) *CfgNode {
                    return switch (cfg.base.extra2()) {
                        .Region => |extra| {
                            if (extra.cached_lca != null and
                                (!@as(*Node, @ptrCast(extra.cached_lca))
                                    .isSub(If) or
                                    @as(*Node, @ptrCast(extra.cached_lca))
                                        .subclass(If).?.ext.id != cfg.base.id))
                                extra.cached_lca = null;

                            if (extra.cached_lca) |lca| {
                                return @ptrCast(lca);
                            } else {
                                var lca = cfg.base.inputs()[0].?.asCfg().?;
                                for (cfg.base.ordInps()[1..]) |i| {
                                    lca = findLca(lca, i.?.asCfg().?);
                                }
                                cfg.base.extra(.Region).cached_lca = lca;
                                (lca.base.subclass(If) orelse return lca)
                                    .ext.id = cfg.base.id;
                                return lca;
                            }
                        },
                        else => cfg.base.cfg0(),
                    };
                }

                pub fn better(
                    cfg: *CfgNode,
                    best: *CfgNode,
                    to_sched: *Node,
                    func: *Self,
                ) bool {
                    return !cfg.base.isBasicBlockEnd() and
                        (idepth(cfg) > idepth(best) or
                            best.base.isBasicBlockEnd() or
                            (to_sched.kind != .MachSplit and
                                func.gcm.loopDepthOf(cfg) <
                                    func.gcm.loopDepthOf(best)));
                }

                pub fn format(
                    self: *const CfgNode,
                    writer: *std.Io.Writer,
                ) !void {
                    try self.base.format(writer);
                }
            };
        }

        fn callCheck(comptime name: []const u8, value: anytype) bool {
            return (comptime optApi(name, fn (@TypeOf(value)) bool)) and
                @field(Backend, name)(value);
        }

        pub const Node = extern struct {
            kind: Kind,
            data_type: mod.DataType = .top,
            // additional ref count for frontends
            tmp_rc: u8 = 0,
            id: u32,

            input_ordered_len: u16,
            input_len: u16,
            output_len: u16 = 0,
            output_cap: u16 = 0,

            input_base: [*]?*Node,
            output_base: [*]Out,
            sloc: Sloc = .none,

            killed_at: if (is_debug) *KillMeta else void = undefined,
            lock_at: if (is_debug) *Lock.Meta else void = undefined,

            edata: void = {},

            pub const KillMeta = struct {
                displayed: []const u8,
                trace: std.builtin.StackTrace,
            };

            pub const OutInner = if (@sizeOf(*Node) == 8) packed struct(u64) {
                node: u48,
                pos: u16,
            } else packed struct(u64) {
                node: u32,
                pos: u32,
            };

            pub const Out = packed struct(u64) {
                inner: OutInner,

                pub fn init(node: *Node, ps: usize, from: ?*Node) Out {
                    if (from) |f| std.debug.assert(node.inputs()[ps] == f);
                    return .{ .inner = .{
                        .node = @intCast(@intFromPtr(node)),
                        .pos = @intCast(ps),
                    } };
                }

                pub fn get(self: Out) *Node {
                    return @as(*Node, @ptrFromInt(self.inner.node));
                }

                pub fn pos(self: Out) usize {
                    return @intCast(self.inner.pos);
                }

                pub fn format(self: *const Out, writer: *std.Io.Writer) !void {
                    try writer.print("{}:{f}", .{ self.pos(), self.get() });
                }
            };

            pub fn accessTy(node: *Node) DataType {
                return switch (node.kind) {
                    .Store => node.value().?.data_type,
                    .Load => node.data_type,
                    else => unreachable,
                };
            }

            pub fn isNextInMemThread(node: *Node) bool {
                return node.kind == .Store or
                    node.kind == .Call or
                    node.kind == .MemCpy or
                    node.kind == .Phi or
                    node.kind == .Return;
            }

            pub fn assertAlive(node: *Node) void {
                if (node.isDead()) {
                    if (is_debug) {
                        print("{s}\n", .{node.killed_at.displayed});
                        std.debug.dumpStackTrace(node.killed_at.trace);
                    }
                    unreachable;
                }
            }

            pub fn normalizedDisjointValues(self: *Node, func: *Self) [2]*Node {
                std.debug.assert(self.extra(.BinOp).op == .disjoint_or);

                var outs: [2]struct { *Node, u8 } = undefined;
                for (&outs, self.inputs()[1..]) |*o, v| {
                    o.* = switch (v.?.extra2()) {
                        .BinOp => |ext| switch (ext.op) {
                            .ishl => .{
                                v.?.inputs()[1].?.inputs()[1].?,
                                switch (v.?.inputs()[2].?.extra2()) {
                                    .CInt => |e| @intCast(e.value),
                                    else => unreachable,
                                },
                            },
                            else => unreachable,
                        },
                        .UnOp => |ext| switch (ext.op) {
                            .uext => .{ v.?.inputs()[1].?, 0 },
                            else => unreachable,
                        },
                        .CInt => |ext| .{ v.?, std.mem.alignBackward(u7, @ctz(ext.value), 8) },
                        else => unreachable,
                    };
                }

                for (0..2) |x| {
                    const y = 1 - x;
                    if (outs[x][0].kind == .CInt) {
                        std.debug.assert(outs[y][0].kind != .CInt);
                        if (outs[x][1] > outs[y][1]) {
                            const prev = outs[x][1];
                            outs[x][1] = outs[y][1] + outs[y][0].data_type.size() * 8;
                            std.debug.assert(outs[x][1] <= prev);
                        } else {
                            outs[x][1] = 0;
                        }

                        outs[x][0] = func.addIntImm(
                            self.sloc,
                            outs[y][0].data_type,
                            outs[x][0].extra(.CInt).value >> @intCast(outs[x][1]),
                        );
                    }
                }

                return .{ outs[0][0], outs[1][0] };
            }

            pub fn loadDatatype(self: *Node) DataType {
                if (@hasDecl(Backend, "loadDatatype"))
                    return Backend.loadDatatype(self);
                return self.accessTy();
            }

            pub fn isKillable(self: *Node) bool {
                return self.kind != .Return and
                    (!@hasDecl(Backend, "isKillable") or
                        Backend.isKillable(self));
            }

            pub fn isDead(self: *Node) bool {
                return self.kind == .Dead;
            }

            pub fn preservesIdentityPhys(self: *Node) bool {
                std.debug.assert(self.kind == .Region or self.kind == .Loop);
                return self.kind == .Region and self.extra(.Region)
                    .preserve_identity_phys;
            }

            pub fn useBlock(
                self: *Node,
                use: *Node,
                pos: usize,
                scheds: []const ?*CfgNode,
            ) *CfgNode {
                _ = self;
                if (use.kind == .Phi) {
                    std.debug.assert(use.inputs()[0].?.kind == .Region or
                        use.inputs()[0].?.kind == .Loop);
                    return use.inputs()[0].?.inputs()[pos - 1].?.asCfg().?;
                }

                if (scheds.len == 0) {
                    return use.cfg0();
                }

                return scheds[use.id].?;
            }

            pub fn isGoodMemOp(self: *Node, local: *Node) bool {
                return (self.isStore() and !self.isSub(MemCpy) and
                    self.value() != local) or self.isLoad();
            }

            const DepOffsetElem = u8;
            const sub_elem_width = 2;
            const per_dep_elem = @bitSizeOf(DepOffsetElem) / sub_elem_width;
            pub const dep_offset = b: {
                const property = "data_dep_offset";
                var offs: [
                    std.mem.alignForward(
                        usize,
                        all_classes.len,
                        @bitSizeOf(DepOffsetElem) / sub_elem_width,
                    )
                ]DepOffsetElem = undefined;
                @memset(&offs, 0);

                for (all_classes, 0..) |cls, i| {
                    var Cursor = cls.type;
                    const off = (while (true) {
                        if (@hasDecl(Cursor, property)) {
                            break @field(Cursor, property);
                        }
                        if (@typeInfo(Cursor) != .@"struct" or
                            !@hasField(Cursor, "base")) break 0;
                        Cursor = @TypeOf(@as(Cursor, undefined).base);
                    } else unreachable) + 1;
                    std.debug.assert(off <= std.math
                        .powi(usize, 2, sub_elem_width) catch unreachable);
                    const slot_idx = i / (per_dep_elem);
                    const shift = (i % (per_dep_elem)) * sub_elem_width;

                    offs[slot_idx] |= off << shift;
                }

                break :b offs;
            };

            pub fn dataDepOffset(self: *Node) usize {
                const kind_idx = @intFromEnum(self.kind);
                const off = dep_offset[kind_idx / per_dep_elem] >>
                    @intCast((kind_idx % per_dep_elem) * sub_elem_width) &
                    ((@as(u16, 1) << sub_elem_width) - 1);

                return off;
            }

            pub fn dataDeps(self: *Node) []*Node {
                if ((self.kind == .Phi and !self.isDataPhi())) return &.{};
                const start = self.dataDepOffset();
                const len = self.input_ordered_len;
                const deps = self.input_base[start..len];
                std.debug.assert(std.mem.indexOfScalar(?*Node, deps, null) ==
                    null);
                return @ptrCast(deps);
            }

            pub fn knownStore(self: *Node, root: *Node) ?*Node {
                if (self.isStore() and !self.isSub(MemCpy) and
                    self.tryBase() == root)
                {
                    return self;
                }
                if (self.kind == .BinOp and self.outputs().len == 1 and
                    self.outputs()[0].get().isStore() and
                    !self.outputs()[0].get().isSub(MemCpy) and
                    self.outputs()[0].get().base() == self)
                {
                    return self.outputs()[0].get();
                }
                return null;
            }

            pub fn knownMemOp(self: *Node) ?struct { *Node, i64 } {
                if (self.isMemOp()) return .{ self, self.getStaticOffset() };
                if (self.kind == .BinOp and self.inputs()[2].?.kind == .CInt and
                    (self.outputs().len) == 1 and
                    (self.outputs()[0].get().isStore() or
                        self.outputs()[0].get().isLoad()) and
                    (self.outputs()[0].get().base()) == (self))
                {
                    return .{
                        self.outputs()[0].get(),
                        self.inputs()[2].?.extra(.CInt).value,
                    };
                }
                return null;
            }

            pub fn knownOffset(self: *Node) struct { *Node, i64 } {
                if (self.kind == .BinOp and self.inputs()[2].?.kind == .CInt) {
                    const op = self.extra(.BinOp).op;
                    if (op != .iadd and op != .isub) return .{ self, 0 };
                    const magnitude = self.inputs()[2].?.extra(.CInt).value;
                    return .{
                        self.inputs()[1].?,
                        if (op == .iadd) magnitude else -magnitude,
                    };
                }
                if (@hasDecl(Backend, "knownOffset")) {
                    return Backend.knownOffset(self);
                }
                return .{ self, 0 };
            }

            pub fn regMask(
                self: *Node,
                func: *Self,
                idx: usize,
                tmp: *utils.Arena,
            ) Regalloc.ReinferRegMask(Backend.Set) {
                return if (comptime optApi("regMask", @TypeOf(regMask)))
                    Backend.regMask(self, func, idx, tmp)
                else
                    unreachable;
            }

            pub fn clobbers(self: *Node, tag: Backend.Set.tag_) u64 {
                return if (@hasDecl(Backend, "clobbers"))
                    Backend.clobbers(self, tag)
                else
                    0;
            }

            pub fn inPlaceSlot(self: *Node) ?usize {
                return if (comptime optApi("inPlaceSlot", @TypeOf(inPlaceSlot)))
                    Backend.inPlaceSlot(self)
                else
                    null;
            }

            pub fn isClone(self: *Node) bool {
                return (comptime bakeFlagBitset("is_clone"))
                    .contains(self.kind);
            }

            pub fn isReadonly(self: *Node) bool {
                return (comptime bakeFlagBitset("is_readonly"))
                    .contains(self.kind);
            }

            pub fn alreadyBefore(
                self: *Node,
                use: *Node,
                block: *CfgNode,
            ) bool {
                std.debug.assert(self.isClone());
                if (self.cfg0() != block) return false;
                const search_from = if (use.kind == .Phi)
                    block.base.outputs().len - 1
                else
                    block.base.posOfOutput(0, use);
                var iter = std.mem.reverseIterator(
                    block.base.outputs()[0..search_from],
                );
                while (iter.next()) |o| {
                    const out: *Node = o.get();
                    if (out == self) return true;
                    if (!out.isClone() and !out.isReadonly()) break;
                }
                return false;
            }

            pub fn noAlias(self: *Node, other: *Node) bool {
                const lsize, const loff, const lbase =
                    self.getOffsetSizeBase() orelse return false;
                const rsize, const roff, const rbase =
                    other.getOffsetSizeBase() orelse return false;

                if (lbase.ptrsNoAlias(rbase)) return true;
                if (lbase != rbase) return false;

                return (loff + lsize <= roff) or (roff + rsize <= loff);
            }

            pub fn fullAlias(self: *Node, other: *Node) bool {
                const lsize, const loff, const lbase =
                    self.getOffsetSizeBase() orelse return false;
                const rsize, const roff, const rbase =
                    other.getOffsetSizeBase() orelse return false;

                if (lbase.ptrsNoAlias(rbase)) return false;
                if (lbase != rbase) return true;

                return (loff <= roff) and (roff + rsize <= loff + lsize);
            }

            pub fn getOffsetSizeBase(self: *Node) ?struct { i64, i64, *Node } {
                const siz: i64 = if (self.kind == .MemCpy and
                    if (self.inputs()[4].?.kind != .CInt) return null else true)
                    self.inputs()[4].?.extra(.CInt).value
                else
                    self.accessTy().size();
                const bas, var off = knownOffset(self.base());
                off += self.getStaticOffset();
                return .{ siz, off, bas };
            }

            pub fn ptrsNoAlias(self: *Node, other: *Node) bool {
                return ((self.kind == .Local or self.kind == .Arg) and
                    (other.kind == .Local or other.kind == .Arg)) and
                    (self != other and
                        (self.kind != .Arg or other.kind != .Arg));
            }

            pub fn isStack(self: *Node) bool {
                return self.kind == .Local or
                    self.kind == .LocalAlloc;
            }

            pub fn anyextra(self: *const Node) []const u64 {
                return @as(
                    [*]const u64,
                    @ptrCast(&self.edata),
                )[0 .. size_map[@intFromEnum(self.kind)] / 8];
            }

            pub fn format(self: *const Node, writer: *std.Io.Writer) !void {
                @constCast(self).assertAlive();
                const colors: std.io.tty.Config = if (!utils.freestanding and
                    writer.vtable.drain == std.fs.File.stderr().writer(&.{})
                        .interface.vtable.drain)
                    std.io.tty.detectConfig(std.fs.File.stderr())
                else
                    .escape_codes;
                @constCast(self).fmt(false, writer, colors);
            }

            fn isVisibel(comptime Ty: type) bool {
                switch (@typeInfo(Ty)) {
                    .@"struct" => |s| {
                        for (s.fields) |f| {
                            if (isVisibel(f.type)) return true;
                        }

                        return false;
                    },
                    .void => {
                        return false;
                    },
                    else => {},
                }

                return true;
            }

            fn logExtra(
                writ: *std.Io.Writer,
                ex: anytype,
                comptime fir: bool,
            ) !void {
                switch (@typeInfo(@TypeOf(ex.*))) {
                    .@"struct" => |s| {
                        comptime var fields = std.mem.reverseIterator(s.fields);
                        comptime var first = fir;
                        inline while (fields.next()) |f| {
                            if (comptime std.mem.eql(u8, f.name, "antidep") or
                                //std.mem.eql(u8, f.name, "loop") or
                                std.mem.eql(u8, f.name, "par_base") or
                                std.mem.eql(u8, f.name, "ret_base") or
                                !isVisibel(f.type))
                            {
                                continue;
                            }

                            comptime var prefix: []const u8 = "";
                            if (!first) prefix = ", ";
                            first = false;

                            const is_base =
                                comptime std.mem.eql(u8, f.name, "base");
                            if (!is_base) {
                                prefix = prefix ++ f.name ++ ": ";
                            }
                            try writ.writeAll(prefix);
                            _ = try logExtra(writ, &@field(ex, f.name), true);
                        }
                    },
                    .@"enum" => |e| {
                        if (e.is_exhaustive) {
                            try writ.print("{s}", .{@tagName(ex.*)});
                        } else if (std.meta.hasFn(@TypeOf(ex.*), "format")) {
                            try writ.print("{f}", .{ex.*});
                        } else {
                            try writ.print("{}", .{ex.*});
                        }
                    },
                    .optional => try writ.print("{?}", .{ex.*}),
                    else => {
                        try writ.print("{}", .{ex.*});
                    },
                }
            }

            pub fn fmt(
                self: *Node,
                scheduled: bool,
                writer: *std.Io.Writer,
                colors: std.io.tty.Config,
            ) void {
                logNid(writer, self.id, colors);
                const name = @tagName(self.kind);

                errdefer unreachable;

                writer.print(
                    " = {s}:{f}",
                    .{ name, self.data_type },
                ) catch unreachable;

                var add_colon_space = false;

                switch (self.kind) {
                    .CInt => {
                        const ext = self.extra(.CInt);
                        switch (self.data_type) {
                            .f64 => try writer.print(" = {d}", .{tf(ext.value)}),
                            .f32 => try writer.print(" = {d}", .{tf32(ext.value)}),
                            else => try writer.print(" = {d}", .{ext.value}),
                        }
                    },
                    inline else => |t| {
                        const ext = self.extra(t);
                        if (@TypeOf(ext.*) != void) {
                            if (comptime isVisibel(@TypeOf(ext.*))) {
                                writer.writeAll(": ") catch unreachable;
                                add_colon_space = true;
                                logExtra(writer, ext, true) catch unreachable;
                            }
                        }
                    },
                }

                const start = @min(
                    @intFromBool(scheduled and
                        (!self.isCfg() or !self.isBasicBlockStart())),
                    self.input_base[0..self.input_len].len,
                );

                for (self.input_base[0..self.input_len][start..], start..) |oo, i| if (oo) |o| {
                    if (!add_colon_space) {
                        writer.writeAll(": ") catch unreachable;
                        add_colon_space = true;
                    } else {
                        if (i == self.input_ordered_len) {
                            writer.writeAll("; ") catch unreachable;
                        } else {
                            writer.writeAll(", ") catch unreachable;
                        }
                    }
                    logNid(writer, o.id, colors);
                };

                if (true or !scheduled) {
                    writer.writeAll(" [") catch unreachable;
                    for (self.output_base[0..self.output_len], 0..) |o, i| {
                        if (i != 0) writer.writeAll(", ") catch unreachable;
                        writer.print("{}:", .{o.pos()}) catch unreachable;
                        logNid(writer, o.get().id, colors);
                    }
                    writer.writeAll("]") catch unreachable;
                }
            }

            pub fn isSwapped(node: *Node) bool {
                return callCheck("isSwapped", node);
            }

            pub fn mem(self: *Node) *Node {
                std.debug.assert(self.isLoad() or self.isStore());
                return self.inputs()[1].?;
            }

            pub fn tryBase(self: *Node) ?*Node {
                std.debug.assert(self.isLoad() or self.isStore());
                return self.inputs()[2];
            }

            pub fn base(self: *Node) *Node {
                std.debug.assert(self.isLoad() or self.isStore());
                return self.inputs()[2].?;
            }

            pub fn value(self: *Node) ?*Node {
                std.debug.assert(self.isStore());
                if (self.inputs().len < 4) return null;
                return self.inputs()[3].?;
            }

            pub fn lhs(self: *Node) *Node {
                std.debug.assert(self.isSub(builtin.BinOp));
                return self.inputs()[1].?;
            }

            pub fn rhs(self: *Node) *Node {
                std.debug.assert(self.kind == .BinOp);
                return self.inputs()[2].?;
            }

            pub fn cpySize(self: *Node) *Node {
                std.debug.assert(self.isSub(MemCpy));
                return self.inputs()[4].?;
            }

            pub fn isLazyPhi(self: *Node, on_loop: *Node) bool {
                std.debug.assert(on_loop.kind == .Loop or
                    on_loop.kind == .Region);
                return self.kind == .Phi and self.inputs()[0] == on_loop and
                    (self.inputs()[2] == null or self.inputs()[1] == null);
            }

            pub fn isLocked(self: *Node) bool {
                return self.tmp_rc != 0;
            }

            pub const Lock = struct {
                // TODO: we can inline the tag in the pointer
                node: *Node,

                pub const Meta = struct {
                    trace: std.builtin.StackTrace,
                };

                pub fn unlock(slf: @This()) void {
                    std.debug.assert(slf.node.isLocked());
                    slf.node.tmp_rc -= 1;
                }
            };

            threadlocal var arna: std.heap.ArenaAllocator = .init(std.heap.page_allocator);

            pub fn lockTmpExtra(self: *Node, slot: anytype) void {
                if (slot.* == 0) {
                    self.lockTmp();
                }
                slot.* += 1;
            }

            pub fn unlockTmpExtra(self: *Node, slot: anytype) void {
                slot.* -= 1;
                if (slot.* == 0) {
                    self.unlockTmp();
                }
            }

            pub fn lockTmp(self: *Node) void {
                self.tmp_rc += 1;
            }

            pub fn unlockTmp(self: *Node) void {
                self.tmp_rc -= 1;
            }

            pub fn lock(self: *Node) Lock {
                if (is_debug and (!self.isLocked() or true) and false) {
                    self.lock_at = arna.allocator().create(Lock.Meta) catch unreachable;
                    self.lock_at.* = Lock.Meta{
                        .trace = std.builtin.StackTrace{
                            .index = undefined,
                            .instruction_addresses = arna.allocator().alloc(usize, 10) catch unreachable,
                        },
                    };

                    std.debug.captureStackTrace(@returnAddress(), &self.lock_at.trace);
                }

                self.tmp_rc += 1;
                return .{ .node = self };
            }

            pub fn inputs(self: *Node) []?*Node {
                return self.input_base[0..self.input_len];
            }

            pub fn ordInps(self: *Node) []?*Node {
                return self.input_base[0..self.input_ordered_len];
            }

            pub fn tryCfg0(self: *Node) ?*CfgNode {
                if (self.kind == .Start) return self.asCfg().?;
                return (self.inputs()[0] orelse return null).subclass(Cfg);
            }

            pub fn cfg0(self: *Node) *CfgNode {
                if (self.kind == .Start) return forceSubclass(self, Cfg);
                if (self.inputs()[0] == null) utils.panic("{f}\n", .{self});
                return forceSubclass((self.inputs()[0].?), Cfg);
            }

            pub fn hasUseFor(self: *Node, idx: usize, def: *Node) bool {
                if (self.kind == .Call and def.kind == .LocalAlloc) {
                    return false;
                }
                return self.dataDepOffset() <= idx and
                    idx < self.input_ordered_len;
            }

            pub fn outputs(self: *Node) []Out {
                return self.output_base[0..self.output_len];
            }

            pub fn posOfOutput(self: *Node, index: usize, output: *Node) usize {
                return std.mem.indexOfScalar(
                    Out,
                    self.outputs(),
                    .init(output, index, self),
                ).?;
            }

            pub fn extra(self: *Node, comptime kind: Kind) *ClassFor(kind) {
                if (self.kind != kind) {
                    utils.panic(
                        "{f} expected {}, got {}",
                        .{ self, kind, self.kind },
                    );
                }
                const ptr: *LayoutFor(kind) = @ptrCast(@alignCast(self));
                return &ptr.ext;
            }

            pub fn extra2(self: *Node) utils.AsRef(Union) {
                const Repr = extern struct { data: *anyopaque, kind: Kind };

                const ptr: *extern struct { base: Node, ext: u8 } =
                    @ptrCast(@alignCast(self));
                return @as(
                    *const utils.AsRef(Union),
                    @ptrCast(&Repr{ .kind = self.kind, .data = &ptr.ext }),
                ).*;
            }

            pub fn isDef(self: *Node) bool {
                return !self.isStore() and
                    !self.isCfg() and
                    (self.kind != .Phi or self.isDataPhi()) and
                    self.kind != .LocalAlloc and
                    self.kind != .Mem and
                    (!@hasDecl(Backend, "isDef") or Backend.isDef(self));
            }

            pub fn kills(self: *Node) bool {
                inline for (std.meta.fields(Backend.Set.tag_)) |f| {
                    if (self.clobbers(@field(Backend.Set.tag_, f.name)) != 0) return true;
                }

                return false;
            }

            pub fn getStaticOffset(self: *Node) i64 {
                std.debug.assert(self.isMemOp());
                return if (@hasDecl(Backend, "getStaticOffset"))
                    Backend.getStaticOffset(self)
                else
                    0;
            }

            pub fn isSubbclass(Full: type, Sub: type) bool {
                var Cursor = Full;
                while (true) {
                    if (Cursor == Sub) return true;
                    if (@typeInfo(Cursor) != .@"struct" or
                        !@hasField(Cursor, "base")) return false;
                    Cursor = @TypeOf(@as(Cursor, undefined).base);
                }
            }

            pub fn bakeSubclassBitset(comptime Sub: type) std.EnumSet(Kind) {
                var bitset = std.EnumSet(Kind).initEmpty();
                for (all_classes, 0..) |c, i| {
                    if (isSubbclass(c.type, Sub)) {
                        bitset.insert(@enumFromInt(i));
                    }
                }
                return bitset;
            }

            pub fn hasFlag(
                comptime Full: type,
                comptime flag: []const u8,
            ) bool {
                var Cursor = Full;
                while (true) {
                    if (@hasDecl(Cursor, flag)) return @field(Cursor, flag);
                    if (@typeInfo(Cursor) != .@"struct" or
                        !@hasField(Cursor, "base")) return false;
                    Cursor = @TypeOf(@as(Cursor, undefined).base);
                }
            }

            pub fn bakeFlagBitset(comptime flag: []const u8) std.EnumSet(Kind) {
                var bitset = std.EnumSet(Kind).initEmpty();
                for (all_classes, 0..) |c, i| {
                    if (hasFlag(c.type, flag)) bitset.insert(@enumFromInt(i));
                }
                return bitset;
            }

            pub fn isSub(self: *const Node, comptime Sub: type) bool {
                return (comptime bakeSubclassBitset(Sub)).contains(self.kind);
            }

            pub fn subclass(self: *Node, comptime Sub: type) ?*LayoutOf(Sub) {
                if (!self.isSub(Sub)) return null;
                return @ptrCast(self);
            }

            pub fn forceSubclass(
                self: *Node,
                comptime Sub: type,
            ) *LayoutOf(Sub) {
                std.debug.assert(self.isSub(Sub));
                return @ptrCast(self);
            }

            pub fn isInterned(kind: Kind, inpts: []const ?*Node) bool {
                return switch (kind) {
                    .CInt,
                    .Poison,
                    .BinOp,
                    .Load,
                    .UnOp,
                    .GlobalAddr,
                    .FramePointer,
                    .Syms,
                    .GetLane,
                    .Local,
                    => true,
                    .Phi => std.mem.indexOfScalar(?*Node, inpts[1..], null) == null,
                    else => callCheck("isInterned", kind),
                };
            }

            pub fn asCfg(self: *Node) ?*CfgNode {
                return self.subclass(Cfg);
            }

            pub fn isCfg(self: *const Node) bool {
                return self.isSub(Cfg);
            }

            pub inline fn isStore(self: *const Node) bool {
                return self.isSub(Store);
            }

            pub inline fn isLoad(self: *const Node) bool {
                return self.isSub(Load);
            }

            pub fn isFloating(self: *const Node) bool {
                return (comptime bakeFlagBitset("is_floating"))
                    .contains(self.kind);
            }

            pub fn isPinned(self: *const Node) bool {
                return (comptime bakeFlagBitset("is_pinned"))
                    .contains(self.kind);
            }

            pub inline fn isMemOp(self: *const Node) bool {
                return self.isSub(MemOp);
            }

            pub fn isDataPhi(self: *Node) bool {
                return self.kind == .Phi and self.data_type != .top;
            }

            pub fn isBasicBlockStart(self: *const Node) bool {
                return (comptime bakeFlagBitset("is_basic_block_start"))
                    .contains(self.kind);
            }

            pub inline fn isBasicBlockEnd(self: *const Node) bool {
                std.debug.assert(self.isCfg());
                return !self.isBasicBlockStart();
            }

            pub const size_map = b: {
                var arr: [all_classes.len]u8 = undefined;
                for (all_classes, &arr) |f, *s| s.* =
                    std.mem.alignForward(u8, @sizeOf(f.type), @alignOf(Node));
                const m = arr;
                break :b m;
            };

            pub fn size(node: *Node) usize {
                return @sizeOf(Node) + size_map[@intFromEnum(node.kind)];
            }

            pub fn hash(
                kind: Kind,
                dt: DataType,
                inpts: []const ?*Node,
                extr: []const u64,
            ) u64 {
                //var hasher = std.hash.Wyhash.init(0);
                //hasher.update(std.mem.asBytes(&kind));
                //hasher.update(std.mem.asBytes(&dt));
                //hasher.update(@ptrCast(inpts));
                //hasher.update(@ptrCast(extr));

                var hsh: u64 = 0;

                // yep, this works just fine
                hsh +%= @intFromEnum(kind);
                hsh +%= @intFromEnum(dt);
                for (inpts) |i| hsh +%= @intFromPtr(i);
                for (extr) |i| hsh +%= i;

                return hsh;
            }

            pub fn cmp(
                akind: Kind,
                bkind: Kind,
                adt: DataType,
                bdt: DataType,
                ainputs: []const ?*Node,
                binputs: []const ?*Node,
                aextra: []const u64,
                bextra: []const u64,
            ) bool {
                return akind == bkind and
                    adt == bdt and
                    std.mem.eql(?*Node, ainputs, binputs) and
                    std.mem.eql(u64, aextra, bextra);
            }
        };

        pub fn init(gpa: std.mem.Allocator) Self {
            var self = Self{ .arena = .init(gpa) };
            self.start = self.addNode(.Start, .none, .top, &.{}, .{});
            return self;
        }

        pub fn deinit(self: *Self) void {
            self.arena.deinit();
            self.* = undefined;
        }

        pub fn reset(self: *Self) void {
            std.debug.assert(self.arena.reset(.retain_capacity));
            self.node_count = 0;
            self.waste = 0;
            self.start = self.addNode(.Start, .none, .top, &.{}, .{});
            self.interner = .{};
            self.gcm.cfg_built = .{};
            self.gcm.loop_tree_built = .{};
            self.stopped_interning = .{};
        }

        const Inserter = struct {
            kind: Kind,
            dt: DataType,
            inputs: []const ?*Node,
            extra: []const u64,
            hsh: u64,

            pub fn hash(s: @This(), _: void) u64 {
                return s.hsh;
            }

            pub fn eql(s: @This(), _: void, a: InternedNode) bool {
                return Node.cmp(
                    s.kind,
                    a.node.kind,
                    s.dt,
                    a.node.data_type,
                    s.inputs,
                    a.node.inputs(),
                    s.extra,
                    a.node.anyextra(),
                );
            }
        };

        const InsertMap = InternMap(Inserter);

        pub fn addSplit(
            self: *Self,
            block: *CfgNode,
            def: *Node,
            dgb: builtin.MachSplit.Dbg,
            counter: *usize,
        ) *Node {
            std.debug.assert(def.isDef());
            counter.* += 1;
            return self.addNode(
                .MachSplit,
                def.sloc,
                def.data_type,
                &.{ &block.base, null },
                .{ .dbg = dgb },
            );
        }

        pub fn splitBefore(
            self: *Self,
            use: *Node,
            idx: usize,
            def: *Node,
            skip: bool,
            dbg: builtin.MachSplit.Dbg,
            counter: *usize,
        ) void {
            std.debug.assert(idx >= use.dataDepOffset());

            const block = if (use.kind == .Phi)
                use.cfg0().base.inputs()[idx - 1].?.inputs()[0].?.asCfg().?
            else
                use.cfg0();

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();
            const mask = use.regMask(self, idx, tmp.arena);

            if (def.isReadonly() and use.kind != .Phi and
                (if (use.inPlaceSlot()) |s|
                    s + use.dataDepOffset() != idx
                else
                    true) and
                mask.setIntersects(def.regMask(self, 0, tmp.arena)))
            {
                return;
            }

            if (skip and def.kind == .MachSplit) {
                if (block == def.cfg0() and def.outputs().len == 1 and
                    mask.count() != 1)
                {
                    return;
                }
            }

            const ins = if (def.isClone() and
                // if we are already cloned, force a split as that can extend
                // the register options
                !def.alreadyBefore(use, block))
            b: {
                if (def.outputs().len == 1) {
                    const cur_block = def.cfg0();
                    const i = cur_block.base.posOfOutput(0, def);

                    std.mem.rotate(Node.Out, cur_block.base.outputs()[i..], 1);
                    cur_block.base.output_len -= 1;
                    def.inputs()[0] = &block.base;
                    self.addUse(&block.base, 0, def);
                    break :b def;
                } else {
                    break :b self.clone(def, block);
                }
            } else self.addSplit(block, if (skip and
                def.kind == .MachSplit and def.cfg0() == block)
            b: {
                break :b def.inputs()[1].?;
            } else def, dbg, counter);

            {
                const lock = def.lock();
                defer lock.unlock();

                self.setInput(use, idx, .nointern, ins);
                if (ins.kind == .MachSplit) self.setInput(ins, 1, .nointern, def);
            }

            const oidx = if (use.kind == .Phi)
                block.base.outputs().len - 2
            else
                block.base.posOfOutput(0, use);
            const to_rotate = block.base.outputs()[oidx..];
            std.mem.rotate(Node.Out, to_rotate, to_rotate.len - 1);
        }

        pub fn getMem(self: *Self) ?*Node {
            return for (self.start.outputs()) |out| {
                if (out.get().kind == .Mem) return out.get();
            } else null;
        }

        pub fn getSyms(self: *Self) *Node {
            for (self.start.outputs()) |out| {
                if (out.get().kind == .Syms) return out.get();
            } else unreachable;
        }

        pub const CallIter = struct {
            rem_syms: []Node.Out,

            pub fn next(self: *CallIter) ?*LayoutOf(builtin.Call) {
                while (self.rem_syms.len != 0) {
                    const o = self.rem_syms[0];
                    self.rem_syms = self.rem_syms[1..];
                    if (o.get().kind != .Call) continue;
                    if (o.get().extra(.Call).id == indirect_call) unreachable;
                    return o.get().subclass(builtin.Call);
                }

                return null;
            }
        };

        pub fn callIter(self: *Self) CallIter {
            return .{ .rem_syms = self.getSyms().outputs() };
        }

        pub fn clone(self: *Self, def: *Node, block: *CfgNode) *Node {
            errdefer unreachable;

            const node_size = def.size();
            const new_slot = try self.arena.allocator()
                .alignedAlloc(u8, .of(Node), node_size);
            @memcpy(new_slot, @as([*]const u8, @ptrCast(def)));
            const new_node: *Node = @ptrCast(new_slot);

            new_node.input_base = (try self.arena.allocator()
                .dupe(?*Node, new_node.inputs())).ptr;
            new_node.output_base = @ptrFromInt(@alignOf(Node.Out));
            new_node.output_cap = 0;
            new_node.output_len = 0;
            new_node.id = self.node_count;
            self.node_count += 1;

            new_node.inputs()[0] = &block.base;
            self.addUse(&block.base, 0, new_node);

            return new_node;
        }

        pub fn internNode(
            self: *Self,
            kind: Kind,
            dt: DataType,
            inputs: []const ?*Node,
            extra: []const u64,
        ) InsertMap.GetOrPutResult {
            const hash = Node.hash(kind, dt, inputs, extra);
            const int = self.interner.getOrPutContextAdapted(
                self.arena.allocator(),
                {},
                Inserter{
                    .kind = kind,
                    .inputs = inputs,
                    .dt = dt,
                    .extra = extra,
                    .hsh = hash,
                },
                .{},
            ) catch unreachable;

            if (!int.found_existing) {
                int.key_ptr.hash = hash;
            }

            return int;
        }

        const Uninserter = struct {
            pub fn hash(_: @This(), k: InternedNode) u64 {
                return k.hash;
            }

            pub fn eql(_: @This(), a: InternedNode, b: InternedNode) bool {
                return a.node == b.node;
            }
        };

        pub fn uninternNode(self: *Self, node: *Node) void {
            if (Node.isInterned(node.kind, node.inputs())) {
                if (!self.interner.remove(.{
                    .node = node,
                    .hash = Node.hash(
                        node.kind,
                        node.data_type,
                        node.inputs(),
                        node.anyextra(),
                    ),
                })) {
                    //    utils.panic("{}\n", .{node});
                }
            }
        }

        pub fn reinternNode(self: *Self, node: *Node) ?*Node {
            if (Node.isInterned(node.kind, node.inputs())) {
                const entry = self.internNode(
                    node.kind,
                    node.data_type,
                    node.inputs(),
                    node.anyextra(),
                );

                if (entry.found_existing) {
                    return entry.key_ptr.node;
                }

                entry.key_ptr.node = node;
            }

            return null;
        }

        pub fn connectOrd(self: *Self, def: *Node, to: *Node) void {
            self.connect(def, to);
            to.input_ordered_len += 1;
        }

        pub fn connect(self: *Self, def: *Node, to: *Node) void {
            if (Node.isInterned(to.kind, to.inputs())) {
                self.uninternNode(to);
            }
            const idx = self.addDep(to, def);
            self.addUse(def, idx, to);
            if (Node.isInterned(to.kind, to.inputs())) {
                _ = self.reinternNode(to);
            }
        }

        pub fn loopDepth(self: *Self, node: *Node) u16 {
            self.gcm.loop_tree_built.assertLocked();
            var cfg = node.asCfg() orelse node.cfg0();
            if (cfg.base.isBasicBlockEnd()) cfg = cfg.idom();
            const tree = &self.gcm.loop_tree[cfg.ext.loop];
            if (tree.depth != 0) return tree.depth;
            if (tree.par == null) {
                tree.par = tree.head.base.cfg0().base.cfg0().ext.loop;
            }
            tree.depth =
                self.loopDepth(&self.gcm.loop_tree[tree.par.?].head.base) + 1;
            return tree.depth;
        }

        pub fn addFieldOffset(
            self: *Self,
            sloc: Sloc,
            base: *Node,
            offset: i64,
        ) *Node {
            return if (offset == 0)
                base
            else if (base.kind == .BinOp and base.inputs()[2].?.kind == .CInt)
                self.addBinOp(
                    sloc,
                    .iadd,
                    .i64,
                    base.inputs()[1].?,
                    self.addIntImm(
                        sloc,
                        .i64,
                        base.inputs()[2].?.extra(.CInt).value + offset,
                    ),
                )
            else
                self.addBinOp(
                    sloc,
                    .iadd,
                    .i64,
                    base,
                    self.addIntImm(sloc, .i64, offset),
                );
        }

        pub fn addGlobalAddr(
            self: *Self,
            sloc: Sloc,
            arbitrary_global_id: u32,
        ) *Node {
            return self.addNode(
                .GlobalAddr,
                sloc,
                .i64,
                &.{ null, self.getSyms() },
                .{ .id = arbitrary_global_id },
            );
        }

        pub fn addFuncAddr(self: *Self, sloc: Sloc, func_id: u32) *Node {
            return self.addNode(
                .FuncAddr,
                sloc,
                .i64,
                &.{ null, self.getSyms() },
                .{ .id = func_id },
            );
        }

        pub fn addCast(
            self: *Self,
            sloc: Sloc,
            to: DataType,
            value: *Node,
        ) *Node {
            return self.addNode(
                .UnOp,
                sloc,
                to,
                &.{ null, value },
                .{ .op = .cast },
            );
        }

        pub const OffsetDirection = enum(u8) {
            iadd = @intFromEnum(BinOp.iadd),
            isub = @intFromEnum(BinOp.isub),
        };

        pub fn addIndexOffset(
            self: *Self,
            sloc: Sloc,
            base: *Node,
            op: OffsetDirection,
            elem_size: u64,
            subscript: *Node,
        ) *Node {
            const offset = if (elem_size == 1)
                subscript
            else if (subscript.kind == .CInt)
                self.addIntImm(
                    sloc,
                    .i64,
                    subscript.extra(.CInt).value *
                        @as(i64, @bitCast(elem_size)),
                )
            else
                self.addBinOp(
                    sloc,
                    .imul,
                    .i64,
                    subscript,
                    self.addIntImm(sloc, .i64, @bitCast(elem_size)),
                );
            return self.addBinOp(
                sloc,
                @enumFromInt(@intFromEnum(op)),
                .i64,
                base,
                offset,
            );
        }

        pub fn addUninit(self: *Self, sloc: Sloc, ty: DataType) *Node {
            return self.addNode(.Poison, sloc, ty, &.{null}, .{});
        }

        pub fn addIntImm(
            self: *Self,
            sloc: Sloc,
            ty: DataType,
            value: i64,
        ) *Node {
            std.debug.assert(ty != .bot);
            return self.addNode(.CInt, sloc, ty, &.{null}, .{ .value = value });
        }

        pub fn addBinOp(
            self: *Self,
            sloc: Sloc,
            op: BinOp,
            ty: DataType,
            lhs: *Node,
            rhs: *Node,
        ) *Node {
            if (lhs.kind == .CInt and rhs.kind == .CInt) {
                return self.addIntImm(
                    sloc,
                    ty,
                    op.eval(lhs.data_type, lhs.extra(.CInt).value, rhs.extra(.CInt).value),
                );
            }

            if ((op == .iadd or op == .isub) and rhs.kind == .CInt and
                rhs.extra(.CInt).value == 0)
            {
                return lhs;
            }

            if (op.isCmp()) std.debug.assert(ty == .i8);

            return self.addNode(
                .BinOp,
                sloc,
                ty,
                &.{ null, lhs, rhs },
                .{ .op = op },
            );
        }

        pub fn addUnOp(
            self: *Self,
            sloc: Sloc,
            op: UnOp,
            ty: DataType,
            oper: *Node,
        ) *Node {
            if (op == .uext and ty.size() < oper.data_type.size()) {
                return oper;
            }
            if (op == .sext and ty.size() < oper.data_type.size()) {
                return oper;
            }
            if (op == .ired and ty.size() == oper.data_type.size()) {
                return oper;
            }
            if (op == .ired and ty.size() >= oper.data_type.size()) {
                utils.panic("{f} {f}", .{ ty, oper });
            }
            if (oper.kind == .CInt) {
                return self.addIntImm(
                    sloc,
                    ty,
                    op.eval(oper.data_type, ty, oper.extra(.CInt).value),
                );
            }
            return self.addNode(
                .UnOp,
                sloc,
                ty,
                &.{ null, oper },
                .{ .op = op },
            );
        }

        pub fn addPhi(self: *Self, sloc: Sloc, ctrl: *Node, lhs: *Node, rhs: *Node) *Node {
            std.debug.assert(ctrl.kind == .Region);
            return self.addNode(
                .Phi,
                sloc,
                lhs.data_type.meet(rhs.data_type),
                &.{ ctrl, lhs, rhs },
                .{},
            );
        }

        fn addMemJoin(self: *Self, to_join: []const *Node) *Node {
            errdefer unreachable;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            if (to_join.len == 1) return to_join[0];

            var loads = std.ArrayList(*Node){};
            for (to_join) |st| {
                var cursor = st;
                while (cursor.kind == .Store) {
                    for (cursor.outputs()) |out| {
                        if (out.pos() == 1 and out.get().kind == .Load) {
                            try loads.append(tmp.arena.allocator(), out.get());
                        }
                    }
                    cursor = cursor.mem();
                }
            }

            for (loads.items) |load| {
                for (to_join) |st| {
                    var cursor = st;
                    while (cursor.kind == .Store) {
                        if (cursor.base() == load.base() and
                            cursor.data_type == load.data_type)
                        {
                            self.subsume(cursor.value().?, load);
                        }

                        cursor = cursor.mem();
                    }
                }
            }

            const inps = try std.mem.concat(
                tmp.arena.allocator(),
                ?*Node,
                &.{ &.{null}, to_join },
            );
            return self.addNode(.MemJoin, .none, .top, inps, .{});
        }

        pub fn addTrap(
            self: *Self,
            sloc: Sloc,
            ctrl: *Node,
            code: u64,
            comptime mode: ModMode,
        ) void {
            if (self.end.inputs()[2] == null) {
                _ = self.setInput(self.end, 2, mode, self.addNode(
                    .TrapRegion,
                    sloc,
                    .top,
                    &.{},
                    .{ .base = .{ .loop = 0 } },
                ));
            }

            const region = self.end.inputs()[2].?;
            const trap = self.addNode(
                .Trap,
                sloc,
                .top,
                &.{ctrl},
                .{ .code = code, .base = .{ .loop = 0 } },
            );

            const idx = self.addDep(region, trap);
            self.addUse(trap, idx, region);
        }

        pub fn addNode(
            self: *Self,
            comptime kind: Kind,
            sloc: Sloc,
            ty: DataType,
            inputs: []const ?*Node,
            extra: ClassFor(kind),
        ) *Node {
            var typ = ty;
            if (kind == .Phi) {
                for (inputs) |i| {
                    if (i) |j| {
                        if (j.kind == .Mem or j.isStore()) typ = .top;
                    }
                }
            }
            var bytes: [Node.size_map[@intFromEnum(kind)] / 8]u64 = @splat(0);
            @as(*ClassFor(kind), @ptrCast(&bytes)).* = extra;
            const node = self.addNodeUntyped(kind, typ, inputs, &bytes);
            node.sloc = sloc;

            return node;
        }

        pub fn addNodeUntyped(
            self: *Self,
            kind: Kind,
            dt: DataType,
            inputs: []const ?*Node,
            extra: []const u64,
        ) *Node {
            if (Node.isInterned(kind, inputs)) {
                const entry = self.internNode(kind, dt, inputs, extra);
                if (!entry.found_existing) {
                    entry.key_ptr.node =
                        self.addNodeNoIntern(kind, dt, inputs, extra);
                }

                const node = entry.key_ptr.node;

                return node;
            } else {
                return self.addNodeNoIntern(kind, dt, inputs, extra);
            }
        }

        pub fn addNodeNoIntern(
            self: *Self,
            kind: Kind,
            ty: DataType,
            inputs: []const ?*Node,
            extra: []const u64,
        ) *Node {
            errdefer unreachable;
            const size = @sizeOf(Node) + extra.len * @sizeOf(u64);
            const node: *Node = @ptrCast(@alignCast(self.arena.allocator()
                .rawAlloc(size, .@"8", @returnAddress()).?));
            const owned_inputs =
                try self.arena.allocator().dupe(?*Node, inputs);

            node.* = .{
                .input_base = owned_inputs.ptr,
                .input_len = @intCast(owned_inputs.len),
                .input_ordered_len = @intCast(owned_inputs.len),
                .output_base = @ptrFromInt(@alignOf(Node.Out)),
                .kind = kind,
                .id = self.node_count,
                .data_type = ty,
            };

            if (node.id > 10000) unreachable;

            self.node_count += 1;

            @memcpy(@as([*]u64, @ptrCast(&node.edata)), extra);

            for (node.ordInps(), 0..) |on, i| if (on) |def| {
                self.addUse(def, i, node);
            };

            return node;
        }

        pub fn kill(func: *Self, self: *Node) void {
            self.assertAlive();

            if (self.kind == .Syms) return;
            if (self.isLocked()) return;

            func.uninternNode(self);

            if (is_debug and false) {
                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();

                const kill_meta = func.arena.allocator()
                    .create(Node.KillMeta) catch unreachable;

                kill_meta.displayed = std.fmt.allocPrint(
                    func.arena.allocator(),
                    "{f}",
                    .{self},
                ) catch unreachable;

                kill_meta.trace.instruction_addresses = tmp.arena.alloc(usize, 20);
                std.debug.captureStackTrace(@returnAddress(), &kill_meta.trace);
                kill_meta.trace.instruction_addresses = func.arena.allocator()
                    .dupe(usize, kill_meta.trace.instruction_addresses) catch
                    unreachable;

                self.killed_at = kill_meta;
            }

            if (self.output_len != 0) {
                for (self.outputs()) |o| {
                    print("{f}\n", .{o});
                }
                utils.panic("{f}\n", .{self});
            }

            std.debug.assert(self.output_len == 0);
            for (self.inputs(), 0..) |oi, j| if (oi) |i| {
                func.removeUse(i, j, self);
            };

            func.waste += self.input_len * @sizeOf(?*Node);
            func.waste += self.size();
            func.waste += @as(usize, self.output_cap) * @sizeOf(Node.Out);
            const kill_meta = self.killed_at;
            self.* = undefined;
            self.killed_at = kill_meta;
            self.kind = .Dead;
        }

        pub fn subsumeNoIntern(
            self: *Self,
            this: *Node,
            target: *Node,
            comptime mode: ModMode,
        ) void {
            const lock = this.lock();
            defer lock.unlock();

            if (this.id == 101) {
                //std.debug.dumpCurrentStackTrace(@returnAddress());
            }

            if (target.outputs().len == 0) {
                self.kill(target);
                return;
            }

            if (this == target) {
                utils.panic("{f} {f}\n", .{ this, target });
            }
            errdefer unreachable;

            const tlock = target.lock();
            defer {
                tlock.unlock();
                if (target.outputs().len == 0) self.kill(target);
            }

            self.ensureOutputCapacity(this, target.outputs().len);

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            for (tmp.arena.dupe(Node.Out, target.outputs())) |use| {
                if (use.get().isDead()) continue;

                if (use.get() == target) {
                    self.removeUse(target, use.pos(), target);
                    target.inputs()[use.pos()] = null;
                } else {
                    _ = self.setInput(use.get(), use.pos(), mode, this);
                }
            }
        }

        pub const ModMode = enum { intern, nointern };

        pub fn subsume(
            self: *Self,
            this: *Node,
            target: *Node,
            comptime mode: ModMode,
        ) void {
            //std.debug. print("subsume: {f} -> {f}\n", .{ target, this });
            if (target.isDead()) return;
            if (this.sloc == Sloc.none) this.sloc = target.sloc;
            if (mode == .intern) self.uninternNode(target);
            self.subsumeNoIntern(this, target, mode);
        }

        pub fn removeUse(self: *Self, def: *Node, idx: usize, use: *Node) void {
            const outs = def.outputs();
            const index = std.mem.indexOfScalar(
                Node.Out,
                outs,
                .init(use, idx, def),
            ) orelse {
                utils.panic(
                    "removeUse: not found {f} {any} {f}",
                    .{ use, outs, def },
                );
            };

            outs[index] = outs[outs.len - 1];
            outs[outs.len - 1] = undefined;
            def.output_len -= 1;

            if (def.output_len == 0) {
                self.kill(def);
            }
        }

        pub fn setInputNoIntern(
            self: *Self,
            use: *Node,
            idx: usize,
            def: ?*Node,
        ) void {
            if (self.setInput(use, idx, .intern, def)) |new| {
                utils.panic("setInputNoIntern: {f}", .{new});
            }
        }

        pub fn setInput(
            self: *Self,
            use: *Node,
            idx: usize,
            comptime mode: ModMode,
            def: switch (mode) {
                .intern => ?*Node,
                .nointern => *Node,
            },
        ) switch (mode) {
            .intern => ?*Node,
            .nointern => void,
        } {
            switch (mode) {
                .intern => self.stopped_interning.assertUnlocked(),
                .nointern => self.stopped_interning.assertLocked(),
            }

            var lock: ?Node.Lock = null;
            if (mode == .intern) {
                if (def) |d| {
                    lock = d.lock();
                }
            } else {
                lock = use.lock();
            }
            defer if (lock) |l| l.unlock();

            if (use.inputs()[idx] == def) return if (mode == .intern) null;
            if (use.inputs()[idx]) |n| {
                self.removeUse(n, idx, use);
            }

            if (mode == .intern) self.uninternNode(use);
            use.inputs()[idx] = def;
            if (mode == .intern) {
                if (def) |d| {
                    _ = self.addUse(d, idx, use);
                }
            } else {
                _ = self.addUse(def, idx, use);
            }
            if (mode == .intern) {
                if (self.reinternNode(use)) |nuse| {
                    self.subsumeNoIntern(nuse, use, mode);
                    return nuse;
                }
            }
            return if (mode == .intern) null;
        }

        pub fn addDep(self: *Self, use: *Node, def: *Node) usize {
            use.assertAlive();
            def.assertAlive();

            if (use.input_ordered_len == use.input_len or
                std.mem.indexOfScalar(
                    ?*Node,
                    use.input_base[use.input_ordered_len..use.input_len],
                    null,
                ) == null)
            {
                self.waste += @sizeOf(?*Node) * use.input_len;
                const new_cap = @max(use.input_len, 1) * 2;
                const new_inputs = self.arena.allocator()
                    .realloc(use.inputs(), new_cap) catch unreachable;
                @memset(new_inputs[use.input_len..], null);
                use.input_base = new_inputs.ptr;
                use.input_len = new_cap;
            }

            for (
                use.input_base[use.input_ordered_len..use.input_len],
                use.input_ordered_len..,
            ) |*slot, i| {
                if (slot.* == null) {
                    slot.* = def;
                    return i;
                }
            } else unreachable;
        }

        pub fn ensureOutputCapacity(
            self: *Self,
            def: *Node,
            at_least: usize,
        ) void {
            def.assertAlive();

            if (def.output_cap < at_least) {
                self.waste += @sizeOf(Node.Out) * @as(usize, def.output_cap);
                const new_cap = @max(@max(def.output_cap, 1) * 2, at_least);
                const new_outputs = self.arena.allocator()
                    .realloc(def.outputs(), new_cap) catch unreachable;
                def.output_base = new_outputs.ptr;
                def.output_cap = @intCast(new_cap);
            }
        }

        pub fn addUse(self: *Self, def: *Node, index: usize, use: *Node) void {
            def.assertAlive();
            use.assertAlive();

            self.ensureOutputCapacity(def, def.output_len + 1);
            def.output_base[def.output_len] = .init(use, index, def);
            def.output_len += 1;
        }

        pub const Frame = struct { *Node, []const Node.Out };

        pub fn traversePostorder(
            ctx: anytype,
            inp: *Node,
            stack: *std.ArrayList(Frame),
            visited: *std.DynamicBitSetUnmanaged,
            gpa: std.mem.Allocator,
        ) void {
            errdefer unreachable;

            const Ctx = if (@typeInfo(@TypeOf(ctx)) == .pointer)
                @TypeOf(ctx.*)
            else
                @TypeOf(ctx);

            try stack.append(gpa, .{ inp, inp.outputs() });
            visited.set(inp.id);
            while (stack.items.len > 0) {
                const frame = &stack.items[stack.items.len - 1];
                if (frame[1].len == 0) {
                    _ = stack.pop();
                    ctx.each(frame[0]);
                    continue;
                }
                const node = frame[1][0];
                frame[1] = frame[1][1..];
                const n = node.get();
                if ((!@hasDecl(Ctx, "filter") or ctx.filter(n)) and
                    !visited.isSet(n.id))
                {
                    visited.set(n.id);
                    try stack.append(gpa, .{ n, n.outputs() });
                }
            }
        }

        pub fn collectPostorder(
            self: *Self,
            arena: std.mem.Allocator,
            visited: *std.DynamicBitSetUnmanaged,
        ) []*CfgNode {
            var postorder = std.ArrayList(*CfgNode).empty;

            collectPostorder2(self, self.start, arena, &postorder, visited);

            std.mem.reverse(*CfgNode, postorder.items);

            return postorder.items;
        }

        pub fn collectPostorder2(
            self: *Self,
            node: *Node,
            arena: std.mem.Allocator,
            pos: *std.ArrayList(*CfgNode),
            visited: *std.DynamicBitSetUnmanaged,
        ) void {
            switch (node.kind) {
                .TrapRegion => return,
                else => {
                    if (visited.isSet(node.id)) {
                        return;
                    }
                    visited.set(node.id);
                },
            }

            if (node.isSwapped()) {
                for (node.outputs()) |o| {
                    if (o.get().isCfg()) {
                        collectPostorder2(self, o.get(), arena, pos, visited);
                    }
                }
            } else {
                var iter = std.mem.reverseIterator(node.outputs());
                while (@as(?Node.Out, iter.next())) |o| {
                    if (o.get().isCfg()) {
                        collectPostorder2(self, o.get(), arena, pos, visited);
                    }
                }
            }

            if (node.isBasicBlockStart()) {
                pos.append(arena, node.asCfg().?) catch unreachable;
            }
        }

        pub fn compact(self: *Self) void {
            if (self.arena.queryCapacity() > self.waste * 2 -| @sizeOf(Node) * 32) return;

            const Inln = inliner.Mixin(Backend);

            const prev_arena = self.arena;
            defer prev_arena.deinit();

            self.arena = .init(self.arena.child_allocator);
            self.interner = .empty;
            self.waste = 0;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const cloned = Inln.cloneNodes(
                self.start,
                self.end,
                self.node_count,
                &self.arena,
                0,
                tmp.arena,
            );

            self.start = cloned.new_node_table[self.start.id];
            self.end = cloned.new_node_table[self.end.id];
            self.node_count = @intCast(cloned.new_node_table.len);
            self.signature = self.signature.dupe(self.arena.allocator());

            Inln.internBatch(self.start, self.end, 0, self, cloned.new_nodes);
        }

        pub fn IdealSig(C: type) type {
            return fn (C, *Self, *Node, *WorkList) ?*Node;
        }

        pub fn logNid(
            wr: *std.Io.Writer,
            nid: usize,
            cc: std.io.tty.Config,
        ) void {
            errdefer unreachable;

            try utils.setColor(cc, wr, @enumFromInt(1 + nid % 15));
            try wr.print("%{d}", .{nid});
            try utils.setColor(cc, wr, .reset);
        }

        pub fn computeStructArgLayout(self: *Self) void {
            var stack_arg_offset: u64 = 0;
            for (self.signature.params(), 0..) |par, j| {
                if (par == .Stack) {
                    const argn = for ((self.getMem() orelse return).outputs()) |o| {
                        switch (o.get().extra2()) {
                            .LocalAlloc => |extra| {
                                if (extra.meta.kind == .parameter and extra.meta.index == j) {
                                    break o.get();
                                }
                            },
                            else => {},
                        }
                    } else {
                        continue; // is dead
                    };

                    stack_arg_offset = std.mem.alignForward(
                        u64,
                        stack_arg_offset,
                        par.Stack.alignmentBytes(),
                    );
                    argn.extra(.LocalAlloc).size = @intCast(stack_arg_offset);
                    stack_arg_offset += par.Stack.size;
                }
            }
        }

        pub fn computeCallSlotSize(self: *Self) struct { bool, u64 } {
            var has_call = false;
            var call_slot_size: u64 = 0;
            for (self.gcm.postorder) |bb| {
                if (bb.base.kind == .MemCpy) has_call = true;
                if (bb.base.kind == .CallEnd) {
                    const call = bb.base.inputs()[0].?;
                    const signature: *Signature = &call.extra(.Call).signature;
                    call_slot_size =
                        @max(signature.stackSize(Backend, call), call_slot_size);
                    has_call = true;
                }
            }
            return .{ has_call, call_slot_size };
        }

        pub fn computeStackLayout(self: *Self, start_pos: i64) i64 {
            const mem = self.getMem() orelse return 0;

            var local_size: i64 = start_pos;

            std.sort.pdq(Node.Out, mem.outputs(), {}, struct {
                fn isBigger(_: void, lhs: Node.Out, rhs: Node.Out) bool {
                    return switch (lhs.get().extra2()) {
                        .LocalAlloc => |l| @ctz(l.size) >
                            switch (rhs.get().extra2()) {
                                .LocalAlloc => |r| @ctz(r.size),
                                else => return true,
                            },
                        else => false,
                    };
                }
            }.isBigger);

            std.debug.assert(self.start.outputs()[1].get().kind == .Mem);
            for (mem.outputs(), 0..) |o, i| {
                if (o.get().kind != .LocalAlloc) {
                    std.debug.assert(for (mem.outputs()[i + 1 ..]) |oo| {
                        if (oo.get().kind == .LocalAlloc) break false;
                    } else true);
                    break;
                }

                const extra = o.get().extra(.LocalAlloc);
                if (extra.meta.kind != .variable) continue;
                const size = extra.size;
                extra.size = @bitCast(local_size);
                local_size += @intCast(size);
            }

            return local_size;
        }

        // returns the loop ranges and wether order was changed
        pub fn backshiftLoopBodies(
            func: *Self,
            scratch: *utils.Arena,
        ) struct { [][2]u32, bool } {
            // so this is slow? maybe we can mark nodes we visited each round
            // and then exit early

            var ranges = scratch.makeArrayList([2]u32, func.gcm.postorder.len);
            var changed = false;
            for (func.gcm.postorder, 0..) |bb, i| {
                if (bb.base.kind != .Loop) continue;

                var backshift_cursor = i + 1;
                for (func.gcm.postorder[i + 1 ..], i + 1..) |inb, j| {
                    var cursor = inb;
                    while (cursor.idepth() >= bb.idepth()) : (cursor =
                        cursor.idom())
                    {
                        if (cursor == bb) {
                            std.mem.rotate(
                                *CfgNode,
                                func.gcm.postorder[backshift_cursor .. j + 1],
                                j - backshift_cursor,
                            );
                            backshift_cursor += 1;
                            changed = true;
                            break;
                        }
                    }
                }

                ranges.appendAssumeCapacity(.{
                    @intCast(i),
                    @intCast(backshift_cursor - 1),
                });
            }

            if (is_debug and !utils.freestanding) {
                for (func.gcm.postorder, 0..) |bb, i| {
                    if (bb.base.kind != .Loop) continue;

                    var seen_non_dom = false;
                    for (func.gcm.postorder[i..]) |inb| {
                        var cursor = inb;
                        while (cursor.idepth() >= bb.idepth()) : (cursor =
                            cursor.idom())
                        {
                            if (cursor == bb) {
                                if (seen_non_dom) {
                                    func.fmtScheduledLog();
                                    utils.panic("\n{f}\n{f}\n", .{ bb, inb });
                                }
                                break;
                            }
                        } else {
                            seen_non_dom = true;
                        }
                    }
                }
            }

            return .{ ranges.items, changed };
        }

        pub fn fmtScheduledLog(self: *Self) void {
            var writer = std.fs.File.stderr().writer(&.{});
            self.fmtScheduled(&writer.interface, .escape_codes);
        }

        pub fn fmtScheduled(
            self: *Self,
            writer: *std.Io.Writer,
            colors: std.io.tty.Config,
        ) void {
            errdefer unreachable;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            if (self.name.len != 0) try writer.print("{s}\n", .{self.name});

            self.start.fmt(true, writer, colors);
            if (self.start.outputs().len > 1 and
                self.start.outputs()[1].get().kind == .Mem)
            {
                for (self.start.outputs()[1].get().outputs()) |oo| {
                    if (oo.get().kind == .LocalAlloc) {
                        try writer.writeAll("\n  ");
                        oo.get().fmt(true, writer, colors);
                    }
                }
            }
            try writer.writeAll("\n");
            for (self.gcm.postorder) |p| {
                p.base.fmt(true, writer, colors);

                try writer.writeAll("\n");
                for (p.base.outputs()) |o| {
                    try writer.writeAll("  ");
                    o.get().fmt(true, writer, colors);
                    try writer.writeAll("\n");
                }
            }
        }

        pub fn fmtUnscheduled(
            self: *Self,
            writer: *std.Io.Writer,
            colors: std.io.tty.Config,
        ) void {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var worklist = Self.WorkList
                .init(tmp.arena.allocator(), self.node_count) catch unreachable;
            worklist.collectAll(self);

            for (worklist.items()) |p| {
                p.fmt(false, writer, colors);
                writer.writeAll("\n") catch unreachable;
            }
        }

        pub fn fmtUnscheduledLog(self: *Self) void {
            var writer = std.fs.File.stderr().writer(&.{});
            self.fmtUnscheduled(&writer.interface, .escape_codes);
        }
    };
}
