const std = @import("std");
pub const utils = @import("../utils.zig");
const Machine = @import("Machine.zig");
const matcher = @import("graph.IdealGen");

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
    return s.masks[0 .. (s.bit_length + @bitSizeOf(Set.MaskInt) - 1) / @bitSizeOf(Set.MaskInt)];
}

pub const infinite_loop_trap = std.math.maxInt(u64);
pub const unreachable_func_trap = infinite_loop_trap - 1;
pub const indirect_call = Machine.max_func - 100;

pub const Sloc = packed struct(i64) {
    namespace: u32,
    index: u32,

    pub const none: Sloc = .{ .namespace = std.math.maxInt(u32), .index = std.math.maxInt(u32) };
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
        return self.isInRange(.ne, .ule) or self.isInRange(.sgt, .sle) or self.isInRange(.fgt, .fle);
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
        return @intFromEnum(min) <= @intFromEnum(self) and @intFromEnum(self) <= @intFromEnum(max);
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
            .sdiv => if (rhs == 0) 0 else switch (dt) {
                .i8 => @divFloor(@as(i8, @truncate(lhs)), @as(i8, @truncate(rhs))),
                .i16 => @divFloor(@as(i16, @truncate(lhs)), @as(i16, @truncate(rhs))),
                .i32 => @divFloor(@as(i32, @truncate(lhs)), @as(i32, @truncate(rhs))),
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
            .bor => lhs | rhs,
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

            .sgt => @intFromBool(lhs > rhs),
            .slt => @intFromBool(lhs < rhs),
            .sge => @intFromBool(lhs >= rhs),
            .sle => @intFromBool(lhs <= rhs),
        }) & dt.mask().?;
    }

    pub fn isComutative(self: BinOp) bool {
        return switch (self) {
            .iadd, .imul, .band, .bor, .bxor, .fadd, .fmul, .ne, .eq => true,
            else => false,
        };
    }

    pub fn isAsociative(self: BinOp) bool {
        return switch (self) {
            .iadd, .imul, .band, .bor, .bxor, .ne, .eq => true,
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
            .band => @as(i64, -1) & ty.mask().?,
            .imul, .sdiv, .udiv => 1,
            .fmul, .fdiv => if (ty == .f64) @bitCast(@as(f64, 1.0)) else @as(u32, @bitCast(@as(f32, 1.0))),
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

    pub fn eval(self: UnOp, src: DataType, dst: DataType, oper: i64) i64 {
        return @as(i64, switch (self) {
            .cast => oper,
            .sext => return switch (src) {
                .i8 => @as(i8, @truncate(oper)),
                .i16 => @as(i16, @truncate(oper)),
                .i32 => @as(i32, @truncate(oper)),
                .i64 => oper,
                else => utils.panic("{}", .{src}),
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
            .fti => if (src == .f64) @intFromFloat(tf(oper)) else @intFromFloat(tf32(oper)),
            .itf => return if (dst == .f64)
                @bitCast(@as(f64, @floatFromInt(oper)))
            else
                @as(u32, @bitCast(@as(f32, @floatFromInt(oper)))),
            .fcst => return if (src == .f64)
                @as(u32, @bitCast(@as(f32, @floatCast(tf(oper)))))
            else
                @bitCast(@as(f64, @floatCast(tf32(oper)))),
        }) & src.mask().?;
    }
};

pub const DataType = enum(u16) {
    bot,
    i8,
    i16,
    i32,
    i64,
    f32,
    f64,
    top,
    _,

    // TODO: derive this from DataType
    pub const Kind = enum(u3) {
        top,
        i8,
        i16,
        i32,
        i64,
        f32,
        f64,
        bot,

        pub fn isFloat(self: Kind) bool {
            return switch (self) {
                .f32, .f64 => true,
                else => false,
            };
        }

        pub fn size(self: Kind) u64 {
            return switch (self) {
                .top, .bot => unreachable,
                .i8 => 1,
                .i16 => 2,
                .i32, .f32 => 4,
                .i64, .f64 => 8,
            };
        }

        pub fn mask(self: Kind) i64 {
            return switch (self) {
                .top, .bot => unreachable,
                .i8 => 0xFF,
                .i16 => 0xFFFF,
                .i32, .f32 => 0xFFFFFFFF,
                .i64, .f64 => -1,
            };
        }
    };

    comptime {
        std.debug.assert(std.meta.fields(Kind).len == std.meta.fields(DataType).len);
    }

    pub const Raw = packed struct(u16) {
        kind: Kind,
        one_less_then_lanes: u5 = 0,
        unused: u8 = 0,

        pub fn lanes(self: Raw) u64 {
            return @as(u64, self.one_less_then_lanes) + 1;
        }
    };

    pub fn memUnitForAlign(alignment: u64, float: bool) DataType {
        if (float) return @enumFromInt(@intFromEnum(DataType.f32) + @min(std.math.log2_int(u64, alignment), 3) - 2);
        return @enumFromInt(@intFromEnum(DataType.i8) + @min(std.math.log2_int(u64, alignment), 3));
    }

    pub fn toRaw(self: DataType) Raw {
        return @bitCast(@intFromEnum(self));
    }

    pub fn fromRaw(raw: Raw) DataType {
        return @enumFromInt(@as(u16, @bitCast(raw)));
    }

    pub fn vec(ty: DataType, lans: u64) DataType {
        const raw = ty.toRaw();
        return .fromRaw(.{
            .kind = raw.kind,
            .one_less_then_lanes = @intCast(raw.lanes() * lans - 1),
        });
    }

    pub fn lanes(self: DataType) u64 {
        return self.toRaw().lanes();
    }

    pub fn size(self: DataType) u64 {
        const raw = self.toRaw();
        return raw.kind.size() * raw.lanes();
    }

    pub fn mask(self: DataType) ?i64 {
        return switch (self) {
            .top, .bot => unreachable,
            .i8 => 0xFF,
            .i16 => 0xFFFF,
            .i32, .f32 => 0xFFFFFFFF,
            .i64, .f64 => -1,
            else => {
                if (self.size() == 8) return -1;
                return null;
            },
        };
    }

    pub fn isSse(self: DataType) bool {
        return self.lanes() != 1;
    }

    pub fn isFloat(self: DataType) bool {
        return switch (self) {
            .f32, .f64 => true,
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
};

pub const AbiParam = union(enum) {
    Reg: DataType,
    Stack: StackSpec,

    pub const StackSpec = packed struct(u64) {
        alignment: u3,
        size: u61,

        pub fn reg(dt: DataType) StackSpec {
            return .{
                .size = @intCast(dt.size()),
                .alignment = @intCast(std.math.log2_int(u64, dt.size())),
            };
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
    refcall,
    systemv,
    ablecall,
    fastcall,
    @"inline",
};

pub const Signature = extern struct {
    par_base: [*]AbiParam = undefined,
    ret_base: ?[*]AbiParam = undefined,
    call_conv: CallConv = .refcall,
    par_count: u8 = 0,
    ret_count: u8 = 0,

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

    pub fn stackSize(self: @This()) u64 {
        switch (self.call_conv) {
            .systemv => {
                var size: u64 = 0;
                for (self.params()) |par| {
                    if (par == .Stack) {
                        size = std.mem.alignForward(u64, size, @as(u64, 1) << par.Stack.alignment);
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

        pub const data_dep_offset = 1;
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
        anal_stage: enum(u8) { is_infinite, has_break, has_dead_break } = .is_infinite,

        pub const is_basic_block_start = true;
    };
    pub const TrapRegion = extern struct {
        base: Cfg = .{},

        pub const is_basic_block_start = true;
    };
    // ===== VALUES ====
    pub const LocalAlloc = extern struct {
        size: u64,
        meta: u32 = std.math.maxInt(u32),
        debug_ty: u32,

        pub const is_floating = true;
        pub const is_pinned = true;
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
    pub const StructArg = extern struct {
        base: mod.Arg,
        spec: AbiParam.StackSpec,
        no_address: bool = false,
        debug_ty: u32,
    };
    pub const StackArgOffset = extern struct {
        offset: u64, // from eg. rsp
    };
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
    };
    // ===== MEMORY =====
    pub const Mem = extern struct {
        pub const is_pinned = true;
    };
    pub const MemJoin = extern struct {};
    pub const MemCpy = mod.MemCpy;
    pub const Load = mod.Load;
    pub const Store = mod.Store;
    pub const GlobalAddr = extern struct {
        id: u32,
        pub const is_clone = true;
    };

    pub const Dead = extern struct {};
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
    var fields: [bdecls.len + cdecls.len]std.builtin.Type.UnionField = undefined;
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
    idepth: u16 = 0,
    antidep: u16 = 0,
    loop: u16 = undefined,
};

const mod = @This();
const gcm = @import("gcm.zig");
const mem2reg = @import("mem2reg.zig");
const static_anal = @import("static_anal.zig");
const inliner = @import("inliner.zig");
const alias_anal = @import("alias_anal.zig");

pub fn FuncNode(comptime Backend: type) type {
    return Func(Backend).Node;
}

pub fn Func(comptime Backend: type) type {
    return struct {
        arena: std.heap.ArenaAllocator,
        interner: InternMap(Uninserter) = .{},
        signature: Signature = .{},
        next_id: u16 = 0,
        corrupted: bool = false,
        waste: usize = 0,
        start: *Node = undefined,
        end: *Node = undefined,
        gcm: gcm.Mixin(Backend) = .{},
        mem2reg: mem2reg.Mixin(Backend) = .{},
        alias_anal: alias_anal.Mixin(Backend) = .{},
        static_anal: static_anal.Mixin(Backend) = .{},
        inliner: inliner.Mixin(Backend) = .{},
        stopped_interning: std.debug.SafetyLock = .{},

        pub fn optApi(comptime decl_name: []const u8, comptime Ty: type) bool {
            const prelude = @typeName(Backend) ++ " requires this unless `pub const i_know_the_api = {}` is declared:";

            const decl = if (@typeInfo(Ty) == .@"fn")
                "pub fn " ++ decl_name ++ @typeName(Ty)[3..]
            else
                "pub const " ++ decl_name ++ ": " ++ @typeName(Ty);

            const known_api = @hasDecl(Backend, "i_know_the_api");
            if (!known_api and !@hasDecl(Backend, decl_name))
                @compileError(prelude ++ " `" ++ decl ++ "`");

            if (@hasDecl(Backend, decl_name) and @TypeOf(@field(Backend, decl_name)) != Ty)
                @compileError("expected `" ++ decl ++
                    "` but the type is: " ++ @typeName(@TypeOf(@field(Backend, decl_name))));

            return @hasDecl(Backend, decl_name);
        }

        pub fn InternMap(comptime Context: type) type {
            return std.hash_map.HashMapUnmanaged(InternedNode, void, Context, std.hash_map.default_max_load_percentage);
        }

        pub const biased_regs = if (optApi("biased_regs", u64)) Backend.biased_regs else 0;
        pub const all_classes = std.meta.fields(Union);

        pub const sclass_spec: struct { vars: if (use_vec) @Vector(8, u8) else [8]u8, len: usize } = collect_sclasses: {
            var variants: [8]u8 = @splat(0);
            var found_count: usize = 0;
            for (all_classes) |class| {
                const size = std.mem.alignForward(u32, @sizeOf(class.type), @alignOf(Node));
                for (variants[0..found_count]) |v| {
                    if (v == size) break;
                } else {
                    variants[found_count] = size;
                    found_count += 1;
                }
            }
            break :collect_sclasses .{ .vars = variants, .len = found_count };
        };

        comptime {
            _ = &sclass_spec;
        }

        const use_vec = @import("builtin").mode != .Debug;

        pub fn sclassOf(kind: Kind) u3 {
            const size = Node.size_map[@intFromEnum(kind)];
            if (use_vec) {
                return std.simd.firstIndexOfValue(sclass_spec.vars, size).?;
            } else {
                for (sclass_spec.vars, 0..) |v, i| {
                    if (size == v) return @intCast(i);
                } else unreachable;
            }
        }

        const Self = @This();

        pub const WorkList = struct {
            list: std.ArrayList(*Node),
            in_list: std.DynamicBitSetUnmanaged,
            allocator: std.mem.Allocator,

            pub fn init(gpa: std.mem.Allocator, cap: usize) !WorkList {
                return .{
                    .list = try .initCapacity(gpa, cap),
                    .in_list = try .initEmpty(gpa, cap),
                    .allocator = gpa,
                };
            }

            pub fn add(self: *WorkList, node: *Node) void {
                errdefer unreachable;

                if (node.isDead()) utils.panic("{f} {any}\n", .{ node, node.inputs() });
                if (self.in_list.bit_length <= node.id) {
                    try self.in_list.resize(
                        self.allocator,
                        try std.math.ceilPowerOfTwo(usize, node.id + 1),
                        false,
                    );
                }

                if (self.in_list.isSet(node.id)) return;
                self.in_list.set(node.id);
                try self.list.append(self.allocator, node);
            }

            pub fn pop(self: *WorkList) ?*Node {
                var node = self.list.pop() orelse return null;
                while (node.isDead()) {
                    node = self.list.pop() orelse return null;
                }
                self.in_list.unset(node.id);
                return node;
            }

            pub fn collectAll(self: *WorkList, func: *Self) void {
                self.add(func.end);
                self.add(func.start);
                var i: usize = 0;
                while (i < self.items().len) : (i += 1) {
                    const n = self.items()[i];
                    for (n.inputs()) |oi| if (oi) |o| self.add(o);
                    for (n.outputs()) |o| self.add(o.get());
                }
            }

            pub fn items(self: *WorkList) []*Node {
                return self.list.items;
            }
        };

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

                pub fn idepth(cfg: *CfgNode) u16 {
                    const extra: *Cfg = &cfg.ext;

                    if (extra.idepth != 0) return extra.idepth;
                    extra.idepth = switch (cfg.base.kind) {
                        .Start => return 0,
                        .Region => @max(
                            cfg.base.inputs()[0].?.asCfg().?.idepth(),
                            cfg.base.inputs()[1].?.asCfg().?.idepth(),
                        ) + 1,
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
                                (!@as(*Node, @ptrCast(extra.cached_lca)).isSub(If) or
                                    @as(*Node, @ptrCast(extra.cached_lca)).subclass(If).?.ext.id != cfg.base.id))
                                extra.cached_lca = null;

                            if (extra.cached_lca) |lca| {
                                return @ptrCast(lca);
                            } else {
                                const lca = findLca(
                                    cfg.base.inputs()[0].?.asCfg().?,
                                    cfg.base.inputs()[1].?.asCfg().?,
                                );
                                cfg.base.extra(.Region).cached_lca = lca;
                                (lca.base.subclass(If) orelse return lca).ext.id = cfg.base.id;
                                return lca;
                            }
                        },
                        else => cfg.base.cfg0(),
                    };
                }

                pub fn better(cfg: *CfgNode, best: *CfgNode, to_sched: *Node, func: *Self) bool {
                    return !cfg.base.isBasicBlockEnd() and (idepth(cfg) > idepth(best) or
                        best.base.isBasicBlockEnd() or
                        (to_sched.kind != .MachSplit and !to_sched.isCheap() and func.gcm.loopDepthOf(cfg) < func.gcm.loopDepthOf(best)));
                }

                pub fn format(self: *const CfgNode, writer: *std.Io.Writer) !void {
                    try self.base.format(writer);
                }

                pub fn scheduleBlockAndRestoreBlockIds(bbc: *CfgNode) void {
                    // we do it here because some loads are scheduled already and removing them in this loop messes up the
                    // cheduling in other blocks, we need to hack this becaus there are no anty deps on loads yet, since this
                    // runs before gcm
                    //

                    const bb = &bbc.base;

                    // carefull, the scheduleBlock messes up the node.schedule
                    //
                    var buf: [2]*Node = undefined;
                    var scheds: [2]u16 = undefined;
                    var len: usize = 0;
                    for (bb.outputs()) |use| {
                        if (use.get().isCfg()) {
                            buf[len] = use.get();
                            scheds[len] = use.get().schedule;
                            len += 1;
                        }
                    }

                    if (bb.isBasicBlockStart()) {
                        scheduleBlock(bb.asCfg().?);
                    }

                    if (!(bb.kind == .If or len == 1)) {
                        unreachable;
                    }

                    for (buf[0..len], scheds[0..len]) |n, s| n.schedule = s;
                }

                pub fn scheduleBlock(bb: *CfgNode) void {
                    var tmp = utils.Arena.scrath(null);
                    defer tmp.deinit();

                    // init meta
                    const extr: []u8 = tmp.arena.alloc(u8, bb.base.outputs().len);
                    for (bb.base.outputs(), extr, 0..) |in, *e, i| {
                        const instr = in.get();
                        instr.schedule = @intCast(i);

                        e.* = 0;

                        if (instr.kind != .Phi) {
                            for (instr.inputs()[1..]) |d| if (d) |def| {
                                // if instr == df, this is a infinite loop
                                if (def.tryCfg0() == bb or instr == def) {
                                    e.* += 1;
                                }
                            };
                        }
                    }

                    const outs = bb.base.outputs();
                    var ready: usize = 0;
                    for (outs) |*o| {
                        if (extr[o.get().schedule] == 0) {
                            std.mem.swap(Node.Out, &outs[ready], o);
                            ready += 1;
                        }
                    }

                    var scheduled: usize = 0;
                    if (ready != scheduled) while (scheduled < outs.len - 1) {
                        if (ready == scheduled) utils.panic(
                            "{} {} {f} {any}",
                            .{ scheduled, outs.len, bb, outs[scheduled..] },
                        );

                        const n = outs[scheduled].get();
                        for (n.outputs()) |def| if (bb == def.get().tryCfg0() and
                            def.get().kind != .Phi)
                        {
                            extr[def.get().schedule] -= 1;
                        };

                        scheduled += 1;

                        for (outs[ready..]) |*o| {
                            if (extr[o.get().schedule] == 0) {
                                std.debug.assert(o.get().kind != .Phi);
                                std.mem.swap(Node.Out, &outs[ready], o);
                                ready += 1;
                            }
                        }
                    };
                }
            };
        }

        fn callCheck(comptime name: []const u8, value: anytype) bool {
            return (comptime optApi(name, fn (@TypeOf(value)) bool)) and @field(Backend, name)(value);
        }

        pub const Node = extern struct {
            kind: Kind,
            id: u16,
            schedule: u16 = std.math.maxInt(u16),
            data_type: mod.DataType = .top,

            input_ordered_len: u16,
            input_len: u16,
            output_len: u16 = 0,
            output_cap: u16 = 0,

            input_base: [*]?*Node,
            output_base: [*]Out,
            sloc: Sloc = .none,

            edata: void = {},

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
                    return .{ .inner = .{ .node = @intCast(@intFromPtr(node)), .pos = @intCast(ps) } };
                }

                pub fn get(self: Out) *Node {
                    return @as(*Node, @ptrFromInt(self.inner.node));
                }

                pub fn pos(self: Out) usize {
                    return @intCast(self.inner.pos);
                }

                pub fn format(self: *const Out, writer: *std.Io.Writer) !void {
                    try writer.print("{}:{any}", .{ self.pos(), self.get() });
                }
            };

            pub fn isDead(self: *Node) bool {
                return self.kind == .Dead;
            }

            pub fn preservesIdentityPhys(self: *Node) bool {
                std.debug.assert(self.kind == .Region or self.kind == .Loop);
                return self.kind == .Region and self.extra(.Region).preserve_identity_phys;
            }

            pub fn useBlock(self: *Node, use: *Node, pos: usize, scheds: []const ?*CfgNode) *CfgNode {
                _ = self;
                if (use.kind == .Phi) {
                    std.debug.assert(use.inputs()[0].?.kind == .Region or use.inputs()[0].?.kind == .Loop);
                    return use.inputs()[0].?.inputs()[pos - 1].?.asCfg().?;
                }

                if (scheds.len == 0) {
                    return use.cfg0();
                }

                return scheds[use.id].?;
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
                        if (@hasDecl(Cursor, property)) break @field(Cursor, property);
                        if (@typeInfo(Cursor) != .@"struct" or !@hasField(Cursor, "base")) break 0;
                        Cursor = @TypeOf(@as(Cursor, undefined).base);
                    } else unreachable) + 1;
                    std.debug.assert(off <= std.math.powi(usize, 2, sub_elem_width) catch unreachable);
                    const slot_idx = i / (per_dep_elem);
                    const shift = (i % (per_dep_elem)) * sub_elem_width;

                    offs[slot_idx] |= off << shift;
                }

                break :b offs;
            };

            pub fn dataDepOffset(self: *Node) usize {
                const kind_idx = @intFromEnum(self.kind);
                return dep_offset[kind_idx / per_dep_elem] >>
                    @intCast((kind_idx % per_dep_elem) * sub_elem_width) & ((@as(u16, 1) << sub_elem_width) - 1);
            }

            // TODO: this is a hack, its here because otherwise everithing gets pulled out of
            // the loop and cloggs the register allocator
            pub fn isCheap(self: *Node) bool {
                return self.kind == .StackArgOffset;
            }

            pub fn dataDeps(self: *Node) []*Node {
                if ((self.kind == .Phi and !self.isDataPhi()) or self.kind == .MemJoin) return &.{};
                const start = self.dataDepOffset();
                const deps = self.input_base[start..self.input_ordered_len];
                std.debug.assert(std.mem.indexOfScalar(?*Node, deps, null) == null);
                return @ptrCast(deps);
            }

            pub fn knownStore(self: *Node, root: *Node) ?*Node {
                if (self.isStore() and !self.isSub(MemCpy) and self.tryBase() == root) {
                    return self;
                }
                if (self.kind == .BinOp and self.outputs().len == 1 and
                    self.outputs()[0].get().isStore() and !self.outputs()[0].get().isSub(MemCpy) and
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
                    (self.outputs()[0].get().isStore() or self.outputs()[0].get().isLoad()) and
                    (self.outputs()[0].get().base()) == (self))
                {
                    return .{ self.outputs()[0].get(), self.inputs()[2].?.extra(.CInt).value };
                }
                return null;
            }

            pub fn knownOffset(self: *Node) struct { *Node, i64 } {
                if (self.kind == .BinOp and self.inputs()[2].?.kind == .CInt) {
                    const op = self.extra(.BinOp).op;
                    if (op != .iadd and op != .isub) return .{ self, 0 };
                    const magnitude = self.inputs()[2].?.extra(.CInt).value;
                    return .{ self.inputs()[1].?, if (op == .iadd) magnitude else -magnitude };
                }
                if (@hasDecl(Backend, "knownOffset")) return Backend.knownOffset(self);
                return .{ self, 0 };
            }

            pub fn regMask(self: *Node, func: *Self, idx: usize, tmp: *utils.Arena) if (@hasDecl(Backend, "Set"))
                Backend.Set
            else
                std.DynamicBitSetUnmanaged {
                return if (comptime optApi("regMask", @TypeOf(regMask))) Backend.regMask(self, func, idx, tmp) else unreachable;
            }

            pub fn clobbers(self: *Node) u64 {
                return if (@hasDecl(Backend, "clobbers")) Backend.clobbers(self) else 0;
            }

            pub fn inPlaceSlot(self: *Node) ?usize {
                return if (comptime optApi("inPlaceSlot", @TypeOf(inPlaceSlot))) Backend.inPlaceSlot(self) else null;
            }

            pub fn isClone(self: *Node) bool {
                return (comptime bakeFlagBitset("is_clone")).contains(self.kind);
            }

            pub fn isReadonly(self: *Node) bool {
                return (comptime bakeFlagBitset("is_readonly")).contains(self.kind);
            }

            pub fn alreadyBefore(self: *Node, use: *Node, block: *CfgNode) bool {
                std.debug.assert(self.isClone());
                if (self.cfg0() != block) return false;
                const search_from = if (use.kind == .Phi) block.base.outputs().len - 1 else block.base.posOfOutput(0, use);
                var iter = std.mem.reverseIterator(block.base.outputs()[0..search_from]);
                while (iter.next()) |o| {
                    const out: *Node = o.get();
                    if (out == self) return true;
                    if (!out.isClone() and !out.isReadonly()) break;
                }
                return false;
            }

            pub fn noAlias(self: *Node, other: *Node) bool {
                const lsize, const loff, const lbase = self.getOffsetSizeBase() orelse return false;
                const rsize, const roff, const rbase = other.getOffsetSizeBase() orelse return false;

                if (lbase.ptrsNoAlias(rbase)) return true;
                if (lbase != rbase) return false;

                return (loff + lsize <= roff) or (roff + rsize <= loff);
            }

            pub fn fullAlias(self: *Node, other: *Node) bool {
                const lsize, const loff, const lbase = self.getOffsetSizeBase() orelse return false;
                const rsize, const roff, const rbase = other.getOffsetSizeBase() orelse return false;

                if (lbase.ptrsNoAlias(rbase)) return false;
                if (lbase != rbase) return true;

                return (loff <= roff) and (roff + rsize <= loff + lsize);
            }

            pub fn getOffsetSizeBase(self: *Node) ?struct { i64, i64, *Node } {
                const siz: i64 = if (self.kind == .MemCpy and
                    if (self.inputs()[4].?.kind != .CInt) return null else true)
                    self.inputs()[4].?.extra(.CInt).value
                else
                    @bitCast(self.data_type.size());
                const bas, var off = knownOffset(self.base());
                off += self.getStaticOffset();
                return .{ siz, off, bas };
            }

            pub fn ptrsNoAlias(self: *Node, other: *Node) bool {
                return ((self.kind == .Local or self.kind == .StructArg or self.kind == .Arg) and
                    (other.kind == .Local or other.kind == .StructArg or other.kind == .Arg)) and
                    (self != other and (self.kind != .Arg or other.kind != .Arg));
            }

            pub fn isStack(self: *Node) bool {
                return self.kind == .Local or self.kind == .StructArg or self.kind == .LocalAlloc;
            }

            pub fn anyextra(self: *const Node) []const u64 {
                return @as([*]const u64, @ptrCast(&self.edata))[0 .. size_map[@intFromEnum(self.kind)] / 8];
            }

            pub fn format(self: *const Node, writer: *std.Io.Writer) !void {
                const colors: std.io.tty.Config = if (!utils.freestanding and
                    writer.vtable.drain == std.fs.File.stderr().writer(&.{}).interface.vtable.drain)
                    std.io.tty.detectConfig(std.fs.File.stderr())
                else
                    .escape_codes;
                self.fmt(null, writer, colors);
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

            fn logExtra(writ: anytype, ex: anytype, comptime fir: bool) !void {
                switch (@typeInfo(@TypeOf(ex.*))) {
                    .@"struct" => |s| {
                        comptime var fields = std.mem.reverseIterator(s.fields);
                        comptime var first = fir;
                        inline while (fields.next()) |f| {
                            if (comptime std.mem.eql(u8, f.name, "antidep") or
                                std.mem.eql(u8, f.name, "loop") or
                                std.mem.eql(u8, f.name, "par_base") or
                                std.mem.eql(u8, f.name, "ret_base") or
                                !isVisibel(f.type))
                            {
                                continue;
                            }

                            comptime var prefix: []const u8 = "";
                            if (!first) prefix = ", ";
                            first = false;

                            const is_base = comptime std.mem.eql(u8, f.name, "base");
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
                self: *const Node,
                scheduled: ?u16,
                writer: anytype,
                colors: std.io.tty.Config,
            ) void {
                logNid(writer, self.id, colors);
                const name = @tagName(self.kind);

                writer.print(" = {s}:{s}", .{ name, @tagName(self.data_type) }) catch unreachable;

                var add_colon_space = false;

                switch (self.kind) {
                    inline else => |t| {
                        const ext = self.extraConst(t);
                        if (@TypeOf(ext.*) != void) {
                            if (comptime isVisibel(@TypeOf(ext.*))) {
                                writer.writeAll(": ") catch unreachable;
                                add_colon_space = true;
                                logExtra(writer, ext, true) catch unreachable;
                            }
                        }
                    },
                }

                for (self.input_base[0..self.input_len][@min(
                    @intFromBool(scheduled != null and
                        (!self.isCfg() or !self.isBasicBlockStart())),
                    self.input_base[0..self.input_len].len,
                )..]) |oo| if (oo) |o| {
                    if (!add_colon_space) {
                        writer.writeAll(": ") catch unreachable;
                        add_colon_space = true;
                    } else {
                        writer.writeAll(", ") catch unreachable;
                    }
                    logNid(writer, o.id, colors);
                };

                if (scheduled == null) {
                    writer.writeAll(" [") catch unreachable;
                    for (self.output_base[0..self.output_len]) |o| {
                        writer.writeAll(", ") catch unreachable;
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
                std.debug.assert(on_loop.kind == .Loop or on_loop.kind == .Region);
                return self.kind == .Phi and self.inputs()[0] == on_loop and
                    (self.inputs()[2] == null or self.inputs()[1] == null);
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
                return forceSubclass((self.inputs()[0].?), Cfg);
            }

            pub fn hasUseFor(self: *Node, idx: usize, def: *Node) bool {
                if (self.kind == .Call and def.kind == .StackArgOffset) return false;
                return self.dataDepOffset() <= idx and idx < self.input_ordered_len;
            }

            pub fn removeUse(self: *Node, idx: usize, use: *Node) void {
                const outs = self.outputs();
                const index = std.mem.indexOfScalar(Out, outs, .init(use, idx, self)) orelse {
                    utils.panic("removeUse: not found {f} {any} {f}", .{ use, self.outputs(), self });
                };

                outs[index] = outs[outs.len - 1];
                outs[outs.len - 1] = undefined;
                self.output_len -= 1;
            }

            pub fn outputs(self: *Node) []Out {
                return self.output_base[0..self.output_len];
            }

            pub fn posOfOutput(self: *Node, index: usize, output: *Node) usize {
                return std.mem.indexOfScalar(Out, self.outputs(), .init(output, index, self)).?;
            }

            pub fn extraConst(self: *const Node, comptime kind: Kind) *const ClassFor(kind) {
                std.debug.assert(self.kind == kind);
                const ptr: *const LayoutFor(kind) = @ptrCast(@alignCast(self));
                return &ptr.ext;
            }

            pub fn extra(self: *Node, comptime kind: Kind) *ClassFor(kind) {
                std.debug.assert(self.kind == kind);
                const ptr: *LayoutFor(kind) = @ptrCast(@alignCast(self));
                return &ptr.ext;
            }

            pub fn extra2(self: *Node) utils.AsRef(Union) {
                const Repr = extern struct { data: *anyopaque, kind: Kind };

                const ptr: *extern struct { base: Node, ext: u8 } = @ptrCast(@alignCast(self));
                return @as(*const utils.AsRef(Union), @ptrCast(&Repr{ .kind = self.kind, .data = &ptr.ext })).*;
            }

            pub fn isDef(self: *Node) bool {
                return !self.isStore() and
                    !self.isCfg() and
                    (self.kind != .Phi or self.isDataPhi()) and
                    self.kind != .LocalAlloc and
                    self.kind != .MemJoin and
                    self.kind != .Mem;
            }

            pub fn kills(self: *Node) bool {
                return self.clobbers() != 0;
            }

            pub fn getStaticOffset(self: *Node) i64 {
                std.debug.assert(self.isMemOp());
                return if (@hasDecl(Backend, "getStaticOffset")) Backend.getStaticOffset(self) else 0;
            }

            pub fn isSubbclass(Full: type, Sub: type) bool {
                var Cursor = Full;
                while (true) {
                    if (Cursor == Sub) return true;
                    if (@typeInfo(Cursor) != .@"struct" or !@hasField(Cursor, "base")) return false;
                    Cursor = @TypeOf(@as(Cursor, undefined).base);
                }
            }

            pub fn bakeSubclassBitset(comptime Sub: type) std.EnumSet(Kind) {
                var bitset = std.EnumSet(Kind).initEmpty();
                for (all_classes, 0..) |c, i| {
                    if (isSubbclass(c.type, Sub)) bitset.insert(@enumFromInt(i));
                }
                return bitset;
            }

            pub fn hasFlag(comptime Full: type, comptime flag: []const u8) bool {
                var Cursor = Full;
                while (true) {
                    if (@hasDecl(Cursor, flag)) return @field(Cursor, flag);
                    if (@typeInfo(Cursor) != .@"struct" or !@hasField(Cursor, "base")) return false;
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

            pub fn forceSubclass(self: *Node, comptime Sub: type) *LayoutOf(Sub) {
                std.debug.assert(self.isSub(Sub));
                return @ptrCast(self);
            }

            pub fn isInterned(kind: Kind, inpts: []const ?*Node) bool {
                return switch (kind) {
                    .CInt, .BinOp, .Load, .UnOp, .GlobalAddr, .FramePointer => true,
                    .Phi => inpts[2] != null,
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
                return (comptime bakeFlagBitset("is_floating")).contains(self.kind);
            }

            pub fn isPinned(self: *const Node) bool {
                return (comptime bakeFlagBitset("is_pinned")).contains(self.kind);
            }

            pub inline fn isMemOp(self: *const Node) bool {
                return self.isSub(MemOp);
            }

            pub fn isDataPhi(self: *Node) bool {
                return self.kind == .Phi and self.data_type != .top;
            }

            pub inline fn isBasicBlockStart(self: *const Node) bool {
                return (comptime bakeFlagBitset("is_basic_block_start")).contains(self.kind);
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

            pub fn hash(kind: Kind, dt: DataType, inpts: []const ?*Node, extr: []const u64) u64 {
                var hasher = std.hash.Wyhash.init(0);
                hasher.update(std.mem.asBytes(&kind));
                hasher.update(std.mem.asBytes(&dt));
                hasher.update(@ptrCast(inpts));
                hasher.update(@ptrCast(extr));
                return hasher.final();
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
            self.next_id = 0;
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

            pub fn hash(_: anytype, k: InternedNode) u64 {
                return k.hash;
            }

            pub fn eql(s: @This(), a: InternedNode, b: InternedNode) bool {
                if (a.hash != b.hash) return false;
                return Node.cmp(
                    s.kind,
                    b.node.kind,
                    s.dt,
                    b.node.data_type,
                    s.inputs,
                    b.node.inputs(),
                    s.extra,
                    b.node.anyextra(),
                );
            }
        };

        const InsertMap = InternMap(Inserter);

        pub fn addSplit(self: *Self, block: *CfgNode, def: *Node, dgb: builtin.MachSplit.Dbg) *Node {
            return self.addNode(.MachSplit, def.sloc, def.data_type, &.{ &block.base, null }, .{ .dbg = dgb });
        }

        pub fn splitBefore(self: *Self, use: *Node, idx: usize, def: *Node, skip: bool, dbg: builtin.MachSplit.Dbg) void {
            std.debug.assert(idx > 0);
            const block = if (use.kind == .Phi)
                use.cfg0().base.inputs()[idx - 1].?.inputs()[0].?.asCfg().?
            else
                use.cfg0();

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();
            const mask = use.regMask(self, idx, tmp.arena);

            if (def.isReadonly() and use.kind != .Phi and
                (if (use.inPlaceSlot()) |s| s + use.dataDepOffset() != idx else true) and
                Backend.setIntersects(mask, def.regMask(self, 0, tmp.arena)))
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
            } else def, dbg);

            self.setInputIgnoreIntern(use, idx, ins);
            if (ins.kind == .MachSplit) self.setInputIgnoreIntern(ins, 1, def);
            const oidx = if (use.kind == .Phi) block.base.outputs().len - 2 else block.base.posOfOutput(0, use);
            const to_rotate = block.base.outputs()[oidx..];
            std.mem.rotate(Node.Out, to_rotate, to_rotate.len - 1);
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
            new_node.id = self.next_id;
            self.next_id += 1;

            new_node.inputs()[0] = &block.base;
            self.addUse(&block.base, 0, new_node);

            return new_node;
        }

        pub fn internNode(self: *Self, kind: Kind, dt: DataType, inputs: []const ?*Node, extra: []const u64) InsertMap.GetOrPutResult {
            const map: *InsertMap = @ptrCast(&self.interner);

            return map.getOrPutContext(self.arena.allocator(), .{
                .node = undefined,
                .hash = Node.hash(kind, dt, inputs, extra),
            }, Inserter{ .kind = kind, .inputs = inputs, .dt = dt, .extra = extra }) catch unreachable;
        }

        const Uninserter = struct {
            pub fn hash(_: anytype, k: InternedNode) u64 {
                return k.hash;
            }

            pub fn eql(_: anytype, a: InternedNode, b: InternedNode) bool {
                return a.node == b.node;
            }
        };

        pub fn uninternNode(self: *Self, node: *Node) void {
            if (Node.isInterned(node.kind, node.inputs())) {
                if (!self.interner.remove(.{
                    .node = node,
                    .hash = Node.hash(node.kind, node.data_type, node.inputs(), node.anyextra()),
                })) {
                    //    utils.panic("{}\n", .{node});
                }
            }
        }

        pub fn reinternNode(self: *Self, node: *Node) ?*Node {
            if (Node.isInterned(node.kind, node.inputs())) {
                const entry = self.internNode(node.kind, node.data_type, node.inputs(), node.anyextra());

                if (entry.found_existing) {
                    return entry.key_ptr.node;
                }

                entry.key_ptr.node = node;
            }

            return null;
        }

        pub fn connect(self: *Self, def: *Node, to: *Node) void {
            std.debug.assert(!Node.isInterned(to.kind, to.inputs()));
            const idx = self.addDep(to, def);
            self.addUse(def, idx, to);
        }

        pub fn loopDepth(self: *Self, node: *Node) u16 {
            self.gcm.loop_tree_built.assertLocked();
            const cfg = node.asCfg() orelse node.cfg0();
            const tree = &self.gcm.loop_tree[cfg.ext.loop];
            if (tree.depth != 0) return tree.depth;
            if (tree.par == null) {
                tree.par = tree.head.base.cfg0().base.cfg0().ext.loop;
            }
            tree.depth = self.loopDepth(&self.gcm.loop_tree[tree.par.?].head.base) + 1;
            return tree.depth;
        }

        pub fn addFieldOffset(self: *Self, sloc: Sloc, base: *Node, offset: i64) *Node {
            return if (offset != 0) if (base.kind == .BinOp and base.inputs()[2].?.kind == .CInt) b: {
                break :b self.addBinOp(sloc, .iadd, .i64, base.inputs()[1].?, self.addIntImm(
                    sloc,
                    .i64,
                    base.inputs()[2].?.extra(.CInt).value + offset,
                ));
            } else self.addBinOp(sloc, .iadd, .i64, base, self.addIntImm(sloc, .i64, offset)) else base;
        }

        pub fn addGlobalAddr(self: *Self, sloc: Sloc, arbitrary_global_id: u32) *Node {
            return self.addNode(.GlobalAddr, sloc, .i64, &.{null}, .{ .id = arbitrary_global_id });
        }

        pub fn addFuncAddr(self: *Self, sloc: Sloc, func_id: u32) *Node {
            return self.addNode(.FuncAddr, sloc, .i64, &.{null}, .{ .id = func_id });
        }

        pub fn addCast(self: *Self, sloc: Sloc, to: DataType, value: *Node) *Node {
            return self.addNode(.UnOp, sloc, to, &.{ null, value }, .{ .op = .cast });
        }

        pub const OffsetDirection = enum(u8) {
            iadd = @intFromEnum(BinOp.iadd),
            isub = @intFromEnum(BinOp.isub),
        };

        pub fn addIndexOffset(self: *Self, sloc: Sloc, base: *Node, op: OffsetDirection, elem_size: u64, subscript: *Node) *Node {
            const offset = if (elem_size == 1)
                subscript
            else if (subscript.kind == .CInt)
                self.addIntImm(sloc, .i64, subscript.extra(.CInt).value * @as(i64, @bitCast(elem_size)))
            else
                self.addBinOp(sloc, .imul, .i64, subscript, self.addIntImm(sloc, .i64, @bitCast(elem_size)));
            return self.addBinOp(sloc, @enumFromInt(@intFromEnum(op)), .i64, base, offset);
        }

        pub fn addUninit(self: *Self, sloc: Sloc, ty: DataType) *Node {
            return self.addIntImm(sloc, ty, @as(i64, @bitCast(@as(u64, 0xaaaaaaaaaaaaaaaa))) & ty.mask().?);
        }

        pub fn addIntImm(self: *Self, sloc: Sloc, ty: DataType, value: i64) *Node {
            std.debug.assert(ty != .bot);
            return self.addNode(.CInt, sloc, ty, &.{null}, .{ .value = value });
        }

        pub fn addBinOp(self: *Self, sloc: Sloc, op: BinOp, ty: DataType, lhs: *Node, rhs: *Node) *Node {
            if (lhs.kind == .CInt and rhs.kind == .CInt) {
                return self.addIntImm(sloc, ty, op.eval(ty, lhs.extra(.CInt).value, rhs.extra(.CInt).value));
            }

            if ((op == .iadd or op == .isub) and rhs.kind == .CInt and rhs.extra(.CInt).value == 0) {
                return lhs;
            }
            return self.addNode(.BinOp, sloc, ty, &.{ null, lhs, rhs }, .{ .op = op });
        }

        pub fn addUnOp(self: *Self, sloc: Sloc, op: UnOp, ty: DataType, oper: *Node) *Node {
            if (!(op != .uext or ty.size() > oper.data_type.size())) utils.panic("{} {f}", .{ ty, oper });
            if (!(op != .sext or ty.size() > oper.data_type.size())) utils.panic("{} {f}", .{ ty, oper });
            if (oper.kind == .CInt and ty.isInt()) {
                return self.addIntImm(sloc, ty, op.eval(oper.data_type, ty, oper.extra(.CInt).value));
            }
            return self.addNode(.UnOp, sloc, ty, &.{ null, oper }, .{ .op = op });
        }

        pub fn addMemJoin(self: *Self, to_join: []const *Node) *Node {
            errdefer unreachable;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            if (to_join.len == 1) return to_join[0];

            var loads = std.ArrayListUnmanaged(*Node){};
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

            const inps = try std.mem.concat(tmp.arena.allocator(), ?*Node, &.{ &.{null}, to_join });
            return self.addNode(.MemJoin, .none, .top, inps, .{});
        }

        pub fn addTrap(self: *Self, sloc: Sloc, ctrl: *Node, code: u64) void {
            self.addTrapLow(sloc, ctrl, code, setInputNoIntern);
        }

        pub fn addTrapIgnoreIntern(self: *Self, sloc: Sloc, ctrl: *Node, code: u64) void {
            self.addTrapLow(sloc, ctrl, code, setInputIgnoreIntern);
        }

        pub fn addTrapLow(self: *Self, sloc: Sloc, ctrl: *Node, code: u64, comptime setter: anytype) void {
            if (self.end.inputs()[2] == null) {
                setter(self, self.end, 2, self.addNode(.TrapRegion, sloc, .top, &.{}, .{}));
            }

            const region = self.end.inputs()[2].?;
            const trap = self.addNode(.Trap, sloc, .top, &.{ctrl}, .{ .code = code });

            const idx = self.addDep(region, trap);
            self.addUse(trap, idx, region);
        }

        pub fn addNode(self: *Self, comptime kind: Kind, sloc: Sloc, ty: DataType, inputs: []const ?*Node, extra: ClassFor(kind)) *Node {
            var typ = ty;
            if (kind == .Phi) {
                if (inputs[1].?.isStore() or inputs[1].?.kind == .Mem) typ = .top;
                if (inputs[2]) |inp| if (inp.isStore() or inp.kind == .Mem) {
                    typ = .top;
                };
            }
            var bytes: [Node.size_map[@intFromEnum(kind)] / 8]u64 = @splat(0);
            @as(*ClassFor(kind), @ptrCast(&bytes)).* = extra;
            const node = self.addNodeUntyped(kind, typ, inputs, &bytes);
            node.sloc = sloc;
            return node;
        }

        pub fn addNodeUntyped(self: *Self, kind: Kind, dt: DataType, inputs: []const ?*Node, extra: []const u64) *Node {
            if (Node.isInterned(kind, inputs)) {
                const entry = self.internNode(kind, dt, inputs, extra);
                if (!entry.found_existing) {
                    entry.key_ptr.node = self.addNodeNoIntern(kind, dt, inputs, extra);
                }

                const node = entry.key_ptr.node;

                return node;
            } else {
                return self.addNodeNoIntern(kind, dt, inputs, extra);
            }
        }

        pub fn addNodeNoIntern(self: *Self, kind: Kind, ty: DataType, inputs: []const ?*Node, extra: []const u64) *Node {
            errdefer unreachable;
            const size = @sizeOf(Node) + extra.len * @sizeOf(u64);
            const node: *Node = @ptrCast(@alignCast(self.arena.allocator().rawAlloc(size, .@"8", @returnAddress()).?));
            const owned_inputs = try self.arena.allocator().dupe(?*Node, inputs);

            node.* = .{
                .input_base = owned_inputs.ptr,
                .input_len = @intCast(owned_inputs.len),
                .input_ordered_len = @intCast(owned_inputs.len),
                .output_base = @ptrFromInt(@alignOf(Node.Out)),
                .kind = kind,
                .id = self.next_id,
                .data_type = ty,
            };

            self.next_id += 1;

            @memcpy(@as([*]u64, @ptrCast(&node.edata)), extra);

            for (node.ordInps(), 0..) |on, i| if (on) |def| {
                self.addUse(def, i, node);
            };

            return node;
        }

        pub fn isDead(node: ?*Node) bool {
            return node == null or node.?.data_type == .bot;
        }

        pub fn kill(func: *Self, self: *Node) void {
            if (self.output_len != 0) utils.panic("{any} {f}\n", .{ self.outputs(), self });
            std.debug.assert(self.output_len == 0);
            for (self.inputs(), 0..) |oi, j| if (oi) |i| {
                i.removeUse(j, self);
            };

            func.waste += self.input_len * @sizeOf(?*Node);
            func.waste += self.size();
            func.waste += self.output_cap * @sizeOf(Node.Out);
            self.* = undefined;
            self.kind = .Dead;
        }

        pub fn subsumeNoKillIgnoreIntern(self: *Self, this: *Node, target: *Node) void {
            self.ensureOutputCapacity(this, target.outputs().len);

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            for (tmp.arena.dupe(Node.Out, target.outputs())) |use| {
                if (use.get().isDead()) continue;
                if (use.get() == target) {
                    target.removeUse(use.pos(), target);
                    target.inputs()[use.pos()] = null;
                } else {
                    _ = self.setInputIgnoreIntern(use.get(), use.pos(), this);
                }
            }
        }

        pub fn subsumeNoKill(self: *Self, this: *Node, target: *Node) void {
            if (this == target) {
                utils.panic("{f} {f}\n", .{ this, target });
            }
            errdefer unreachable;

            self.ensureOutputCapacity(this, target.outputs().len);

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            for (tmp.arena.dupe(Node.Out, target.outputs())) |use| {
                if (use.get().isDead()) continue;

                if (use.get() == target) {
                    target.removeUse(use.pos(), target);
                    target.inputs()[use.pos()] = null;
                } else {
                    _ = self.setInput(use.get(), use.pos(), this);
                }
            }
        }

        pub fn subsumeIgnoreIntern(self: *Self, this: *Node, target: *Node) void {
            if (this.sloc == Sloc.none) this.sloc = target.sloc;
            self.subsumeNoKillIgnoreIntern(this, target);
            self.kill(target);
        }

        pub fn subsume(self: *Self, this: *Node, target: *Node) void {
            if (this.sloc == Sloc.none) this.sloc = target.sloc;
            self.uninternNode(target);
            self.subsumeNoKill(this, target);
            self.kill(target);
        }

        pub fn setInputNoIntern(self: *Self, use: *Node, idx: usize, def: ?*Node) void {
            if (self.setInput(use, idx, def)) |new| {
                utils.panic("setInputNoIntern: {f}", .{new});
            }
        }

        pub fn setInputIgnoreIntern(self: *Self, use: *Node, idx: usize, def: *Node) void {
            self.stopped_interning.assertLocked();
            if (use.inputs()[idx] == def) return;
            if (use.inputs()[idx]) |n| n.removeUse(idx, use);
            use.inputs()[idx] = def;
            self.addUse(def, idx, use);
        }

        pub fn setInput(self: *Self, use: *Node, idx: usize, def: ?*Node) ?*Node {
            self.stopped_interning.assertUnlocked();

            if (use.inputs()[idx] == def) return null;
            if (use.inputs()[idx]) |n| {
                n.removeUse(idx, use);
            }

            self.uninternNode(use);
            use.inputs()[idx] = def;
            if (def) |d| {
                _ = self.addUse(d, idx, use);
            }
            if (self.reinternNode(use)) |nuse| {
                self.subsumeNoKill(nuse, use);
                self.kill(use);
                return nuse;
            }
            return null;
        }

        pub fn addDep(self: *Self, use: *Node, def: *Node) usize {
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

        pub fn ensureOutputCapacity(self: *Self, def: *Node, at_least: usize) void {
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

            const Ctx = if (@typeInfo(@TypeOf(ctx)) == .pointer) @TypeOf(ctx.*) else @TypeOf(ctx);

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
                if ((!@hasDecl(Ctx, "filter") or ctx.filter(n)) and !visited.isSet(n.id)) {
                    visited.set(n.id);
                    try stack.append(gpa, .{ n, n.outputs() });
                }
            }
        }

        pub fn iterPeeps(
            self: *Self,
            ctx: anytype,
            strategy: fn (@TypeOf(ctx), *Self, *Node, *WorkList) ?*Node,
        ) void {
            self.gcm.cfg_built.assertUnlocked();

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var worklist = WorkList.init(tmp.arena.allocator(), self.next_id * 2) catch unreachable;
            worklist.collectAll(self);

            while (worklist.pop()) |t| {
                if (t.isDead()) continue;

                if (t.outputs().len == 0 and t != self.end) {
                    for (t.inputs()) |ii| if (ii) |ia| worklist.add(ia);
                    self.uninternNode(t);
                    self.kill(t);
                    continue;
                }

                if (strategy(ctx, self, t, &worklist)) |nt| {
                    for (t.inputs()) |ii| if (ii) |ia| worklist.add(ia);
                    for (t.outputs()) |o| worklist.add(o.get());
                    self.subsume(nt, t);
                    continue;
                }
            }
        }

        pub fn collectDfs(
            self: *Self,
            arena: std.mem.Allocator,
            visited: *std.DynamicBitSetUnmanaged,
        ) []*CfgNode {
            var postorder = std.ArrayList(*CfgNode).empty;
            collectPostorder3(self, self.start, arena, &postorder, visited, true);
            return postorder.items;
        }

        pub fn collectPostorder3(
            self: *Self,
            node: *Node,
            arena: std.mem.Allocator,
            pos: *std.ArrayList(*CfgNode),
            visited: *std.DynamicBitSetUnmanaged,
            comptime only_basic: bool,
        ) void {
            if (visited.isSet(node.id)) {
                return;
            }
            visited.set(node.id);
            pos.append(arena, node.asCfg().?) catch unreachable;
            for (node.outputs()) |o| if (o.get().isCfg()) collectPostorder3(self, o.get(), arena, pos, visited, only_basic);
        }

        pub fn compact(self: *Self) void {
            if (self.arena.queryCapacity() > self.waste * 2) return;

            const Inln = inliner.Mixin(Backend);

            const prev_arena = self.arena;
            defer prev_arena.deinit();
            self.arena = .init(self.arena.child_allocator);
            self.waste = 0;
            self.interner = undefined;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const cloned = Inln.cloneNodes(self.start, self.end, self.next_id, &self.arena, 0, tmp.arena);

            self.start = cloned.new_node_table[self.start.id];
            self.end = cloned.new_node_table[self.end.id];
            self.next_id = @intCast(cloned.new_node_table.len);
            self.signature = self.signature.dupe(self.arena.allocator());
        }

        pub fn idealizeDead(_: anytype, self: *Self, node: *Node, worklist: *WorkList) ?*Node {
            const inps = node.inputs();

            var is_dead = node.kind == .Region and isDead(inps[0]) and isDead(inps[1]);
            is_dead = is_dead or (node.kind != .Start and node.kind != .Region and
                node.kind != .TrapRegion and node.isCfg() and isDead(inps[0]));

            if (is_dead and node.kind == .Return and inps[0] != null) {
                worklist.add(inps[0].?);
                worklist.add(inps[1].?);
                self.setInputNoIntern(node, 0, null);
                self.setInputNoIntern(node, 1, null);
                for (3..node.inputs().len) |i| {
                    if (inps[i] == null) continue;
                    worklist.add(inps[i].?);
                    self.setInputNoIntern(node, i, null);
                }
                return null;
            }

            if (node.kind == .TrapRegion) {
                is_dead = true;
                for (node.inputs(), 0..) |*inp, i| {
                    if (inp.* != null and isDead(inp.*)) {
                        inp.*.?.removeUse(i, node);
                        worklist.add(inp.*.?);
                        inp.* = null;
                    }
                    is_dead = is_dead and isDead(inp.*);
                }

                var retain: usize = 0;
                for (node.inputs(), 0..) |a, i| {
                    if (a != null) {
                        const idx = a.?.posOfOutput(i, node);
                        node.inputs()[retain] = a;
                        a.?.outputs()[idx] = .init(node, retain, a);
                        retain += 1;
                    }
                }
                node.input_len = @intCast(retain);
                node.input_ordered_len = @intCast(retain);

                if (is_dead) {
                    std.debug.assert(for (node.inputs()) |i| {
                        if (i != null) break false;
                    } else true);

                    self.setInputNoIntern(self.end, 2, null);

                    worklist.add(node);
                }

                return null;
            }

            if (node.kind == .If and node.data_type != .bot and
                node.inputs()[1].?.kind != .CInt)
            {
                var cursor = node.cfg0();
                while (cursor.base.kind != .Entry) : (cursor = cursor.idom()) {
                    if (cursor.base.data_type == .bot) break;
                    if (cursor.base.kind != .Then and cursor.base.kind != .Else) continue;

                    const if_node = cursor.base.inputs()[0].?;
                    if (if_node.kind != .If) continue;

                    if (if_node.inputs()[1].? == node.inputs()[1].?) {
                        self.setInputNoIntern(node, 1, self.addIntImm(
                            node.sloc,
                            .i8,
                            @intFromBool(cursor.base.kind == .Then),
                        ));
                        for (node.outputs()) |o| worklist.add(o.get());
                        return null;
                    }
                }
            }

            if (is_dead and node.data_type != .bot) {
                node.data_type = .bot;
                for (node.outputs()) |o| worklist.add(o.get());
                return null;
            }

            if (node.kind == .Region) eliminate_branch: {
                std.debug.assert(node.inputs().len == 2);
                const idx = for (node.inputs(), 0..) |in, i| {
                    if (isDead(in)) break i;
                } else break :eliminate_branch;

                var iter = std.mem.reverseIterator(node.outputs());
                while (iter.next()) |ot| if (ot.get().kind == .Phi) {
                    const o = ot.get();
                    for (o.outputs()) |oo| worklist.add(oo.get());
                    worklist.add(o.inputs()[idx + 1].?);
                    self.subsume(o.inputs()[(1 - idx) + 1].?, o);
                };

                return node.inputs()[1 - idx].?;
            }

            if (node.kind == .Region) eliminate_if: {
                for (node.outputs()) |o| {
                    if (!o.get().isCfg()) break :eliminate_if;
                }

                if (node.inputs()[0].?.inputs()[0] == node.inputs()[1].?.inputs()[0]) {
                    return node.inputs()[0].?.inputs()[0].?.inputs()[0];
                }
            }

            if (node.kind == .Loop) remove: {
                if (!isDead(node.inputs()[1])) break :remove;

                var iter = std.mem.reverseIterator(node.outputs());
                while (iter.next()) |ot| if (ot.get().kind == .Phi) {
                    const o = ot.get();
                    for (o.outputs()) |oo| worklist.add(oo.get());
                    worklist.add(o.inputs()[2].?);
                    self.subsume(o.inputs()[1].?, o);
                };

                return node.inputs()[0].?;
            }

            if (node.kind == .Then and node.inputs()[0].?.kind == .If) {
                const if_node = node.inputs()[0].?;
                const cond = if_node.inputs()[1].?;
                if (cond.kind == .CInt and cond.extra(.CInt).value != 0) {
                    if_node.data_type = .bot;
                    worklist.add(if_node.outputs()[1].get());
                    return if_node.inputs()[0].?;
                }
            }

            if (node.kind == .Else and node.inputs()[0].?.kind == .If) {
                const if_node = node.inputs()[0].?;
                const cond = if_node.inputs()[1].?;
                if (cond.kind == .CInt and cond.extra(.CInt).value == 0) {
                    if_node.data_type = .bot;
                    worklist.add(if_node.outputs()[0].get());
                    return if_node.inputs()[0].?;
                }
            }

            if (node.kind == .Store) {
                if (node.value().?.data_type.size() == 0) {
                    return node.mem();
                }
            }

            std.debug.assert(node.kind != .Load or node.data_type.size() != 0);

            if (node.kind == .Phi) {
                const l, const r = .{ inps[1].?, inps[2].? };

                if (l == r and !node.cfg0().base.preservesIdentityPhys()) {
                    return l;
                }

                if (r == node) {
                    return l;
                }
            }

            return null;
        }

        pub fn idealize(ctx: anytype, self: *Self, node: *Node, work: *WorkList) ?*Node {
            errdefer unreachable;

            if (node.data_type == .bot) return null;

            if (idealizeDead(ctx, self, node, work)) |w| return w;

            if (matcher.idealize(ctx, self, node, work)) |w| return w;

            var tmp = utils.Arena.scrathFromAlloc(work.allocator);
            defer tmp.deinit();

            const inps = node.inputs();

            if (node.kind == .Store) {
                if (node.outputs().len == 1) {
                    const succ = node.outputs()[0].get();
                    if (succ.kind == .Store and
                        succ.data_type == node.data_type and
                        succ.base() == node.base())
                    {
                        return node.mem();
                    }
                }

                const base, _ = node.base().knownOffset();

                if (base.kind == .Local) eliminate_stack: {
                    for (base.outputs()) |o| {
                        _ = o.get().knownStore(base) orelse {
                            break :eliminate_stack;
                        };
                    }

                    for (base.outputs()) |o| if (o.get().knownStore(base).? != node) {
                        work.add(o.get().knownStore(base).?);
                    };

                    return node.mem();
                }

                if (base.kind == .Local and node.outputs().len == 1 and node.outputs()[0].get().kind == .Return) {
                    return node.mem();
                }

                if (base.kind == .Local and node.tryCfg0() != null) {
                    const dinps = tmp.arena.dupe(?*Node, node.inputs());
                    dinps[0] = null;
                    const st = self.addNode(.Store, node.sloc, node.data_type, dinps, .{});
                    work.add(st);
                    return st;
                }
            }

            // pull loads up the memory chain with hope that they find a store
            // with the same addr and type to just use the value
            //
            if (node.kind == .Load) {
                var earlier = node.mem();
                const base, _ = node.base().knownOffset();

                if (base.kind == .Local and node.tryCfg0() != null) {
                    const dinps = tmp.arena.dupe(?*Node, node.inputs());
                    dinps[0] = null;
                    const st = self.addNode(.Load, node.sloc, node.data_type, dinps, .{});
                    work.add(st);
                    return st;
                }

                while ((earlier.kind == .Store and
                    (earlier.tryCfg0() == node.tryCfg0() or node.tryCfg0() == null) and
                    earlier.noAlias(node)))
                {
                    earlier = earlier.mem();
                }

                if (earlier.kind == .Store and
                    earlier.base() == node.base() and
                    earlier.data_type == node.data_type)
                {
                    return earlier.value();
                }

                if (false and earlier != node.mem()) {
                    return self.addNode(.Load, node.sloc, node.data_type, &.{ inps[0], earlier, inps[2] }, .{});
                }
            }

            // Is this a single memcpy to a local that is only loaded from
            // that is also the last in the memory thread?
            //
            if (node.kind == .MemCpy) memcpy: {
                const mem = inps[1].?;
                const dst = inps[2].?;
                const src = inps[3].?;

                if (dst == src) {
                    return mem;
                }

                // If store happens after us, it could be a swap so be pesimiztic
                //
                for (node.outputs()) |use| {
                    if (if (use.get().knownMemOp()) |op| !op[0].isLoad() else false) break :memcpy;
                }

                // We cause side effects if our dest is not .Local
                //
                if (dst.kind != .Local and (dst.kind != .BinOp or
                    dst.inputs()[1].?.kind != .Local)) break :memcpy;

                // NOTE: if the size of the memcpy does not match, we do not care
                // since reading uninitialized memory is undefined behavior

                const scanned = if (dst.kind == .BinOp) dst.inputs()[1].? else dst;
                for (scanned.outputs()) |use| {
                    if (if (use.get().knownMemOp()) |op| !op[0].isLoad() and use.get() != node else true) {
                        break :memcpy;
                    }
                }

                self.subsume(src, dst);
                return mem;
            }

            if (node.isLoad()) {
                const base, const offset = node.base().knownOffset();
                if (base.kind == .GlobalAddr) fold_const_read: {
                    const res = ctx.out.readFromSym(
                        base.extra(.GlobalAddr).id,
                        offset + node.getStaticOffset(),
                        node.data_type.size(),
                        false,
                    ) orelse break :fold_const_read;

                    switch (res) {
                        .value => |v| return self.addIntImm(node.sloc, node.data_type, v),
                        .global => |g| return self.addGlobalAddr(node.sloc, g),
                    }
                }
            }

            if (node.kind == .Call and node.data_type != .bot) {
                const force_inline = node.extra(.Call).signature.call_conv == .@"inline";
                if (ctx.out.getInlineFunc(Backend, node.extra(.Call).id, force_inline)) |inline_func| {
                    inline_func.inliner.inlineInto(self, node, work);
                    return null;
                }
            }

            return if (comptime optApi("idealize", IdealSig(@TypeOf(ctx))))
                Backend.idealize(ctx, self, node, work)
            else
                null;
        }

        fn IdealSig(C: type) type {
            return fn (C, *Self, *Node, *WorkList) ?*Node;
        }

        pub fn logNid(wr: anytype, nid: usize, cc: std.io.tty.Config) void {
            errdefer unreachable;

            try utils.setColor(cc, wr, @enumFromInt(1 + nid % 15));
            try wr.print("%{d}", .{nid});
            try utils.setColor(cc, wr, .reset);
        }

        pub fn collectPostorder(
            self: *Self,
            arena: std.mem.Allocator,
            visited: *std.DynamicBitSetUnmanaged,
        ) []*CfgNode {
            var postorder = std.ArrayList(*CfgNode).empty;

            collectPostorder2(self, self.start, arena, &postorder, visited, true);

            return postorder.items;
        }

        pub fn collectPostorderAll(self: *Self, arena: std.mem.Allocator, visited: *std.DynamicBitSetUnmanaged) []*CfgNode {
            var postorder = std.ArrayList(*CfgNode).init(arena);
            self.collectPostorder2(self.start, arena, &postorder, visited, false);
            return postorder.items;
        }

        pub fn collectPostorder2(
            self: *Self,
            node: *Node,
            arena: std.mem.Allocator,
            pos: *std.ArrayList(*CfgNode),
            visited: *std.DynamicBitSetUnmanaged,
            comptime only_basic: bool,
        ) void {
            switch (node.kind) {
                .TrapRegion => return,
                .Region => {
                    if (!visited.isSet(node.id)) {
                        visited.set(node.id);
                        if (node.inputs()[0].?.inputs()[0] != null and node.inputs()[1].?.inputs()[0] != null) {
                            return;
                        }
                    }
                },
                else => {
                    if (visited.isSet(node.id)) {
                        return;
                    }
                    visited.set(node.id);
                },
            }

            if (!only_basic or node.isBasicBlockStart()) pos.append(arena, node.asCfg().?) catch unreachable;
            if (node.isSwapped()) {
                var iter = std.mem.reverseIterator(node.outputs());
                while (iter.next()) |o| if (o.get().isCfg()) collectPostorder2(self, o.get(), arena, pos, visited, only_basic);
            } else {
                for (node.outputs()) |o| if (o.get().isCfg()) collectPostorder2(self, o.get(), arena, pos, visited, only_basic);
            }
        }

        pub fn fmtScheduled(self: *Self, writer: anytype, colors: std.io.tty.Config) void {
            errdefer unreachable;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var visited = try std.DynamicBitSetUnmanaged.initEmpty(tmp.arena.allocator(), self.next_id);

            self.start.fmt(self.gcm.block_count, writer, colors);
            if (self.start.outputs().len > 1 and self.start.outputs()[1].get().kind == .Mem) {
                for (self.start.outputs()[1].get().outputs()) |oo| if (oo.get().kind == .LocalAlloc) {
                    try writer.writeAll("\n  ");
                    oo.get().fmt(self.gcm.instr_count, writer, colors);
                };
            }
            try writer.writeAll("\n");
            for (collectPostorder(self, tmp.arena.allocator(), &visited)) |p| {
                p.base.fmt(self.gcm.block_count, writer, colors);

                try writer.writeAll("\n");
                for (p.base.outputs()) |o| {
                    try writer.writeAll("  ");
                    o.get().fmt(self.gcm.instr_count, writer, colors);
                    try writer.writeAll("\n");
                }
            }
        }

        pub fn fmtUnscheduled(self: *Self, writer: anytype, colors: std.io.tty.Config) void {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var worklist = Self.WorkList.init(tmp.arena.allocator(), self.next_id) catch unreachable;
            worklist.collectAll(self);

            for (worklist.items()) |p| {
                p.fmt(null, writer, colors);
                writer.writeAll("\n") catch unreachable;
            }
        }
    };
}
