const std = @import("std");
pub const utils = @import("../utils.zig");

fn tu(int: i64) u64 {
    return @bitCast(int);
}

fn tf(int: i64) f64 {
    return @bitCast(int);
}

pub const infinite_loop_trap = std.math.maxInt(u64);
pub const unreachable_func_trap = infinite_loop_trap - 1;

pub const Sloc = packed struct(u64) {
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
            .fadd => @bitCast(tf(lhs) + tf(rhs)),
            .isub => lhs -% rhs,
            .fsub => @bitCast(tf(lhs) - tf(rhs)),
            .imul => lhs *% rhs,
            .fmul => @bitCast(tf(lhs) * tf(rhs)),
            .udiv => if (rhs == 0) 0 else @bitCast(tu(lhs) / tu(rhs)),
            .sdiv => if (rhs == 0) 0 else @divFloor(lhs, rhs),
            .fdiv => @bitCast(tf(lhs) / tf(rhs)),
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

            .fgt => @intFromBool(tf(lhs) > tf(rhs)),
            .flt => @intFromBool(tf(lhs) < tf(rhs)),
            .fge => @intFromBool(tf(lhs) >= tf(rhs)),
            .fle => @intFromBool(tf(lhs) <= tf(rhs)),

            .sgt => @intFromBool(lhs > rhs),
            .slt => @intFromBool(lhs < rhs),
            .sge => @intFromBool(lhs >= rhs),
            .sle => @intFromBool(lhs <= rhs),
        }) & dt.mask();
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
    itf32,
    itf64,
    fti,
    fcst,

    pub fn eval(self: UnOp, src: DataType, oper: i64) i64 {
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
            .ineg => -oper,
            .fneg => return @bitCast(-tf(oper)),
            .not => @intFromBool(oper == 0),
            .bnot => ~oper,
            .fti => @intFromFloat(tf(oper)),
            .itf64, .itf32 => return @bitCast(@as(f64, @floatFromInt(oper))),
            .fcst => return oper,
        }) & src.mask();
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

    pub fn size(self: DataType) u64 {
        return switch (self) {
            .top, .bot => unreachable,
            .i8 => 1,
            .i16 => 2,
            .i32, .f32 => 4,
            .i64, .f64 => 8,
        };
    }

    pub fn mask(self: DataType) i64 {
        return switch (self) {
            .top, .bot => unreachable,
            .i8 => 0xFF,
            .i16 => 0xFFFF,
            .i32, .f32 => 0xFFFFFFFF,
            .i64, .f64 => -1,
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
    pub const FramePointer = extern struct {};
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
    pub const Phi = extern struct {
        pub const is_pinned = true;
    };
    pub const Arg = mod.Arg;
    pub const StructArg = extern struct {
        base: mod.Arg,
        spec: AbiParam.StackSpec,
        no_address: bool = false,
    };
    pub const StackArgOffset = extern struct {
        offset: u64, // from eg. rsp
    };
    pub const CInt = extern struct {
        value: i64,
    };
    pub const CFlt32 = extern struct {
        value: f32,
    };
    pub const CFlt64 = extern struct {
        value: f64,
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
    pub const MachMove = extern struct {};
    // ===== MEMORY =====
    pub const Mem = extern struct {
        pub const is_pinned = true;
    };
    pub const Local = extern struct {
        size: u64,
        no_address: bool = false,

        pub const data_dep_offset = 1;
    };
    pub const MemCpy = mod.MemCpy;
    pub const Load = mod.Load;
    pub const Store = mod.Store;
    pub const GlobalAddr = extern struct {
        id: u32,
    };
    pub const Split = extern struct {};
    pub const Join = extern struct {};
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

pub fn FuncNode(comptime Backend: type) type {
    return Func(Backend).Node;
}

pub fn Func(comptime Backend: type) type {
    return struct {
        arena: std.heap.ArenaAllocator,
        interner: InternMap(Uninserter) = .{},
        signature: Signature = .{},
        next_id: u16 = 0,
        root: *Node = undefined,
        end: *Node = undefined,
        gcm: gcm.GcmMixin(Backend) = .{},
        mem2reg: mem2reg.Mem2RegMixin(Backend) = .{},
        static_anal: static_anal.StaticAnalMixin(Backend) = .{},

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
            return std.hash_map.HashMapUnmanaged(InternedNode, void, Context, 70);
        }

        pub const all_classes = std.meta.fields(Union);

        const Self = @This();

        pub const WorkList = struct {
            list: std.ArrayList(*Node),
            in_list: std.DynamicBitSetUnmanaged,

            pub fn init(gpa: std.mem.Allocator, cap: usize) !WorkList {
                return .{
                    .list = try .initCapacity(gpa, cap * 2),
                    .in_list = try .initEmpty(gpa, cap * 2),
                };
            }

            pub fn add(self: *WorkList, node: *Node) void {
                errdefer unreachable;

                if (node.id == std.math.maxInt(u16)) utils.panic("{} {any}\n", .{ node, node.inputs() });
                if (self.in_list.bit_length <= node.id) {
                    try self.in_list.resize(
                        self.list.allocator,
                        try std.math.ceilPowerOfTwo(usize, node.id + 1),
                        false,
                    );
                }

                if (self.in_list.isSet(node.id)) return;
                self.in_list.set(node.id);
                try self.list.append(node);
            }

            pub fn pop(self: *WorkList) ?*Node {
                var node = self.list.pop() orelse return null;
                while (node.id == std.math.maxInt(u16)) {
                    node = self.list.pop() orelse return null;
                }
                self.in_list.unset(node.id);
                return node;
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
                        if (!lc.base.isCfg()) utils.panic("{}", .{lc.base});
                        if (!rc.base.isCfg()) utils.panic("{}", .{rc.base});
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
                                @as(*Node, @ptrCast(extra.cached_lca)).id == std.math.maxInt(u16))
                                extra.cached_lca = null;

                            if (extra.cached_lca) |lca| {
                                return @ptrCast(lca);
                            } else {
                                const lca = findLca(cfg.base.inputs()[0].?.asCfg().?, cfg.base.inputs()[1].?.asCfg().?);
                                cfg.base.extra(.Region).cached_lca = lca;
                                return lca;
                            }
                        },
                        else => cfg.base.cfg0(),
                    };
                }

                pub fn better(cfg: *CfgNode, best: *CfgNode, to_sched: *Node, func: *Self) bool {
                    return !cfg.base.isBasicBlockEnd() and (idepth(cfg) > idepth(best) or
                        best.base.isBasicBlockEnd() or
                        (to_sched.kind != .MachMove and func.gcm.loopDepthOf(cfg) < func.gcm.loopDepthOf(best)));
                }

                pub fn format(self: *const CfgNode, comptime a: anytype, b: anytype, writer: anytype) !void {
                    try self.base.format(a, b, writer);
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
            output_base: [*]*Node,
            sloc: Sloc = .none,

            pub fn preservesIdentityPhys(self: *Node) bool {
                std.debug.assert(self.kind == .Region or self.kind == .Loop);
                return self.kind == .Region and self.extra(.Region).preserve_identity_phys;
            }

            pub fn useBlock(self: *Node, use: *Node, scheds: []const ?*CfgNode) *CfgNode {
                if (use.kind == .Phi) {
                    std.debug.assert(use.inputs()[0].?.kind == .Region or use.inputs()[0].?.kind == .Loop);
                    for (use.inputs()[0].?.inputs(), use.inputs()[1..]) |b, u| {
                        if (u.? == self) {
                            return subclass(b.?, Cfg).?;
                        }
                    }
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

            pub fn dataDeps(self: *Node) []?*Node {
                if (self.kind == .Phi and !self.isDataPhi()) return &.{};
                const kind_idx = @intFromEnum(self.kind);
                const start: usize = dep_offset[kind_idx / per_dep_elem] >>
                    @intCast((kind_idx % per_dep_elem) * sub_elem_width) & ((@as(u16, 1) << sub_elem_width) - 1);
                return self.input_base[start..self.input_ordered_len];
            }

            pub fn knownStore(self: *Node, root: *Node) ?*Node {
                if (self.isStore() and !self.isSub(MemCpy) and self.base() == root) {
                    return self;
                }
                if (self.kind == .BinOp and self.outputs().len == 1 and
                    self.outputs()[0].isStore() and !self.outputs()[0].isSub(MemCpy) and
                    self.outputs()[0].base() == self)
                {
                    return self.outputs()[0];
                }
                return null;
            }

            pub fn knownMemOp(self: *Node) ?struct { *Node, i64 } {
                if (self.isMemOp()) return .{ self, self.getStaticOffset() };
                if (self.kind == .BinOp and self.inputs()[2].?.kind == .CInt and
                    (self.outputs().len) == 1 and
                    (self.outputs()[0].isStore() or self.outputs()[0].isLoad()) and
                    (self.outputs()[0].base()) == (self))
                {
                    return .{ self.outputs()[0], self.inputs()[2].?.extra(.CInt).value };
                }
                return null;
            }

            pub fn knownOffset(self: *Node) struct { *Node, i64 } {
                if (self.kind == .BinOp and self.inputs()[2].?.kind == .CInt) {
                    const op = self.extra(.BinOp).op;
                    const magnitude = self.inputs()[2].?.extra(.CInt).value;
                    std.debug.assert(op == .iadd or op == .isub);
                    return .{ self.inputs()[1].?, if (op == .iadd) magnitude else -magnitude };
                }
                if (@hasDecl(Backend, "knownOffset")) return Backend.knownOffset(self);
                return .{ self, 0 };
            }

            pub fn allowedRegsFor(self: *Node, idx: usize, tmp: *utils.Arena) ?std.DynamicBitSetUnmanaged {
                return if (comptime optApi("allowedRegsFor", @TypeOf(allowedRegsFor))) Backend.allowedRegsFor(self, idx, tmp) else null;
            }

            pub fn regKills(self: *Node, tmp: *utils.Arena) ?std.DynamicBitSetUnmanaged {
                return if (comptime optApi("regKills", @TypeOf(regKills))) Backend.regKills(self, tmp) else null;
            }

            pub fn inPlaceSlot(self: *Node) ?usize {
                return if (comptime optApi("inPlaceSlot", @TypeOf(inPlaceSlot))) Backend.inPlaceSlot(self) else null;
            }

            pub fn noAlias(self: *Node, other: *Node) bool {
                const lsize: i64 = @bitCast(self.data_type.size());
                const rsize: i64 = @bitCast(other.data_type.size());
                const lbase, var loff = knownOffset(self.base());
                const rbase, var roff = knownOffset(other.base());
                loff += self.getStaticOffset();
                roff += other.getStaticOffset();

                if ((lbase.kind == .Local or lbase.kind == .StructArg) and
                    (rbase.kind == .Local or rbase.kind == .StructArg))
                    return (lbase != rbase) or (loff + lsize <= roff) or (roff + rsize <= loff);
                if (lbase.kind == .Local and rbase.kind == .Arg) return true;
                if (rbase.kind == .Arg and rbase.kind == .Local) return true;
                if (lbase == rbase) return (loff + lsize <= roff) or (roff + rsize <= loff);
                return false;
            }

            pub fn isStack(self: *Node) bool {
                return self.kind == .Local or self.kind == .StructArg;
            }

            pub fn regBias(self: *Node) ?u16 {
                return if (@hasDecl(Backend, "regBias")) Backend.regBias(self) else null;
            }

            pub fn carried(self: *Node) ?usize {
                return if (@hasDecl(Backend, "carried")) Backend.carried(self) else null;
            }

            pub fn clobbers(self: *Node) u64 {
                return if (@hasDecl(Backend, "clobbers")) Backend.clobbers(self) else 0;
            }

            pub fn anyextra(self: *const Node) *const anyopaque {
                const any: *const extern struct { n: Node, ex: u8 } = @ptrCast(self);
                return &any.ex;
            }

            pub fn format(self: *const Node, comptime _: anytype, _: anytype, writer: anytype) !void {
                const colors: std.io.tty.Config = if (!utils.freestanding and
                    writer.writeFn == utils.getStdErr().writeFn)
                    std.io.tty.detectConfig(std.io.getStdErr())
                else
                    .no_color;
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

                writer.print(" = {s}", .{name}) catch unreachable;

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
                        logNid(writer, o.id, colors);
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

            pub fn base(self: *Node) *Node {
                std.debug.assert(self.isLoad() or self.isStore());
                return self.inputs()[2].?;
            }

            pub fn value(self: *Node) *Node {
                std.debug.assert(self.isStore());
                return self.inputs()[3].?;
            }

            pub fn isLazyPhi(self: *Node, on_loop: *Node) bool {
                std.debug.assert(on_loop.kind == .Loop or on_loop.kind == .Region);
                return self.kind == .Phi and self.inputs()[0] == on_loop and
                    (self.inputs()[2] == null or self.inputs()[1] == null);
            }

            pub fn inputs(self: *Node) []?*Node {
                return self.input_base[0..self.input_len];
            }

            pub fn kill(self: *Node) void {
                if (self.output_len != 0) utils.panic("{any} {}\n", .{ self.outputs(), self });
                std.debug.assert(self.output_len == 0);
                for (self.inputs()) |oi| if (oi) |i| {
                    i.removeUse(self);
                };

                self.* = undefined;
                self.id = std.math.maxInt(u16);
            }

            pub fn tryCfg0(self: *Node) ?*CfgNode {
                if (self.kind == .Start) return self.asCfg().?;
                return (self.inputs()[0] orelse return null).subclass(Cfg);
            }

            pub fn cfg0(self: *Node) *CfgNode {
                if (self.kind == .Start) return forceSubclass(self, Cfg);
                return forceSubclass((self.inputs()[0].?), Cfg);
            }

            pub fn removeUse(self: *Node, use: *Node) void {
                const outs = self.outputs();
                const index = std.mem.indexOfScalar(*Node, outs, use).?;
                std.mem.swap(*Node, &outs[index], &outs[outs.len - 1]);
                self.output_len -= 1;
            }

            pub fn outputs(self: *Node) []*Node {
                return self.output_base[0..self.output_len];
            }

            pub fn extraConst(self: *const Node, comptime kind: Kind) *const ClassFor(kind) {
                std.debug.assert(self.kind == kind);
                const ptr: *const LayoutFor(kind) = @alignCast(@ptrCast(self));
                return &ptr.ext;
            }

            pub fn extra(self: *Node, comptime kind: Kind) *ClassFor(kind) {
                std.debug.assert(self.kind == kind);
                const ptr: *LayoutFor(kind) = @alignCast(@ptrCast(self));
                return &ptr.ext;
            }

            pub fn extra2(self: *Node) utils.AsRef(Union) {
                const Repr = extern struct { data: *anyopaque, kind: Kind };

                const ptr: *extern struct { base: Node, ext: u8 } = @alignCast(@ptrCast(self));
                return @bitCast(Repr{ .kind = self.kind, .data = &ptr.ext });
            }

            pub fn isDef(self: *Node) bool {
                return !self.isStore() and
                    !self.isCfg() and
                    (self.kind != .Phi or self.isDataPhi()) and
                    (self.kind != .Local or !self.extra(.Local).no_address) and
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

            pub inline fn isPinned(self: *const Node) bool {
                return (comptime bakeFlagBitset("is_pinned")).contains(self.kind);
            }

            pub inline fn isMemOp(self: *const Node) bool {
                return self.isSub(MemOp);
            }

            pub fn isDataPhi(self: *Node) bool {
                // TODO: get rid of this recursion
                const test_val = self.kind == .Phi and self.data_type != .top;
                const true_val = self.kind == .Phi and
                    ((!(self.input_base[1].?.isMemOp() or self.input_base[1].?.kind == .Mem) or
                        self.input_base[1].?.kind == .Local) or
                        self.input_base[1].?.isLoad()) and
                    (self.input_base[1].?.kind != .Phi or self.input_base[1].?.isDataPhi());
                if (test_val != true_val) {
                    utils.panic("{} {}\n", .{ self, self.inputs()[1].? });
                }
                return test_val;
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
                for (all_classes, &arr) |f, *s| s.* = @sizeOf(f.type);
                const m = arr;
                break :b m;
            };

            pub fn size(node: *Node) usize {
                return @sizeOf(Node) + std.mem.alignForward(
                    usize,
                    size_map[@intFromEnum(node.kind)],
                    @alignOf(Node),
                );
            }

            pub fn hash(kind: Kind, dt: DataType, inpts: []const ?*Node, extr: *const anyopaque) u64 {
                var hasher = std.hash.Fnv1a_64.init();
                hasher.update(std.mem.asBytes(&kind));
                hasher.update(std.mem.asBytes(&dt));
                hasher.update(@ptrCast(inpts));
                hasher.update(@as([*]const u8, @ptrCast(extr))[0..size_map[@intFromEnum(kind)]]);
                return hasher.final();
            }

            pub fn cmp(
                akind: Kind,
                bkind: Kind,
                adt: DataType,
                bdt: DataType,
                ainputs: []const ?*Node,
                binputs: []const ?*Node,
                aextra: *const anyopaque,
                bextra: *const anyopaque,
            ) bool {
                return akind == bkind and
                    adt == bdt and
                    std.mem.eql(?*Node, ainputs, binputs) and
                    std.mem.eql(
                        u8,
                        @as([*]const u8, @ptrCast(aextra))[0..size_map[@intFromEnum(akind)]],
                        @as([*]const u8, @ptrCast(bextra))[0..size_map[@intFromEnum(bkind)]],
                    );
            }
        };

        pub fn init(gpa: std.mem.Allocator) Self {
            var self = Self{ .arena = .init(gpa) };
            self.root = self.addNode(.Start, .top, &.{}, .{});
            return self;
        }

        pub fn deinit(self: *Self) void {
            self.arena.deinit();
            self.* = undefined;
        }

        pub fn reset(self: *Self) void {
            std.debug.assert(self.arena.reset(.retain_capacity));
            self.next_id = 0;
            self.root = self.addNode(.Start, .top, &.{}, .{});
            self.interner = .{};
            self.gcm.cfg_built = .{};
            self.gcm.loop_tree_built = .{};
        }

        const Inserter = struct {
            kind: Kind,
            dt: DataType,
            inputs: []const ?*Node,
            extra: *const anyopaque,

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

        pub fn internNode(self: *Self, kind: Kind, dt: DataType, inputs: []const ?*Node, extra: *const anyopaque) InsertMap.GetOrPutResult {
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
            self.addUse(def, to);
            self.addDep(to, def);
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

        pub fn addFieldOffset(self: *Self, base: *Node, offset: i64) *Node {
            return if (offset != 0) if (base.kind == .BinOp and base.inputs()[2].?.kind == .CInt) b: {
                break :b self.addBinOp(.iadd, .i64, base.inputs()[1].?, self.addIntImm(
                    .i64,
                    base.inputs()[2].?.extra(.CInt).value + offset,
                ));
            } else self.addBinOp(.iadd, .i64, base, self.addIntImm(.i64, offset)) else base;
        }

        pub fn addGlobalAddr(self: *Self, arbitrary_global_id: u32) *Node {
            return self.addNode(.GlobalAddr, .i64, &.{null}, .{ .id = arbitrary_global_id });
        }

        pub fn addCast(self: *Self, to: DataType, value: *Node) *Node {
            return self.addNode(.UnOp, to, &.{ null, value }, .{ .op = .cast });
        }

        pub const OffsetDirection = enum(u8) {
            iadd = @intFromEnum(BinOp.iadd),
            isub = @intFromEnum(BinOp.isub),
        };

        pub fn addIndexOffset(self: *Self, base: *Node, op: OffsetDirection, elem_size: u64, subscript: *Node) *Node {
            const offset = if (elem_size == 1)
                subscript
            else if (subscript.kind == .CInt)
                self.addIntImm(.i64, subscript.extra(.CInt).value * @as(i64, @bitCast(elem_size)))
            else
                self.addBinOp(.imul, .i64, subscript, self.addIntImm(.i64, @bitCast(elem_size)));
            return self.addBinOp(@enumFromInt(@intFromEnum(op)), .i64, base, offset);
        }

        pub fn addIntImm(self: *Self, ty: DataType, value: i64) *Node {
            std.debug.assert(ty != .bot);
            const val = self.addNode(.CInt, ty, &.{null}, .{ .value = value });
            std.debug.assert(val.data_type.isInt());
            return val;
        }

        pub fn addFlt64Imm(self: *Self, value: f64) *Node {
            return self.addNode(.CFlt64, .f64, &.{null}, .{ .value = value });
        }

        pub fn addFlt32Imm(self: *Self, value: f32) *Node {
            return self.addNode(.CFlt32, .f32, &.{null}, .{ .value = value });
        }

        pub fn addBinOp(self: *Self, op: BinOp, ty: DataType, lhs: *Node, rhs: *Node) *Node {
            if (lhs.kind == .CInt and rhs.kind == .CInt) {
                return self.addIntImm(ty, op.eval(ty, lhs.extra(.CInt).value, rhs.extra(.CInt).value));
            } else if (lhs.kind == .CFlt64 and rhs.kind == .CFlt64) {
                return self.addFlt64Imm(@bitCast(op.eval(
                    ty,
                    @bitCast(lhs.extra(.CFlt64).*),
                    @bitCast(rhs.extra(.CFlt64).*),
                )));
            }
            if ((op == .iadd or op == .iadd) and rhs.kind == .CInt and rhs.extra(.CInt).value == 0) {
                return lhs;
            }
            return self.addNode(.BinOp, ty, &.{ null, lhs, rhs }, .{ .op = op });
        }

        pub fn addUnOp(self: *Self, op: UnOp, ty: DataType, oper: *Node) *Node {
            if (oper.kind == .CInt and ty.isInt()) {
                return self.addIntImm(ty, op.eval(oper.data_type, oper.extra(.CInt).value));
            } else if (oper.kind == .CFlt64 and ty == .f64) {
                return self.addFlt64Imm(@bitCast(op.eval(oper.data_type, @bitCast(oper.extra(.CFlt64).*))));
            } else if (oper.kind == .CFlt32 and ty == .f32) {
                return self.addFlt32Imm(@floatCast(@as(f64, @bitCast(op.eval(
                    oper.data_type,
                    @bitCast(@as(f64, @floatCast(oper.extra(.CFlt32).value))),
                )))));
            }
            return self.addNode(.UnOp, ty, &.{ null, oper }, .{ .op = op });
        }

        pub fn addTrap(self: *Self, ctrl: *Node, code: u64) void {
            if (self.end.inputs()[2] == null) {
                self.setInputNoIntern(self.end, 2, self.addNode(.TrapRegion, .top, &.{}, .{}));
            }

            const region = self.end.inputs()[2].?;
            const trap = self.addNode(.Trap, .top, &.{ctrl}, .{ .code = code });

            self.addDep(region, trap);
            self.addUse(trap, region);
        }

        pub fn addSplit(self: *Self, ctrl: *Node, def: *Node) *Node {
            return if (comptime optApi("addSplit", @TypeOf(addSplit))) Backend.addSplit(self, ctrl, def) else unreachable;
        }

        pub fn addNode(self: *Self, comptime kind: Kind, ty: DataType, inputs: []const ?*Node, extra: ClassFor(kind)) *Node {
            var typ = ty;
            if (kind == .Phi) {
                if (inputs[1].?.isStore() or inputs[1].?.kind == .Mem) typ = .top;
                if (inputs[2]) |inp| if (inp.isStore() or inp.kind == .Mem) {
                    typ = .top;
                };
            }
            const node = self.addNodeUntyped(kind, typ, inputs, extra);
            return node;
        }

        pub fn addNodeUntyped(self: *Self, kind: Kind, dt: DataType, inputs: []const ?*Node, extra: anytype) *Node {
            if (Node.isInterned(kind, inputs)) {
                const entry = self.internNode(kind, dt, inputs, &extra);
                if (!entry.found_existing) {
                    entry.key_ptr.node = self.addNodeNoIntern(kind, dt, inputs, extra);
                }

                const node = entry.key_ptr.node;

                return node;
            } else {
                return self.addNodeNoIntern(kind, dt, inputs, extra);
            }
        }

        pub fn addNodeNoIntern(self: *Self, kind: Kind, ty: DataType, inputs: []const ?*Node, extra: anytype) *Node {
            const Layout = extern struct {
                base: Node,
                extra: @TypeOf(extra),
            };

            const node = self.arena.allocator().create(Layout) catch unreachable;
            const owned_inputs = self.arena.allocator().dupe(?*Node, inputs) catch unreachable;

            node.* = .{
                .base = .{
                    .input_base = owned_inputs.ptr,
                    .input_len = @intCast(owned_inputs.len),
                    .input_ordered_len = @intCast(owned_inputs.len),
                    .output_base = @ptrFromInt(@alignOf(*Node)),
                    .kind = kind,
                    .id = self.next_id,
                    .data_type = ty,
                },
                .extra = extra,
            };

            for (owned_inputs) |on| if (on) |def| {
                self.addUse(def, &node.base);
            };

            self.next_id += 1;

            return &node.base;
        }

        pub fn isDead(node: ?*Node) bool {
            return node == null or node.?.data_type == .bot;
        }

        pub fn subsumeNoKill(self: *Self, this: *Node, target: *Node) void {
            if (this == target) {
                utils.panic("{} {}\n", .{ this, target });
            }
            errdefer unreachable;

            for (try self.arena.allocator().dupe(*Node, target.outputs())) |use| {
                if (use.id == std.math.maxInt(u16)) continue;
                const index = std.mem.indexOfScalar(?*Node, use.inputs(), target) orelse {
                    utils.panic("{} {any} {}", .{ this, target.outputs(), use });
                };

                if (use == target) {
                    target.inputs()[index] = null;
                    target.removeUse(target);
                } else {
                    _ = self.setInput(use, index, this);
                }
            }
        }

        pub fn subsume(self: *Self, this: *Node, target: *Node) void {
            if (this.sloc == Sloc.none) this.sloc = target.sloc;
            self.uninternNode(target);
            self.subsumeNoKill(this, target);
            target.kill();
        }

        pub fn setInputNoIntern(self: *Self, use: *Node, idx: usize, def: ?*Node) void {
            std.debug.assert(self.setInput(use, idx, def) == null);
        }

        pub fn setInput(self: *Self, use: *Node, idx: usize, def: ?*Node) ?*Node {
            if (use.inputs()[idx] == def) return null;
            if (use.inputs()[idx]) |n| {
                n.removeUse(use);
            }

            self.uninternNode(use);
            use.inputs()[idx] = def;
            if (def) |d| {
                self.addUse(d, use);
            }
            if (self.reinternNode(use)) |nuse| {
                self.subsumeNoKill(nuse, use);
                use.kill();
                return nuse;
            }
            return null;
        }

        pub fn addDep(self: *Self, use: *Node, def: *Node) void {
            if (use.input_ordered_len == use.input_len or
                std.mem.indexOfScalar(
                    ?*Node,
                    use.input_base[use.input_ordered_len..use.input_len],
                    null,
                ) == null)
            {
                const new_cap = @max(use.input_len, 1) * 2;
                const new_inputs = self.arena.allocator().realloc(use.inputs(), new_cap) catch unreachable;
                @memset(new_inputs[use.input_len..], null);
                use.input_base = new_inputs.ptr;
                use.input_len = new_cap;
            }

            for (use.input_base[use.input_ordered_len..use.input_len]) |*slot| {
                if (slot.* == null) {
                    slot.* = def;
                    break;
                }
            } else unreachable;
        }

        pub fn addUse(self: *Self, def: *Node, use: *Node) void {
            if (def.output_len == def.output_cap) {
                const new_cap = @max(def.output_cap, 1) * 2;
                const new_outputs = self.arena.allocator().realloc(def.outputs(), new_cap) catch unreachable;
                def.output_base = new_outputs.ptr;
                def.output_cap = new_cap;
            }

            def.output_base[def.output_len] = use;
            def.output_len += 1;
        }

        pub const Frame = struct { *Node, []const ?*Node };

        pub fn traversePostorder(ctx: anytype, inp: *Node, stack: *std.ArrayList(Frame), visited: *std.DynamicBitSet) void {
            const Ctx = if (@typeInfo(@TypeOf(ctx)) == .pointer) @TypeOf(ctx.*) else @TypeOf(ctx);
            const dir = Ctx.dir;

            stack.append(.{ inp, @field(Node, dir)(inp) }) catch unreachable;
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
                if (node) |n| if ((!@hasDecl(Ctx, "filter") or ctx.filter(n)) and !visited.isSet(n.id)) {
                    visited.set(n.id);
                    stack.append(.{ n, @field(Node, dir)(n) }) catch unreachable;
                };
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
            worklist.add(self.end);
            worklist.add(self.root);
            var i: usize = 0;
            while (i < worklist.list.items.len) : (i += 1) {
                for (worklist.list.items[i].inputs()) |oi| if (oi) |o| {
                    worklist.add(o);
                };

                for (worklist.list.items[i].outputs()) |o| {
                    worklist.add(o);
                }
            }

            while (worklist.pop()) |t| {
                if (t.id == std.math.maxInt(u16)) continue;

                if (t.outputs().len == 0 and t != self.end) {
                    for (t.inputs()) |ii| if (ii) |ia| worklist.add(ia);
                    self.uninternNode(t);
                    t.kill();
                    continue;
                }

                if (strategy(ctx, self, t, &worklist)) |nt| {
                    for (t.inputs()) |ii| if (ii) |ia| worklist.add(ia);
                    for (t.outputs()) |o| worklist.add(o);
                    self.subsume(nt, t);
                    continue;
                }
            }
        }

        pub fn collectDfs(self: *Self, arena: std.mem.Allocator, visited: *std.DynamicBitSet) []*CfgNode {
            var postorder = std.ArrayList(*CfgNode).init(arena);
            collectPostorder3(self, self.root, arena, &postorder, visited, true);
            return postorder.items;
        }

        pub fn collectPostorder3(
            self: *Self,
            node: *Node,
            arena: std.mem.Allocator,
            pos: *std.ArrayList(*CfgNode),
            visited: *std.DynamicBitSet,
            comptime only_basic: bool,
        ) void {
            if (visited.isSet(node.id)) {
                return;
            }
            visited.set(node.id);
            pos.append(node.asCfg().?) catch unreachable;
            for (node.outputs()) |o| if (o.isCfg()) collectPostorder3(self, o, arena, pos, visited, only_basic);
        }

        pub fn idealizeDead(_: anytype, self: *Self, node: *Node, worklist: *WorkList) ?*Node {
            const inps = node.inputs();

            var is_dead = node.kind == .Region and isDead(inps[0]) and isDead(inps[1]);
            is_dead = is_dead or (node.kind != .Start and node.kind != .Region and
                node.kind != .TrapRegion and node.isCfg() and isDead(inps[0]));

            if (is_dead and node.kind == .Return and inps[0] != null) {
                worklist.add(inps[0].?);
                self.setInputNoIntern(node, 0, null);
                return null;
            }

            if (node.kind == .TrapRegion) {
                is_dead = true;
                for (node.inputs()) |*inp| {
                    if (inp.* != null and isDead(inp.*)) {
                        inp.*.?.removeUse(node);
                        worklist.add(inp.*.?);
                        inp.* = null;
                    }
                    is_dead = is_dead and isDead(inp.*);
                }

                var retain: usize = 0;
                for (node.inputs()) |a| {
                    if (a != null) {
                        node.inputs()[retain] = a;
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
                while (cursor.base.kind != .Entry and
                    cursor.base.id != std.math.maxInt(u16)) : (cursor = cursor.idom())
                {
                    if (cursor.base.kind != .Then and cursor.base.kind != .Else) continue;

                    const if_node = cursor.base.inputs()[0].?;
                    if (if_node.kind != .If) continue;

                    if (if_node.inputs()[1].? == node.inputs()[1].?) {
                        self.setInputNoIntern(node, 1, self.addIntImm(
                            .i8,
                            @intFromBool(cursor.base.kind == .Then),
                        ));
                        for (node.outputs()) |o| worklist.add(o);
                        return null;
                    }
                }
            }

            if (is_dead and node.data_type != .bot) {
                node.data_type = .bot;
                for (node.outputs()) |o| worklist.add(o);
                return null;
            }

            if (node.kind == .Region) eliminate_branch: {
                std.debug.assert(node.inputs().len == 2);
                const idx = for (node.inputs(), 0..) |in, i| {
                    if (isDead(in)) break i;
                } else break :eliminate_branch;

                var iter = std.mem.reverseIterator(node.outputs());
                while (iter.next()) |o| if (o.kind == .Phi) {
                    for (o.outputs()) |oo| worklist.add(oo);
                    self.subsume(o.inputs()[(1 - idx) + 1].?, o);
                };

                return node.inputs()[1 - idx].?;
            }

            if (node.kind == .Region) eliminate_if: {
                for (node.outputs()) |o| {
                    if (!o.isCfg()) break :eliminate_if;
                }

                if (node.inputs()[0].?.inputs()[0] == node.inputs()[1].?.inputs()[0]) {
                    return node.inputs()[0].?.inputs()[0].?.inputs()[0];
                }
            }

            if (node.kind == .Loop) remove: {
                if (!isDead(node.inputs()[1])) break :remove;

                var iter = std.mem.reverseIterator(node.outputs());
                while (iter.next()) |o| if (o.kind == .Phi) {
                    for (o.outputs()) |oo| worklist.add(oo);
                    self.subsume(o.inputs()[1].?, o);
                };

                return node.inputs()[0].?;
            }

            if (node.kind == .Then and node.inputs()[0].?.kind == .If) {
                const if_node = node.inputs()[0].?;
                const cond = if_node.inputs()[1].?;
                if (cond.kind == .CInt and cond.extra(.CInt).value != 0) {
                    if_node.data_type = .bot;
                    worklist.add(if_node.outputs()[1]);
                    return if_node.inputs()[0].?;
                }
            }

            if (node.kind == .Else and node.inputs()[0].?.kind == .If) {
                const if_node = node.inputs()[0].?;
                const cond = if_node.inputs()[1].?;
                if (cond.kind == .CInt and cond.extra(.CInt).value == 0) {
                    if_node.data_type = .bot;
                    worklist.add(if_node.outputs()[0]);
                    return if_node.inputs()[0].?;
                }
            }

            if (node.kind == .Store) {
                if (node.value().data_type.size() == 0) {
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
            if (node.data_type == .bot) return null;

            if (idealizeDead(ctx, self, node, work)) |w| return w;

            var tmp = utils.Arena.scrathFromAlloc(work.list.allocator);
            defer tmp.deinit();

            const inps = node.inputs();

            if (node.kind == .Store) {
                const base, _ = node.base().knownOffset();

                if (base.kind == .Local) eliminate_stack: {
                    for (base.outputs()) |o| {
                        _ = o.knownStore(base) orelse {
                            break :eliminate_stack;
                        };
                    }

                    for (base.outputs()) |o| if (o.knownStore(base).? != node) {
                        work.add(o.knownStore(base).?);
                    };

                    return node.mem();
                }

                if (base.kind == .Local and node.tryCfg0() != null) {
                    const dinps = tmp.arena.dupe(?*Node, node.inputs());
                    dinps[0] = null;
                    const st = self.addNode(.Store, node.data_type, dinps, .{});
                    work.add(st);
                    return st;
                }
            }

            if (node.kind == .Load) {
                var earlier = node.mem();
                const base, _ = node.base().knownOffset();

                if (base.kind == .Local and node.tryCfg0() != null) {
                    const dinps = tmp.arena.dupe(?*Node, node.inputs());
                    dinps[0] = null;
                    const st = self.addNode(.Load, node.data_type, dinps, .{});
                    work.add(st);
                    return st;
                }

                while (earlier.kind == .Store and
                    (earlier.tryCfg0() == node.tryCfg0() or node.tryCfg0() == null) and
                    earlier.noAlias(node))
                {
                    earlier = earlier.mem();
                }

                if (earlier.kind == .Store and
                    earlier.base() == node.base() and
                    earlier.data_type == node.data_type)
                {
                    return earlier.value();
                }

                if (earlier != node.mem()) {
                    return self.addNode(.Load, node.data_type, &.{ inps[0], earlier, inps[2] }, .{});
                }
            }

            if (false and node.kind == .MemCpy) memcpy: {
                const ctrl = inps[0].?;
                _ = ctrl; // autofix
                const mem = inps[1].?;
                const dst = inps[2].?;
                const src = inps[3].?;
                const len = inps[4].?;
                _ = len; // autofix

                if (dst == src) {
                    return mem;
                }

                if (src.kind == .Local and dst.kind == .Local) {
                    for (src.outputs()) |use| {
                        if (use.knownMemOp()) |op| {
                            if (op[0] == node) continue;
                            if (op[0].kind != .Store) {
                                break :memcpy;
                            }
                        } else break :memcpy;
                    }

                    self.subsume(dst, src);
                    return mem;
                }
            }

            if (node.kind == .UnOp) {
                const op: UnOp = node.extra(.UnOp).op;
                const oper = inps[1].?;

                if (oper.kind == .CInt and node.data_type.isInt()) {
                    return self.addIntImm(node.data_type, op.eval(oper.data_type, oper.extra(.CInt).value));
                }

                if (node.data_type.meet(inps[1].?.data_type) == inps[1].?.data_type) {
                    if (op == .uext or op == .sext) {
                        return inps[1];
                    }
                }
            }

            if (node.kind == .BinOp) {
                const lhs = node.inputs()[1].?;
                const rhs = node.inputs()[2].?;
                if (lhs.kind == .CInt and rhs.kind == .CInt) {
                    return self.addIntImm(
                        lhs.data_type.meet(rhs.data_type),
                        node.extra(.BinOp).op.eval(
                            lhs.data_type,
                            lhs.extra(.CInt).value,
                            rhs.extra(.CInt).value,
                        ),
                    );
                }
            }

            if (node.kind == .Phi) {
                _, const l, const r = .{ inps[0].?, inps[1].?, inps[2].? };

                if (l == r and !node.cfg0().base.preservesIdentityPhys()) {
                    return l;
                }

                if (r == node) {
                    return l;
                }
            }

            if (node.isLoad()) {
                const base, const offset = node.base().knownOffset();
                if (base.kind == .GlobalAddr) fold_const_read: {
                    const value = ctx.out.readFromSym(
                        base.extra(.GlobalAddr).id,
                        offset + node.getStaticOffset(),
                        node.data_type.size(),
                    ) orelse break :fold_const_read;

                    return self.addIntImm(node.data_type, value);
                }
            }

            if (node.kind == .Call and node.data_type != .bot) {
                if (ctx.out.getInlineFunc(node.extra(.Call).id)) |inline_func| {
                    inline_func.inlineInto(Backend, self, node, work);
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

        pub fn collectPostorder(self: *Self, arena: std.mem.Allocator, visited: *std.DynamicBitSet) []*CfgNode {
            var postorder = std.ArrayList(*CfgNode).init(arena);

            collectPostorder2(self, self.root, arena, &postorder, visited, true);

            return postorder.items;
        }

        pub fn collectPostorderAll(self: *Self, arena: std.mem.Allocator, visited: *std.DynamicBitSet) []*CfgNode {
            var postorder = std.ArrayList(*CfgNode).init(arena);
            self.collectPostorder2(self.root, arena, &postorder, visited, false);
            return postorder.items;
        }

        pub fn collectPostorder2(
            self: *Self,
            node: *Node,
            arena: std.mem.Allocator,
            pos: *std.ArrayList(*CfgNode),
            visited: *std.DynamicBitSet,
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

            if (!only_basic or node.isBasicBlockStart()) pos.append(node.asCfg().?) catch unreachable;
            if (node.isSwapped()) {
                var iter = std.mem.reverseIterator(node.outputs());
                while (iter.next()) |o| if (o.isCfg()) collectPostorder2(self, o, arena, pos, visited, only_basic);
            } else {
                for (node.outputs()) |o| if (o.isCfg()) collectPostorder2(self, o, arena, pos, visited, only_basic);
            }
        }

        pub fn fmtScheduled(self: *Self, writer: anytype, colors: std.io.tty.Config) void {
            errdefer unreachable;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var visited = try std.DynamicBitSet.initEmpty(tmp.arena.allocator(), self.next_id);

            self.root.fmt(self.gcm.block_count, writer, colors);
            try writer.writeAll("\n");
            for (collectPostorder(self, tmp.arena.allocator(), &visited)) |p| {
                p.base.fmt(self.gcm.block_count, writer, colors);

                try writer.writeAll("\n");
                for (p.base.outputs()) |o| {
                    try writer.writeAll("  ");
                    o.fmt(self.gcm.instr_count, writer, colors);
                    try writer.writeAll("\n");
                }
            }
        }

        pub fn fmtUnscheduled(self: *Self, writer: anytype, colors: std.io.tty.Config) void {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var worklist = Self.WorkList.init(tmp.arena.allocator(), self.next_id) catch unreachable;

            worklist.add(self.root);
            worklist.add(self.end);
            var i: usize = 0;
            while (i < worklist.list.items.len) : (i += 1) {
                for (worklist.list.items[i].inputs()) |oi| if (oi) |o| {
                    worklist.add(o);
                };

                for (worklist.list.items[i].outputs()) |o| {
                    worklist.add(o);
                }
            }

            std.mem.reverse(*Node, worklist.list.items);

            for (worklist.list.items) |p| {
                p.fmt(null, writer, colors);
                writer.writeAll("\n") catch unreachable;
            }
        }
    };
}
