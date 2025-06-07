const std = @import("std");
pub const utils = @import("../utils.zig");

fn tu(int: i64) u64 {
    return @bitCast(int);
}

fn tf(int: i64) f64 {
    return @bitCast(int);
}

pub const infinite_loop_trap = std.math.maxInt(u64);

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

    pub fn eval(self: BinOp, lhs: i64, rhs: i64) i64 {
        return switch (self) {
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
    itf32,
    itf64,
    fti,
    fcst,

    pub fn eval(self: UnOp, src: DataType, oper: i64) i64 {
        return switch (self) {
            .cast => oper,
            .sext => switch (src) {
                .i8 => @as(i8, @truncate(oper)),
                .i16 => @as(i16, @truncate(oper)),
                .i32 => @as(i32, @truncate(oper)),
                .int => oper,
                else => utils.panic("{}", .{src}),
            },
            .uext => switch (src) {
                .i8 => @as(u8, @truncate(tu(oper))),
                .i16 => @as(u16, @truncate(tu(oper))),
                .i32 => @as(u32, @truncate(tu(oper))),
                .int => oper,
                else => unreachable,
            },
            .ired => oper,
            .ineg => -oper,
            .fneg => @bitCast(-tf(oper)),
            .not => @intFromBool(oper == 0),
            .bnot => ~oper,
            .fti => @intFromFloat(tf(oper)),
            .itf64, .itf32 => @bitCast(@as(f64, @floatFromInt(oper))),
            .fcst => oper,
        };
    }
};

pub const DataType = enum(u16) {
    top,
    i8,
    i16,
    i32,
    int,
    f32,
    f64,
    bot,

    pub fn size(self: DataType) u64 {
        return switch (self) {
            .top, .bot => unreachable,
            .i8 => 1,
            .i16 => 2,
            .i32, .f32 => 4,
            .int, .f64 => 8,
        };
    }

    pub fn isInt(self: DataType) bool {
        return switch (self) {
            .i8, .i16, .i32, .int => true,
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

pub const Builtin = union(enum) {
    Start: Cfg,
    // [Start]
    Arg: usize,
    // [Start]
    Entry: Cfg,
    // [Start]
    Mem,
    Never: Cfg,
    // [Cfg, ret]
    Return: Cfg,
    // [Cfg]
    Trap: extern struct {
        base: Cfg = .{},
        code: u64,
    },
    // [?Cfg]
    CInt: i64,
    // [?Cfg]
    CFlt32: f32,
    CFlt64: f64,
    // [?Cfg, lhs, rhs]
    BinOp: mod.BinOp,
    // [?Cfg, lhs, rhs]
    UnOp: mod.UnOp,
    // [?Cfg, Mem]
    Local: u64,
    // [?Cfg, thread, ptr]
    Load: Load,
    // [?Cfg, thread, ptr, value, ...antideps]
    Store: Store,
    // [?Cfg, thread, dst, src, size, ...antideps]
    MemCpy: MemCpy,
    // [?Cfg]
    GlobalAddr: extern struct {
        id: u32,
    },
    // [?Cfg, ...lane]
    Split,
    // [?Cfg, ...lane]
    Join,
    // [Cfg, ..args]
    Call: extern struct {
        base: Cfg = .{},
        id: u32,
        ret_count: u32,
    },
    // [Call]
    CallEnd: Cfg,
    // [CallEnd]
    Ret: usize,
    // [Cfg, cond],
    If: If,
    // [If]
    Then: Cfg,
    // [If]
    Else: Cfg,
    // [lCfg, rCfg]
    Region: extern struct {
        base: Cfg = .{},
        preserve_identity_phys: bool = false,
        cached_lca: ?*align(8) anyopaque = null,
    },
    // [traps...]
    TrapRegion: Cfg,
    // [entryCfg, backCfg]
    Loop: Cfg,
    // [Cfg]
    Jmp: Cfg,
    // [Region, lhs, rhs]
    Phi,
    // [Cfg, inp]
    MachMove,

    pub const is_basic_block_start = .{ .Entry, .CallEnd, .Then, .Else, .Region, .Loop, .TrapRegion };
    pub const is_basic_block_end = .{ .Return, .Call, .If, .Jmp, .Never, .Trap };
    pub const is_mem_op = .{ .Load, .MemCpy, .Local, .Store, .Return, .Call, .Mem };
    pub const is_pinned = .{ .Ret, .Phi, .Mem };
};

pub const If = extern struct {
    base: Cfg = .{},
};

pub fn UnionOf(comptime MachNode: type) type {
    var builtin = @typeInfo(Builtin);
    builtin.@"union".decls = &.{};
    builtin.@"union".tag_type = KindOf(MachNode);
    const field_ref = std.meta.fields(MachNode);
    builtin.@"union".fields = builtin.@"union".fields ++ field_ref;
    return @Type(builtin);
}

pub fn KindOf(comptime MachNode: type) type {
    var builtin = @typeInfo(std.meta.Tag(Builtin));
    builtin.@"enum".tag_type = u16;
    const field_ref = std.meta.fields(std.meta.Tag(MachNode));
    var fields = field_ref[0..field_ref.len].*;
    for (&fields, builtin.@"enum".fields.len..) |*f, i| {
        f.value = i;
    }
    builtin.@"enum".fields = builtin.@"enum".fields ++ fields;
    return @Type(builtin);
}

pub const Cfg = extern struct {
    idepth: u16 = 0,
    antidep: u16 = 0,
    loop: u16 = undefined,
};
pub const Load = extern struct {};
pub const Store = extern struct {};
pub const MemCpy = extern struct {
    base: Store = .{},
};

const mod = @This();
const gcm = @import("gcm.zig");
const mem2reg = @import("mem2reg.zig");
const static_anal = @import("static_anal.zig");

pub fn Func(comptime MachNode: type) type {
    return struct {
        arena: std.heap.ArenaAllocator,
        interner: InternMap(Uninserter) = .{},
        params: []const mod.DataType = &.{},
        returns: []const mod.DataType = &.{},
        next_id: u16 = 0,
        block_count: u16 = undefined,
        instr_count: u16 = undefined,
        root: *Node = undefined,
        end: *Node = undefined,
        gcm: gcm.GcmMixin(MachNode) = .{},
        mem2reg: mem2reg.Mem2RegMixin(MachNode) = .{},
        static_anal: static_anal.StaticAnalMixin(MachNode) = .{},

        pub fn optApi(comptime decl_name: []const u8, comptime Ty: type) bool {
            const prelude = @typeName(MachNode) ++ " requires this unless `pub const i_know_the_api = {}` is declared:";

            const decl = if (@typeInfo(Ty) == .@"fn")
                "pub fn " ++ decl_name ++ @typeName(Ty)[3..]
            else
                "pub const " ++ decl_name ++ ": " ++ @typeName(Ty);

            const known_api = @hasDecl(MachNode, "i_know_the_api");
            if (!known_api and !@hasDecl(MachNode, decl_name))
                @compileError(prelude ++ " `" ++ decl ++ "`");

            if (@hasDecl(MachNode, decl_name) and @TypeOf(@field(MachNode, decl_name)) != Ty)
                @compileError("expected `" ++ decl ++
                    "` but the type is: " ++ @typeName(@TypeOf(@field(MachNode, decl_name))));

            return @hasDecl(MachNode, decl_name);
        }

        pub fn InternMap(comptime Context: type) type {
            return std.hash_map.HashMapUnmanaged(InternedNode, void, Context, 70);
        }

        pub const all_classes = std.meta.fields(Builtin) ++ std.meta.fields(MachNode);

        const Self = @This();

        pub const WorkList = struct {
            list: std.ArrayList(*Node),
            in_list: std.DynamicBitSet,

            pub fn init(gpa: std.mem.Allocator, cap: usize) !WorkList {
                return .{
                    .list = try .initCapacity(gpa, cap * 2),
                    .in_list = try .initEmpty(gpa, cap * 2),
                };
            }

            pub fn add(self: *WorkList, node: *Node) void {
                if (node.id == std.math.maxInt(u16)) utils.panic("{} {any}\n", .{ node, node.inputs() });
                if (self.in_list.isSet(node.id)) return;
                self.in_list.set(node.id);
                self.list.appendAssumeCapacity(node);
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

        pub const Kind = KindOf(MachNode);
        pub const Union = UnionOf(MachNode);

        pub fn bakeBitset(comptime name: []const u8) std.EnumSet(Kind) {
            var set = std.EnumSet(Kind).initEmpty();
            for (@field(Builtin, name)) |k| set.insert(k);
            if (optApi(name, []const Kind)) for (@field(MachNode, name)) |k| set.insert(k);
            return set;
        }

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
                        else => idepth(cfg.base.cfg0().?) + 1,
                    };
                    return extra.idepth;
                }

                pub fn findLca(left: *CfgNode, right: *CfgNode) *CfgNode {
                    var lc, var rc = .{ left, right };
                    while (lc != rc) {
                        if (!lc.base.isCfg()) utils.panic("{}", .{lc.base});
                        if (!rc.base.isCfg()) utils.panic("{}", .{rc.base});
                        const diff = @as(i64, idepth(lc)) - idepth(rc);
                        if (diff >= 0) lc = lc.idom();
                        if (diff <= 0) rc = rc.idom();
                    }
                    return lc;
                }

                pub fn idom(cfg: *CfgNode) *CfgNode {
                    return switch (cfg.base.kind) {
                        .Region => if (cfg.base.extra(.Region).cached_lca) |cached|
                            @ptrCast(cached)
                        else {
                            const lca = findLca(cfg.base.inputs()[0].?.asCfg().?, cfg.base.inputs()[1].?.asCfg().?);
                            cfg.base.extra(.Region).cached_lca = lca;
                            return lca;
                        },
                        else => cfg.base.cfg0().?,
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
            return (comptime optApi(name, fn (@TypeOf(value)) bool)) and @field(MachNode, name)(value);
        }

        const is_basic_block_start = bakeBitset("is_basic_block_start");
        const is_basic_block_end = bakeBitset("is_basic_block_end");
        const is_mem_op = bakeBitset("is_mem_op");
        const is_pinned = bakeBitset("is_pinned");
        const is_temporary = bakeBitset("is_temporary");

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
                    return use.cfg0().?;
                }

                return scheds[use.id].?;
            }

            pub fn dataDeps(self: *Node) []?*Node {
                if ((self.kind == .Phi and !self.isDataPhi()) or self.kind == .Mem) return &.{};
                const start: usize = @intFromBool(self.isMemOp());
                return self.input_base[1 + start + @intFromBool(self.kind == .Return) .. self.input_ordered_len];
            }

            pub fn knownStore(self: *Node, root: *Node) ?*Node {
                if (self.isStore() and !self.isSub(MemCpy) and self.base() == root) return self;
                if (self.kind == .BinOp and self.outputs().len == 1 and self.outputs()[0].isStore() and !self.isSub(MemCpy) and self.outputs()[0].base() == self) {
                    return self.outputs()[0];
                }
                return null;
            }

            pub fn knownMemOp(self: *Node) ?struct { *Node, i64 } {
                if (self.isMemOp()) return .{ self, self.getStaticOffset() };
                if (self.kind == .BinOp and self.inputs()[2].?.kind == .CInt and
                    (self.outputs().len) == 1 and (self.outputs()[0].isStore() or self.outputs()[0].isLoad()) and (self.outputs()[0].base()) == (self))
                {
                    return .{ self.outputs()[0], self.inputs()[2].?.extra(.CInt).* };
                }
                return null;
            }

            pub fn knownOffset(self: *Node) struct { *Node, i64 } {
                if (self.kind == .BinOp and self.inputs()[2].?.kind == .CInt) {
                    std.debug.assert(self.extra(.BinOp).* == .iadd or self.extra(.BinOp).* == .isub);
                    return .{ self.inputs()[1].?, if (self.extra(.BinOp).* == .iadd)
                        self.inputs()[2].?.extra(.CInt).*
                    else
                        -self.inputs()[2].?.extra(.CInt).* };
                }
                if (@hasDecl(MachNode, "knownOffset")) return MachNode.knownOffset(self);
                return .{ self, 0 };
            }

            pub fn allowedRegsFor(self: *Node, idx: usize, tmp: *utils.Arena) ?std.DynamicBitSetUnmanaged {
                return if (comptime optApi("allowedRegsFor", @TypeOf(allowedRegsFor))) MachNode.allowedRegsFor(self, idx, tmp) else null;
            }

            pub fn regKills(self: *Node, tmp: *utils.Arena) ?std.DynamicBitSetUnmanaged {
                return if (comptime optApi("regKills", @TypeOf(regKills))) MachNode.regKills(self, tmp) else null;
            }

            pub fn inPlaceSlot(self: *Node) ?usize {
                return if (comptime optApi("inPlaceSlot", @TypeOf(inPlaceSlot))) MachNode.inPlaceSlot(self) else null;
            }

            pub fn noAlias(self: *Node, other: *Node) bool {
                const lsize: i64 = @bitCast(self.data_type.size());
                const rsize: i64 = @bitCast(other.data_type.size());
                const lbase, const loff = knownOffset(self.base());
                const rbase, const roff = knownOffset(other.base());

                if (lbase.kind == .Local and rbase.kind == .Local)
                    return (lbase != rbase) or (loff + lsize <= roff) or (roff + rsize <= loff);
                if (lbase.kind == .Local and rbase.kind == .Arg) return true;
                if (lbase.kind == .Arg and rbase.kind == .Local) return true;
                return false;
            }

            pub fn regBias(self: *Node) ?u16 {
                return if (@hasDecl(MachNode, "regBias")) MachNode.regBias(self) else null;
            }

            pub fn carried(self: *Node) ?usize {
                return if (@hasDecl(MachNode, "carried")) MachNode.carried(self) else null;
            }

            pub fn clobbers(self: *Node) u64 {
                return if (@hasDecl(MachNode, "clobbers")) MachNode.clobbers(self) else 0;
            }

            pub fn anyextra(self: *const Node) *const anyopaque {
                const any: *const extern struct { n: Node, ex: u8 } = @ptrCast(self);
                return &any.ex;
            }

            pub fn format(self: *const Node, comptime _: anytype, _: anytype, writer: anytype) !void {
                const colors = .no_color;
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
                            if (comptime std.mem.eql(u8, f.name, "antidep") or !isVisibel(f.type)) {
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

                for (self.input_base[0..self.input_len][@min(@intFromBool(scheduled != null and
                    (!self.isCfg() or !self.isBasicBlockStart())), self.input_base[0..self.input_len].len)..]) |oo| if (oo) |o|
                {
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

            pub fn cfg0(self: *Node) ?*CfgNode {
                if (self.kind == .Start) return subclass(self, Cfg);
                return subclass((self.inputs()[0] orelse return null), Cfg);
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

            pub fn getStaticOffset(self: *Node) i64 {
                std.debug.assert(self.isMemOp());
                return if (@hasDecl(MachNode, "getStaticOffset")) MachNode.getStaticOffset(self) else 0;
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

            pub fn isSub(self: *const Node, comptime Sub: type) bool {
                return (comptime bakeSubclassBitset(Sub)).contains(self.kind);
            }

            pub fn subclass(self: *Node, comptime Sub: type) ?*LayoutOf(Sub) {
                if (!self.isSub(Sub)) return null;
                return @ptrCast(self);
            }

            pub fn isInterned(kind: Kind, inpts: []const ?*Node) bool {
                return switch (kind) {
                    .CInt, .BinOp, .Load, .UnOp, .GlobalAddr => true,
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
                return is_pinned.contains(self.kind);
            }

            pub inline fn isMemOp(self: *const Node) bool {
                return is_mem_op.contains(self.kind);
            }

            pub fn isDataPhi(self: *const Node) bool {
                // TODO: get rid of this recursion
                return self.kind == .Phi and //and self.data_type != .top;
                    (!self.input_base[1].?.isMemOp() or self.input_base[1].?.isLoad()) and
                    (self.input_base[1].?.kind != .Phi or self.input_base[1].?.isDataPhi());
            }

            pub inline fn isBasicBlockStart(self: *const Node) bool {
                return is_basic_block_start.contains(self.kind);
            }

            pub inline fn isBasicBlockEnd(self: *const Node) bool {
                return is_basic_block_end.contains(self.kind);
            }

            pub const size_map = b: {
                var arr: [all_classes.len]u8 = undefined;
                for (all_classes, &arr) |f, *s| s.* = @sizeOf(f.type);
                const m = arr;
                break :b m;
            };

            pub fn hash(kind: Kind, dt: DataType, inpts: []const ?*Node, extr: *const anyopaque) u64 {
                var hasher = std.hash.Fnv1a_64.init();
                hasher.update(@as(*const [2]u8, @ptrCast(&kind)));
                hasher.update(@as(*const [1]u8, @ptrCast(&dt)));
                hasher.update(@as([*]const u8, @ptrCast(inpts.ptr))[0 .. inpts.len * @sizeOf(?*Node)]);
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
                    std.mem.eql(?*Node, ainputs, binputs) and
                    adt == bdt and
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
                std.debug.assert(self.interner.remove(.{ .node = node, .hash = Node.hash(node.kind, node.data_type, node.inputs(), node.anyextra()) }));
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
            const cfg = node.asCfg() orelse node.cfg0().?;
            const tree = &self.gcm.loop_tree[cfg.ext.loop];
            if (tree.depth != 0) return tree.depth;
            if (tree.par == null) {
                tree.par = tree.head.base.cfg0().?.base.cfg0().?.ext.loop;
            }
            tree.depth = self.loopDepth(&self.gcm.loop_tree[tree.par.?].head.base) + 1;
            return tree.depth;
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
            return if (comptime optApi("addSplit", @TypeOf(addSplit))) MachNode.addSplit(self, ctrl, def) else unreachable;
        }

        pub fn addNode(self: *Self, comptime kind: Kind, ty: DataType, inputs: []const ?*Node, extra: ClassFor(kind)) *Node {
            const node = self.addNodeUntyped(kind, ty, inputs, extra);
            return node;
        }

        pub fn addNodeUntyped(self: *Self, kind: Kind, dt: DataType, inputs: []const ?*Node, extra: anytype) *Node {
            if (Node.isInterned(kind, inputs)) {
                const entry = self.internNode(kind, dt, inputs, &extra);
                if (!entry.found_existing) {
                    entry.key_ptr.node = self.addNodeNoIntern(kind, dt, inputs, extra);
                } else {
                    entry.key_ptr.node.data_type = entry.key_ptr.node.data_type.meet(dt);
                }

                return entry.key_ptr.node;
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
            std.debug.assert(this != target);
            //std.debug.print("{} {} {any}\n", .{ target, this, target.outputs() });

            for (self.arena.allocator().dupe(*Node, target.outputs()) catch unreachable) |use| {
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

            //if (@import("builtin").mode == .Debug) {
            //    var iter = self.interner.iterator();
            //    while (iter.next()) |e| std.debug.assert(e.key_ptr.node.id != std.math.maxInt(u16));
            //}

            //if (target.outputs().len != 0)
            //    utils.panic("-- {any}\n", .{target.outputs()})
            //else
            //    std.debug.print("--\n", .{});
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
            if (use.input_ordered_len == use.input_len or std.mem.indexOfScalar(?*Node, use.input_base[use.input_ordered_len..use.input_len], null) == null) {
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

        pub fn iterPeeps(self: *Self, max_peep_iters: usize, strategy: fn (*Self, *Node, *WorkList) ?*Node) void {
            self.gcm.cfg_built.assertUnlocked();

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var worklist = WorkList.init(tmp.arena.allocator(), self.next_id) catch unreachable;
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

            var fuel = max_peep_iters;
            while (worklist.pop()) |t| {
                if (fuel == 0) break;
                fuel -= 1;

                if (t.id == std.math.maxInt(u16)) continue;

                if (t.outputs().len == 0 and t != self.end) {
                    for (t.inputs()) |ii| if (ii) |ia| worklist.add(ia);
                    self.uninternNode(t);
                    t.kill();
                    continue;
                }

                if (strategy(self, t, &worklist)) |nt| {
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

        pub fn idealizeDead(self: *Self, node: *Node, worklist: *WorkList) ?*Node {
            const inps = node.inputs();

            var is_dead = node.kind == .Region and isDead(inps[0]) and isDead(inps[1]);
            is_dead = is_dead or (node.kind != .Start and node.kind != .Region and node.kind != .Return and
                node.isCfg() and isDead(inps[0]));

            if (is_dead) {
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

            if (node.kind == .Store) {
                if (node.value().data_type.size() == 0) {
                    return node.mem();
                }
            }

            std.debug.assert(node.kind != .Load or node.data_type.size() != 0);

            if (node.kind == .Phi) {
                const l, const r = .{ inps[1].?, inps[2].? };

                if (l == r and !node.cfg0().?.base.preservesIdentityPhys()) {
                    return l;
                }

                if (r == node) {
                    return l;
                }
            }

            return null;
        }

        pub fn idealize(self: *Self, node: *Node, worklist: *WorkList) ?*Node {
            if (node.data_type == .bot) return null;

            if (self.idealizeDead(node, worklist)) |w| return w;

            var tmp = utils.Arena.scrath(null);
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
                        worklist.add(o.knownStore(base).?);
                    };

                    return node.mem();
                }

                if (base.kind == .Local and node.cfg0() != null) {
                    const dinps = tmp.arena.dupe(?*Node, node.inputs());
                    dinps[0] = null;
                    const st = self.addNode(.Store, node.data_type, dinps, .{});
                    worklist.add(st);
                    return st;
                }
            }

            if (node.kind == .Load) {
                var earlier = node.mem();
                const base, _ = node.base().knownOffset();

                if (base.kind == .Local and node.cfg0() != null) {
                    const dinps = tmp.arena.dupe(?*Node, node.inputs());
                    dinps[0] = null;
                    const st = self.addNode(.Load, node.data_type, dinps, .{});
                    worklist.add(st);
                    return st;
                }

                while (earlier.kind == .Store and
                    (earlier.cfg0() == node.cfg0() or node.cfg0() == null) and
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

            if (node.kind == .UnOp) {
                const op: UnOp = node.extra(.UnOp).*;
                const oper = inps[1].?;

                if (oper.kind == .CInt and node.data_type.isInt()) {
                    return self.addNode(.CInt, node.data_type, &.{null}, op.eval(oper.data_type, oper.extra(.CInt).*));
                }

                if (node.data_type.meet(inps[1].?.data_type) == inps[1].?.data_type) {
                    if (op == .uext or op == .sext) {
                        return inps[1];
                    }
                }
            }

            if (node.kind == .Phi) {
                _, const l, const r = .{ inps[0].?, inps[1].?, inps[2].? };

                if (l == r and !node.cfg0().?.base.preservesIdentityPhys()) {
                    return l;
                }

                if (r == node) {
                    return l;
                }
            }

            return if (comptime optApi("idealize", @TypeOf(idealize))) MachNode.idealize(self, node, worklist) else null;
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

            self.root.fmt(self.block_count, writer, colors);
            try writer.writeAll("\n");
            for (collectPostorder(self, tmp.arena.allocator(), &visited)) |p| {
                p.base.fmt(self.block_count, writer, colors);

                try writer.writeAll("\n");
                for (p.base.outputs()) |o| {
                    try writer.writeAll("  ");
                    o.fmt(self.instr_count, writer, colors);
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
