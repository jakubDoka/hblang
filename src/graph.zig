const std = @import("std");
const root = @import("utils.zig");

fn tu(int: i64) u64 {
    return @bitCast(int);
}

pub const BinOp = enum(u8) {
    iadd,
    isub,
    imul,
    udiv,
    sdiv,

    band,
    bor,

    ne,
    eq,
    ugt,
    sgt,
    ult,
    slt,
    uge,
    sge,
    ule,
    sle,

    pub fn eval(self: BinOp, lhs: i64, rhs: i64) i64 {
        return switch (self) {
            .iadd => lhs +% rhs,
            .isub => lhs -% rhs,
            .imul => lhs *% rhs,
            .udiv => @bitCast(tu(lhs) / tu(rhs)),
            .sdiv => @divFloor(lhs, rhs),

            .band => lhs & rhs,
            .bor => lhs | rhs,

            .ne => @intFromBool(lhs != rhs),
            .eq => @intFromBool(lhs == rhs),

            .ugt => @intFromBool(tu(lhs) > tu(rhs)),
            .ult => @intFromBool(tu(lhs) < tu(rhs)),
            .uge => @intFromBool(tu(lhs) >= tu(rhs)),
            .ule => @intFromBool(tu(lhs) <= tu(rhs)),

            .sgt => @intFromBool(lhs > rhs),
            .slt => @intFromBool(lhs < rhs),
            .sge => @intFromBool(lhs >= rhs),
            .sle => @intFromBool(lhs <= rhs),
        };
    }
};

pub const UnOp = enum(u8) {
    sext,
    uext,
    ired,
    neg,

    pub fn eval(self: UnOp, src: DataType, oper: i64) i64 {
        return switch (self) {
            .sext => switch (src) {
                .i8 => @as(i8, @truncate(oper)),
                .i16 => @as(i16, @truncate(oper)),
                .i32 => @as(i32, @truncate(oper)),
                else => unreachable,
            },
            .uext => switch (src) {
                .i8 => @as(u8, @truncate(tu(oper))),
                .i16 => @as(u16, @truncate(tu(oper))),
                .i32 => @as(u32, @truncate(tu(oper))),
                else => unreachable,
            },
            .ired => oper,
            .neg => -oper,
        };
    }
};

pub const DataType = enum(u16) {
    top,
    i8,
    i16,
    i32,
    int,
    bot,

    pub fn size(self: DataType) usize {
        return switch (self) {
            .top => 0,
            .i8 => 1,
            .i16 => 2,
            .i32 => 4,
            .int => 8,
            else => unreachable,
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

        if (self.isInt()) {
            std.debug.assert(other.isInt());
            return @enumFromInt(@max(@intFromEnum(self), @intFromEnum(other)));
        }

        unreachable;
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
    // [Cfg, ret]
    Return: Cfg,
    // [?Cfg]
    CInt: i64,
    // [?Cfg, lhs, rhs]
    BinOp: mod.BinOp,
    // [?Cfg, lhs, rhs]
    UnOp: mod.UnOp,
    // [?Cfg, Mem]
    Local: usize,
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
    If: Cfg,
    // [If]
    Then: Cfg,
    // [If]
    Else: Cfg,
    // [lCfg, rCfg]
    Region: Cfg,
    // [entryCfg, backCfg]
    Loop: Cfg,
    // [Cfg]
    Jmp: Cfg,
    // [Region, lhs, rhs]
    Phi,
    // [Cfg, inp]
    MachMove,

    pub const is_basic_block_start = .{ .Entry, .CallEnd, .Then, .Else, .Region, .Loop };
    pub const is_basic_block_end = .{ .Return, .Call, .If, .Jmp };
    pub const is_mem_op = .{ .Load, .MemCpy, .Local, .Store, .Return, .Call, .Mem };
    pub const is_pinned = .{ .Ret, .Phi, .Mem };
};

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
};
pub const Load = extern struct {};
pub const Store = extern struct {};
pub const MemCpy = extern struct {
    base: Store = .{},
};

const mod = @This();

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
        after_gcm: std.debug.SafetyLock = .{},

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
                if (node.id == std.math.maxInt(u16)) std.debug.panic("{} {any}\n", .{ node, node.inputs() });
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
                            cfg.base.inputs()[0].?.asCfg().?.idepth(),
                        ) + 1,
                        else => idepth(cfg.base.cfg0().?) + 1,
                    };
                    return extra.idepth;
                }

                pub fn findLca(left: *CfgNode, right: *CfgNode) *CfgNode {
                    var lc, var rc = .{ left, right };
                    while (lc != rc) {
                        if (!lc.base.isCfg()) std.debug.panic("{}", .{lc.base});
                        if (!rc.base.isCfg()) std.debug.panic("{}", .{rc.base});
                        const diff = @as(i64, idepth(lc)) - idepth(rc);
                        if (diff >= 0) lc = lc.base.cfg0().?;
                        if (diff <= 0) rc = rc.base.cfg0().?;
                    }
                    return lc;
                }

                pub fn idom(cfg: *CfgNode) *CfgNode {
                    return switch (cfg.base.kind) {
                        .Region => findLca(cfg.base.inputs()[0].?.asCfg().?, cfg.base.inputs()[1].?.asCfg().?),
                        else => cfg.base.cfg0().?,
                    };
                }

                pub fn better(cfg: *CfgNode, best: *CfgNode, to_sched: *Node) bool {
                    return idepth(cfg) > idepth(best) or
                        (cfg.base.kind == .Jmp and cfg.base.outputs()[0].kind == .Loop and to_sched.kind != .MachMove) or
                        best.base.isBasicBlockEnd();
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

            pub fn useBlock(self: *Node, use: *Node, scheds: []const ?*CfgNode) *CfgNode {
                if (use.kind == .Phi) {
                    std.debug.assert(use.inputs()[0].?.kind == .Region or use.inputs()[0].?.kind == .Loop);
                    for (use.inputs()[0].?.inputs(), use.inputs()[1..]) |b, u| {
                        if (u.? == self) {
                            return subclass(b.?, Cfg).?;
                        }
                    }
                }
                return scheds[use.id].?;
            }

            pub fn dataDeps(self: *Node) []?*Node {
                if ((self.kind == .Phi and !self.isDataPhi()) or self.kind == .Mem) return &.{};
                const start: usize = @intFromBool(self.isMemOp());
                return self.input_base[1 + start .. self.input_ordered_len];
            }

            pub fn anyextra(self: *const Node) *const anyopaque {
                const any: *const extern struct { n: Node, ex: u8 } = @ptrCast(self);
                return &any.ex;
            }

            pub fn format(self: *const Node, comptime _: anytype, _: anytype, writer: anytype) !void {
                const colors = .escape_codes;
                self.fmt(null, writer, colors);
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

                const utils = struct {
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
                            else => {
                                try writ.print("{}", .{ex.*});
                            },
                        }
                    }
                };

                switch (self.kind) {
                    inline else => |t| {
                        const ext = self.extraConst(t);
                        if (@TypeOf(ext.*) != void) {
                            if (comptime utils.isVisibel(@TypeOf(ext.*))) {
                                writer.writeAll(": ") catch unreachable;
                                add_colon_space = true;
                                utils.logExtra(writer, ext, true) catch unreachable;
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
                return self.kind == .Phi and self.inputs()[0] == on_loop and self.inputs()[2] == null;
            }

            pub fn inputs(self: *Node) []?*Node {
                return self.input_base[0..self.input_len];
            }

            pub fn kill(self: *Node) void {
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
                const ptr: *const LayoutFor(kind) = @ptrCast(self);
                return &ptr.ext;
            }

            pub fn extra(self: *Node, comptime kind: Kind) *ClassFor(kind) {
                std.debug.assert(self.kind == kind);
                const ptr: *LayoutFor(kind) = @ptrCast(self);
                return &ptr.ext;
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
                return self.kind == .Phi and (!self.input_base[1].?.isMemOp() or self.input_base[1].?.isLoad()) and (self.input_base[1].?.kind != .Phi or self.input_base[1].?.isDataPhi());
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

            pub fn hash(kind: Kind, inpts: []const ?*Node, extr: *const anyopaque) u64 {
                var hasher = std.hash.Fnv1a_64.init();
                hasher.update(@as(*const [2]u8, @ptrCast(&kind)));
                hasher.update(@as([*]const u8, @ptrCast(inpts.ptr))[0 .. inpts.len * @sizeOf(?*Node)]);
                hasher.update(@as([*]const u8, @ptrCast(extr))[0..size_map[@intFromEnum(kind)]]);
                return hasher.final();
            }

            pub fn cmp(
                akind: Kind,
                bkind: Kind,
                ainputs: []const ?*Node,
                binputs: []const ?*Node,
                aextra: *const anyopaque,
                bextra: *const anyopaque,
            ) bool {
                return akind == bkind and
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
            self.root = self.addNode(.Start, &.{}, .{});
            return self;
        }

        pub fn deinit(self: *Self) void {
            self.arena.deinit();
            self.* = undefined;
        }

        pub fn reset(self: *Self) void {
            std.debug.assert(self.arena.reset(.retain_capacity));
            self.next_id = 0;
            self.root = self.addNode(.Start, &.{}, .{});
            self.interner = .{};
            self.after_gcm = .{};
        }

        const Inserter = struct {
            kind: Kind,
            inputs: []const ?*Node,
            extra: *const anyopaque,

            pub fn hash(_: anytype, k: InternedNode) u64 {
                return k.hash;
            }

            pub fn eql(s: @This(), a: InternedNode, b: InternedNode) bool {
                if (a.hash != b.hash) return false;
                return Node.cmp(s.kind, b.node.kind, s.inputs, b.node.inputs(), s.extra, b.node.anyextra());
            }
        };

        const InsertMap = InternMap(Inserter);

        pub fn internNode(self: *Self, kind: Kind, inputs: []const ?*Node, extra: *const anyopaque) InsertMap.GetOrPutResult {
            const map: *InsertMap = @ptrCast(&self.interner);

            return map.getOrPutContext(self.arena.allocator(), .{
                .node = undefined,
                .hash = Node.hash(kind, inputs, extra),
            }, Inserter{ .kind = kind, .inputs = inputs, .extra = extra }) catch unreachable;
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
                std.debug.assert(self.interner.remove(.{ .node = node, .hash = Node.hash(node.kind, node.inputs(), node.anyextra()) }));
            }
        }

        pub fn reinternNode(self: *Self, node: *Node) ?*Node {
            if (Node.isInterned(node.kind, node.inputs())) {
                const entry = self.internNode(node.kind, node.inputs(), node.anyextra());

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

        pub fn addTypedNode(self: *Self, comptime kind: Kind, ty: DataType, inputs: []const ?*Node, extra: ClassFor(kind)) *Node {
            const node = self.addNode(kind, inputs, extra);
            node.data_type = ty;
            return node;
        }

        pub fn addNode(self: *Self, comptime kind: Kind, inputs: []const ?*Node, extra: ClassFor(kind)) *Node {
            const node = self.addNodeUntyped(kind, inputs, extra);
            if (kind == .Phi) node.data_type = node.inputs()[1].?.data_type;
            return node;
        }

        pub fn addNodeUntyped(self: *Self, kind: Kind, inputs: []const ?*Node, extra: anytype) *Node {
            if (Node.isInterned(kind, inputs)) {
                const entry = self.internNode(kind, inputs, &extra);
                if (!entry.found_existing) entry.key_ptr.node = self.addNodeNoIntern(kind, inputs, extra);
                return entry.key_ptr.node;
            } else {
                return self.addNodeNoIntern(kind, inputs, extra);
            }
        }

        pub fn addNodeNoIntern(self: *Self, kind: Kind, inputs: []const ?*Node, extra: anytype) *Node {
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
            for (self.arena.allocator().dupe(*Node, target.outputs()) catch unreachable) |use| {
                if (use.id == std.math.maxInt(u16)) continue;
                const index = std.mem.indexOfScalar(?*Node, use.inputs(), target) orelse {
                    std.debug.panic("{} {any} {}", .{ this, target.outputs(), use });
                };

                _ = self.setInput(use, index, this);
            }

            var iter = self.interner.iterator();
            while (iter.next()) |e| std.debug.assert(e.key_ptr.node.id != std.math.maxInt(u16));
        }

        pub fn subsume(self: *Self, this: *Node, target: *Node) void {
            self.subsumeNoKill(this, target);
            self.uninternNode(target);
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
            self.after_gcm.assertUnlocked();

            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            var worklist = WorkList.init(tmp.arena.allocator(), self.next_id) catch unreachable;
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

        pub fn gcm(self: *Self) void {
            self.after_gcm.lock();
            @import("gcm.zig").gcm(MachNode, self);
        }

        pub fn mem2reg(self: *Self) void {
            self.after_gcm.assertUnlocked();
            @import("mem2reg.zig").mem2reg(MachNode, self);
        }

        pub fn idealizeDead(self: *Self, node: *Node, worklist: *WorkList) ?*Node {
            const inps = node.inputs();

            var is_dead = node.kind == .Region and isDead(inps[0]) and isDead(inps[1]);
            is_dead = is_dead or (node.kind != .Start and node.kind != .Region and
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

                if (l == r) return l;

                if (r == node) return l;
            }

            return null;
        }

        pub fn idealize(self: *Self, node: *Node, worklist: *WorkList) ?*Node {
            if (node.data_type == .bot) return null;

            if (self.idealizeDead(node, worklist)) |w| return w;

            const inps = node.inputs();

            if (false and node.isStore()) {
                if (node.base().kind == .Local and node.cfg0() != null) {
                    const dinps = self.arena.allocator().dupe(?*Node, node.inputs()) catch unreachable;
                    dinps[0] = null;
                    const st = self.addNode(.Store, dinps, {});
                    worklist.add(st);
                    return st;
                }

                if (node.base().kind == .Local and node.outputs().len == 1 and node.outputs()[0].kind == .Return) {
                    return node.mem();
                }
            }

            if (false and node.kind == .Load) {
                var earlier = node.mem();

                if (node.base().kind == .Local and node.cfg0() != null) {
                    const ld = self.addNode(.Load, &.{ null, inps[1], inps[2] }, {});
                    worklist.add(ld);
                    return ld;
                }

                while (earlier.isStore() and
                    (earlier.cfg0() == node.cfg0() or node.cfg0() == null) and
                    noAlias(earlier.base(), node.base()))
                {
                    earlier = earlier.mem();
                }

                if (earlier.isStore() and
                    earlier.base() == node.base() and
                    earlier.data_type == node.data_type)
                {
                    return earlier.value();
                }

                if (earlier.kind == .Phi) {
                    std.debug.assert(earlier.inputs().len == 3);
                    var l, var r = .{ earlier.inputs()[1].?, earlier.inputs()[2].? };

                    while (l.isStore() and
                        (l.cfg0() == node.cfg0() or node.cfg0() == null) and
                        noAlias(l.base(), node.base()))
                    {
                        l = l.mem();
                    }

                    while (r.isStore() and
                        (r.cfg0() == node.cfg0() or node.cfg0() == null) and
                        noAlias(r.base(), node.base()))
                    {
                        r = r.mem();
                    }

                    if (l.isStore() and r.isStore() and
                        l.base() == r.base() and l.base() == node.base() and
                        l.data_type == r.data_type and l.data_type == node.data_type)
                    {
                        return self.addNode(.Phi, &.{ earlier.inputs()[0].?, l.value(), r.value() }, {});
                    }
                }

                if (earlier != node.mem()) {
                    return self.addNode(.Load, &.{ inps[0], earlier, inps[2] }, {});
                }
            }

            if (node.kind == .UnOp) {
                const op = node.extra(.UnOp).*;
                if (node.data_type.meet(inps[1].?.data_type) == inps[1].?.data_type) {
                    if (op == .uext or op == .sext) {
                        return inps[1];
                    }
                }
            }

            if (node.kind == .Phi) {
                _, const l, const r = .{ inps[0].?, inps[1].?, inps[2].? };

                if (l == r) return l;

                if (r == node) return l;
            }

            return if (comptime optApi("idealize", @TypeOf(idealize))) MachNode.idealize(self, node, worklist) else null;
        }

        pub fn noAlias(lbase: *Node, rbase: *Node) bool {
            if (lbase.kind == .Local and rbase.kind == .Local) return lbase != rbase;
            if (lbase.kind == .Local and rbase.kind == .Arg) return true;
            if (lbase.kind == .Arg and rbase.kind == .Local) return true;
            return false;
        }

        pub fn logNid(wr: anytype, nid: usize, cc: std.io.tty.Config) void {
            cc.setColor(wr, @enumFromInt(1 + nid % 15)) catch unreachable;
            wr.print("%{d}", .{nid}) catch unreachable;
            cc.setColor(wr, .reset) catch unreachable;
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
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            var visited = std.DynamicBitSet.initEmpty(tmp.arena.allocator(), self.next_id) catch unreachable;

            self.root.fmt(self.block_count, writer, colors);
            writer.writeAll("\n") catch unreachable;
            for (collectPostorder(self, tmp.arena.allocator(), &visited)) |p| {
                p.base.fmt(self.block_count, writer, colors);

                writer.writeAll("\n") catch unreachable;
                for (p.base.outputs()) |o| {
                    writer.writeAll("  ") catch unreachable;
                    o.fmt(self.instr_count, writer, colors);
                    writer.writeAll("\n") catch unreachable;
                }
            }
        }

        pub fn fmtUnscheduled(self: *Self, writer: anytype, colors: std.io.tty.Config) void {
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            var worklist = Self.WorkList.init(tmp.arena.allocator(), self.next_id) catch unreachable;

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
