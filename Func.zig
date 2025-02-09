arena: std.heap.ArenaAllocator,
tmp_arena: std.heap.ArenaAllocator,
interner: std.hash_map.HashMapUnmanaged(InternedNode, void, void, 70) = .{},
next_id: u16 = 0,
block_count: u16 = undefined,
instr_count: u16 = undefined,
root: *Node = undefined,
end: *Node = undefined,

pub const InternedNode = struct {
    hash: u64,
    node: *Node,
};

const std = @import("std");
const Lexer = @import("Lexer.zig");
const Types = @import("Types.zig");
const Func = @This();

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
        std.debug.assert(node.id != std.math.maxInt(u16));
        if (self.in_list.isSet(node.id)) return;
        self.in_list.set(node.id);
        self.list.appendAssumeCapacity(node);
    }

    pub fn pop(self: *WorkList) ?*Node {
        var node = self.list.popOrNull() orelse return null;
        while (node.id == std.math.maxInt(u16)) {
            node = self.list.popOrNull() orelse return null;
        }
        self.in_list.unset(node.id);
        return node;
    }
};

pub const DataType = enum(u16) {
    void,
    mem,
    dead,
};

pub const Node = extern struct {
    kind: NodeKind,
    id: u16,
    schedule: u16 = undefined,
    data_type: DataType = .void,

    input_ordered_len: u16,
    input_len: u16,
    output_len: u16 = 0,
    output_cap: u16 = 0,

    input_base: [*]?*Node,
    output_base: [*]*Node,

    const User = packed struct(usize) {
        pointer: usize,

        pub fn node(self: User) *Node {
            return @ptrFromInt(self.pointer);
        }
    };

    pub fn anyextra(self: *const Node) *const anyopaque {
        const any: *const extern struct { n: Node, ex: u8 } = @ptrCast(self);
        return &any.ex;
    }

    pub fn format(self: *const Node, comptime _: anytype, _: anytype, writer: anytype) !void {
        const colors = .escape_codes;

        @import("HbvmGen.zig").gcm.fmt(self, null, writer, colors);
    }

    pub fn mem(self: *Node) *Node {
        std.debug.assert(self.kind == .Load or self.kind == .Store);
        return self.inputs()[1].?;
    }

    pub fn base(self: *Node) *Node {
        std.debug.assert(self.kind == .Load or self.kind == .Store);
        return self.inputs()[2].?;
    }

    pub fn isLazyPhi(self: *Node, on_loop: *Node) bool {
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

    pub fn removeUse(self: *Node, use: *Node) void {
        const outs = self.outputs();
        const index = std.mem.indexOfScalar(*Node, outs, use).?;
        std.mem.swap(*Node, &outs[index], &outs[outs.len - 1]);
        self.output_len -= 1;
    }

    pub fn outputs(self: *Node) []*Node {
        return self.output_base[0..self.output_len];
    }

    pub fn extraConst(self: *const Node, comptime kind: BuiltinNodeKind) *const ExtFor(kind) {
        std.debug.assert(self.kind == toKind(kind));
        const ptr: *const LayoutFor(kind) = @ptrCast(self);
        return &ptr.extra;
    }

    pub fn extra(self: *Node, comptime kind: BuiltinNodeKind) *ExtFor(kind) {
        std.debug.assert(self.kind == toKind(kind));
        const ptr: *LayoutFor(kind) = @ptrCast(self);
        return &ptr.extra;
    }

    pub fn subclass(self: *Node, comptime Ext: type) ?*SubclassFor(Ext) {
        switch (toBuiltinKind(self.kind) orelse return null) {
            inline else => |t| if (comptime isSubbclass(ExtFor(t), Ext)) {
                return @ptrCast(self);
            },
        }

        return null;
    }

    pub fn isSubbclass(Full: type, Sub: type) bool {
        var Cursor = Full;
        while (true) {
            if (Cursor == Sub) return true;
            if (@typeInfo(Cursor) != .@"struct" or !@hasField(Cursor, "base")) return false;
            Cursor = @TypeOf(@as(Cursor, undefined).base);
        }
    }

    pub fn cfg0(self: *Node) ?*SubclassFor(Extra.Cfg) {
        if (self.kind == .Start) return self.subclass(Extra.Cfg);
        return (self.inputs()[0] orelse return null).subclass(Extra.Cfg);
    }

    pub fn useBlock(self: *Node, use: *Node, scheds: []const ?*CfgNode) *CfgNode {
        if (use.kind == .Phi) {
            std.debug.assert(use.inputs()[0].?.kind == .Region or use.inputs()[0].?.kind == .Loop);
            for (use.inputs()[0].?.inputs(), use.inputs()[1..]) |b, u| {
                if (u.? == self) {
                    return b.?.subclass(Extra.Cfg).?;
                }
            }
        }
        return scheds[use.id].?;
    }
};

pub const CfgNode = SubclassFor(Extra.Cfg);

pub const Extra = union(enum(u16)) {
    Start: Cfg,
    // [Start]
    Arg: usize,
    // [Start]
    Entry: Cfg,
    // [Start]
    Mem: void,
    // [Cfg, ret]
    Return: Cfg,
    // [?Cfg]
    CInt: i64,
    // [?Cfg, lhs, rhs]
    BinOp: Lexer.Lexeme,
    // [?Cfg, Mem]
    Local: usize,
    // [?Cfg, thread, ptr]
    Load,
    // [?Cfg, thread, ptr, value, ...antideps]
    Store,
    // [Cfg, ..args]
    Call: extern struct {
        base: Cfg = .{},
        id: Types.Func,
    },
    // [Call]
    CallEnd: Cfg,
    // [CallEnd]
    Ret: void,
    // [Cfg, cond],
    If: extern struct {
        base: Cfg = .{},
        swapped: bool = false,
    },
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

    pub const Cfg = extern struct {
        idepth: u16 = 0,
        antidep: u16 = 0,
    };

    pub fn isInterned(kind: BuiltinNodeKind) bool {
        return switch (kind) {
            .CInt, .BinOp, .Load => true,
            else => false,
        };
    }
};

pub const BuiltinNodeKind = std.meta.Tag(Extra);

pub const NodeKind = b: {
    var enm = @typeInfo(BuiltinNodeKind);
    enm.@"enum".is_exhaustive = false;
    break :b @Type(enm);
};

pub fn ExtFor(comptime kind: BuiltinNodeKind) type {
    return @typeInfo(Extra).@"union".fields[@intFromEnum(kind)].type;
}

fn LayoutFor(comptime kind: BuiltinNodeKind) type {
    return extern struct {
        base: Node,
        extra: ExtFor(kind),
    };
}

fn SubclassFor(comptime Ext: type) type {
    return extern struct {
        base: Node,
        extra: Ext,
    };
}

pub fn toKind(kind: anytype) NodeKind {
    return @enumFromInt(@intFromEnum(kind));
}

pub fn toBuiltinKind(kind: NodeKind) ?BuiltinNodeKind {
    if (@typeInfo(BuiltinNodeKind).@"enum".fields.len > @intFromEnum(kind)) {
        return @enumFromInt(@intFromEnum(kind));
    }

    return null;
}

pub fn init(gpa: std.mem.Allocator) Func {
    var self = Func{
        .arena = .init(gpa),
        .tmp_arena = .init(gpa),
    };
    self.root = self.addNode(.Start, &.{}, .{});
    return self;
}

pub fn deinit(self: *Func) void {
    self.arena.deinit();
    self.tmp_arena.deinit();
    self.* = undefined;
}

pub fn reset(self: *Func) void {
    std.debug.assert(self.arena.reset(.free_all));
    self.next_id = 0;
    self.root = self.addNode(.Start, &.{}, .{});
    self.interner = .{};
}

pub fn TagPayloadOfLinear(comptime Union: type, comptime tag: std.meta.Tag(Union)) type {
    const base = @typeInfo(@TypeOf(tag)).@"enum".fields[0].value;
    return @typeInfo(Union).@"union".fields[@intFromEnum(tag) - base].type;
}

pub fn hashNode(comptime Enum: type, kind: std.meta.Tag(Enum), inputs: []const ?*Node, extra: *const anyopaque) u64 {
    var hasher = std.hash.Fnv1a_64.init();

    hasher.update(@as(*const [2]u8, @ptrCast(&kind)));
    hasher.update(@as([*]const u8, @ptrCast(inputs.ptr))[0 .. inputs.len * @sizeOf(?*Node)]);

    switch (kind) {
        inline else => |k| {
            const ext: *const TagPayloadOfLinear(Enum, k) = @alignCast(@ptrCast(extra));
            hasher.update(std.mem.asBytes(ext));
        },
    }

    return hasher.final();
}

pub fn cmpNode(
    comptime Enum: type,
    akind: std.meta.Tag(Enum),
    bkind: std.meta.Tag(Enum),
    ainputs: []const ?*Node,
    binputs: []const ?*Node,
    aextra: *const anyopaque,
    bextra: *const anyopaque,
) bool {
    if (akind != bkind) return false;

    if (!std.mem.eql(?*Node, ainputs, binputs)) return false;

    switch (akind) {
        inline else => |k| {
            const aext: *const TagPayloadOfLinear(Enum, k) = @alignCast(@ptrCast(aextra));
            const bext: *const TagPayloadOfLinear(Enum, k) = @alignCast(@ptrCast(bextra));
            return std.meta.eql(aext.*, bext.*);
        },
    }
}

pub fn addNode(self: *Func, comptime kind: BuiltinNodeKind, inputs: []const ?*Node, extra: ExtFor(kind)) *Node {
    return self.addMachNode(Extra, kind, inputs, extra);
}

pub fn addMachNode(
    self: *Func,
    comptime Mach: type,
    comptime kind: std.meta.Tag(Mach),
    inputs: []const ?*Node,
    extra: TagPayloadOfLinear(Mach, kind),
) *Node {
    return self.addMachNodeLow(Mach, kind, inputs, extra);
}

pub fn addMachNodeLow(self: *Func, comptime Enum: type, kind: std.meta.Tag(Enum), inputs: []const ?*Node, extra: anytype) *Node {
    if (@hasDecl(Enum, "isInterned") and Enum.isInterned(kind)) {
        const Inserter = struct {
            kind: @TypeOf(kind),
            inputs: []const ?*Node,
            extra: *const anyopaque,

            pub fn hash(_: anytype, k: InternedNode) u64 {
                return k.hash;
            }

            pub fn eql(s: @This(), a: InternedNode, b: InternedNode) bool {
                if (a.hash != b.hash) return false;
                return cmpNode(Enum, s.kind, toBuiltinKind(b.node.kind) orelse return false, s.inputs, b.node.inputs(), s.extra, b.node.anyextra());
            }
        };

        const map: *std.hash_map.HashMapUnmanaged(InternedNode, void, Inserter, 70) = @ptrCast(&self.interner);

        const entry = map.getOrPutContext(self.arena.allocator(), .{
            .node = undefined,
            .hash = hashNode(Enum, kind, inputs, &extra),
        }, Inserter{ .kind = kind, .inputs = inputs, .extra = &extra }) catch unreachable;

        if (!entry.found_existing) entry.key_ptr.node = self.addNodeLow(toKind(kind), inputs, extra);
        return entry.key_ptr.node;
    } else {
        return self.addNodeLow(toKind(kind), inputs, extra);
    }
}

pub fn addNodeLow(self: *Func, kind: NodeKind, inputs: []const ?*Node, extra: anytype) *Node {
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
            .output_base = (self.arena.allocator().alloc(*Node, 0) catch unreachable).ptr,
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
    return node == null or node.?.data_type == .dead;
}

pub fn subsume(self: *Func, this: *Node, target: *Node) void {
    for (target.outputs()) |use| {
        const index = std.mem.indexOfScalar(?*Node, use.inputs(), target) orelse {
            std.debug.panic("{} {any} {}", .{ this, target.outputs(), use });
        };

        use.inputs()[index] = this;
        self.addUse(this, use);
    }

    target.output_len = 0;
    target.kill();
}

pub fn setInput(self: *Func, use: *Node, idx: usize, def: ?*Node) void {
    if (use.inputs()[idx] == def) return;
    if (use.inputs()[idx]) |n| {
        n.removeUse(use);
    }

    use.inputs()[idx] = def;
    if (def) |d| {
        self.addUse(d, use);
    }
}

pub fn addDep(self: *Func, use: *Node, def: *Node) void {
    if (use.input_ordered_len == use.input_len) {
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

pub fn addUse(self: *Func, def: *Node, use: *Node) void {
    if (def.output_len == def.output_cap) {
        const new_cap = @max(def.output_cap, 1) * 2;
        const new_outputs = self.arena.allocator().realloc(def.outputs(), new_cap) catch unreachable;
        def.output_base = new_outputs.ptr;
        def.output_cap = new_cap;
    }

    def.output_base[def.output_len] = use;
    def.output_len += 1;
}

pub inline fn beginTmpAlloc(self: *Func) std.mem.Allocator {
    std.debug.assert(self.tmp_arena.reset(.retain_capacity));
    return self.tmp_arena.allocator();
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

pub fn logNid(wr: anytype, nid: usize, cc: std.io.tty.Config) void {
    cc.setColor(wr, @enumFromInt(1 + nid % 15)) catch unreachable;
    wr.print("%{d}", .{nid}) catch unreachable;
    cc.setColor(wr, .reset) catch unreachable;
}

pub fn todo(comptime variant: anytype, comptime message: []const u8) void {
    if (@hasField(Extra, @tagName(variant))) @compileError(message);
}
