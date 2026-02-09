func: Func,
scope: ?*Func.Node = undefined,
root_mem: *Func.Node = undefined,

pub const max_func_id = graph.indirect_call - 1;

const std = @import("std");
const utils = graph.utils;
const graph = @import("graph.zig");
const Builder = @This();

const Func = graph.Func(Builder);
pub const i_know_the_api = {};
pub const BuildNode = Func.Node;
pub const Kind = Func.Kind;

pub const DataType = graph.DataType;
pub const BinOp = graph.BinOp;
pub const UnOp = graph.UnOp;
pub const classes = enum {
    // [Cfg, mem, ...values]
    pub const Scope = extern struct {};

    pub const Stub = extern struct {};
};

pub fn isKillable(self: *BuildNode) bool {
    return self.kind != .Scope;
}

pub fn SpecificNode(comptime _: Kind) type {
    return *BuildNode;
}

pub fn init(gpa: std.mem.Allocator) Builder {
    return .{ .func = .init(gpa) };
}

pub fn deinit(self: *Builder) void {
    self.func.deinit();
    self.* = undefined;
}

pub const Signature = struct {
    scratch: *utils.Arena,
    cc: graph.CallConv,
    abi_params: std.ArrayList(graph.AbiParam) = .empty,
    ccbl: graph.CcBuilder = .{},

    pub fn addParam(
        self: *Signature,
        bl: *Builder,
        sloc: graph.Sloc,
        abi: graph.AbiParam,
        debug_ty: u32,
    ) *BuildNode {
        const node = switch (abi) {
            .Reg => |r| b: {
                const ab = self.ccbl.handleReg(self.cc, r);
                if (ab == .Stack) {
                    return self.addParam(bl, sloc, ab, debug_ty);
                }

                break :b bl.func.addNode(
                    .Arg,
                    sloc,
                    r,
                    &.{bl.func.start},
                    .{ .index = self.abi_params.items.len },
                );
            },
            .Stack => |s| bl.addLocalWithMeta(sloc, .{
                .kind = .parameter,
                .index = @intCast(self.abi_params.items.len),
            }, s.size, debug_ty),
        };

        self.abi_params.append(self.scratch.allocator(), abi) catch unreachable;

        return node;
    }

    pub fn end(self: *Signature, bl: *Builder, rets: ?[]const graph.AbiParam) void {
        var rts = rets;
        if (rts) |r| if (r.len == 1 and r[0] == .Stack or r.len == 2 and self.cc == .systemv) {
            rts = &.{};
        };
        bl.func.signature = .init(self.cc, self.abi_params.items, rts, bl.arena());
        self.* = undefined;
    }
};

pub const BuildToken = enum { @"please call Builder.begin() first, then Builder.end()" };

/// Begins a build of a function, returns a token to end the build body building.
/// the `params` and `returns` are copied
pub fn begin(
    self: *Builder,
    call_conv: graph.CallConv,
    scratch: *utils.Arena,
) struct { Signature, BuildToken } {
    const ctrl = self.func.addNode(.Entry, .none, .top, &.{self.func.start}, .{});
    self.root_mem = self.func.addNode(.Mem, .none, .top, &.{self.func.start}, .{});
    _ = self.func.addNode(.Syms, .none, .top, &.{self.func.start}, .{});
    self.scope = self.func.addNode(.Scope, .none, .top, &.{ ctrl, self.root_mem }, .{});
    self.func.end = self.func.addNode(.Return, .none, .top, &.{ null, null, null }, .{});

    return .{ .{ .cc = call_conv, .scratch = scratch }, @enumFromInt(0) };
}

pub fn arena(self: *Builder) std.mem.Allocator {
    return self.func.arena.allocator();
}

pub fn end(self: *Builder, _: BuildToken) void {
    if (!self.isUnreachable()) self.addReturn(&.{});

    if (std.debug.runtime_safety) {
        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        var worklist = Func.WorkList.init(tmp.arena.allocator(), self.func.next_id) catch unreachable;
        worklist.collectAll(&self.func);

        for (worklist.items()) |node| {
            std.debug.assert(node.kind != .Scope);
            std.debug.assert(node.kind != .Stub);
            if (node.isLocked()) {
                std.debug.dumpStackTrace(node.lock_at.trace);
                utils.panic("{f}\n", .{node});
            }
        }
    }
}

pub fn peep(self: *Builder, node: *BuildNode) *BuildNode {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var wl = Func.WorkList.init(tmp.arena.allocator(), 0) catch unreachable;
    const res = Func.idealize(self, &self.func, node, &wl) orelse return node;

    self.func.subsume(res, node, .intern);

    return res;
}

// #MEM ========================================================================

pub fn addLocal(self: *Builder, sloc: graph.Sloc, size: u64, debug_ty: u32) SpecificNode(.Local) {
    return self.addLocalWithMeta(sloc, .{ .kind = .variable, .index = undefined }, size, debug_ty);
}

pub fn addLocalWithMeta(self: *Builder, sloc: graph.Sloc, meta: graph.LocalMeta, size: u64, debug_ty: u32) SpecificNode(.Local) {
    const alloc = self.func.addNode(.LocalAlloc, sloc, .i64, &.{self.root_mem}, .{
        .size = size,
        .meta = meta,
        .debug_ty = debug_ty,
    });
    return self.func.addNode(.Local, sloc, .i64, &.{ null, alloc }, .{});
}

pub fn resizeLocal(_: *Builder, here: SpecificNode(.Local), to_size: u64, debug_ty: u32) void {
    std.debug.assert(here.inputs()[1].?.extra(.LocalAlloc).size == 0);
    here.inputs()[1].?.extra(.LocalAlloc).size = to_size;
    here.inputs()[1].?.extra(.LocalAlloc).debug_ty = debug_ty;
}

pub fn addLoad(self: *Builder, sloc: graph.Sloc, addr: *BuildNode, ty: DataType) SpecificNode(.Store) {
    const true_base, _ = addr.knownOffset();
    //std.debug.assert(true_base.kind != .Local or (offset >= 0 and
    //    @as(u64, @intCast(offset)) + ty.size() < true_base.inputs()[1].?.extra(.LocalAlloc).size));
    const ctrl = if (true_base.kind == .Local or true_base.kind == .GlobalAddr) null else self.control();
    return self.func.addNode(.Load, sloc, ty, &.{ ctrl, self.memory(), addr }, .{});
}

pub fn addFieldLoad(self: *Builder, sloc: graph.Sloc, base: *BuildNode, offset: i64, ty: DataType) *BuildNode {
    return self.addLoad(sloc, self.addFieldOffset(sloc, base, offset), ty);
}

pub fn addBitIndexLoad(
    self: *Builder,
    sloc: graph.Sloc,
    base: *Func.Node,
    subscript: *Func.Node,
    ty: DataType,
) *BuildNode {
    std.debug.assert(base.data_type.isInt());
    std.debug.assert(ty.isInt());

    const elem_size_imm = self.addIntImm(sloc, base.data_type, ty.size());
    const index = self.addBinOp(sloc, .imul, base.data_type, subscript, elem_size_imm);
    const shift = self.addBinOp(sloc, .ushr, base.data_type, base, index);
    const red = self.addUnOp(sloc, .ired, ty, shift);

    return red;
}

pub fn addBitFieldLoad(self: *Builder, sloc: graph.Sloc, base: *BuildNode, offset: i64, ty: DataType) *BuildNode {
    std.debug.assert(base.data_type.isInt());
    std.debug.assert(ty.isInt());

    if (base.data_type == ty) {
        std.debug.assert(offset == 0);
        return base;
    }

    const shift_amount = self.addIntImm(sloc, base.data_type, offset * 8);
    const shift = self.addBinOp(sloc, .ushr, base.data_type, base, shift_amount);
    const red = self.addUnOp(sloc, .ired, ty, shift);

    return red;
}

pub fn addStore(self: *Builder, sloc: graph.Sloc, addr: *BuildNode, ty: DataType, value: *BuildNode) void {
    addr.assertAlive();
    value.assertAlive();

    if (value.data_type == .bot) return;
    if (value.data_type.size() == 0) utils.panic("{f}", .{value.data_type});
    const mem = self.memory();
    const ctrl = self.control();
    const store = self.func.addNode(.Store, sloc, ty, &.{ ctrl, mem, addr, value }, .{});
    self.func.setInputNoIntern(self.scope orelse return, 1, store);
}

pub fn addFieldStore(
    self: *Builder,
    sloc: graph.Sloc,
    base: *BuildNode,
    offset: i64,
    ty: DataType,
    value: *BuildNode,
) void {
    _ = self.addStore(sloc, self.addFieldOffset(sloc, base, offset), ty, value);
}

pub fn addSpill(self: *Builder, sloc: graph.Sloc, value: *BuildNode, debug_ty: u32) SpecificNode(.Local) {
    const local = self.addLocal(sloc, value.data_type.size(), debug_ty);
    _ = self.addStore(sloc, local, value.data_type, value);
    return local;
}

pub fn addFixedMemCpy(self: *Builder, sloc: graph.Sloc, dst: *BuildNode, src: *BuildNode, size: u64) void {
    if (src == dst) return;

    const mem = self.memory();
    const ctrl = self.control();
    const siz = self.addIntImm(sloc, .i64, @bitCast(size));
    const mcpy = self.func.addNode(.MemCpy, sloc, .top, &.{ ctrl, mem, dst, src, siz }, .{});
    self.func.setInputNoIntern(self.scope orelse return, 1, mcpy);
}

pub fn addFieldOffset(self: *Builder, sloc: graph.Sloc, base: *BuildNode, offset: i64) *BuildNode {
    return self.func.addFieldOffset(sloc, base, offset);
}

pub fn addGlobalAddr(self: *Builder, sloc: graph.Sloc, arbitrary_global_id: u32) SpecificNode(.GlobalAddr) {
    std.debug.assert(arbitrary_global_id != 0xaaaaaaaa);
    return self.func.addGlobalAddr(sloc, arbitrary_global_id);
}

pub fn addFuncAddr(self: *Builder, sloc: graph.Sloc, arbitrary_func_id: u32) SpecificNode(.FuncAddr) {
    return self.func.addFuncAddr(sloc, arbitrary_func_id);
}

// #MATH =======================================================================

pub fn addCast(self: *Builder, sloc: graph.Sloc, to: DataType, value: *BuildNode) SpecificNode(.UnOp) {
    return self.func.addCast(sloc, to, value);
}

pub fn addFramePointer(self: *Builder, sloc: graph.Sloc, as: DataType) SpecificNode(.FramePointer) {
    return self.func.addNode(.FramePointer, sloc, as, &.{null}, .{});
}

pub fn addIndexOffset(
    self: *Builder,
    sloc: graph.Sloc,
    base: *BuildNode,
    op: Func.OffsetDirection,
    elem_size: u64,
    subscript: *BuildNode,
) SpecificNode(.BinOp) {
    return self.func.addIndexOffset(sloc, base, op, elem_size, subscript);
}

pub fn addUninit(self: *Builder, sloc: graph.Sloc, ty: DataType) SpecificNode(.CInt) {
    return self.func.addUninit(sloc, ty);
}

pub fn addIntImm(self: *Builder, sloc: graph.Sloc, ty: DataType, value: i64) SpecificNode(.CInt) {
    return self.func.addIntImm(sloc, ty, value);
}

pub fn addBinOp(self: *Builder, sloc: graph.Sloc, op: BinOp, ty: DataType, lhs: *BuildNode, rhs: *BuildNode) SpecificNode(.BinOp) {
    return self.func.addBinOp(sloc, op, ty, lhs, rhs);
}

pub fn addUnOp(self: *Builder, sloc: graph.Sloc, op: UnOp, ty: DataType, oper: *BuildNode) SpecificNode(.BinOp) {
    return self.func.addUnOp(sloc, op, ty, oper);
}

// #SCOPE ======================================================================

pub fn memory(self: *Builder) ?*Func.Node {
    return self._readScopeValue(1);
}

pub fn control(self: *Builder) ?*Func.Node {
    return getScopeValues(self.scope orelse return null)[0];
}

pub const scope_value_start = 2;

pub const Pins = struct {
    scope: *BuildNode,

    pub fn push(self: Pins, bl: *Builder, value: *BuildNode) u16 {
        return bl.pushToScope(self.scope, value);
    }

    pub fn getValue(self: Pins, index: usize) *Func.Node {
        return getScopeValues(self.scope)[index];
    }

    pub fn pop(self: Pins, bl: *Builder) *Func.Node {
        const value = self.getValue(self.scope.input_ordered_len - 1);
        bl._truncateScope(self.scope, self.scope.input_ordered_len - 1);
        return value;
    }

    pub fn truncate(self: Pins, bl: *Builder, back_to: usize) void {
        bl._truncateScope(self.scope, back_to);
    }

    pub fn deinit(self: Pins, bl: *Builder) void {
        killScope(&bl.func, self.scope);
    }

    pub fn len(self: Pins) usize {
        return getScopeValues(self.scope).len;
    }

    pub fn set(self: Pins, bl: *Builder, idx: usize, value: *BuildNode) void {
        bl.func.setInputNoIntern(self.scope, idx, value);
    }
};

pub fn addPins(self: *Builder) Pins {
    return .{ .scope = self.func.addNode(.Scope, .none, .top, &.{}, .{}) };
}

pub fn pushScopeValue(self: *Builder, value: *BuildNode) u16 {
    return self.pushToScope(self.scope orelse return 0, value) - scope_value_start;
}

pub fn setScopeValue(self: *Builder, index: usize, value: *BuildNode) void {
    self.func.setInputNoIntern(self.scope orelse return, scope_value_start + index, value);
}

fn pushToScopeFn(self: *Func, scope: *Func.Node, value: *Func.Node) u16 {
    if (scope.input_ordered_len == scope.input_len) {
        const new_cap = @max(1, scope.input_len) * 2;
        const new_alloc = self.arena.allocator().realloc(
            scope.input_base[0..scope.input_len],
            new_cap,
        ) catch unreachable;
        @memset(new_alloc[scope.input_len..], null);
        scope.input_base = new_alloc.ptr;
        scope.input_len = @intCast(new_alloc.len);
    }

    scope.input_base[scope.input_ordered_len] = value;
    self.addUse(value, scope.input_ordered_len, scope);
    scope.input_ordered_len += 1;
    return scope.input_ordered_len - 1;
}

fn pushToScope(self: *Builder, scope: *BuildNode, value: *BuildNode) u16 {
    return pushToScopeFn(&self.func, scope, value);
}

pub fn getScopeValue(self: *Builder, index: usize) *Func.Node {
    return self._readScopeValue(scope_value_start + index) orelse self.addStub(.none, .top);
}

pub fn getScopeValues(scope: SpecificNode(.Scope)) []*BuildNode {
    std.debug.assert(scope.kind == .Scope);
    for (scope.input_base[0..scope.input_ordered_len]) |e| std.debug.assert(e != null);
    return @ptrCast(scope.input_base[0..scope.input_ordered_len]);
}

pub fn _readScopeValue(self: *Builder, index: usize) ?*Func.Node {
    return getScopeValueMulty(&self.func, self.scope orelse return null, index);
}

pub fn getScopeValueMulty(func: *Func, scope: *BuildNode, index: usize) *Func.Node {
    const values = getScopeValues(scope);
    return switch (values[index].kind) {
        .Scope => {
            const loop = values[index];
            const initVal = getScopeValueMulty(func, loop, index);
            const items = getScopeValues(loop);
            if (!items[index].isLazyPhi(items[0])) {
                const phi = func.addNode(.Phi, initVal.sloc, initVal.data_type, &.{ items[0], initVal, null }, .{});
                std.debug.assert(phi.isLazyPhi(items[0]));
                func.setInputNoIntern(loop, index, phi);
            }

            func.setInputNoIntern(scope, index, items[index]);
            return values[index];
        },
        else => values[index],
    };
}

pub fn mergeScopes(
    func: *Func,
    lhs: SpecificNode(.Scope),
    rhs: SpecificNode(.Scope),
) SpecificNode(.Scope) {
    var lhs_values = getScopeValues(lhs);
    var rhs_values = getScopeValues(rhs);

    const relevant_size = @max(lhs_values.len, rhs_values.len);

    for (lhs_values.len..relevant_size) |i| {
        const other = rhs_values[i];
        _ = pushToScopeFn(func, lhs, func.addUninit(other.sloc, other.data_type));
    }

    for (rhs_values.len..relevant_size) |i| {
        const other = lhs_values[i];
        _ = pushToScopeFn(func, rhs, func.addUninit(other.sloc, other.data_type));
    }

    lhs_values = getScopeValues(lhs);
    rhs_values = getScopeValues(rhs);

    const new_ctrl = func.addNode(.Region, .none, .top, &.{ lhs_values[0], rhs_values[0] }, .{});

    const start = 1;
    for (lhs_values[start..relevant_size], rhs_values[start..relevant_size], start..) |lh, rh, i| {
        if (lh == rh) continue;
        const thn = getScopeValueMulty(func, lhs, i);
        const els = getScopeValueMulty(func, rhs, i);
        const phi = func.addNode(.Phi, thn.sloc, thn.data_type.meet(els.data_type), &.{ new_ctrl, thn, els }, .{});
        func.setInputNoIntern(rhs, i, phi);
    }

    func.setInputNoIntern(rhs, 0, new_ctrl);
    killScope(func, lhs);

    return rhs;
}

pub fn cloneScope(self: *Builder) SpecificNode(.Scope) {
    const values = getScopeValues(self.scope orelse return self.func.addNode(.Scope, .none, .top, &.{}, .{}));
    return self.func.addNode(.Scope, .none, .top, values, .{});
}

pub inline fn truncateScope(self: *Builder, back_to: usize) void {
    self._truncateScope(self.scope orelse return, scope_value_start + back_to);
}

pub fn scopeSize(self: *Builder) u16 {
    return (self.scope orelse return 0).input_ordered_len - scope_value_start;
}

pub fn _truncateScope(self: *Builder, scope: SpecificNode(.Scope), back_to: usize) void {
    while (scope.input_ordered_len > back_to) {
        scope.input_ordered_len -= 1;
        self.func.setInputNoIntern(scope, scope.input_ordered_len, null);
    }
}

pub fn killScope(func: *Func, scope: SpecificNode(.Scope)) void {
    scope.input_len = scope.input_ordered_len;
    func.kill(scope);
}

// #CONTROL ====================================================================

pub fn returns(self: *Builder) bool {
    return self.func.end.inputs()[0] != null;
}

pub fn isUnreachable(self: *Builder) bool {
    return self.scope == null;
}

pub const If = struct {
    if_node: *BuildNode,
    saved_branch: union {
        else_: SpecificNode(.Scope),
        then: ?SpecificNode(.Scope),
    },

    const EndToken = enum { @"please call IfBuilder.beginElse() first, then IfBuilder.end()" };

    pub fn beginElse(self: *If, builder: *Builder) EndToken {
        const then = builder.scope;
        if (self.saved_branch.else_.inputs().len == 0) {
            self.saved_branch = .{ .then = null };
            return @enumFromInt(0);
        }
        builder.scope = self.saved_branch.else_;
        self.saved_branch = .{ .then = then };
        builder.func.setInputNoIntern(
            builder.scope.?,
            0,
            builder.func.addNode(.Else, .none, .top, &.{self.if_node}, .{}),
        );
        return @enumFromInt(0);
    }

    pub fn end(self: *If, builder: *Builder, _: EndToken) void {
        const then = self.saved_branch.then orelse return;
        const else_ = builder.scope orelse {
            builder.scope = then;
            return;
        };
        builder.scope = mergeScopes(&builder.func, then, else_);
        self.* = undefined;
        return;
    }
};

pub fn addIfAndBeginThen(self: *Builder, sloc: graph.Sloc, cond: *BuildNode) If {
    const else_ = self.cloneScope();

    const builder_scope = self.scope orelse {
        return .{
            .if_node = self.func.addNode(.If, sloc, .top, &.{}, .{ .id = 0 }),
            .saved_branch = .{ .else_ = else_ },
        };
    };

    const if_node = self.func.addNode(.If, sloc, .top, &.{ self.control(), cond }, .{ .id = 0 });
    self.func.setInputNoIntern(builder_scope, 0, self.func.addNode(.Then, .none, .top, &.{if_node}, .{}));
    return .{
        .if_node = if_node,
        .saved_branch = .{ .else_ = else_ },
    };
}

pub fn addPhi(self: *Builder, sloc: graph.Sloc, lhs: *BuildNode, rhs: *BuildNode) SpecificNode(.Phi) {
    if (self.scope == null) return self.func.addNode(.Phi, sloc, .top, &.{}, .{});

    std.debug.assert(self.control().?.kind == .Region);
    return self.func.addNode(
        .Phi,
        sloc,
        lhs.data_type.meet(rhs.data_type),
        &.{ self.control(), lhs, rhs },
        .{},
    );
}

pub const Loop = struct {
    scope: BuildNode.Lock,
    control: std.EnumArray(Control, ?SpecificNode(.Scope)) = .initFill(null),

    pub const Control = enum { @"break", @"continue" };

    pub fn markBreaking(self: *Loop) void {
        const loop = getScopeValues(self.scope.node)[0].extra(.Loop);
        loop.anal_stage = .has_break;
    }

    pub fn addControl(self: *Loop, builder: *Builder, kind: Loop.Control) void {
        const builder_scope = builder.scope orelse return;

        if (self.control.getPtr(kind).*) |ctrl| {
            const rhs = mergeScopes(&builder.func, builder_scope, ctrl);
            getScopeValues(rhs)[0].extra(.Region).preserve_identity_phys = kind == .@"continue";
        } else {
            builder._truncateScope(builder_scope, self.scope.node.inputs().len);
            self.control.set(kind, builder_scope);
        }
        if (kind == .@"break") self.markBreaking();
        builder.scope = null;
    }

    pub fn joinContinues(self: *Loop, builder: *Builder) void {
        if (self.control.get(.@"continue")) |cscope| {
            if (builder.scope) |scope| {
                builder.scope = mergeScopes(&builder.func, scope, cscope);
                builder.control().?.extra(.Region).preserve_identity_phys = true;
            } else {
                builder.scope = cscope;
            }

            self.control.set(.@"continue", null);
        }
    }

    pub fn end(self: *Loop, builder: *Builder) void {
        defer self.* = undefined;
        if (self.control.get(.@"continue")) |cscope| {
            if (builder.scope) |scope| {
                builder.scope = mergeScopes(&builder.func, scope, cscope);
                builder.control().?.extra(.Region).preserve_identity_phys = true;
            } else {
                builder.scope = cscope;
            }
        }

        const init_values = getScopeValues(self.scope.node);

        if (init_values.len == 0) return;

        const start = 1;
        if (builder.scope) |backedge| {
            const update_values = getScopeValues(backedge);
            for (init_values[start..], update_values[start..]) |ini, update| {
                // NOTE: first value is the cfg
                if (ini.isLazyPhi(init_values[0])) {
                    if (update.kind == .Scope or update == ini) {
                        builder.func.subsume(ini.inputs()[1].?, ini, .intern);
                    } else {
                        builder.func.setInputNoIntern(ini, 2, update);
                    }
                }
            }
            builder.func.setInputNoIntern(init_values[0], 1, update_values[0]);
        } else {
            for (init_values[start..]) |ini| {
                if (ini.isLazyPhi(init_values[0])) {
                    builder.func.subsume(ini.inputs()[1].?, ini, .intern);
                }
            }
            builder.func.subsume(
                init_values[0].inputs()[0].?,
                init_values[0],
                .intern,
            );
        }

        if (builder.scope) |scope| {
            std.debug.assert(scope != self.scope.node);
            killScope(&builder.func, scope);
        }
        builder.scope = self.control.get(.@"break");

        defer {
            self.scope.unlock();
            killScope(&builder.func, self.scope.node);
        }
        const exit = builder.scope orelse {
            return;
        };

        const exit_values = getScopeValues(exit)[0..init_values.len];
        for (init_values[start..], exit_values[start..], start..) |ini, exi, i| {
            if (exi.kind == .Scope) {
                builder.func.setInputNoIntern(exit, i, ini);
            }
        }
    }
};

pub fn addLoopAndBeginBody(self: *Builder, sloc: graph.Sloc) Loop {
    const scope = self.scope orelse return .{
        .scope = self.cloneScope().lock(),
    };

    const loop = self.func.addNode(.Loop, sloc, .top, &.{
        self.control(),
        null,
    }, .{});

    self.func.setInputNoIntern(scope, 0, loop);
    const pscope = self.cloneScope();
    for (1..scope.input_ordered_len) |i| {
        self.func.setInputNoIntern(scope, i, pscope);
    }
    return .{ .scope = pscope.lock() };
}

pub const Block = struct {
    prev_scope: ?BuildNode.Lock = null,

    pub fn addBreak(self: *Block, bl: *Builder) void {
        const scope = bl.scope orelse return;

        if (self.prev_scope) |ps| {
            ps.unlock();
            self.prev_scope = mergeScopes(&bl.func, scope, ps.node).lock();
        } else {
            self.prev_scope = if (bl.scope) |s| s.lock() else null;
        }
        bl.scope = null;
    }

    pub fn end(self: *Block, bl: *Builder) void {
        if (self.prev_scope) |s| {
            s.unlock();
            bl.scope = s.node;
        }
    }
};

pub fn addBlock(_: *Builder) Block {
    return .{};
}

pub const arg_prefix_len: usize = 3;

pub const Call = struct {
    call: *BuildNode,
    scratch: *utils.Arena,
    cc: graph.CallConv,
    abi_params: std.ArrayList(graph.AbiParam) = .empty,
    ccbl: graph.CcBuilder = .{},

    pub const Slot = union(enum) {
        Scalar: union { unfilled: void, filled: *BuildNode },
        Stack: *BuildNode,
    };

    pub fn pushArg(
        self: *Call,
        bl: *Builder,
        sloc: graph.Sloc,
        param: graph.AbiParam,
        value: *BuildNode,
    ) void {
        var slot = self.allocArgSlot(bl, sloc, param);
        switch (slot) {
            .Stack => |s| {
                switch (param) {
                    .Stack => |sp| bl.addFixedMemCpy(sloc, s, value, sp.size),
                    .Reg => |r| {
                        bl.addStore(sloc, s, r, value);
                    },
                }
            },
            .Scalar => |*s| s.* = .{ .filled = value },
        }
        self.commitArgSlot(bl, slot);
    }

    pub fn allocArgSlot(
        self: *Call,
        bl: *Builder,
        sloc: graph.Sloc,
        param: graph.AbiParam,
    ) Slot {
        switch (param) {
            .Stack => |s| {
                self.abi_params.append(
                    self.scratch.allocator(),
                    param,
                ) catch unreachable;
                const location = bl.addLocalWithMeta(
                    sloc,
                    .{ .kind = .argument, .index = undefined },
                    s.size,
                    0,
                );
                return .{ .Stack = location };
            },
            .Reg => |r| {
                const pr = self.ccbl.handleReg(self.cc, r);

                if (pr == .Stack) {
                    return self.allocArgSlot(bl, sloc, pr);
                }

                self.abi_params.append(
                    self.scratch.allocator(),
                    pr,
                ) catch unreachable;

                return .{ .Scalar = .{ .unfilled = {} } };
            },
        }
    }

    pub fn commitArgSlot(self: *Call, bl: *Builder, slot: Slot) void {
        switch (slot) {
            .Scalar => |s| {
                _ = pushToScope(bl, self.call, s.filled);
            },
            .Stack => |s| {
                std.debug.assert(s.kind == .Local);
                _ = pushToScope(bl, self.call, s.inputs()[1].?);
            },
        }
    }

    pub fn lateInitSym(self: *Call, sym: u32) void {
        self.call.extra(.Call).id = sym;
    }

    pub fn prependRefRet(self: *Call, bl: *Builder, addr: *BuildNode) void {
        self.abi_params.insert(
            self.scratch.allocator(),
            0,
            .{ .Reg = .i64 },
        ) catch unreachable;

        _ = bl.pushToScope(self.call, addr);

        const apl = arg_prefix_len +
            @intFromBool(self.call.extra(.Call).id == graph.indirect_call);

        const ord = self.call.ordInps()[apl..];

        std.mem.rotate(?*BuildNode, ord, ord.len - 1);

        // we need to rewire all positions, sadly
        for (ord, 0..) |i, j| {
            const prev_idx = if (j == 0) ord.len - 1 else j - 1;
            const inp = i.?;

            for (inp.outputs()) |*o| {
                if (o.get() == self.call and o.pos() == apl + prev_idx) {
                    o.* = .init(self.call, apl + j, inp);
                    break;
                }
            } else unreachable;
        }
    }

    pub fn end(
        self: *Call,
        bl: *Builder,
        sloc: graph.Sloc,
        return_params: ?[]const graph.AbiParam,
        ret_buf: *[2]*BuildNode,
    ) []*BuildNode {
        const scope = bl.scope orelse {
            if (return_params) |rp| {
                @memset(ret_buf, bl.addStub(sloc, .i64));
                return ret_buf[0..rp.len];
            } else {
                return undefined;
            }
        };

        bl.func.setInputNoIntern(self.call, 0, bl.control());
        bl.func.setInputNoIntern(self.call, 1, bl.memory());
        const call_end = bl.func.addNode(.CallEnd, sloc, .top, &.{self.call}, .{});
        bl.func.setInputNoIntern(scope, 0, call_end);
        const call_mem = bl.func.addNode(.Mem, sloc, .top, &.{call_end}, .{});
        bl.func.setInputNoIntern(scope, 1, call_mem);

        const extra = self.call.extra(.Call);

        extra.signature =
            .init(self.cc, self.abi_params.items, return_params, bl.arena());

        std.debug.assert(extra.signature.params().len ==
            self.call.ordInps().len - arg_prefix_len -
                @intFromBool(extra.id == graph.indirect_call));

        if (return_params) |rp| {
            if (rp.len == 1 and rp[0] == .Stack) return &.{};

            for (rp, ret_buf[0..rp.len], 0..) |v, *slt, i| {
                slt.* = bl.func.addNode(.Ret, sloc, v.Reg, &.{call_end}, .{ .index = i });
            }
            return ret_buf[0..rp.len];
        } else {
            bl.addTrap(.none, graph.unreachable_func_trap);
            return undefined;
        }
    }
};

pub const CallId = union(enum) { fptr: *BuildNode, sym: u32, special: u32 };

pub fn addCall(
    self: *Builder,
    scratch: *utils.Arena,
    sloc: graph.Sloc,
    call_conv: graph.CallConv,
    id: CallId,
) Call {
    var buf: [4]?*BuildNode = undefined;
    var inps = std.ArrayList(?*BuildNode).initBuffer(&buf);

    inps.appendAssumeCapacity(null);
    inps.appendAssumeCapacity(null);
    inps.appendAssumeCapacity(switch (id) {
        .special, .fptr => null,
        .sym => self.func.getSyms(),
    });
    switch (id) {
        .fptr => |f| inps.appendAssumeCapacity(f),
        .sym, .special => {},
    }

    return .{
        .scratch = scratch,
        .cc = call_conv,
        .call = self.func.addNode(.Call, sloc, .top, inps.items, .{
            .id = switch (id) {
                .fptr => graph.indirect_call,
                .special, .sym => |i| i,
            },
            .signature = .empty,
        }),
    };
}

pub fn addReturn(self: *Builder, values: []const *BuildNode) void {
    const scope = self.scope orelse return;

    const ret = self.func.end;
    const inps = ret.inputs();
    if (inps[0] != null) {
        const new_ctrl = self.func.addNode(.Region, .none, .top, &.{ inps[0].?, self.control() }, .{});
        self.func.setInputNoIntern(ret, 0, new_ctrl);
        const new_mem = self.func.addNode(.Phi, .none, .top, &.{ new_ctrl, inps[1], self.memory() }, .{});
        self.func.setInputNoIntern(ret, 1, new_mem);
        for (inps[3..ret.input_ordered_len], values, 3..) |curr, next, vidx| {
            const new_value = self.func.addNode(.Phi, curr.?.sloc, curr.?.data_type.meet(next.data_type), &.{ new_ctrl, curr, next }, .{});
            self.func.setInputNoIntern(ret, vidx, new_value);
        }
    } else {
        self.func.setInputNoIntern(ret, 0, self.control());
        self.func.setInputNoIntern(ret, 1, self.memory());

        for (values) |v| {
            const idx = self.func.addDep(ret, v);
            self.func.addUse(v, idx, ret);
            ret.input_ordered_len += 1;
        }
    }

    killScope(&self.func, scope);
    self.scope = null;
}

pub fn addTrap(self: *Builder, sloc: graph.Sloc, code: u64) void {
    const scope = self.scope orelse return;

    self.func.addTrap(sloc, self.control().?, code, .intern);

    killScope(&self.func, scope);
    self.scope = null;
}

pub fn addStub(self: *Builder, sloc: graph.Sloc, ty: DataType) SpecificNode(.CInt) {
    return self.func.addNode(.Stub, sloc, ty, &.{}, .{});
}
