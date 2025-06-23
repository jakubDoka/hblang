func: Func,
scope: ?*Func.Node = undefined,
root_mem: *Func.Node = undefined,
pins: *Func.Node = undefined,

const std = @import("std");
const root = graph.utils;
const graph = @import("graph.zig");
const Builder = @This();

pub const Func = graph.Func(Builder);
pub const i_know_the_api = {};
pub const BuildNode = Func.Node;
pub const Kind = Func.Kind;

pub const DataType = graph.DataType;
pub const BinOp = graph.BinOp;
pub const UnOp = graph.UnOp;
pub const classes = enum {
    // [Cfg, mem, ...values]
    pub const Scope = extern struct {
        pub const is_temporary = true;
    };
};

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

pub const BuildToken = enum { @"please call Builder.begin() first, then Builder.end()" };

/// Begins a build of a function, returns a token to end the build body building.
/// the `params` and `returns` are copied
pub fn begin(
    self: *Builder,
    call_conv: graph.CallConv,
    params: []const graph.AbiParam,
    returns: ?[]const graph.AbiParam,
) BuildToken {
    const ctrl = self.func.addNode(.Entry, .top, &.{self.func.root}, .{});
    self.root_mem = self.func.addNode(.Mem, .top, &.{self.func.root}, .{});
    self.scope = self.func.addNode(.Scope, .top, &.{ ctrl, self.root_mem }, .{});
    self.func.end = self.func.addNode(.Return, .top, &.{ null, null, null }, .{});
    self.pins = self.func.addNode(.Scope, .top, &.{}, .{});

    self.func.signature = .init(call_conv, params, returns, self.func.arena.allocator());

    return @enumFromInt(0);
}

pub fn addParam(self: *Builder, idx: usize) SpecificNode(.Arg) {
    return switch (self.func.signature.params()[idx]) {
        .Reg => |ty| self.func.addNode(.Arg, ty, &.{self.func.root}, .{ .index = idx }),
        .Stack => |spec| self.func.addNode(.StructArg, .i64, &.{self.func.root}, .{
            .base = .{ .index = idx },
            .spec = spec,
        }),
    };
}

pub fn end(self: *Builder, _: BuildToken) void {
    //std.debug.assert(getScopeValues(self.pins).len == 0);
    killScope(self.pins);

    if (!self.isUnreachable()) self.addReturn(&.{});

    if (std.debug.runtime_safety) {
        var tmp = root.Arena.scrath(null);
        defer tmp.deinit();

        var worklist = Func.WorkList.init(tmp.arena.allocator(), self.func.next_id) catch unreachable;
        worklist.add(self.func.end);
        worklist.add(self.func.root);
        var i: usize = 0;
        while (i < worklist.list.items.len) : (i += 1) {
            for (worklist.list.items[i].inputs()) |oi| if (oi) |o| {
                worklist.add(o);
            };

            for (worklist.list.items[i].outputs()) |o| {
                worklist.add(o);
            }
        }

        for (worklist.list.items) |node| {
            std.debug.assert(node.kind != .Scope);
        }
    }
}

// #MEM ========================================================================

pub fn addLocal(self: *Builder, sloc: graph.Sloc, size: u64) SpecificNode(.Local) {
    const local = self.func.addNode(.Local, .i64, &.{ null, self.root_mem }, .{ .size = size });
    local.sloc = sloc;
    return local;
}

pub fn resizeLocal(_: *Builder, here: SpecificNode(.Local), to_size: u64) void {
    std.debug.assert(here.extra(.Local).size == 0);
    here.extra(.Local).size = to_size;
}

pub fn addLoad(self: *Builder, addr: *BuildNode, ty: DataType) SpecificNode(.Store) {
    const ctrl = if (addr.kind == .Local) null else self.control();
    return self.func.addNode(.Load, ty, &.{ ctrl, self.memory(), addr }, .{});
}

pub fn addFieldLoad(self: *Builder, base: *BuildNode, offset: i64, ty: DataType) *BuildNode {
    return self.addLoad(self.addFieldOffset(base, offset), ty);
}

pub fn addStore(self: *Builder, addr: *BuildNode, ty: DataType, value: *BuildNode) void {
    if (value.data_type == .bot) return;
    if (value.data_type.size() == 0) root.panic("{}", .{value.data_type});
    const mem = self.memory();
    const ctrl = self.control();
    const store = self.func.addNode(.Store, ty, &.{ ctrl, mem, addr, value }, .{});
    self.func.setInputNoIntern(self.scope.?, 1, store);
}

pub fn addFieldStore(self: *Builder, base: *BuildNode, offset: i64, ty: DataType, value: *BuildNode) void {
    _ = self.addStore(self.addFieldOffset(base, offset), ty, value);
}

pub fn addSpill(self: *Builder, sloc: graph.Sloc, value: *BuildNode) SpecificNode(.Local) {
    const local = self.addLocal(sloc, value.data_type.size());
    _ = self.addStore(local, value.data_type, value);
    return local;
}

pub fn addFixedMemCpy(self: *Builder, dst: *BuildNode, src: *BuildNode, size: u64) void {
    const mem = self.memory();
    const ctrl = self.control();
    const siz = self.addIntImm(.i64, @bitCast(size));
    const mcpy = self.func.addNode(.MemCpy, .top, &.{ ctrl, mem, dst, src, siz }, .{});
    self.func.setInputNoIntern(self.scope.?, 1, mcpy);
}

pub fn addFieldOffset(self: *Builder, base: *BuildNode, offset: i64) *BuildNode {
    return self.func.addFieldOffset(base, offset);
}

pub fn addGlobalAddr(self: *Builder, arbitrary_global_id: u32) SpecificNode(.GlobalAddr) {
    return self.func.addGlobalAddr(arbitrary_global_id);
}

// #MATH =======================================================================

pub fn addCast(self: *Builder, to: DataType, value: *BuildNode) SpecificNode(.UnOp) {
    return self.func.addCast(to, value);
}

pub fn addFramePointer(self: *Builder, as: DataType) SpecificNode(.FramePointer) {
    return self.func.addNode(.FramePointer, as, &.{null}, .{});
}

pub fn addIndexOffset(
    self: *Builder,
    base: *BuildNode,
    op: Func.OffsetDirection,
    elem_size: u64,
    subscript: *BuildNode,
) SpecificNode(.BinOp) {
    return self.func.addIndexOffset(base, op, elem_size, subscript);
}

pub fn addIntImm(self: *Builder, ty: DataType, value: i64) SpecificNode(.CInt) {
    return self.func.addIntImm(ty, value);
}

pub fn addFlt64Imm(self: *Builder, value: f64) SpecificNode(.CFlt64) {
    return self.func.addFlt64Imm(value);
}

pub fn addFlt32Imm(self: *Builder, value: f32) SpecificNode(.CFlt32) {
    return self.func.addFlt32Imm(value);
}

pub fn addBinOp(self: *Builder, op: BinOp, ty: DataType, lhs: *BuildNode, rhs: *BuildNode) SpecificNode(.BinOp) {
    return self.func.addBinOp(op, ty, lhs, rhs);
}

pub fn addUnOp(self: *Builder, op: UnOp, ty: DataType, oper: *BuildNode) SpecificNode(.BinOp) {
    return self.func.addUnOp(op, ty, oper);
}

// #SCOPE ======================================================================

pub fn memory(self: *Builder) *Func.Node {
    return self._readScopeValue(1);
}

pub fn control(self: *Builder) *Func.Node {
    return getScopeValues(self.scope.?)[0];
}

pub const scope_value_start = 2;

pub fn pushPin(self: *Builder, value: *BuildNode) void {
    self.pushToScope(self.pins, value);
}

pub fn pushScopeValue(self: *Builder, value: *BuildNode) void {
    self.pushToScope(self.scope.?, value);
}

fn pushToScope(self: *Builder, scope: *BuildNode, value: *BuildNode) void {
    if (scope.input_ordered_len == scope.input_len) {
        const new_cap = @max(1, scope.input_len) * 2;
        const new_alloc = self.func.arena.allocator().realloc(
            scope.input_base[0..scope.input_len],
            new_cap,
        ) catch unreachable;
        scope.input_base = new_alloc.ptr;
        scope.input_len = @intCast(new_alloc.len);
    }

    scope.input_base[scope.input_ordered_len] = value;
    scope.input_ordered_len += 1;
    self.func.addUse(value, scope);
}

pub fn getPinValue(self: *Builder, index: usize) *Func.Node {
    return getScopeValueMulty(&self.func, self.pins, index);
}

pub fn getScopeValue(self: *Builder, index: usize) *Func.Node {
    return self._readScopeValue(scope_value_start + index);
}

pub fn getScopeValues(scope: SpecificNode(.Scope)) []*BuildNode {
    std.debug.assert(scope.kind == .Scope);
    for (scope.input_base[0..scope.input_ordered_len]) |e| std.debug.assert(e != null);
    return @ptrCast(scope.input_base[0..scope.input_ordered_len]);
}

pub fn _readScopeValue(self: *Builder, index: usize) *Func.Node {
    return getScopeValueMulty(&self.func, self.scope.?, index);
}

pub fn getScopeValueMulty(func: *Func, scope: *BuildNode, index: usize) *Func.Node {
    const values = getScopeValues(scope);
    return switch (values[index].kind) {
        .Scope => {
            const loop = values[index];
            const initVal = getScopeValueMulty(func, loop, index);
            const items = getScopeValues(loop);
            if (!items[index].isLazyPhi(items[0])) {
                const phi = func.addNode(.Phi, initVal.data_type, &.{ items[0], initVal, null }, .{});
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
    const lhs_values = getScopeValues(lhs);
    const rhs_values = getScopeValues(rhs);

    const relevant_size = @min(lhs_values.len, rhs_values.len);

    const new_ctrl = func.addNode(.Region, .top, &.{ lhs_values[0], rhs_values[0] }, .{});

    const start = 1;
    for (lhs_values[start..relevant_size], rhs_values[start..relevant_size], start..) |lh, rh, i| {
        if (lh == rh) continue;
        const thn = getScopeValueMulty(func, lhs, i);
        const els = getScopeValueMulty(func, rhs, i);
        const phi = func.addNode(.Phi, thn.data_type.meet(els.data_type), &.{ new_ctrl, thn, els }, .{});
        func.setInputNoIntern(rhs, i, phi);
    }

    func.setInputNoIntern(rhs, 0, new_ctrl);
    killScope(lhs);

    return rhs;
}

pub fn cloneScope(self: *Builder) SpecificNode(.Scope) {
    const values = getScopeValues(self.scope.?);
    return self.func.addNode(.Scope, .top, values, .{});
}

pub inline fn truncateScope(self: *Builder, back_to: usize) void {
    self._truncateScope(self.scope orelse return, scope_value_start + back_to);
}

pub inline fn truncatePins(self: *Builder, back_to: usize) void {
    self._truncateScope(self.pins, back_to);
}

pub fn _truncateScope(self: *Builder, scope: SpecificNode(.Scope), back_to: usize) void {
    while (scope.input_ordered_len > back_to) {
        scope.input_ordered_len -= 1;
        self.func.setInputNoIntern(scope, scope.input_ordered_len, null);
    }
}

pub fn killScope(scope: SpecificNode(.Scope)) void {
    scope.input_len = scope.input_ordered_len;
    scope.kill();
}

// #CONTROL ====================================================================

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
        builder.scope = self.saved_branch.else_;
        self.saved_branch = .{ .then = then };
        builder.func.setInputNoIntern(
            builder.scope.?,
            0,
            builder.func.addNode(.Else, .top, &.{self.if_node}, .{}),
        );
        return @enumFromInt(0);
    }

    pub fn end(self: *If, builder: *Builder, _: EndToken) void {
        const then = self.saved_branch.then orelse return;
        const else_ = builder.scope orelse {
            builder.scope = self.saved_branch.then;
            return;
        };
        builder.scope = mergeScopes(&builder.func, then, else_);
        self.* = undefined;
        return;
    }
};

pub fn addIfAndBeginThen(self: *Builder, sloc: graph.Sloc, cond: *BuildNode) If {
    const else_ = self.cloneScope();
    const if_node = self.func.addNode(.If, .top, &.{ self.control(), cond }, .{});
    if_node.sloc = sloc;
    self.func.setInputNoIntern(self.scope.?, 0, self.func.addNode(.Then, .top, &.{if_node}, .{}));
    return .{
        .if_node = if_node,
        .saved_branch = .{ .else_ = else_ },
    };
}

pub const Loop = struct {
    scope: SpecificNode(.Scope),
    control: std.EnumArray(Control, ?SpecificNode(.Scope)) = .{ .values = .{ null, null } },

    pub const Control = enum { @"break", @"continue" };

    pub fn markBreaking(self: *Loop) void {
        const loop = getScopeValues(self.scope)[0].extra(.Loop);
        loop.anal_stage = .has_break;
    }

    pub fn addControl(self: *Loop, builder: *Builder, kind: Loop.Control) void {
        if (self.control.getPtr(kind).*) |ctrl| {
            const rhs = mergeScopes(&builder.func, builder.scope.?, ctrl);
            getScopeValues(rhs)[0].extra(.Region).preserve_identity_phys = kind == .@"continue";
        } else {
            builder._truncateScope(builder.scope.?, self.scope.inputs().len);
            self.control.set(kind, builder.scope.?);
        }
        if (kind == .@"break") self.markBreaking();
        builder.scope = null;
    }

    pub fn end(self: *Loop, builder: *Builder) void {
        defer self.* = undefined;
        if (self.control.get(.@"continue")) |cscope| {
            if (builder.scope) |scope| {
                builder.scope = mergeScopes(&builder.func, scope, cscope);
                builder.control().extra(.Region).preserve_identity_phys = true;
            } else {
                builder.scope = cscope;
            }
        }

        const init_values = getScopeValues(self.scope);
        const start = 1;
        if (builder.scope) |backedge| {
            const update_values = getScopeValues(backedge);
            for (init_values[start..], update_values[start..]) |ini, update| {
                if (ini.isLazyPhi(init_values[0])) {
                    if (update.kind == .Scope) {
                        builder.func.subsume(ini.inputs()[1].?, ini);
                    } else {
                        builder.func.setInputNoIntern(ini, 2, update);
                    }
                }
            }
            builder.func.setInputNoIntern(init_values[0], 1, update_values[0]);
        } else {
            for (init_values[start..]) |ini| {
                if (ini.isLazyPhi(init_values[0])) {
                    builder.func.subsume(ini.inputs()[1].?, ini);
                }
            }
            builder.func.subsume(init_values[0].inputs()[0].?, init_values[0]);
        }

        if (builder.scope) |scope| killScope(scope);

        builder.scope = self.control.get(.@"break");
        defer killScope(self.scope);
        const exit = builder.scope orelse {
            return;
        };

        const exit_values = getScopeValues(exit);
        for (init_values[start..], exit_values[start..], start..) |ini, exi, i| {
            if (exi.kind == .Scope) {
                builder.func.setInputNoIntern(exit, i, ini);
            }
        }
    }
};

pub fn addLoopAndBeginBody(self: *Builder, sloc: graph.Sloc) Loop {
    const loop = self.func.addNode(.Loop, .top, &.{
        self.control(),
        null,
    }, .{});
    loop.sloc = sloc;
    self.func.setInputNoIntern(self.scope.?, 0, loop);
    const pscope = self.cloneScope();
    for (1..self.scope.?.input_ordered_len) |i| {
        self.func.setInputNoIntern(self.scope.?, i, pscope);
    }
    return .{ .scope = pscope };
}

pub const CallArgs = struct {
    params: []const graph.AbiParam,
    arg_slots: []*BuildNode,
    returns: ?[]const graph.AbiParam,
    return_slots: ?[]*BuildNode,
    hint: enum { @"construst this with Builder.allocCallArgs()" },
};

const arg_prefix_len = 2;

pub fn allocCallArgs(
    _: *Builder,
    scratch: *root.Arena,
    params: []const graph.AbiParam,
    returns: ?[]const graph.AbiParam,
) CallArgs {
    const args = scratch.alloc(*BuildNode, arg_prefix_len + params.len +
        if (returns) |r| r.len else 0);
    return .{
        .params = params,
        .returns = returns,
        .arg_slots = args[arg_prefix_len..][0..params.len],
        .return_slots = if (returns != null) args[arg_prefix_len + params.len ..] else null,
        .hint = @enumFromInt(0),
    };
}

pub fn addCall(
    self: *Builder,
    call_conv: graph.CallConv,
    arbitrary_call_id: u32,
    args_with_initialized_arg_slots: CallArgs,
) ?[]const *BuildNode {
    errdefer unreachable;

    const args = args_with_initialized_arg_slots;
    for (args.arg_slots, args.params) |ar, pr| if (ar.data_type != ar.data_type.meet(pr.getReg())) {
        root.panic("{} != {}", .{ ar.data_type, ar.data_type.meet(pr.getReg()) });
    };
    const full_args = (args.arg_slots.ptr - arg_prefix_len)[0 .. arg_prefix_len + args.params.len];
    var stack_offset: u64 = 0;
    for (args.params, args.arg_slots) |par, *arg| {
        if (par == .Stack) {
            stack_offset = std.mem.alignForward(
                u64,
                stack_offset,
                @as(u64, 1) << par.Stack.alignment,
            );
            const location = self.func.addNode(
                .StackArgOffset,
                .i64,
                &.{null},
                .{ .offset = stack_offset },
            );
            self.addFixedMemCpy(location, arg.*, par.Stack.size);
            stack_offset += par.Stack.size;
            arg.* = location;
        }
    }

    full_args[0] = self.control();
    full_args[1] = self.memory();

    const call = self.func.addNode(.Call, .top, full_args, .{
        .id = arbitrary_call_id,
        .signature = .init(call_conv, args.params, args.returns, self.func.arena.allocator()),
    });
    const call_end = self.func.addNode(.CallEnd, .top, &.{call}, .{});
    self.func.setInputNoIntern(self.scope.?, 0, call_end);
    const call_mem = self.func.addNode(.Mem, .top, &.{call_end}, .{});
    self.func.setInputNoIntern(self.scope.?, 1, call_mem);

    if (args.return_slots) |rslots| {
        for (rslots, args.returns.?, 0..) |*slt, rty, i| {
            slt.* = self.func.addNode(.Ret, rty.getReg(), &.{call_end}, .{ .index = i });
        }
    } else {
        self.addTrap(graph.unreachable_func_trap);
    }

    return args.return_slots;
}

pub fn addReturn(self: *Builder, values: []const *BuildNode) void {
    for (values, self.func.signature.returns().?) |val, rtt|
        if (val.data_type != val.data_type.meet(rtt.getReg()))
            root.panic("{s} != {s}", .{ @tagName(val.data_type), @tagName(rtt.getReg()) });

    const ret = self.func.end;
    const inps = ret.inputs();
    if (inps[0] != null) {
        const new_ctrl = self.func.addNode(.Region, .top, &.{ inps[0].?, self.control() }, .{});
        self.func.setInputNoIntern(ret, 0, new_ctrl);
        const new_mem = self.func.addNode(.Phi, .top, &.{ new_ctrl, inps[1], self.memory() }, .{});
        self.func.setInputNoIntern(ret, 1, new_mem);
        for (inps[3..ret.input_ordered_len], values, 3..) |curr, next, vidx| {
            const new_value = self.func.addNode(.Phi, curr.?.data_type.meet(next.data_type), &.{ new_ctrl, curr, next }, .{});
            self.func.setInputNoIntern(ret, vidx, new_value);
        }
    } else {
        self.func.setInputNoIntern(ret, 0, self.control());
        self.func.setInputNoIntern(ret, 1, self.memory());

        for (values) |v| {
            self.func.addDep(ret, v);
            self.func.addUse(v, ret);
            ret.input_ordered_len += 1;
        }
    }

    killScope(self.scope.?);
    self.scope = null;
}

pub fn addTrap(self: *Builder, code: u64) void {
    self.func.addTrap(self.control(), code);

    killScope(self.scope.?);
    self.scope = null;
}
