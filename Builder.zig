types: *Types,
func: Func,
scope: Scope = undefined,
loops: std.ArrayList(*Loop) = undefined,
return_mem: ?*Func.Node = undefined,
return_value: ?*Func.Node = undefined,
return_ctrl: ?*Func.Node = undefined,
file: Types.File = undefined,
ast: Ast = undefined,
arena: std.mem.Allocator = undefined,
ctrl: ?*Func.Node = undefined,
mem: *Func.Node = undefined,
fdata: *Types.FuncData = undefined,

const std = @import("std");
const Ast = @import("parser.zig");
const Func = @import("Func.zig").Func(union(enum) {});
const Types = @import("Types.zig");
const Builder = @This();

const Scope = std.ArrayList(ScopeEntry);

const ScopeEntry = union(enum) {
    Node: *Func.Node,
    LazyPhy: *Loop,
};

const Loop = struct {
    ctrl: *Func.Node,
    scope: Scope,
    control: std.EnumArray(Control, ?ControlData) = .{ .values = .{ null, null } },

    const Control = enum { break_, continume_ };

    const ControlData = struct {
        ctrl: *Func.Node,
        scope: Scope,
    };
};

pub fn init(gpa: std.mem.Allocator, types: *Types) Builder {
    return .{
        .types = types,
        .func = .init(gpa),
    };
}

pub fn deinit(self: *Builder) void {
    self.func.deinit();
    self.* = undefined;
}

pub fn build(self: *Builder, file: Types.File, func: Types.Func) void {
    self.file = file;
    self.ast = self.types.getFile(file).*;
    self.arena = self.func.beginTmpAlloc();
    self.scope = .init(self.arena);
    self.loops = .init(self.arena);
    self.fdata = self.types.get(func);
    self.return_value = null;
    self.return_ctrl = null;

    self.ctrl = self.func.addNode(.Entry, &.{self.func.root}, .{});
    self.mem = self.func.addNode(.Mem, &.{self.func.root}, {});
    self.return_mem = null;
    self.scope.append(.{ .Node = self.mem }) catch unreachable;

    var i: usize = 0;
    for (self.fdata.args) |ty| {
        if (ty == .void) continue;
        std.debug.assert(ty == .uint or ty == .ptr);
        const arg = self.func.addNode(.Arg, &.{self.func.root}, i);
        const local = self.func.addNode(.Local, &.{ null, self.mem }, 8);
        const mem = self.resolveMem();
        self.scope.items[0].Node = self.func.addNode(.Store, &.{ self.ctrl, mem, local, arg }, {});
        self.scope.append(.{ .Node = local }) catch unreachable;
        i += 1;
    }

    _ = self.emit(self.ast.exprs.get(self.fdata.ast).Fn.body);

    self.func.end = self.func.addNode(.Return, &.{
        self.return_ctrl orelse self.ctrl,
        self.return_mem orelse self.resolveMem(),
        self.return_value,
    }, .{});
}

inline fn getAst(self: *Builder, expr: Ast.Id) Ast.Expr {
    return self.ast.exprs.get(expr);
}

inline fn getAstSlice(self: *Builder, slice: Ast.Slice) []Ast.Id {
    return self.ast.exprs.view(slice);
}

inline fn tokenSrc(self: *Builder, idx: u32) []const u8 {
    return self.ast.tokenSrc(idx);
}

inline fn jmp(self: *Builder, from: ?*Func.Node) *Func.Node {
    return self.func.addNode(.Jmp, &.{from}, .{});
}

fn resolveIdent(func: *Func, scope: []ScopeEntry, index: usize) *Func.Node {
    return switch (scope[index]) {
        .Node => |n| n,
        .LazyPhy => |loop| {
            const initVal = resolveIdent(func, loop.scope.items, index);
            if (!loop.scope.items[index].Node.isLazyPhi(loop.ctrl)) {
                loop.scope.items[index] = .{ .Node = func.addNode(.Phi, &.{ loop.ctrl, initVal, null }, {}) };
            }
            scope[index] = loop.scope.items[index];
            return scope[index].Node;
        },
    };
}

fn mergeScopes(func: *Func, lhs: []ScopeEntry, rhs: []ScopeEntry, region: *Func.Node) void {
    for (lhs, rhs, 0..) |lh, *rh, i| {
        if (lh == .LazyPhy and rh.* == .LazyPhy and lh.LazyPhy == rh.LazyPhy) continue;
        if (lh == .Node and rh.* == .Node and lh.Node == rh.Node) continue;
        const thn = resolveIdent(func, lhs, i);
        const els = resolveIdent(func, rhs, i);
        rh.* = .{ .Node = func.addNode(.Phi, &.{ region, thn, els }, {}) };
        if (i == 0) rh.Node.data_type = .mem;
    }
}

fn loopCtrl(self: *Builder, kind: Loop.Control) void {
    const loop = self.loops.getLast();

    if (loop.control.getPtr(kind).*) |*ctrl| {
        ctrl.ctrl = self.func.addNode(.Region, &.{ self.jmp(self.ctrl), self.jmp(ctrl.ctrl) }, .{});
        mergeScopes(&self.func, self.scope.items[0..ctrl.scope.items.len], ctrl.scope.items, ctrl.ctrl);
    } else {
        loop.control.set(kind, .{
            .ctrl = self.ctrl.?,
            .scope = self.scope.clone() catch unreachable,
        });
        std.debug.assert(loop.control.getPtr(kind).*.?.scope.items.len >= loop.scope.items.len);
        loop.control.getPtr(kind).*.?.scope.items.len = loop.scope.items.len;
    }
    self.ctrl = null;
}

fn resolveMem(self: *Builder) *Func.Node {
    return resolveIdent(&self.func, self.scope.items, 0);
}

fn emit(self: *Builder, expr: Ast.Id) ?*Func.Node {
    switch (self.getAst(expr)) {
        .Comment => return null,
        .Void => return null,
        .Integer => |e| {
            return self.func.addNode(.CInt, &.{null}, std.fmt.parseInt(i64, self.tokenSrc(e.index), 10) catch unreachable);
        },
        .Ident => |e| {
            const ident = resolveIdent(&self.func, self.scope.items, e.id.index + 1);
            std.debug.assert(ident.kind == .Local);
            return self.func.addNode(.Load, &.{ null, self.resolveMem(), ident }, {});
        },
        .Block => |e| {
            const prev_scope_height = self.scope.items.len;
            defer self.scope.items.len = prev_scope_height;

            for (self.getAstSlice(e.stmts)) |s| {
                _ = self.emit(s);
            }

            return self.ctrl;
        },
        .If => |e| {
            const cond = self.emit(e.cond);
            const if_node = self.func.addNode(.If, &.{ self.ctrl, cond }, .{});

            var saved_scope = self.scope.clone() catch unreachable;
            self.ctrl = self.func.addNode(.Then, &.{if_node}, .{});
            _ = self.emit(e.then);
            const then_cfg = self.ctrl;

            std.mem.swap(Scope, &self.scope, &saved_scope);

            self.ctrl = self.func.addNode(.Else, &.{if_node}, .{});
            _ = self.emit(e.else_);
            const else_cfg = self.ctrl;

            self.ctrl = self.func.addNode(.Region, &.{ self.jmp(then_cfg), self.jmp(else_cfg) }, .{});

            const then_scope = saved_scope;

            mergeScopes(&self.func, then_scope.items, self.scope.items, self.ctrl.?);

            return self.ctrl;
        },
        .Loop => |e| {
            var loop = Loop{
                .ctrl = self.func.addNode(.Loop, &.{ self.jmp(self.ctrl), null }, .{}),
                .scope = self.scope.clone() catch unreachable,
            };
            self.ctrl = loop.ctrl;

            self.loops.append(&loop) catch unreachable;
            @memset(self.scope.items[0..1], .{ .LazyPhy = &loop });
            _ = self.emit(e.body);
            _ = self.loops.pop();

            if (loop.control.get(.continume_)) |cscope| {
                self.ctrl = self.func.addNode(.Region, &.{ self.jmp(cscope.ctrl), self.jmp(self.ctrl) }, .{});
                mergeScopes(&self.func, cscope.scope.items, self.scope.items, self.ctrl.?);
            }

            for (loop.scope.items[0..1], self.scope.items[0..1]) |l, *c| {
                if (c.* != .LazyPhy) {
                    std.debug.assert(l.Node.isLazyPhi(loop.ctrl));
                    l.Node.data_type = .mem;
                    self.func.setInput(l.Node, 2, c.Node);
                }
            }

            self.func.setInput(loop.ctrl, 1, self.jmp(self.ctrl));

            const break_ = loop.control.get(.break_) orelse {
                self.ctrl = null;
                return self.ctrl;
            };

            for (loop.scope.items[0..1], break_.scope.items[0..1]) |c, *b| {
                if (b.* == .LazyPhy) {
                    b.* = c;
                }
            }

            self.ctrl = break_.ctrl;
            self.scope = break_.scope;

            return self.ctrl;
        },
        .UnOp => |e| switch (e.op) {
            .@"&" => {
                return self.emit(e.oper).?.base();
            },
            .@"*" => {
                const oper = self.emit(e.oper).?;
                const load = self.func.addNode(.Load, &.{ null, self.resolveMem(), oper }, {});
                return load;
            },
            else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
        },
        .Break => |_| {
            self.loopCtrl(.break_);
            return self.ctrl;
        },
        .Continue => |_| {
            self.loopCtrl(.continume_);
            return self.ctrl;
        },
        .Return => |e| {
            const value = self.emit(e.value);
            const mem = self.resolveMem();
            if (self.return_ctrl) |ret_ctrl| {
                self.return_ctrl = self.func.addNode(.Region, &.{
                    self.jmp(ret_ctrl),
                    self.jmp(self.ctrl),
                }, .{});
                self.return_mem = self.func.addNode(.Phi, &.{ self.return_ctrl, self.return_mem, mem }, {});
                self.return_mem.?.data_type = .mem;
                if (self.return_value != null) {
                    self.return_value = self.func.addNode(.Phi, &.{ self.return_ctrl, self.return_value, value }, {});
                }
            } else {
                self.return_mem = mem;
                self.return_ctrl = self.ctrl;
                self.return_value = value;
            }

            self.ctrl = null;
            return null;
        },
        .BinOp => |e| switch (e.op) {
            .@":=" => {
                const value = self.emit(e.rhs).?;
                const local = self.func.addNode(.Local, &.{ null, self.mem }, 8);
                const mem = self.resolveMem();
                self.scope.items[0].Node = self.func.addNode(.Store, &.{ self.ctrl, mem, local, value }, {});
                self.scope.append(.{ .Node = local }) catch unreachable;
                return null;
            },
            .@"=" => {
                const loc = self.emit(e.lhs).?;
                std.debug.assert(loc.kind == .Load);
                const val = self.emit(e.rhs).?;

                const base = loc.base();
                const mem = self.resolveMem();
                self.scope.items[0].Node = self.func.addNode(.Store, &.{ self.ctrl, mem, base, val }, {});

                return null;
            },
            else => return self.func.addNode(.BinOp, &.{ null, self.emit(e.lhs), self.emit(e.rhs) }, e.op),
        },
        .Call => |e| {
            self.fdata.tail = false;

            const fixed_args = 2;
            const args = self.arena.alloc(?*Func.Node, fixed_args + e.args.len()) catch unreachable;
            args[0] = self.ctrl;
            args[1] = resolveIdent(&self.func, self.scope.items, 0);
            var len: usize = fixed_args;
            for (self.getAstSlice(e.args)) |a| {
                args[len] = self.emit(a);
                if (args[len] != null) len += 1;
            }
            const call = self.func.addNode(.Call, args[0..len], .{ .id = self.types.resolveFunc(self.file, e.called) });
            self.ctrl = self.func.addNode(.CallEnd, &.{call}, .{});
            self.scope.items[0].Node = self.func.addNode(.Mem, &.{self.ctrl}, {});
            return self.func.addNode(.Ret, &.{self.ctrl}, {});
        },
        else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
    }
}
