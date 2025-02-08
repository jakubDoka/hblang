types: *Types,
func: Func,
scope: Scope = undefined,
loops: std.ArrayList(*Loop) = undefined,
return_value: ?*Func.Node = undefined,
return_ctrl: ?*Func.Node = undefined,
file: Types.File = undefined,
ast: Ast = undefined,
arena: std.mem.Allocator = undefined,
ctrl: ?*Func.Node = undefined,
fdata: *Types.FuncData = undefined,

const std = @import("std");
const Ast = @import("parser.zig");
const Func = @import("Func.zig");
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

    var i: usize = 0;
    for (self.fdata.args) |ty| {
        if (ty == .void) continue;
        std.debug.assert(ty == .uint);
        const arg = self.func.addNode(.Arg, &.{self.func.root}, i);
        self.scope.append(.{ .Node = arg }) catch unreachable;
        i += 1;
    }

    self.ctrl = self.func.addNode(.Entry, &.{self.func.root}, .{});

    _ = self.emit(self.ast.exprs.get(self.fdata.ast).Fn.body);

    self.func.end = self.func.addNode(.Return, &.{ self.return_ctrl orelse self.ctrl, self.return_value }, .{});
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

fn emit(self: *Builder, expr: Ast.Id) ?*Func.Node {
    switch (self.getAst(expr)) {
        .Comment => return null,
        .Void => return null,
        .Integer => |e| {
            return self.func.addNode(.CInt, &.{null}, std.fmt.parseInt(i64, self.tokenSrc(e.index), 10) catch unreachable);
        },
        .Ident => |e| {
            return resolveIdent(&self.func, self.scope.items, e.id.index);
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
            @memset(self.scope.items, .{ .LazyPhy = &loop });
            _ = self.emit(e.body);
            _ = self.loops.pop();

            if (loop.control.get(.continume_)) |cscope| {
                self.ctrl = self.func.addNode(.Region, &.{ self.jmp(cscope.ctrl), self.jmp(self.ctrl) }, .{});
                mergeScopes(&self.func, cscope.scope.items, self.scope.items, self.ctrl.?);
            }

            for (loop.scope.items, self.scope.items) |l, *c| {
                if (c.* != .LazyPhy) {
                    std.debug.assert(l.Node.isLazyPhi(loop.ctrl));
                    self.func.setInput(l.Node, 2, c.Node);
                }
            }

            self.func.setInput(loop.ctrl, 1, self.jmp(self.ctrl));

            const break_ = loop.control.get(.break_) orelse {
                self.ctrl = null;
                return self.ctrl;
            };

            for (loop.scope.items, break_.scope.items) |c, *b| {
                if (b.* == .LazyPhy) {
                    b.* = c;
                }
            }

            self.ctrl = break_.ctrl;
            self.scope = break_.scope;

            return self.ctrl;
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
            if (self.return_value) |other| {
                const ret_ctrl = self.return_ctrl.?;

                self.return_ctrl = self.func.addNode(.Region, &.{
                    self.jmp(ret_ctrl),
                    self.jmp(self.ctrl),
                }, .{});
                self.return_value = self.func.addNode(.Phi, &.{ self.return_ctrl, other, value }, {});
            } else {
                self.return_ctrl = self.ctrl;
                self.return_value = value;
            }

            self.ctrl = null;
            return null;
        },
        .BinOp => |e| switch (e.op) {
            .@":=" => {
                self.scope.append(.{ .Node = self.emit(e.rhs).? }) catch unreachable;
                return null;
            },
            .@"=" => {
                self.scope.items[self.getAst(e.lhs).Ident.id.index] = .{ .Node = self.emit(e.rhs).? };
                return null;
            },
            .@"+=", .@"-=" => {
                self.scope.items[self.getAst(e.lhs).Ident.id.index] = .{
                    .Node = self.func.addNode(.BinOp, &.{ null, self.emit(e.lhs), self.emit(e.rhs) }, e.op.assOp()),
                };
                return null;
            },
            else => return self.func.addNode(.BinOp, &.{ null, self.emit(e.lhs), self.emit(e.rhs) }, e.op),
        },
        .Call => |e| {
            self.fdata.tail = false;

            const args = self.arena.alloc(?*Func.Node, 1 + e.args.len()) catch unreachable;
            args[0] = self.ctrl;
            var len: usize = 1;
            for (self.getAstSlice(e.args)) |a| {
                args[len] = self.emit(a);
                if (args[len] != null) len += 1;
            }
            self.ctrl = self.func.addNode(.Call, args[0..len], .{ .id = self.types.resolveFunc(self.file, e.called) });
            self.ctrl = self.func.addNode(.CallEnd, &.{self.ctrl}, .{});
            return self.func.addNode(.Ret, &.{self.ctrl}, {});
        },
        else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
    }
}
