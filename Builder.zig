types: *Types,
func: Func,
scope: std.ArrayListUnmanaged(*Func.Node) = .{},
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
    self.scope.items.len = 0;
    self.fdata = self.types.get(func);
    self.return_value = null;
    self.return_ctrl = null;

    var i: usize = 0;
    for (self.fdata.args) |ty| {
        if (ty == .void) continue;
        std.debug.assert(ty == .uint);
        const arg = self.func.addNode(.Arg, &.{self.func.root}, i);
        self.scope.append(self.arena, arg) catch unreachable;
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

fn emit(self: *Builder, expr: Ast.Id) ?*Func.Node {
    switch (self.getAst(expr)) {
        .Comment => return null,
        .Integer => |e| {
            return self.func.addNode(.CInt, &.{null}, std.fmt.parseInt(i64, self.tokenSrc(e.index), 10) catch unreachable);
        },
        .Ident => |e| {
            return self.scope.items[e.id.index];
        },
        .Block => |e| {
            for (self.getAstSlice(e.stmts)) |s| {
                _ = self.emit(s);
            }

            return self.ctrl;
        },
        .If => |e| {
            const cond = self.emit(e.cond);
            const if_node = self.func.addNode(.If, &.{ self.ctrl, cond }, .{});

            var saved_scope = self.scope.clone(self.arena) catch unreachable;
            self.ctrl = self.func.addNode(.Then, &.{if_node}, .{});
            _ = self.emit(e.then);
            const then_cfg = self.ctrl;

            std.mem.swap(std.ArrayListUnmanaged(*Func.Node), &self.scope, &saved_scope);

            self.ctrl = self.func.addNode(.Else, &.{if_node}, .{});
            _ = self.emit(e.else_);
            const else_cfg = self.ctrl;

            self.ctrl = self.func.addNode(.Region, &.{
                self.func.addNode(.Jmp, &.{then_cfg}, .{}),
                self.func.addNode(.Jmp, &.{else_cfg}, .{}),
            }, .{});

            const then_scope = saved_scope;

            for (then_scope.items, self.scope.items) |then, *else_| {
                if (then != else_.*) {
                    else_.* = self.func.addNode(.Phi, &.{ self.ctrl, then, else_.* }, {});
                }
            }

            return self.ctrl;
        },
        //.Loop => |e| {

        //},
        .Return => |e| {
            const value = self.emit(e.value);
            if (self.return_value) |other| {
                const ret_ctrl = self.return_ctrl.?;

                self.return_ctrl = self.func.addNode(.Region, &.{
                    self.func.addNode(.Jmp, &.{ret_ctrl}, .{}),
                    self.func.addNode(.Jmp, &.{self.ctrl}, .{}),
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
                self.scope.append(self.arena, self.emit(e.rhs).?) catch unreachable;
                return null;
            },
            .@"=" => {
                self.scope.items[self.getAst(e.lhs).Ident.id.index] = self.emit(e.rhs).?;
                return null;
            },
            .@"+=", .@"-=" => {
                self.scope.items[self.getAst(e.lhs).Ident.id.index] =
                    self.func.addNode(.BinOp, &.{ null, self.emit(e.lhs), self.emit(e.rhs) }, e.op.assOp());
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
