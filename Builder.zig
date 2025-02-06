file: Types.File = undefined,
ast: Ast = undefined,
arena: std.mem.Allocator = undefined,
types: *Types,
ctrl: *Func.Node = undefined,
func: Func,
scope: std.ArrayListUnmanaged(*Func.Node) = .{},

const std = @import("std");
const Ast = @import("parser.zig");
const Func = @import("Func.zig");
const Types = @import("Types.zig");
const Codegen = @This();

pub fn init(gpa: std.mem.Allocator, types: *Types) Codegen {
    return .{
        .types = types,
        .func = .init(gpa),
    };
}

pub fn deinit(self: *Codegen) void {
    self.func.deinit();
    self.* = undefined;
}

pub fn build(self: *Codegen, file: Types.File, func: Types.Func) void {
    self.file = file;
    self.ast = self.types.getFile(file).*;
    self.arena = self.func.beginTmpAlloc();
    self.scope.items.len = 0;

    const fdata: *Types.FuncData = self.types.get(func);

    for (fdata.args, 0..) |ty, i| {
        std.debug.assert(ty == .uint);
        const arg = self.func.addNode(.Arg, &.{self.func.root}, i);
        self.scope.append(self.arena, arg) catch unreachable;
    }

    self.ctrl = self.func.addNode(.Entry, &.{self.func.root}, .{});

    _ = self.emit(self.ast.exprs.get(fdata.ast).Fn.body);

    std.debug.assert(self.ctrl.kind == .Return);
    self.func.end = self.ctrl;
}

inline fn getAst(self: *Codegen, expr: Ast.Id) Ast.Expr {
    return self.ast.exprs.get(expr);
}

inline fn getAstSlice(self: *Codegen, slice: Ast.Slice) []Ast.Id {
    return self.ast.exprs.view(slice);
}

inline fn tokenSrc(self: *Codegen, idx: u32) []const u8 {
    return self.ast.tokenSrc(idx);
}

fn emit(self: *Codegen, expr: Ast.Id) *Func.Node {
    switch (self.getAst(expr)) {
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
        .Return => |e| {
            const value = self.emit(e.value);
            self.ctrl = self.func.addNode(.Return, &.{ self.ctrl, value }, .{});
            return self.ctrl;
        },
        .BinOp => |e| {
            return self.func.addNode(.BinOp, &.{ null, self.emit(e.lhs), self.emit(e.rhs) }, e.op);
        },
        .Call => |e| {
            const args = self.arena.alloc(?*Func.Node, 1 + e.args.len()) catch unreachable;
            args[0] = self.ctrl;
            for (self.getAstSlice(e.args), args[1..]) |a, *s| s.* = self.emit(a);
            self.ctrl = self.func.addNode(.Call, args, .{ .id = self.types.resolveFunc(self.file, e.called) });
            self.ctrl = self.func.addNode(.CallEnd, &.{self.ctrl}, .{});
            return self.func.addNode(.Ret, &.{self.ctrl}, {});
        },
        else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
    }
}
