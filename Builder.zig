ast: Ast = undefined,
ctrl: *Func.Node = undefined,
func: Func,

const std = @import("std");
const Ast = @import("parser.zig");
const Func = @import("Func.zig");
const Codegen = @This();

pub fn init(gpa: std.mem.Allocator) Codegen {
    return .{
        .func = .init(gpa),
    };
}

pub fn deinit(self: *Codegen) void {
    _ = self; // autofix
}

pub fn generate(self: *Codegen, ast: Ast, func: Ast.Id) void {
    self.ast = ast;
    self.ctrl = self.func.addNode(.Entry, &.{self.func.root}, .{});

    _ = self.emit(self.ast.exprs.get(func).Fn.body);

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
        .Block => |e| {
            for (self.getAstSlice(e.stmts)) |s| {
                _ = self.emit(s);
            }

            return self.ctrl;
        },
        .Return => |e| {
            self.ctrl = self.func.addNode(.Return, &.{ self.ctrl, self.emit(e.value) }, .{});
            return self.ctrl;
        },
        else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
    }
}
