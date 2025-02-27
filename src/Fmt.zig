buf: *std.ArrayList(u8),
indent: u32 = 0,
ast: *const Ast,

const std = @import("std");
const Ast = @import("Ast.zig");
const Id = Ast.Id;
const Slice = Ast.Slice;
const Lexer = @import("Lexer.zig");
const Error = std.mem.Allocator.Error;
const Fmt = @This();

pub fn fmt(self: *Fmt) Error!void {
    const items = self.ast.exprs.view(self.ast.items);
    for (items, 1..) |id, i| {
        try self.fmtExpr(id);
        if (items.len > i) {
            if (id.tag() != .Comment) try self.autoInsertSep(items[i], .@";");
            try self.preserveSpace(items[i]);
        }
        try self.buf.appendSlice("\n");
    }
}

pub fn fmtExpr(self: *Fmt, id: Id) Error!void {
    return self.fmtExprPrec(id, 255);
}

fn preserveSpace(self: *Fmt, id: anytype) Error!void {
    const pos = self.ast.posOf(id);
    const preceding = self.ast.source[0..pos.index];
    const preceding_whitespace = preceding[std.mem.trimRight(u8, preceding, " \t\r\n").len..];
    const nline_count = std.mem.count(u8, preceding_whitespace, "\n");
    if (nline_count > 1) try self.buf.appendSlice("\n");
}

fn autoInsertSep(self: *Fmt, id: anytype, sep: Lexer.Lexeme) Error!void {
    const pos = self.ast.posOf(id);
    const starting_token = Lexer.peek(self.ast.source, pos.index);
    if (starting_token.kind.precedence() < 255) try self.buf.appendSlice(@tagName(sep));
}

fn fmtExprPrec(self: *Fmt, id: Id, prec: u8) Error!void {
    switch (self.ast.exprs.get(id)) {
        .Void => {},
        .Wildcard => try self.buf.appendSlice("_"),
        .Comment => |c| {
            const comment_token = Lexer.peek(self.ast.source, c.index);
            const content = std.mem.trimRight(u8, comment_token.view(self.ast.source), "\n");
            try self.buf.appendSlice(content);
        },
        .Idk => try self.buf.appendSlice("idk"),
        .Ident => |i| try self.buf.appendSlice(Lexer.peekStr(self.ast.source, i.pos.index)),
        .Fn => |f| {
            try self.buf.appendSlice("fn");
            try self.fmtSlice(f.pos.flag.indented, f.args, .@"(", .@",", .@")");
            try self.buf.appendSlice(": ");
            try self.fmtExpr(f.ret);
            try self.buf.appendSlice(" ");
            try self.fmtExpr(f.body);
        },
        inline .Union, .Struct, .Enum => |s, t| {
            const name = comptime b: {
                var nm = @tagName(t)[0..].*;
                nm[0] = std.ascii.toLower(nm[0]);
                break :b nm[0..] ++ "";
            };

            try self.buf.appendSlice(name);

            if (s.alignment.tag() != .Void) {
                try self.buf.appendSlice(" align(");
                try self.fmtExpr(s.alignment);
                try self.buf.appendSlice(")");
            }

            const forced = for (self.ast.exprs.view(s.fields)) |e| {
                if (t == .Enum and e.tag() != .Tag) break true;
                if (t != .Enum and self.ast.exprs.get(e).BinOp.lhs.tag() != .Tag) break true;
            } else false;
            if (s.pos.flag.indented or forced) try self.buf.appendSlice(" ");
            try self.fmtSliceLow(s.pos.flag.indented or forced, forced, s.fields, .@"{", .@";", .@"}");
        },
        .Directive => |d| {
            try self.buf.appendSlice(Lexer.peekStr(self.ast.source, d.pos.index));
            try self.fmtSlice(d.pos.flag.indented, d.args, .@"(", .@",", .@")");
        },
        .Range => |r| {
            try self.fmtExpr(r.start);
            try self.buf.appendSlice("..");
            try self.fmtExpr(r.end);
        },
        .Index => |i| {
            try self.fmtExpr(i.base);
            try self.buf.appendSlice("[");
            try self.fmtExpr(i.subscript);
            try self.buf.appendSlice("]");
        },
        .Call => |c| {
            try self.fmtExpr(c.called);
            try self.fmtSlice(c.arg_pos.flag.indented, c.args, .@"(", .@",", .@")");
        },
        .Tag => |t| {
            try self.buf.appendSlice(".");
            try self.buf.appendSlice(Lexer.peekStr(self.ast.source, t.index + 1));
        },
        .Unwrap => |u| {
            try self.fmtExpr(u);
            try self.buf.appendSlice(".?");
        },
        .Deref => |u| {
            try self.fmtExpr(u);
            try self.buf.appendSlice(".*");
        },
        .Field => |f| {
            try self.fmtExpr(f.base);
            try self.buf.appendSlice(".");
            try self.buf.appendSlice(Lexer.peekStr(self.ast.source, f.field.index));
        },
        inline .Ctor, .Tupl, .Arry => |v, t| {
            try self.fmtExprPrec(v.ty, 0);
            const start = if (t == .Ctor) .@".{" else if (t == .Tupl) .@".(" else .@".[";
            const sep = if (t == .Ctor) .@";" else .@",";
            const end = if (t == .Ctor) .@"}" else if (t == .Tupl) .@")" else .@"]";
            try self.fmtSlice(v.pos.flag.indented, v.fields, start, sep, end);
        },
        .Buty => |b| try self.buf.appendSlice(Lexer.peekStr(self.ast.source, b.pos.index)),
        .Block => |b| {
            try self.fmtSliceLow(b.pos.flag.indented, true, b.stmts, .@"{", .@";", .@"}");
        },
        .SliceTy => |s| {
            const unprec = 1;
            if (prec < unprec) try self.buf.appendSlice("(");
            try self.buf.appendSlice("[");
            try self.fmtExpr(s.len);
            try self.buf.appendSlice("]");
            try self.fmtExpr(s.elem);
            if (prec < unprec) try self.buf.appendSlice(")");
        },
        .If => |i| {
            if (i.pos.flag.@"comptime") try self.buf.appendSlice("$");
            try self.buf.appendSlice("if ");
            try self.fmtExpr(i.cond);
            try self.buf.appendSlice(" ");
            try self.fmtExpr(i.then);
            if (i.else_.tag() != .Void) {
                try self.buf.appendSlice(" else ");
                try self.fmtExpr(i.else_);
            }
        },
        .Loop => |l| {
            if (l.pos.flag.@"comptime") try self.buf.appendSlice("$");
            try self.buf.appendSlice("loop ");
            try self.fmtExpr(l.body);
        },
        .Break => try self.buf.appendSlice("break"),
        .Continue => try self.buf.appendSlice("continue"),
        .Return => |r| {
            try self.buf.appendSlice("return");
            if (r.value.tag() != .Void) {
                try self.buf.appendSlice(" ");
                try self.fmtExpr(r.value);
            }
        },
        .UnOp => |o| {
            const unprec = 1;
            if (prec < unprec) try self.buf.appendSlice("(");
            try self.buf.appendSlice(o.op.repr());
            try self.fmtExprPrec(o.oper, unprec);
            if (prec < unprec) try self.buf.appendSlice(")");
        },
        .BinOp => |co| {
            var o = co;
            if (o.op == .@"=" and self.ast.exprs.get(o.rhs) == .BinOp and self.ast.exprs.get(o.rhs).BinOp.lhs == o.lhs) {
                o.op = self.ast.exprs.get(o.rhs).BinOp.op.toAssignment();
                o.rhs = self.ast.exprs.get(o.rhs).BinOp.rhs;
            }
            if (prec < o.op.precedence()) try self.buf.appendSlice("(");
            try self.fmtExprPrec(o.lhs, o.op.precedence());
            // TODO: linebreaks
            if (o.op != .@":") try self.buf.appendSlice(" ");
            try self.buf.appendSlice(o.op.repr());
            try self.buf.appendSlice(" ");
            if (o.rhs.tag() == .BinOp and self.ast.exprs.get(o.rhs).BinOp.op.precedence() == o.op.precedence()) {
                try self.buf.appendSlice("(");
                try self.fmtExprPrec(o.rhs, 255);
                try self.buf.appendSlice(")");
            } else {
                try self.fmtExprPrec(o.rhs, o.op.precedence());
            }
            if (prec < o.op.precedence()) try self.buf.appendSlice(")");
        },
        .Use => |use| {
            try self.buf.writer().print(
                "@{s}({s})",
                .{ @tagName(use.pos.flag.use_kind), Lexer.peekStr(self.ast.source, use.pos.index) },
            );
        },
        .Integer => |i| try self.buf.appendSlice(Lexer.peekStr(self.ast.source, i.index)),
        .Bool => |b| try self.buf.appendSlice(if (b.value) "true" else "false"),
        .String => |s| try self.buf.appendSlice(Lexer.peekStr(self.ast.source, s.pos.index)),
        .Null => try self.buf.appendSlice("null"),
    }
}

inline fn fmtSlice(
    self: *Fmt,
    indent: bool,
    slice: anytype,
    start: Lexer.Lexeme,
    sep: Lexer.Lexeme,
    end: Lexer.Lexeme,
) Error!void {
    return self.fmtSliceLow(indent, false, slice, start, sep, end);
}

fn fmtSliceLow(
    self: *Fmt,
    indent: bool,
    forced: bool,
    slice: anytype,
    start: Lexer.Lexeme,
    sep: Lexer.Lexeme,
    end: Lexer.Lexeme,
) Error!void {
    try self.buf.appendSlice(start.repr());

    if (indent) {
        self.indent += 1;
        try self.buf.appendSlice("\n");
    }

    const view = self.ast.exprs.view(slice);
    for (view, 1..) |id, i| {
        if (indent) for (0..self.indent) |_| try self.buf.appendSlice("\t");
        if (@TypeOf(id) == Ast.Arg) {
            try self.fmtExpr(id.bindings);
            try self.buf.appendSlice(": ");
            try self.fmtExpr(id.ty);
        } else try self.fmtExpr(id);
        if (forced) {
            if (view.len > i and indent) {
                try self.autoInsertSep(view[i], sep);
                try self.preserveSpace(view[i]);
            }
        } else if (indent or i != view.len) {
            try self.buf.appendSlice(sep.repr());
            if (!indent) try self.buf.appendSlice(" ");
        }
        if (indent) try self.buf.appendSlice("\n");
    }

    if (indent) {
        self.indent -= 1;
        for (0..self.indent) |_| try self.buf.appendSlice("\t");
    }

    try self.buf.appendSlice(end.repr());
}
