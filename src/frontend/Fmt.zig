buf: *std.ArrayList(u8),
indent: u32 = 0,
is_if_or_while: bool = false,
ast: *const Ast,

const std = @import("std");
const Ast = @import("Ast.zig");
const Id = Ast.Id;
const Slice = Ast.Slice;
const Lexer = @import("Lexer.zig");
const Error = std.mem.Allocator.Error;
const root = @import("hb");
const Fmt = @This();

pub fn needsSpace(c: u8) bool {
    return (c >= 'a' and c <= 'z') or
        (c >= 'A' and c <= 'Z') or
        (c >= '0' and c <= '9') or
        (c >= 127);
}

pub const Class = enum(u8) {
    blank,
    comment,
    keyword,
    identifier,
    directive,
    number,
    string,
    op,
    assign,
    paren,
    bracket,
    colon,
    comma,
    dot,
    ctor,

    pub fn toTtyColor(self: Class) []const std.io.tty.Color {
        return switch (self) {
            .blank => unreachable,
            .comment => &.{.dim},
            .keyword => &.{ .bright_white, .bold },
            .identifier => &.{},
            .directive => &.{ .bright_white, .bold },
            .number => &.{.cyan},
            .string => &.{.green},
            .op => &.{.dim},
            .assign => &.{.dim},
            .paren => &.{.dim},
            .bracket => &.{.dim},
            .colon => &.{.dim},
            .comma => &.{.dim},
            .dot => &.{.dim},
            .ctor => &.{.dim},
        };
    }

    pub fn fromLexeme(leme: Lexer.Lexeme) ?Class {
        return switch (leme) {
            inline else => |t| {
                if (comptime @tagName(t)[0] == '@')
                    return .directive;
                if (comptime std.mem.startsWith(u8, @tagName(t), "ty_"))
                    return .identifier;
                if (comptime std.mem.endsWith(u8, @tagName(t), "="))
                    return .assign;
                if (comptime std.ascii.isLower(@tagName(t)[0]) or
                    @tagName(t)[0] == '$')
                    return .keyword;
                if (comptime std.mem.indexOfAny(
                    u8,
                    @tagName(t),
                    "!^*/%+-<>&|.,~?",
                ) != null)
                    return .op;

                comptime unreachable;
            },
            .true,
            .false,
            .BinInteger,
            .OctInteger,
            .DecInteger,
            .HexInteger,
            .Float,
            => .number,
            .@"<=", .@"==", .@">=" => .op,
            .Ident, .@"$", ._ => .identifier,
            .Comment => .comment,
            .@".(", .@".[", .@".{" => .ctor,
            .@"[", .@"]" => .bracket,
            .@"(", .@")", .@"{", .@"}" => .paren,
            .@"\"", .@"`", .@"'" => .string,
            .@":", .@";", .@"#", .@"\\", .@"," => .comma,
            .@"." => .dot,
            .@"unterminated string" => .comment,
            .Eof => null,
        };
    }
};

pub fn minify(source: [:0]u8) usize {
    var writer = source.ptr;
    var reader = source;
    var prevNeedsWhitespace = false;
    var prevNeedsNewline = false;

    while (true) {
        var lexer = Lexer.init(reader, 0);
        const token = lexer.next();

        switch (token.kind) {
            .Eof => break,
            else => {},
        }

        const cpyLen = token.end - token.pos;

        var prefix: ?u8 = null;
        if (prevNeedsWhitespace and needsSpace(reader[token.pos])) {
            prefix = ' ';
            std.debug.assert(token.pos != 0);
        }

        prevNeedsWhitespace = needsSpace(reader[token.end - 1]);

        const inbetweenNewlines =
            std.mem.count(u8, reader[0..token.pos], "\n") +
            if (token.kind.precedence(false) != 255) @as(usize, 1) else 0;

        const extraPrefixNewlines =
            if (inbetweenNewlines > 1)
                @as(usize, 1) + @intFromBool(token.kind.precedence(false) == 255)
            else
                @intFromBool(prevNeedsNewline);

        if (token.kind == .Comment and reader[token.end - 1] != '/') {
            prevNeedsNewline = true;
            prevNeedsWhitespace = false;
        } else {
            prevNeedsNewline = false;
        }

        const sstr = reader[token.pos..token.end];
        reader = reader[token.end..];

        if (extraPrefixNewlines != 0) {
            for (0..extraPrefixNewlines) |_| {
                writer[0] = '\n';
                writer += 1;
            }
        } else if (prefix) |p| {
            writer[0] = p;
            writer += 1;
        }

        std.mem.copyForwards(u8, writer[0..cpyLen], sstr);
        writer += cpyLen;
    }

    return @intCast(writer - source.ptr);
}

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

fn preserveWrapping(self: *Fmt, id: anytype) Error!bool {
    const pos = self.ast.posOf(id);
    const preceding = self.ast.source[0..pos.index];
    const preceding_whitespace = preceding[std.mem.trimRight(u8, preceding, " \t\r\n").len..];
    const nline_count = std.mem.count(u8, preceding_whitespace, "\n");
    if (nline_count > 0) {
        try self.buf.appendSlice("\n");
        try self.buf.appendNTimes('\t', self.indent + 1);
        return true;
    }
    return false;
}

fn autoInsertSep(self: *Fmt, id: anytype, sep: Lexer.Lexeme) Error!void {
    errdefer unreachable;

    const pos = self.ast.posOf(id);
    const starting_token = Lexer.peek(self.ast.source, pos.index);
    const trimmed = std.mem.trimRight(u8, self.ast.source[0..pos.index], "\n\r\t ;");
    const prev_line = std.mem.lastIndexOfScalar(u8, trimmed, '\n') orelse 0;

    var last_token: Lexer.Lexeme = .Eof;
    {
        var tmp = root.utils.Arena.scrath(null);
        defer tmp.deinit();

        var lexer = Lexer.init(try tmp.arena.allocator().dupeZ(u8, self.ast.source[prev_line..pos.index]), 0);
        while (true) {
            var next = lexer.next();
            while (next.kind == .@";") : (next = lexer.next()) {}
            if (next.kind == .Eof) break;
            // semicolon should never be last
            last_token = next.kind;
        }
    }

    if ((starting_token.kind.precedence(false) < 255 or last_token == .@"return") and last_token != .Comment)
        try self.buf.appendSlice(@tagName(sep));
}

fn fmtDecl(self: *Fmt, d: *Ast.Decl) Error!void {
    try self.fmtExpr(d.bindings);
    if (d.ty.tag() != .Void) {
        try self.buf.appendSlice(": ");
        try self.fmtExpr(d.ty);
        if (d.value.tag() != .Void) {
            try self.buf.appendSlice(" ");
        }
    } else {
        try self.buf.appendSlice(" :");
    }
    if (d.value.tag() != .Void) {
        try self.buf.appendSlice("= ");
        try self.fmtExpr(d.value);
    }
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
        .Die => try self.buf.appendSlice("die"),
        .Ident => |i| try self.buf.appendSlice(Lexer.peekStr(self.ast.source, i.pos.index)),
        .Fn => |f| {
            const fn_prec = 1;
            if (prec < fn_prec) try self.buf.appendSlice("(");
            try self.buf.appendSlice("fn");
            try self.fmtSlice(f.pos.flag.indented, f.args, .@"(", .@",", .@")");
            try self.buf.appendSlice(": ");
            try self.fmtExpr(f.ret);
            try self.buf.appendSlice(" ");
            try self.fmtExpr(f.body);
            if (prec < fn_prec) try self.buf.appendSlice(")");
        },
        .FnPtr => |f| {
            try self.buf.appendSlice("^fn");
            try self.fmtSlice(f.pos.flag.indented, f.args, .@"(", .@",", .@")");
            try self.buf.appendSlice(": ");
            try self.fmtExpr(f.ret);
        },
        .Type => |s| {
            const name = switch (s.kind) {
                inline .@"struct", .@"union", .@"enum" => |t| @tagName(t),
                else => unreachable,
            };

            try self.buf.appendSlice(name);

            if (s.tag.tag() != .Void) {
                try self.buf.appendSlice("(");
                try self.fmtExpr(s.tag);
                try self.buf.appendSlice(")");
            }

            if (s.alignment.tag() != .Void) {
                try self.buf.appendSlice(" align(");
                try self.fmtExpr(s.alignment);
                try self.buf.appendSlice(")");
            }

            const forced = for (self.ast.exprs.view(s.fields)) |e| {
                if (s.kind == .@"enum" and e.tag() != .Tag and (e.tag() == .Decl and
                    self.ast.exprs.get(e).Decl.bindings.tag() != .Tag)) break true;
                if (s.kind != .@"enum" and (e.tag() == .Decl and
                    self.ast.exprs.get(e).Decl.bindings.tag() != .Tag)) break true;
            } else false;
            if (s.pos.flag.indented or forced) try self.buf.appendSlice(" ");
            try self.fmtSliceLow(s.pos.flag.indented or forced, forced, s.fields, .@"{", .@";", .@"}");
        },
        .Directive => |d| {
            try self.buf.appendSlice("@");
            try self.buf.appendSlice(@tagName(d.kind));
            try self.fmtSlice(d.pos.flag.indented, d.args, .@"(", .@",", .@")");
        },
        .Range => |r| {
            try self.fmtExpr(r.start);
            try self.buf.appendSlice("..");
            try self.fmtExpr(r.end);
        },
        .Index => |i| {
            try self.fmtExprPrec(i.base, 0);
            try self.buf.appendSlice("[");
            try self.fmtExpr(i.subscript);
            try self.buf.appendSlice("]");
        },
        .Call => |c| {
            try self.fmtExprPrec(c.called, 0);
            try self.fmtSlice(c.arg_pos.flag.indented, c.args, .@"(", .@",", .@")");
        },
        .Tag => |t| {
            try self.buf.appendSlice(".");
            try self.buf.appendSlice(Lexer.peekStr(self.ast.source, t.index + 1));
        },
        .Defer => |d| {
            try self.buf.appendSlice("defer ");
            try self.fmtExpr(d.*);
        },
        .Unwrap => |u| {
            try self.fmtExprPrec(u.*, 0);
            try self.buf.appendSlice(".?");
        },
        .Deref => |u| {
            try self.fmtExprPrec(u.*, 0);
            try self.buf.appendSlice(".*");
        },
        .Field => |f| {
            try self.fmtExprPrec(f.base, 0);
            _ = try self.preserveWrapping(Ast.Pos{ .index = f.field.index - 1 });
            try self.buf.appendSlice(".");
            try self.buf.appendSlice(Lexer.peekStr(self.ast.source, f.field.index));
        },
        inline .Ctor, .Tupl, .Arry => |v, t| {
            try self.fmtExprPrec(v.ty, 0);
            const start = if (t == .Ctor) .@".{" else if (t == .Tupl) .@".(" else .@".[";
            const sep = .@",";
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
            {
                const prev_is_if_or_while = self.is_if_or_while;
                defer self.is_if_or_while = prev_is_if_or_while;
                self.is_if_or_while = true;
                try self.fmtExpr(i.cond);
            }
            try self.buf.appendSlice(" ");
            try self.fmtExpr(i.then);
            if (i.else_.tag() != .Void) {
                try self.buf.appendSlice(" else ");
                try self.fmtExpr(i.else_);
            }
        },
        .Match => |m| {
            if (m.pos.flag.@"comptime") try self.buf.appendSlice("$");
            try self.buf.appendSlice("match ");
            try self.fmtExpr(m.value);
            try self.buf.appendSlice(" ");
            try self.fmtSlice(true, m.arms, .@"{", .@",", .@"}");
        },
        .Loop => |l| {
            if (l.pos.flag.@"comptime") try self.buf.appendSlice("$");

            if (l.body.tag() == .If and self.ast.exprs.get(l.body).If.pos == l.pos) {
                try self.buf.appendSlice("while");
                if (l.label.tag() != .Void) {
                    try self.buf.appendSlice(":");
                    try self.fmtExpr(l.label);
                }
                try self.buf.appendSlice(" ");
                const if_body = self.ast.exprs.get(l.body).If;
                {
                    const prev_is_if_or_while = self.is_if_or_while;
                    defer self.is_if_or_while = prev_is_if_or_while;
                    self.is_if_or_while = true;
                    try self.fmtExpr(if_body.cond);
                }
                try self.buf.appendSlice(" ");
                try self.fmtExpr(if_body.then);
            } else {
                try self.buf.appendSlice("loop");
                if (l.label.tag() != .Void) {
                    try self.buf.appendSlice(":");
                    try self.fmtExpr(l.label);
                }
                try self.buf.appendSlice(" ");
                try self.fmtExpr(l.body);
            }
        },
        .For => |f| {
            try self.buf.appendSlice("for");
            if (f.label.tag() != .Void) {
                try self.buf.appendSlice(":");
                try self.fmtExpr(f.label);
            }
            try self.buf.appendSlice(" ");
            for (self.ast.exprs.view(f.iters), 0..) |*iter, i| {
                if (i != 0) try self.buf.appendSlice(", ");
                try self.fmtDecl(iter);
            }
            try self.buf.appendSlice(" ");
            try self.fmtExpr(f.body);
        },
        .Break => |b| {
            try self.buf.appendSlice("break");
            if (b.label.tag() != .Void) {
                try self.buf.appendSlice(":");
                try self.fmtExpr(b.label);
            }
        },
        .Continue => |c| {
            try self.buf.appendSlice("continue");
            if (c.label.tag() != .Void) {
                try self.buf.appendSlice(":");
                try self.fmtExpr(c.label);
            }
        },
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
        .Decl => |d| try self.fmtDecl(d),
        .BinOp => |co| {
            var o = co.*;
            if (o.op == .@"=" and o.rhs.tag() == .BinOp and self.ast.exprs.get(o.rhs).BinOp.lhs == o.lhs) {
                o.op = self.ast.exprs.get(o.rhs).BinOp.op.toAssignment();
                o.rhs = self.ast.exprs.get(o.rhs).BinOp.rhs;
            }

            const should_parenthesize = prec < o.op.precedence(self.is_if_or_while);

            if (should_parenthesize) try self.buf.appendSlice("(");

            if (o.lhs.tag() == .BinOp and self.ast.exprs.get(o.lhs).BinOp.rhs.tag() == .Return) {
                try self.buf.appendSlice("(");
                try self.fmtExprPrec(o.lhs, 255);
                try self.buf.appendSlice(")");
            } else {
                try self.fmtExprPrec(o.lhs, o.op.precedence(self.is_if_or_while));
            }

            try self.buf.appendSlice(" ");
            try self.buf.appendSlice(o.op.repr());
            if (!try self.preserveWrapping(o.rhs)) try self.buf.appendSlice(" ");

            if (o.rhs.tag() == .BinOp and self.ast.exprs.get(o.rhs).BinOp
                .op.precedence(self.is_if_or_while) == o.op.precedence(self.is_if_or_while))
            {
                try self.buf.appendSlice("(");
                try self.fmtExprPrec(o.rhs, 255);
                try self.buf.appendSlice(")");
            } else {
                try self.fmtExprPrec(o.rhs, o.op.precedence(self.is_if_or_while));
            }

            if (should_parenthesize) try self.buf.appendSlice(")");
        },
        .Use => |use| {
            try self.buf.writer().print(
                "@{s}({s})",
                .{ @tagName(use.pos.flag.use_kind), Lexer.peekStr(self.ast.source, use.pos.index) },
            );
        },
        .Integer => |i| try self.buf.appendSlice(Lexer.peekStr(self.ast.source, i.pos.index)),
        .Float => |f| try self.buf.appendSlice(Lexer.peekStr(self.ast.source, f.index)),
        .Bool => |b| try self.buf.appendSlice(if (b.value) "true" else "false"),
        .String => |s| try self.buf.appendSlice(Lexer.peekStr(self.ast.source, s.pos.index)),
        .Quotes => |s| try self.buf.appendSlice(Lexer.peekStr(self.ast.source, s.pos.index)),
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
    indent_hint: bool,
    forced: bool,
    slice: anytype,
    start: Lexer.Lexeme,
    sep: Lexer.Lexeme,
    end: Lexer.Lexeme,
) Error!void {
    const prev_is_if_or_while = self.is_if_or_while;
    defer self.is_if_or_while = prev_is_if_or_while;
    self.is_if_or_while = false;

    try self.buf.appendSlice(start.repr());

    const view = self.ast.exprs.view(slice);

    const indent = indent_hint or
        (@TypeOf(view[0]) == Ast.Id and for (view) |v| {
            if (v.tag() == .Comment) break true;
        } else false);

    if (indent) {
        self.indent += 1;
        try self.buf.appendSlice("\n");
    }

    for (view, 1..) |id, i| {
        if (indent) try self.buf.appendNTimes('\t', self.indent);
        if (@TypeOf(id) == Ast.Arg) {
            try self.fmtExpr(id.bindings);
            try self.buf.appendSlice(": ");
            try self.fmtExpr(id.ty);
        } else if (@TypeOf(id) == Ast.CtorField) {
            try self.buf.appendSlice(self.ast.tokenSrc(id.pos.index));
            if (id.pos.index != if (self.ast.exprs.getTyped(.Ident, id.value)) |ident| ident.pos.index else std.math.maxInt(u31)) {
                try self.buf.appendSlice(": ");
                try self.fmtExpr(id.value);
            }
        } else if (@TypeOf(id) == Ast.MatchArm) {
            try self.fmtExpr(id.pat);
            try self.buf.appendSlice(" => ");
            try self.fmtExpr(id.body);
        } else try self.fmtExpr(id);
        if (forced) {
            if (view.len > i and indent) {
                try self.autoInsertSep(view[i], sep);
                try self.preserveSpace(view[i]);
            }
        } else if (indent or i != view.len) {
            if (@TypeOf(id) != Ast.Id or id.tag() != .Comment)
                try self.buf.appendSlice(sep.repr());
            if (!indent) try self.buf.appendSlice(" ");
        }
        if (indent) try self.buf.appendSlice("\n");
    }

    if (indent) {
        self.indent -= 1;
        try self.buf.appendNTimes('\t', self.indent);
    }

    try self.buf.appendSlice(end.repr());
}
