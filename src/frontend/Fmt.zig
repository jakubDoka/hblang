const hb = @import("hbf");
const Lexer = hb.frontend.Lexer.Prelexed;
const std = @import("std");
const utils = hb.utils;

indent: u32 = 0,
in_if_or_while: bool = false,
needs_semi: bool = false,
error_pos: u32 = undefined,
lex: Lexer,
out: *std.Io.Writer,

const Fmt = @This();
const Error = std.Io.Writer.Error || error{SyntaxError};

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
        var lexer = hb.frontend.Lexer.init(reader, 0);
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

pub fn fmt(
    path: []const u8,
    source: [:0]const u8,
    clobber: ?*utils.Arena,
    out: *std.Io.Writer,
    error_out: ?*std.Io.Writer,
    error_colors: std.Io.tty.Config,
) Error!void {
    var tmp = utils.Arena.scrath(clobber);
    defer tmp.deinit();

    const lexed = Lexer.prelex(source, tmp.arena);

    var self = Fmt{
        .lex = .{ .source = source, .tokens = lexed, .cursor = .start },
        .out = out,
    };

    self.run() catch |err| switch (err) {
        error.WriteFailed => return error.WriteFailed,
        error.SyntaxError => {
            if (error_out) |o| {
                hb.frontend.Codegen.reportLow(
                    path,
                    source,
                    self.error_pos,
                    "syntax error, cant format",
                    &.{""},
                    error_colors,
                    o,
                ) catch unreachable;
            }
            return error.SyntaxError;
        },
    };

    return;
}

pub fn run(self: *Fmt) Error!void {
    const iter = self.lex.list(.@";", .@"unterminated string");

    var first = true;
    while (iter.next()) {
        if (self.stickyFollows() and self.lex.cursor != .start) {
            try self.out.writeByte(';');
        }
        if (!first) try self.preserveNewlines(1);
        first = false;
        try self.expr();
    }
}

pub fn preserveNewlines(self: *Fmt, min: usize) !void {
    if (self.lex.cursor == .start) return;
    const prev_pos = self.lex.get(self.lex.cursor.prev()).end;
    const next_pos = self.lex.peekNext().pos;
    const relevant = self.lex.source[prev_pos..next_pos];
    const nline_count = @max(@min(std.mem.count(u8, relevant, "\n"), 2), min);
    try self.out.splatByteAll('\n', nline_count);
}

pub fn expectMany(self: *Fmt, kinds: []const Lexer.Lexeme) Error!void {
    const tok = self.lex.next();
    if (std.mem.indexOfScalar(Lexer.Lexeme, kinds, tok.kind) == null) {
        self.error_pos = tok.pos;
        return error.SyntaxError;
    }
    try self.out.writeAll(tok.view(self.lex.source));
}

pub fn expect(self: *Fmt, kind: Lexer.Lexeme) Error!void {
    const tok = self.lex.next();
    if (tok.kind != kind) {
        self.error_pos = tok.pos;
        return error.SyntaxError;
    }
    try self.out.writeAll(tok.view(self.lex.source));
}

pub fn expr(self: *Fmt) Error!void {
    return self.exprPrec(254);
}

pub fn exprPrec(self: *Fmt, prevPrec: u8) Error!void {
    const tok = self.lex.next();

    if (tok.kind == .@"$") {
        try self.out.writeByte('$');
    }

    try self.out.writeAll(tok.view(self.lex.source));
    switch (tok.kind.expand()) {
        .Ident,
        .@"$",
        .@"'",
        .@"\"",
        .Type,
        .Float,
        ._,
        .DecInteger,
        .BinInteger,
        .OctInteger,
        .HexInteger,
        .true,
        .false,
        .null,
        .idk,
        .die,
        => {},
        .Comment => return,
        .@"." => {
            try self.expect(.Ident);
        },
        .@"fn" => {
            try self.expect(.@"(");
            try self.list(.param, false, .@",", .@")");

            try self.expect(.@":");
            try self.space();
            _ = try self.expr();

            if (self.lex.peekNext().kind.canStartExpression()) {
                try self.space();
                _ = try self.expr();
            } else {
                self.needs_semi = self.lex.peekNext().kind == .@";";
            }
        },
        .@"$if", .@"if" => {
            try self.space();
            try self.expr();
            try self.space();
            try self.expr();
            if (try self.eatMatchPrefix(" ", .@"else")) {
                try self.space();
                try self.expr();
            }
        },
        .@"{" => {
            try self.list(.expr, true, .@";", .@"}");
        },
        .@".{" => {
            try self.list(.ctor_field, false, .@",", .@"}");
        },
        .@".[" => {
            try self.list(.expr, false, .@",", .@"]");
        },
        .@".(" => {
            try self.list(.expr, false, .@",", .@")");
        },
        .@"[" => {
            if (!try self.eatMatch(.@"]")) {
                try self.expr();
                try self.expect(.@"]");
            }
            try self.exprPrec(1);
        },
        .@"&", .@"!", .@"~", .@"-", .@"^", .@"?", .@"#" => {
            try self.exprPrec(1);
        },
        .@"return" => {
            if (self.lex.peekNext().kind.canStartExpression()) {
                try self.space();
                try self.expr();
            } else {
                self.needs_semi = self.lex.peekNext().kind == .@";";
            }
        },
        .@"for" => {
            while (true) {
                try self.space();
                try self.expr();
                if (!try self.eatMatch(.@",")) break;
            }

            try self.space();
            try self.expr();
        },
        .@"break", .@"continue" => {
            try self.label();
        },
        .@"struct", .@"union", .@"enum" => br: {
            if (tok.kind == .@"enum" and self.lex.peekNext().kind == .@")") {
                break :br;
            }

            if (try self.eatMatch(.@"(")) {
                try self.expr();
                try self.expect(.@")");
            }

            if (try self.eatMatchPrefix(" ", .@"align")) {
                try self.expect(.@"(");
                try self.expr();
                try self.expect(.@")");
            }

            try self.listExt(.decl, false, .@"{", .@";", .@"}");
        },
        .match, .@"$match" => {
            try self.space();
            try self.expr();
            try self.space();
            try self.expect(.@"{");
            try self.list(.match_arm, true, .@",", .@"}");
        },
        .loop, .@"$loop" => {
            try self.label();
            try self.space();
            try self.expr();
        },
        .@"while", .@"$while" => {
            try self.label();
            try self.space();
            try self.expr();
            try self.space();
            try self.expr();
        },
        .@"defer" => {
            try self.space();
            try self.expr();
        },
        .@"(" => {
            try self.expr();
            try self.expect(.@")");
        },
        .Directive => {
            _ = try self.expect(.@"(");
            try self.list(.expr, false, .@",", .@")");
        },
        else => {
            self.error_pos = self.lex.pos();
            return error.SyntaxError;
        },
    }

    while (true) {
        const expr_end = self.lex.get(self.lex.cursor.prev()).end;
        const top = self.lex.peekNext();

        const prec = top.kind.precedence(self.in_if_or_while);

        if (prec >= prevPrec) break;

        self.lex.cursor = top.idx.next();

        const nline_count = std.mem.count(u8, self.lex.source[expr_end..top.pos], "\n");
        if (nline_count != 0) {
            try self.nline();
            try self.windent(1);
        } else {
            switch (top.kind) {
                .@":", .@"(", .@".(", .@".[", .@".{", .@"[", .@".", .@".*", .@".?", .@".." => {},
                else => {
                    try self.space();
                },
            }
        }

        try self.out.writeAll(top.view(self.lex.source));

        switch (top.kind) {
            .@"(", .@".(" => {
                try self.list(.expr, false, .@",", .@")");
            },
            .@".[" => {
                try self.list(.expr, false, .@",", .@"]");
            },
            .@".{" => {
                try self.list(.expr, false, .@",", .@"}");
            },
            .@"[" => br: {
                const seen_slc = try self.eatMatch(.@"..");
                if (try self.eatMatch(.@"]")) break :br;
                try self.expr();
                if (!seen_slc and try self.eatMatch(.@"..")) {
                    if (try self.eatMatch(.@"]")) break :br;
                    try self.expr();
                }
                try self.expect(.@"]");
            },
            .@".?", .@".*" => {},
            .@".." => {
                if (self.lex.peekNext().kind.canStartExpression()) {
                    _ = try self.exprPrec(prec);
                }
            },
            .@"." => {
                _ = try self.exprPrec(prec);
            },
            else => {
                try self.space();
                _ = try self.exprPrec(prec);
            },
        }
    }
}

pub fn label(self: *Fmt) !void {
    if (try self.eatMatch(.@":")) try self.expect(.Ident);
}

const ItemKind = enum {
    expr,
    param,
    ctor_field,
    decl,
    match_arm,
};

pub fn list(
    self: *Fmt,
    comptime item: ItemKind,
    force_indent: bool,
    comptime sep: Lexer.Lexeme,
    comptime end: Lexer.Lexeme,
) Error!void {
    return self.listExt(item, force_indent, null, sep, end);
}

pub fn listExt(
    self: *Fmt,
    comptime item: ItemKind,
    force_indent: bool,
    comptime pref: ?Lexer.Lexeme,
    comptime sep: Lexer.Lexeme,
    comptime end: Lexer.Lexeme,
) Error!void {
    var indent = force_indent;

    if (!indent) {
        const prev_pos = self.lex.cursor;
        const iter = self.lex.list(sep, end);

        if (pref) |p| {
            _ = try self.lex.expect(p);
        }

        while (true) {
            switch (iter.nextExt()) {
                .has_next => {},
                .end => break,
                .trailing_end => {
                    indent = true;
                    break;
                },
            }

            if (self.lex.peekNext().kind == .Comment) {
                indent = true;
                break;
            }

            if (item == .decl and self.lex.peekNext().kind != .@".") {
                indent = true;
                break;
            }

            switch (item) {
                .expr,
                .param,
                .ctor_field,
                .decl,
                => self.lex.skipExprDropErr(),
                .match_arm => {
                    self.lex.skipExprDropErr();
                    _ = self.lex.next();
                    self.lex.skipExprDropErr();
                },
            }
        }

        self.lex.cursor = prev_pos;
    }

    if (indent) {
        self.indent += 1;
        if (pref != null) try self.space();
    }

    if (pref) |p| try self.expect(p);

    const iter = self.lex.list(sep, end);
    var i: usize = 0;
    var has_any = false;
    var had_comment = false;
    var is_field = false;
    while (iter.next()) : (i += 1) {
        has_any = true;

        if (i != 0 and !had_comment) {
            if (sep != .@";" or is_field or self.stickyFollows()) {
                try self.out.writeAll(@tagName(sep));
            }

            if (!indent) {
                try self.space();
            }
        }

        if (indent) {
            try self.preserveNewlines(1);
            try self.windent(0);
        }

        is_field = self.lex.peekNext().kind == .@".";
        had_comment = self.lex.peekNext().kind == .Comment;

        switch (item) {
            .param, .expr, .decl => try self.expr(),
            .ctor_field => {
                try self.expectMany(&.{ .@"$", .Ident });
                if (try self.eatMatch(.@":")) {
                    try self.space();
                    _ = try self.expr();
                }
            },
            .match_arm => {
                if (!try self.eatMatch(.@"else")) {
                    try self.expr();
                }
                try self.space();
                try self.expect(.@"=>");
                try self.space();
                try self.expr();
            },
        }

        is_field = is_field or self.needs_semi;
        self.needs_semi = false;
    }

    if (indent) self.indent -= 1;

    if (indent and has_any) {
        if (!had_comment) {
            if (sep != .@";" or is_field or self.stickyFollows()) {
                try self.out.writeAll(@tagName(sep));
            }
        }

        try self.nline();
        try self.windent(0);
    }

    try self.out.writeAll(@tagName(end));
}

pub fn eatMatch(self: *Fmt, comptime tok: Lexer.Lexeme) !bool {
    return self.eatMatchPrefix("", tok);
}

pub fn eatMatchPrefix(self: *Fmt, prefix: []const u8, comptime tok: Lexer.Lexeme) !bool {
    if (self.lex.eatMatchOrRevert(tok)) {
        try self.out.writeAll(prefix);
        try self.out.writeAll(@tagName(tok));
        return true;
    }

    return false;
}

pub fn space(self: *Fmt) !void {
    try self.out.writeByte(' ');
}

pub fn nline(self: *Fmt) !void {
    try self.out.writeByte('\n');
}

pub fn windent(self: *Fmt, extra: usize) !void {
    try self.out.splatByteAll('\t', self.indent + extra);
}

pub fn stickyFollows(self: *Fmt) bool {
    const tok = self.lex.peekNext();
    return tok.kind.precedence(false) != 255;
}
