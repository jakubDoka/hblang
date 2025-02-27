source: []const u8,
cursor: u32,

const std = @import("std");
const Types = @import("Types.zig");

const Lexer = @This();
pub const Pos = u32;

pub const Lexeme = enum(u8) {
    Eof = 0,
    void,
    bool,
    u8,
    u16,
    u32,
    uint,
    i8,
    i16,
    i32,
    int,
    type,
    @"fn",
    @"return",
    @"if",
    @"$if",
    @"$loop",
    @"else",
    loop,
    @"break",
    @"continue",
    @"union",
    @"struct",
    null,
    idk,
    true,
    false,
    @"@" = '@',
    @"$" = '$',
    @"\"" = '"',
    @"{" = '{',
    @"}" = '}',
    @"[" = '[',
    @"]" = ']',
    @"(" = '(',
    @")" = ')',
    @":" = ':',
    @";" = ';',
    @"," = ',',
    @"." = '.',
    @"&" = '&',
    @"^" = '^',
    @"!" = '!',
    @"?" = '?',
    @"-" = '-',
    @"+" = '+',
    @"*" = '*',
    @"/" = '/',
    @"<" = '<',
    @">" = '>',
    @"=" = '=',
    Ident = 128,
    Comment,
    Integer,
    @"@CurrentScope",
    @"@use",
    @"@TypeOf",
    @"@as",
    @"@int_cast",
    @"@size_of",
    @"@align_of",
    @"@bit_cast",
    @"@ecall",
    @"@embed",
    @"@inline",
    @"@len_of",
    @"@kind_of",
    @"@Any",
    @"@error",
    @"@ChildOf",
    @"@target",
    @"_",
    @".{",
    @".(",
    @".[",
    @"..",
    @"+=" = '+' + 128,
    @"-=" = '-' + 128,
    @":=" = ':' + 128,
    @"==" = '=' + 128,
    @"!=" = '!' + 128,
    @"<=" = '<' + 128,
    @">=" = '>' + 128,

    // TODO: reverse the order because this does not look like precedence
    pub fn precedence(self: Lexeme) u8 {
        return switch (self) {
            .@":" => 16,
            .@"=", .@":=", .@"+=", .@"-=" => 15,
            .@"<", .@">", .@"<=", .@">=", .@"==", .@"!=" => 6,
            .@"+", .@"-" => 4,
            .@"*", .@"/" => 3,
            .@".", .@".{", .@".(", .@".[" => 0,
            else => 255,
        };
    }

    pub fn toBinOp(self: Lexeme, ty: Types.Id) @import("graph.zig").BinOp {
        const unsigned = ty.isUnsigned();
        return switch (self) {
            .@"+" => .iadd,
            .@"-" => .isub,
            .@"*" => .imul,
            .@"/" => if (unsigned) .udiv else .sdiv,
            .@"<" => if (unsigned) .ult else .slt,
            .@">" => if (unsigned) .ugt else .sgt,
            .@"<=" => if (unsigned) .ule else .sle,
            .@">=" => if (unsigned) .uge else .sge,
            .@"==" => .eq,
            .@"!=" => .ne,
            else => std.debug.panic("{s}", .{@tagName(self)}),
        };
    }

    pub fn isComparison(self: Lexeme) bool {
        return self.precedence() == 6;
    }

    pub fn repr(self: Lexeme) []const u8 {
        return @tagName(self);
    }

    pub fn isAssignment(self: Lexeme) bool {
        return self.precedence() == 15;
    }

    pub fn assOp(self: Lexeme) Lexeme {
        return @enumFromInt(@as(u8, @intFromEnum(self) - 128));
    }

    pub fn cantStartExpression(self: Lexeme) bool {
        return switch (self) {
            .@"}", .@";", .@",", .@")" => true,
            else => false,
        };
    }

    pub fn innerOp(self: Lexeme) ?Lexeme {
        const byte: u8 = @intFromEnum(self);
        switch (byte -| 128) {
            '+', '-' => return @enumFromInt(byte - 128),
            else => return null,
        }
    }

    pub fn toAssignment(self: Lexeme) Lexeme {
        return @enumFromInt(@intFromEnum(self) + 128);
    }

    pub fn format(self: *const Lexeme, comptime _: anytype, _: anytype, writer: anytype) !void {
        try writer.writeAll(@tagName(self.*));
    }
};

pub const Token = struct {
    pos: Pos,
    end: u32,
    kind: Lexeme,

    pub fn init(pos: Pos, end: u32, kind: Lexeme) Token {
        return Token{ .pos = pos, .end = end, .kind = kind };
    }

    pub fn view(self: Token, source: []const u8) []const u8 {
        return source[self.pos..self.end];
    }
};

pub fn init(source: []const u8, cursor: u32) Lexer {
    return Lexer{ .source = source, .cursor = cursor };
}

pub fn peek(source: []const u8, cursor: u32) Token {
    var lexer = init(source, cursor);
    return lexer.next();
}

pub fn peekStr(source: []const u8, cursor: u32) []const u8 {
    return peek(source, cursor).view(source);
}

pub fn next(self: *Lexer) Token {
    while (self.cursor < self.source.len) {
        const pos = self.cursor;
        self.cursor += 1;
        const kind: Lexeme = switch (self.source[pos]) {
            0...32 => continue,
            '@' => b: {
                while (self.cursor < self.source.len) switch (self.source[self.cursor]) {
                    'a'...'z', 'A'...'Z', '_' => self.cursor += 1,
                    else => break,
                };

                const ident = self.source[pos..self.cursor];
                inline for (std.meta.fields(Lexeme)) |field| {
                    if (field.name[0] != '@') continue;
                    if (std.mem.eql(u8, field.name, ident)) break :b @field(Lexeme, field.name);
                }

                break :b .@"@";
            },
            '$' => b: {
                while (self.cursor < self.source.len) switch (self.source[self.cursor]) {
                    'a'...'z', 'A'...'Z', '0'...'9', '_', 128...255 => self.cursor += 1,
                    else => break,
                };

                const ident = self.source[pos..self.cursor];
                inline for (std.meta.fields(Lexeme)) |field| {
                    if (field.name[0] != '$') continue;
                    if (std.mem.eql(u8, field.name, ident)) break :b @field(Lexeme, field.name);
                }

                break :b .@"$";
            },
            'a'...'z', 'A'...'Z', '_', 128...255 => b: {
                while (self.cursor < self.source.len) switch (self.source[self.cursor]) {
                    'a'...'z', 'A'...'Z', '0'...'9', '_', 128...255 => self.cursor += 1,
                    else => break,
                };

                const ident = self.source[pos..self.cursor];
                inline for (std.meta.fields(Lexeme)) |field| {
                    if (comptime !std.ascii.isLower(field.name[0]) and field.name[0] != '_' and !std.mem.eql(u8, field.name, "Self")) continue;
                    if (std.mem.eql(u8, field.name, ident)) break :b @field(Lexeme, field.name);
                }
                break :b .Ident;
            },
            '0'...'9' => b: {
                while (self.cursor < self.source.len) switch (self.source[self.cursor]) {
                    '0'...'9' => self.cursor += 1,
                    else => break,
                };
                break :b .Integer;
            },
            '"' => b: {
                while (self.cursor < self.source.len) switch (self.source[self.cursor]) {
                    '"' => break,
                    '\\' => self.cursor += 2,
                    else => self.cursor += 1,
                };
                self.cursor += 1;
                break :b .@"\"";
            },
            '/' => |c| if (self.advanceIf('*')) ml: {
                var nesting: u8 = 1;
                while (nesting > 0) switch (self.advance() orelse break) {
                    '/' => if (self.advanceIf('*')) {
                        nesting += 1;
                    },
                    '*' => if (self.advanceIf('/')) {
                        nesting -= 1;
                    },
                    else => {},
                };
                break :ml .Comment;
            } else if (self.advanceIf('/')) l: {
                while (self.advance()) |ch| if (ch == '\n') break;
                break :l .Comment;
            } else @enumFromInt(c),
            '.' => if (self.advanceIf('{'))
                .@".{"
            else if (self.advanceIf('('))
                .@".("
            else if (self.advanceIf('.'))
                .@".."
            else if (self.advanceIf('['))
                .@".["
            else
                .@".",
            ':', '<', '>', '+', '-', '=', '!' => |c| @enumFromInt(if (self.advanceIf('=')) c + 128 else c),
            else => |c| @enumFromInt(c),
        };
        return Token.init(pos, self.cursor, kind);
    }

    return Token.init(self.cursor, self.cursor, .Eof);
}

inline fn advance(self: *Lexer) ?u8 {
    if (self.cursor < self.source.len) {
        defer self.cursor += 1;
        return self.source[self.cursor];
    }
    return null;
}

inline fn advanceIf(self: *Lexer, c: u8) bool {
    if (self.source[self.cursor] == c) {
        self.cursor += 1;
        return true;
    }
    return false;
}
