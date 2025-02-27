source: []const u8,
cursor: u32,

const std = @import("std");
const Types = @import("Types.zig");

const Lexer = @This();
pub const Pos = u32;

pub const Lexeme = enum(u16) {
    Eof = 3,
    Ident,
    Comment,
    Integer,

    @"fn",
    @"return",
    @"if",
    @"$if",
    @"$loop",
    @"else",
    loop,
    @"break",
    @"continue",
    @"enum",
    @"union",
    @"struct",
    @"align",
    null,
    idk,
    true,
    false,

    @"!" = '!',
    @"&" = '&',
    @"(" = '(',
    @")" = ')',
    @"*" = '*',
    @"+" = '+',
    @"," = ',',
    @"-" = '-',
    @"." = '.',
    @"/" = '/',
    @":" = ':',
    @";" = ';',
    @"<" = '<',
    @"=" = '=',
    @">" = '>',
    @"?" = '?',
    @"@" = '@',
    @"[" = '[',
    @"\"" = '"',
    @"]" = ']',
    @"^" = '^',
    @"_" = '_',
    @"{" = '{',
    @"}" = '}',
    @"$" = '$',

    @".{" = '{' + 128,
    @".(" = '(' + 128,
    @".[" = '[' + 128,
    @".." = '.' + 128,

    @"!=" = '!' + 128,
    @"+=" = '+' + 128,
    @"-=" = '-' + 128,
    @":=" = ':' + 128,
    @"<=" = '<' + 128,
    @"==" = '=' + 128,
    @">=" = '>' + 128,

    ty_never = 0x100,
    ty_void,
    ty_bool,
    ty_u8,
    ty_u16,
    ty_u32,
    ty_uint,
    ty_i8,
    ty_i16,
    ty_i32,
    ty_int,
    ty_type,

    @"@CurrentScope" = 0x200,
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

    comptime {
        //std.debug.assert(Lexeme.@"@TypeOf".expand().Directive == .TypeOf);
        //std.debug.assert(Lexeme.ty_never.expand().Type == .never);
        //@compileLog(std.mem.asBytes(&Lexeme.@"@")[0..2].*, std.mem.asBytes(&Expanded.@"@")[0..2].*);
        //std.debug.assert(Lexeme.@"@".expand() == .@"@");
    }

    const data = @typeInfo(Lexeme).@"enum";

    fn SubEnum(comptime prefix: []const u8) type {
        var type_count = 0;
        var start = std.math.maxInt(u16) + 1;
        for (data.fields, 0..) |f, i| if (f.name.len > prefix.len and std.mem.startsWith(u8, f.name, prefix)) {
            type_count += 1;
            start = @min(i, start);
        };

        var fields: [type_count]std.builtin.Type.EnumField = undefined;
        for (&fields, data.fields[start..][0..type_count], 0..) |*v, ty, i| {
            v.* = .{ .name = ty.name[prefix.len..], .value = i };
        }

        return @Type(.{ .@"enum" = .{
            .tag_type = u8,
            .fields = &fields,
            .decls = &.{},
            .is_exhaustive = true,
        } });
    }

    pub const Type = SubEnum("ty_");
    pub const Directive = SubEnum("@");

    pub const Expanded = b: {
        const void_variant_count = for (data.fields, 0..) |f, i| {
            if (f.value > 255) break i;
        } else unreachable;

        const fields = data.fields[0..void_variant_count].* ++ [_]std.builtin.Type.EnumField{
            .{ .name = "Type", .value = 1 },
            .{ .name = "Directive", .value = 2 },
        };

        const tag = @Type(.{ .@"enum" = .{
            .tag_type = u8,
            .fields = &fields,
            .decls = &.{},
            .is_exhaustive = true,
        } });

        var variants: [void_variant_count + 2]std.builtin.Type.UnionField = undefined;
        for (variants[0..void_variant_count], data.fields[0..void_variant_count]) |*v, vv| {
            v.* = .{ .name = vv.name, .type = void, .alignment = 0 };
        }

        variants[void_variant_count + 0] = .{ .name = "Type", .type = Type, .alignment = @alignOf(Type) };
        variants[void_variant_count + 1] = .{ .name = "Directive", .type = Directive, .alignment = @alignOf(Directive) };

        break :b @Type(.{ .@"union" = .{ .layout = .@"extern", .tag_type = tag, .fields = &variants, .decls = &.{} } });
    };

    pub fn expand(self: Lexeme) Expanded {
        var vl = @intFromEnum(self);
        if (vl >= 256) vl = @byteSwap(vl);
        return @bitCast(vl);
    }

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
        const byte = @intFromEnum(self);
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
                    if (comptime !std.ascii.isLower(field.name[0]) and field.name[0] != '_') continue;
                    const start = comptime if (std.mem.startsWith(u8, field.name, "ty_")) 3 else 0;
                    if (std.mem.eql(u8, field.name[start..], ident)) break :b @field(Lexeme, field.name);
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
