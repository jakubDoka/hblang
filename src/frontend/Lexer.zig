source: [:0]const u8,
cursor: u32,

const std = @import("std");
//const Types = @import("Types.zig");

const Lexer = @This();
pub const Pos = u32;

pub const Lexeme = enum(u16) {
    Eof = 3,
    Ident,
    Comment,
    Float,

    @"unterminated string",

    @"fn",
    @"return",
    @"defer",
    die,
    @"if",
    @"$if",
    @"else",
    match,
    @"$match",
    @"$loop",
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
    @"'" = '\'',
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
    @"%" = '%',
    @"#" = '#',
    @"[" = '[',
    @"\"" = '"',
    @"\\" = '\\',
    @"]" = ']',
    @"^" = '^',
    @"_" = '_',
    @"{" = '{',
    @"}" = '}',
    @"$" = '$',
    @"`" = '`',
    @"|" = '|',
    @"~" = '~',

    BinInteger = 128 | 2,
    OctInteger = 128 | 8,
    DecInteger = 128 | 10,
    HexInteger = 128 | 16,

    @".*",
    @".?",
    @".{" = '{' + 128,
    @".(" = '(' + 128,
    @".[" = '[' + 128,
    @".." = '.' + 128,

    @"<<" = '<' - 10,
    @">>" = '>' - 10,
    @"=>",

    @"!=" = '!' + 128,
    @"+=" = '+' + 128,
    @"-=" = '-' + 128,
    @"*=" = '*' + 128,
    @"/=" = '/' + 128,
    @"%=" = '%' + 128,
    @"|=" = '|' + 128,
    @"^=" = '^' + 128,
    @"&=" = '&' + 128,
    @"<<=" = '<' - 10 + 128,
    @">>=" = '>' - 10 + 128,
    @":=" = ':' + 128,
    @"<=" = '<' + 128,
    @"==" = '=' + 128,
    @">=" = '>' + 128,
    @"||=" = '|' + 32 + 128,
    @"&&=" = '&' + 32 + 128,

    @"||" = '|' + 32,
    @"&&" = '&' + 32,

    ty_never = 0x100,
    ty_void,
    ty_bool,
    ty_u8,
    ty_u16,
    ty_u32,
    ty_u64,
    ty_uint,
    ty_i8,
    ty_i16,
    ty_i32,
    ty_i64,
    ty_int,
    ty_f32,
    ty_f64,
    ty_type,

    @"@CurrentScope" = 0x200,
    @"@RootScope",
    @"@use",
    @"@TypeOf",
    @"@as",
    @"@int_cast",
    @"@size_of",
    @"@align_of",
    @"@bit_cast",
    @"@ecall",
    @"@syscall",
    @"@embed",
    @"@inline",
    @"@len_of",
    @"@kind_of",
    @"@name_of",
    @"@is_comptime",
    @"@Any",
    @"@error",
    @"@ChildOf",
    @"@target",
    @"@int_to_float",
    @"@float_to_int",
    @"@float_cast",
    @"@has_decl",
    @"@import",

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
            .@":",
            .@":=",
            .@"=",
            .@"+=",
            .@"-=",
            .@"*=",
            .@"/=",
            .@"%=",
            .@"|=",
            .@"^=",
            .@"&=",
            .@"<<=",
            .@">>=",
            .@"&&=",
            .@"||=",
            => 15,
            .@"|", .@"&", .@"||", .@"&&" => 8,
            .@"<", .@">", .@"<=", .@">=", .@"==", .@"!=" => 7,
            .@"^" => 6,
            .@"<<", .@">>" => 5,
            .@"+", .@"-" => 4,
            .@"*", .@"/", .@"%" => 3,
            .@".", .@".{", .@".(", .@".[", .@".?", .@".*" => 0,
            else => 255,
        };
    }

    pub fn isComparison(self: Lexeme) bool {
        return self.precedence() == 7;
    }

    pub fn repr(self: Lexeme) []const u8 {
        return @tagName(self);
    }

    pub fn isAssignment(self: Lexeme) bool {
        return self.precedence() == 15;
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
            '+',
            '-',
            '*',
            '/',
            '%',
            '&',
            '^',
            '|',
            '<' - 10,
            '>' - 10,
            '|' + 32,
            '&' + 32,
            => return @enumFromInt(byte - 128),
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

pub fn init(source: [:0]const u8, cursor: u32) Lexer {
    return Lexer{ .source = source, .cursor = cursor };
}

pub fn peek(source: [:0]const u8, cursor: u32) Token {
    var lexer = init(source, cursor);
    return lexer.next();
}

pub fn peekStr(source: [:0]const u8, cursor: u32) []const u8 {
    return peek(source, cursor).view(source);
}

fn isKeyword(name: []const u8) bool {
    return name[0] == '@' or (name[0] == '$' and name.len != 1) or std.ascii.isLower(name[0]) or name[0] == '_';
}

const keyword_map = b: {
    var count = 0;
    for (std.meta.fields(Lexeme)) |f| count += @intFromBool(isKeyword(f.name));

    var list: [count]struct { []const u8, Lexeme } = undefined;
    var i: usize = 0;
    for (std.meta.fields(Lexeme)) |field| {
        if (!isKeyword(field.name)) continue;
        const start = if (std.mem.startsWith(u8, field.name, "ty_")) 3 else 0;
        list[i] = .{ field.name[start..], @enumFromInt(field.value) };
        i += 1;
    }

    break :b std.StaticStringMap(Lexeme).initComptime(list);
};

pub fn next(self: *Lexer) Token {
    const State = enum {
        start,
        ident,
        equal,
        op_equal,
        angle_bracket,
        shift,
        dot,
        slash,
        line_commnet,
        double_quotes,
        double_quotes_slash,
        quotes,
        quotes_slash,
        and_or,
        short_circuit,
        zero,
        bin,
        oct,
        dec,
        hex,
        dec_dot,
        float,
    };

    var pos = self.cursor;
    const kind: Lexeme = state: switch (State.start) {
        .start => switch (self.source[self.cursor]) {
            0 => break :state .Eof,
            1...32, 127 => {
                self.cursor += 1;
                pos += 1;
                continue :state .start;
            },
            '$', '@', 'a'...'z', 'A'...'Z', '_', 128...255 => continue :state .ident,
            '0' => continue :state .zero,
            '1'...'9' => continue :state .dec,
            '"' => continue :state .double_quotes,
            '\'' => continue :state .quotes,
            '/' => continue :state .slash,
            '.' => continue :state .dot,
            '=' => continue :state .equal,
            '<', '>' => continue :state .angle_bracket,
            '|', '&' => continue :state .and_or,
            ':', '+', '-', '*', '%', '^', '!' => continue :state .op_equal,
            '#', '(', ')', ',', ';', '?', '[', '\\', ']', '`', '{', '}', '~' => |c| {
                self.cursor += 1;
                break :state @enumFromInt(c);
            },
        },
        .ident => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                'a'...'z', 'A'...'Z', '0'...'9', '_', 128...255 => continue :state .ident,
                else => {
                    if (keyword_map.get(self.source[pos..self.cursor])) |k| break :state k;
                    switch (self.source[pos]) {
                        '$' => |c| break :state @enumFromInt(c),
                        else => break :state .Ident,
                    }
                },
            }
        },
        .equal => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '=' => {
                    self.cursor += 1;
                    break :state .@"==";
                },
                '>' => {
                    self.cursor += 1;
                    break :state .@"=>";
                },
                else => break :state .@"=",
            }
        },
        .op_equal => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '=' => {
                    self.cursor += 1;
                    break :state @enumFromInt(self.source[self.cursor - 2] + 128);
                },
                else => break :state @enumFromInt(self.source[self.cursor - 1]),
            }
        },
        .and_or => {
            if (self.source[self.cursor] == self.source[self.cursor + 1]) {
                self.cursor += 1;
                continue :state .short_circuit;
            }
            continue :state .op_equal;
        },
        .angle_bracket => {
            if (self.source[self.cursor] == self.source[self.cursor + 1]) {
                self.cursor += 1;
                continue :state .shift;
            }
            continue :state .op_equal;
        },
        .short_circuit => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '=' => {
                    self.cursor += 1;
                    break :state @enumFromInt(@as(u16, self.source[self.cursor - 2]) + 32 + 128);
                },
                else => break :state @enumFromInt(self.source[self.cursor - 2] + 32),
            }
        },
        .shift => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '=' => {
                    self.cursor += 1;
                    break :state @enumFromInt(self.source[self.cursor - 2] - 10 + 128);
                },
                else => break :state @enumFromInt(self.source[self.cursor - 2] - 10),
            }
        },
        .dot => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '{' => {
                    self.cursor += 1;
                    break :state .@".{";
                },
                '(' => {
                    self.cursor += 1;
                    break :state .@".(";
                },
                '[' => {
                    self.cursor += 1;
                    break :state .@".[";
                },
                '.' => {
                    self.cursor += 1;
                    break :state .@"..";
                },
                '?' => {
                    self.cursor += 1;
                    break :state .@".?";
                },
                '*' => {
                    self.cursor += 1;
                    break :state .@".*";
                },
                else => break :state .@".",
            }
        },
        .slash => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '/' => continue :state .line_commnet,
                '=' => {
                    self.cursor += 1;
                    break :state .@"/=";
                },
                else => break :state .@"/",
            }
        },
        .line_commnet => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '\n', 0 => break :state .Comment,
                else => continue :state .line_commnet,
            }
        },
        .quotes => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '\'' => {
                    self.cursor += 1;
                    break :state .@"'";
                },
                '\\' => {
                    self.cursor += 1;
                    continue :state .quotes_slash;
                },
                0 => break :state .@"unterminated string",
                else => continue :state .quotes,
            }
        },
        .quotes_slash => switch (self.source[self.cursor]) {
            0 => break :state .@"unterminated string",
            else => continue :state .quotes,
        },
        .double_quotes => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '"' => {
                    self.cursor += 1;
                    break :state .@"\"";
                },
                '\\' => {
                    self.cursor += 1;
                    continue :state .double_quotes_slash;
                },
                0 => break :state .@"unterminated string",
                else => continue :state .double_quotes,
            }
        },
        .double_quotes_slash => switch (self.source[self.cursor]) {
            0 => break :state .@"unterminated string",
            else => continue :state .double_quotes,
        },
        .zero => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                'b' => continue :state .bin,
                'o' => continue :state .oct,
                else => {
                    self.cursor -= 1;
                    continue :state .dec;
                },
                'x' => continue :state .hex,
            }
        },
        .bin => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '0'...'1' => continue :state .bin,
                else => break :state .BinInteger,
            }
        },
        .oct => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '0'...'7' => continue :state .oct,
                else => break :state .OctInteger,
            }
        },
        .dec => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '0'...'9' => continue :state .dec,
                '.' => continue :state .dec_dot,
                else => break :state .DecInteger,
            }
        },
        .hex => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '0'...'9', 'a'...'f', 'A'...'F' => continue :state .hex,
                else => break :state .HexInteger,
            }
        },
        .dec_dot => {
            switch (self.source[self.cursor + 1]) {
                '.' => break :state .DecInteger,
                else => continue :state .float,
            }
        },
        .float => {
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '0'...'9' => continue :state .float,
                else => break :state .Float,
            }
        },
    };

    return Token.init(pos, self.cursor, kind);
}

inline fn advance(self: *Lexer) u8 {
    defer self.cursor += 1;
    return self.source[self.cursor];
}

inline fn advanceIf(self: *Lexer, c: u8) bool {
    if (self.source[self.cursor] == c) {
        self.cursor += 1;
        return true;
    }
    return false;
}
