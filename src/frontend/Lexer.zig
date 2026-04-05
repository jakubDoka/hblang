source: [:0]const u8,
cursor: u32,

const std = @import("std");
const hb = @import("hbf");
const utils = hb.utils;
const File = hb.frontend.DeclIndex.File;

const Lexer = @This();
pub const Pos = u32;

pub const Lexeme = enum(u16) {
    Eof = 3,
    Ident,
    Comment,
    Float,

    // TODO: this should be a cached function call that points to a comptime
    // value basically equivalent to using an @eval but better because the
    // resulting value is cached
    @"$fn",
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
    @"$while",
    @"while",
    @"$for",
    @"for",
    @"break",
    @"continue",
    @"struct",
    @"union",
    @"enum",
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

    @"unterminated string",

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

    @"||" = '|' + 32,
    @"&&" = '&' + 32,

    @"||=" = '|' + 32 + 1,
    @"&&=" = '&' + 32 + 1,

    @"$||" = '|' + 32 + 2,
    @"$&&" = '&' + 32 + 2,

    ty_never = 0x100,
    ty_void,
    ty_bool,
    ty_u8,
    ty_u16,
    ty_u32,
    ty_uint,
    ty_u64,
    ty_i8,
    ty_i16,
    ty_i32,
    ty_int,
    ty_i64,
    ty_f32,
    ty_f64,
    ty_type,
    ty_template,

    @"@CurrentScope" = 0x200,
    @"@RootScope",
    @"@use",
    @"@TypeOf",
    @"@as",
    @"@field_name",
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
    @"@type_name",
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
    @"@export",
    @"@frame_pointer",
    @"@handler",
    @"@eval",
    @"@type_info",
    @"@Type",
    @"@thread_local_storage",
    @"@parent_ptr",
    @"@alloc_global",
    @"@decl_count_of",
    @"@ReturnType",
    @"@Builtins",
    @"@simd",
    @"@splat",
    @"@count_trailing_zeros",
    @"@bitmask",

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
            v.* = .{ .name = vv.name, .type = void, .alignment = 1 };
        }

        variants[void_variant_count + 0] = .{ .name = "Type", .type = Type, .alignment = @alignOf(Type) };
        variants[void_variant_count + 1] = .{ .name = "Directive", .type = Directive, .alignment = @alignOf(Directive) };

        break :b @Type(.{ .@"union" = .{ .layout = .auto, .tag_type = tag, .fields = &variants, .decls = &.{} } });
    };

    pub fn isKeyword(self: Lexeme) bool {
        return @intFromEnum(Lexeme.@"fn") <= @intFromEnum(self) and
            @intFromEnum(self) <= @intFromEnum(Lexeme.false);
    }

    pub fn expand(self: Lexeme) Expanded {
        var vl = @intFromEnum(self);
        if (vl >= 256) vl = @byteSwap(vl);
        return @as(*const Expanded, @ptrCast(&vl)).*;
    }

    pub fn precedence(self: Lexeme, in_if_or_while: bool) u8 {
        return switch (self) {
            .@":",
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
            .@"&&", .@"$&&" => 14,
            .@":=" => if (in_if_or_while) 13 else 15,
            .@"||", .@"$||" => 12,
            .@".." => 11,
            .@"|", .@"&" => 8,
            .@"<", .@">", .@"<=", .@">=", .@"==", .@"!=" => 7,
            .@"^" => 6,
            .@"<<", .@">>" => 5,
            .@"+", .@"-" => 4,
            .@"*", .@"/", .@"%" => 3,
            .@".", .@".{", .@".(", .@".[", .@"(", .@"[", .@".?", .@".*" => 0,
            else => 255,
        };
    }

    pub fn isComparison(self: Lexeme) bool {
        return self.precedence(false) == 7;
    }

    pub fn repr(self: Lexeme) []const u8 {
        return @tagName(self);
    }

    pub fn canStartExpression(self: Lexeme) bool {
        return switch (self) {
            .@"}", .@";", .@",", .@")", .@"]" => false,
            else => true,
        };
    }

    pub fn innerOp(self: Lexeme) ?Lexeme {
        const byte = @intFromEnum(self);

        switch (self) {
            .@"||=", .@"&&=" => return @enumFromInt(byte - 1),
            .@"+=",
            .@"-=",
            .@"*=",
            .@"/=",
            .@"%=",
            .@"&=",
            .@"^=",
            .@"|=",
            .@"<<=",
            .@">>=",
            => return @enumFromInt(byte - 128),
            else => return null,
        }
    }

    pub fn toAssignment(self: Lexeme) Lexeme {
        const shift: usize = if (self == .@"||" or self == .@"&&") 1 else 128;
        return @enumFromInt(@intFromEnum(self) + shift);
    }

    pub fn format(self: *const Lexeme, writer: *std.io.Writer) !void {
        try writer.writeAll(@tagName(self.*));
    }
};

pub const Token = struct {
    pos: Pos,
    end: u32,
    kind: Lexeme,
    idx: File.TokenIdx = undefined,

    pub fn init(pos: Pos, end: u32, kind: Lexeme) Token {
        return Token{ .pos = pos, .end = end, .kind = kind };
    }

    pub fn view(self: Token, source: []const u8) []const u8 {
        return source[self.pos..self.end];
    }
};

pub const Prelexed = struct {
    pub const Internal = struct {
        kind: Lexer.Lexeme,
        len: u16,
        pos: u32,
    };

    pub const Lexeme = Lexer.Lexeme;
    pub const Token = Lexer.Token;

    tokens: []const Internal,
    source: [:0]const u8,
    cursor: File.TokenIdx,

    pub fn sub(self: Prelexed, cursor: File.TokenIdx) Prelexed {
        return .{
            .tokens = self.tokens,
            .source = self.source,
            .cursor = cursor,
        };
    }

    pub fn pos(self: *Prelexed) u32 {
        return self.curr().pos;
    }

    pub fn next(self: *Prelexed) Lexer.Token {
        defer self.cursor = self.cursor.next();
        return self.curr();
    }

    pub fn get(self: *Prelexed, idxe: File.TokenIdx) Lexer.Token {
        const tok = self.tokens[idxe.raw()];
        return .{
            .pos = tok.pos,
            .end = tok.pos + tok.len,
            .kind = tok.kind,
            .idx = self.cursor,
        };
    }

    pub fn curr(self: *Prelexed) Lexer.Token {
        return self.get(self.cursor);
    }

    pub fn prelex(source: [:0]const u8, scratch: *utils.Arena) []const Internal {
        var toks = std.ArrayList(Internal).empty;
        var lex = Lexer.init(source, 0);
        while (true) {
            const tok = lex.next();
            toks.append(scratch.allocator(), .{
                .kind = tok.kind,
                .pos = tok.pos,
                .len = @intCast(tok.end - tok.pos),
            }) catch unreachable;
            if (tok.kind == .Eof) break;
        }
        return toks.items;
    }

    pub fn expect(self: *Prelexed, kind: Lexer.Lexeme) !Lexer.Token {
        const res = self.peekNext();
        if (res.kind != kind) return error.SyntaxError;
        self.cursor = res.idx.next();
        return res;
    }

    pub fn eatUntilSameLevelToken(self: *@This(), kinds: []const Lexer.Lexeme) Lexer.Lexeme {
        var depth: usize = 0;
        while (true) {
            const tok = self.next();

            if (depth == 0) {
                for (kinds) |kind| {
                    if (tok.kind == kind) {
                        return tok.kind;
                    }
                }
            }

            switch (tok.kind) {
                .Eof => return tok.kind,
                .@".{", .@".(", .@".[", .@"{", .@"(", .@"[" => {
                    depth += 1;
                },
                .@"}", .@")", .@"]" => {
                    if (depth == 0) return tok.kind;
                    depth -= 1;
                },
                else => {},
            }
        }
    }

    pub fn eatUntilClosingDelimeter(self: *@This()) void {
        var depth: usize = 0;
        while (true) {
            const tok = self.next();
            switch (tok.kind) {
                .Eof => break,
                .@".{", .@".(", .@".[", .@"{", .@"(", .@"[" => {
                    depth += 1;
                },
                .@"}", .@")", .@"]" => {
                    if (depth == 0) break;
                    depth -= 1;
                },
                else => {},
            }
        }
    }

    pub fn list(self: *Prelexed, comptime sep: Lexer.Lexeme, comptime end: Lexer.Lexeme) *struct {
        lexer: Prelexed,

        pub fn nextExt(slf: *@This()) enum { has_next, end, trailing_end } {
            const tok = slf.lexer.peekNext();
            switch (tok.kind) {
                sep => {
                    slf.lexer.cursor = tok.idx.next();
                    const ptok = slf.lexer.peekNext();
                    if (ptok.kind == end) {
                        slf.lexer.cursor = ptok.idx.next();
                        return .trailing_end;
                    }

                    return .has_next;
                },
                end => {
                    slf.lexer.cursor = tok.idx.next();
                    return .end;
                },
                .Eof => return .end,
                else => return .has_next,
            }
        }

        pub fn next(slf: *@This()) bool {
            return slf.nextExt() == .has_next;
        }

        pub fn recover(slf: *@This()) bool {
            var depth: usize = 0;
            while (true) {
                const tok = slf.lexer.next();
                switch (tok.kind) {
                    sep => {
                        if (depth > 0) {
                            continue;
                        }

                        const ptok = slf.lexer.peekNext();
                        if (ptok.kind == end) {
                            slf.lexer.cursor = ptok.idx.next();
                            return true;
                        }

                        return false;
                    },
                    .Eof => return true,
                    .@".{", .@".(", .@".[", .@"{", .@"(", .@"[" => {
                        depth += 1;
                    },
                    .@"}", .@")", .@"]" => {
                        if (depth == 0) return true;
                        depth -= 1;
                    },
                    else => {},
                }
            }
        }
    } {
        return @ptrCast(self);
    }

    pub fn eatIdent(self: *Prelexed) ?struct { Lexer.Token, bool } {
        const tok = self.next();
        return .{ tok, switch (tok.kind) {
            .Ident => false,
            .@"$" => true,
            else => return null,
        } };
    }

    pub fn eatMatchOrRevert(self: *Prelexed, kind: Lexer.Lexeme) bool {
        const tok = self.peekNext();
        if (tok.kind != kind) {
            return false;
        }
        self.cursor = tok.idx.next();
        return true;
    }

    pub fn eatMatch(self: *Prelexed, kind: Lexer.Lexeme) bool {
        const tok = self.next();
        if (tok.kind != kind) {
            self.cursor = tok.idx;
            return false;
        }
        return true;
    }

    pub fn peekNext(self: Prelexed) Lexer.Token {
        var s = self;
        return s.next();
    }

    pub fn slit(self: *Prelexed, comptime tok: Lexer.Lexeme) Lexer.Token {
        const vl = self.next();
        if (vl.kind != tok) utils.panic("{s} != {s}", .{ @tagName(vl.kind), @tagName(tok) });
        return vl;
    }

    pub const SkipError = error{SyntaxError};

    pub fn skipExprDropErr(lex: *Prelexed) void {
        lex.skipExpr() catch {};
    }

    pub fn skipExpr(lex: *Prelexed) SkipError!void {
        return lex.skipExprPrec(254);
    }

    pub fn skipLabel(lex: *Prelexed) SkipError!void {
        if (lex.eatMatch(.@":")) {
            _ = try lex.expect(.Ident);
        }
    }

    pub fn skipExprPrec(lex: *Prelexed, prevPrec: u8) SkipError!void {
        try lex.skipUnitExpr();

        while (true) {
            const top = lex.peekNext();

            const prec = top.kind.precedence(false);
            if (prec >= prevPrec) break;

            lex.cursor = top.idx.next();

            try lex.skipSuffix(top, prec);
        }
    }

    pub fn skipSuffix(lex: *Prelexed, top: Lexer.Token, prevPrec: u8) SkipError!void {
        switch (top.kind) {
            .@"." => {
                _ = try lex.expect(.Ident);

                if (lex.eatMatch(.@"(")) {
                    lex.eatUntilClosingDelimeter();
                }
            },
            .@".*", .@".?" => {},
            .@".{", .@".[", .@"[", .@".(", .@"(" => {
                lex.eatUntilClosingDelimeter();
            },
            else => {
                try lex.skipExprPrec(prevPrec);
            },
        }
    }

    pub fn skipUnitExpr(lex: *Prelexed) SkipError!void {
        const tok = lex.next();
        return switch (tok.kind.expand()) {
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

            .@"(", .@"{", .@".{" => {
                lex.eatUntilClosingDelimeter();
            },
            .@"[" => {
                lex.eatUntilClosingDelimeter();
                try lex.skipExprPrec(1);
            },
            .@"?", .@"~", .@"-", .@"!", .@"&", .@"#", .@"^" => lex.skipExprPrec(1),
            .@"enum", .@"union", .@"struct" => {
                if (lex.eatMatch(.@"(")) {
                    lex.eatUntilClosingDelimeter();
                }

                if (lex.eatMatch(.@"align")) {
                    _ = try lex.expect(.@"(");
                    lex.eatUntilClosingDelimeter();
                }

                _ = try lex.expect(.@"{");
                lex.eatUntilClosingDelimeter();
            },
            .@"fn" => {
                _ = try lex.expect(.@"(");
                lex.eatUntilClosingDelimeter();

                _ = try lex.expect(.@":");
                try lex.skipExpr();
                if (lex.peekNext().kind.canStartExpression()) {
                    try lex.skipExpr();
                }
            },
            .@"if", .@"$if" => {
                try lex.skipExpr();
                try lex.skipExpr();

                if (lex.eatMatch(.@"else")) {
                    try lex.skipExpr();
                }
            },
            .@"while", .@"$while" => {
                _ = try lex.skipLabel();
                try lex.skipExpr();
                try lex.skipExpr();
            },
            .loop, .@"$loop" => {
                _ = try lex.skipLabel();
                try lex.skipExpr();
            },
            .match, .@"$match" => {
                try lex.skipExpr();
                try lex.skipExpr();
            },
            .@"for" => {
                while (true) {
                    try lex.skipExpr();
                    if (!lex.eatMatch(.@",")) break;
                }
                try lex.skipExpr();
            },
            .@"break", .@"continue" => _ = try lex.skipLabel(),
            .@"return" => {
                try lex.skipExpr();
            },
            .Directive => {
                _ = try lex.expect(.@"(");
                lex.eatUntilClosingDelimeter();
            },
            .@"." => {
                _ = try lex.expect(.Ident);

                if (lex.eatMatch(.@"(")) {
                    lex.eatUntilClosingDelimeter();
                }
            },
            else => return error.SyntaxError,
        };
    }
};

pub fn init(source: [:0]const u8, cursor: u32) Lexer {
    return Lexer{ .source = source, .cursor = cursor };
}

fn isKeyword(name: []const u8) bool {
    return name[0] == '@' or (name[0] == '$' and name.len != 1) or std.ascii.isLower(name[0]) or name[0] == '_';
}

pub const all_keywords = b: {
    @setEvalBranchQuota(2000);

    const auto_migration_mapping = [_]struct { []const u8, Lexeme }{
        .{ "@sizeof", .@"@size_of" },
        .{ "@alignof", .@"@align_of" },
        .{ "@bitcast", .@"@bit_cast" },
        .{ "@eca", .@"@ecall" },
        .{ "@lenof", .@"@len_of" },
        .{ "@kindof", .@"@kind_of" },
        .{ "@intcast", .@"@int_cast" },
        .{ "@nameof", .@"@type_name" },
        .{ "@name_of", .@"@type_name" },
        .{ "@itf", .@"@int_to_float" },
        .{ "@fti", .@"@float_to_int" },
        .{ "@floatcast", .@"@float_cast" },
    };

    var count = 0;
    for (std.meta.fields(Lexeme)) |f| count += @intFromBool(isKeyword(f.name));

    var lista: [count + auto_migration_mapping.len]struct { []const u8, Lexeme } = undefined;
    var i: usize = 0;
    for (std.meta.fields(Lexeme)) |field| {
        if (!isKeyword(field.name)) continue;
        const start = if (std.mem.startsWith(u8, field.name, "ty_")) 3 else 0;
        lista[i] = .{ field.name[start..], @enumFromInt(field.value) };
        i += 1;
    }

    for (auto_migration_mapping) |em| {
        lista[i] = em;
        i += 1;
    }

    break :b lista;
};

const QueryVec = @Vector(std.simd.suggestVectorLength(u8).?, u8);

const keyword_prefixes align(@alignOf(QueryVec)) = b: {
    @setEvalBranchQuota(2000);

    const aligned_count = std.mem.alignForward(usize, all_keywords.len, @sizeOf(QueryVec));

    var prefixes: [aligned_count]u8 = @splat(0);

    for (all_keywords, 0..) |kw, i| {
        prefixes[i] = @truncate(std.hash.Fnv1a_32.hash(kw[0]));
    }

    break :b prefixes;
};

pub fn resolveKeyword(prefix: u8, kw: []const u8) ?Lexeme {
    const search_vec: QueryVec = @splat(prefix);

    for (@as([]const QueryVec, @ptrCast(&keyword_prefixes)), 0..) |prefix_vec, i| {
        var mask: std.meta.Int(.unsigned, @sizeOf(QueryVec)) = @bitCast(prefix_vec == search_vec);
        mask &= @as(@TypeOf(mask), std.math.maxInt(@TypeOf(mask))) >>
            @intCast((i + 1) * @sizeOf(QueryVec) -| all_keywords.len);
        while (mask != 0) : (mask &= mask - 1) {
            const index = i * @sizeOf(QueryVec) + @ctz(mask);
            if (std.mem.eql(u8, all_keywords[index][0], kw)) return all_keywords[index][1];
        }
    }

    return null;
}

pub fn isIdentByte(ident: u8) bool {
    return switch (ident) {
        'a'...'z', 'A'...'Z', '0'...'9', '_', 128...255 => true,
        else => false,
    };
}

pub fn compareIdent(
    source: [:0]const u8,
    offset: u32,
    ref: []const u8,
) bool {
    comptime {
        std.debug.assert(""[0] == 0);
    }

    return source.len - offset >= ref.len and
        // NOTE: shortcut but also prevent false match on prefix
        // NOTE: this assumes terminator
        !isIdentByte(source[offset + ref.len]) and
        std.mem.eql(u8, source[offset..][0..ref.len], ref);
}

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
        dollar,
    };

    var pos = self.cursor;
    var ident_hash = std.hash.Fnv1a_32.init();

    const kind: Lexeme = state: switch (State.start) {
        .start => switch (self.source[self.cursor]) {
            0 => break :state .Eof,
            // This mathes on the newline simbols and slits the whitespace in one go
            1...31 => {
                const V = @Vector(16, u8);

                if (self.source.len - self.cursor >= @sizeOf(V)) {
                    @branchHint(.likely);

                    const vec: V = @bitCast(self.source[self.cursor..][0..@sizeOf(V)].*);
                    const whitespace_mask = vec > @as(V, @splat(32));
                    const whitespace_bits: std.meta.Int(.unsigned, @sizeOf(V)) =
                        @bitCast(whitespace_mask);

                    self.cursor += @ctz(whitespace_bits);
                    pos += @ctz(whitespace_bits);
                } else {
                    self.cursor += 1;
                    pos += 1;
                }

                continue :state .start;
            },
            ' ', 127 => {
                self.cursor += 1;
                pos += 1;
                continue :state .start;
            },
            '$' => continue :state .dollar,
            '@', 'a'...'z', 'A'...'Z', '_', 128...255 => continue :state .ident,
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
        .dollar => {
            ident_hash.update(self.source[self.cursor..][0..1]);
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                '|', '&' => {
                    self.cursor += 2;
                    // We dont validate, but nobody will notice, fmt will fix it anyway
                    break :state @enumFromInt(self.source[self.cursor - 1] + 32 + 2);
                },
                else => continue :state .ident,
            }
        },
        .ident => {
            ident_hash.update(self.source[self.cursor..][0..1]);
            self.cursor += 1;
            switch (self.source[self.cursor]) {
                'a'...'z', 'A'...'Z', '0'...'9', '_', 128...255 => continue :state .ident,
                else => {
                    if (resolveKeyword(@truncate(ident_hash.final()), self.source[pos..self.cursor])) |k| break :state k;
                    switch (self.source[pos]) {
                        '$' => |c| {
                            pos += 1;
                            break :state @enumFromInt(c);
                        },
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
                    break :state @enumFromInt(@as(u16, self.source[self.cursor - 2]) + 32 + 1);
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
