exprs: Store,
path: []const u8,
source: []const u8,
items: Slice,

const std = @import("std");
const root = @import("utils.zig");
const Lexer = @import("Lexer.zig");
const Fmt = @import("Fmt.zig");
const Parser = @import("Parser.zig");
const Types = @import("Types.zig");
const Ast = @This();
pub const Loader = Parser.Loader;
pub const Store = root.EnumStore(Id, Expr);

pub const Id = root.EnumId(Kind);
pub const Slice = root.EnumSlice(Id);
pub const Idents = root.EnumSlice(Ident);

pub var colors: std.io.tty.Config = .no_color;

pub const Ident = enum(u32) {
    _,

    pub fn init(token: Lexer.Token) Ident {
        return @enumFromInt(token.pos + @intFromBool(token.kind == .@"$"));
    }

    pub fn pos(self: Ident) u32 {
        return @intFromEnum(self);
    }
};

pub fn cmpLow(pos: u32, source: []const u8, repr: []const u8) bool {
    return std.mem.eql(u8, Lexer.peekStr(source, pos), repr);
}

pub fn Payload(comptime kind: Kind) type {
    return std.meta.TagPayload(Expr, kind);
}

pub const Kind = enum {
    Void,
    Comment,
    Wildcard,
    Idk,
    Ident,
    Buty,
    Fn,
    Struct,
    Directive,
    Index,
    Call,
    Tag,
    Unwrap,
    Deref,
    Field,
    Ctor,
    Tupl,
    Arry,
    If,
    Loop,
    Break,
    Continue,
    Return,
    Block,
    SliceTy,
    UnOp,
    BinOp,
    Use,
    Integer,
    Bool,
    Null,
    String,
};

pub const Arg = struct {
    bindings: Id,
    ty: Id,
};

pub const Expr = union(Kind) {
    Void,
    Comment: Pos,
    Wildcard: Pos,
    Idk: Pos,
    Ident: struct {
        pos: Pos = Pos.init(0),
        id: Ident = Ident.init(Lexer.Token.init(0, 0, .Eof)),
    },
    Buty: struct {
        pos: Pos,
        bt: Lexer.Lexeme,
    },
    Fn: struct {
        pos: Pos,
        comptime_args: Idents,
        captures: Idents,
        args: root.EnumSlice(Arg),
        ret: Id,
        body: Id,
    },
    Struct: struct {
        pos: Pos,
        captures: root.EnumSlice(Ident),
        fields: Slice,
    },
    Directive: struct {
        pos: Pos,
        args: Slice,
    },
    Index: struct {
        base: Id,
        subscript: Id,
    },
    Call: struct {
        called: Id,
        arg_pos: Pos,
        args: Slice,
    },
    Tag: Pos,
    Unwrap: Id,
    Deref: Id,
    Field: struct {
        base: Id,
        field: Pos,
    },
    Ctor: struct {
        pos: Pos,
        ty: Id,
        fields: Slice,
    },
    Tupl: struct {
        pos: Pos,
        ty: Id,
        fields: Slice,
    },
    Arry: struct {
        pos: Pos,
        ty: Id,
        fields: Slice,
    },
    If: struct {
        pos: Pos,
        cond: Id,
        then: Id,
        else_: Id,
    },
    Loop: struct {
        pos: Pos,
        body: Id,
    },
    Break: Pos,
    Continue: Pos,
    Return: struct {
        pos: Pos,
        value: Id,
    },
    Block: struct {
        pos: Pos,
        stmts: Slice,
    },
    SliceTy: struct {
        pos: Pos,
        len: Id,
        elem: Id,
    },
    UnOp: struct {
        pos: Pos,
        op: Lexer.Lexeme,
        oper: Id,
    },
    BinOp: struct {
        lhs: Id,
        op: Lexer.Lexeme,
        rhs: Id,
    },
    Use: struct {
        pos: Pos,
        file: Types.File,
    },
    Integer: Pos,
    Bool: struct {
        pos: Pos,
        value: bool,
    },
    Null: Pos,
    String: struct {
        pos: Pos,
        end: u32,
    },
};

pub const Pos = packed struct(Pos.Repr) {
    const Repr = u32;

    index: std.meta.Int(.unsigned, @bitSizeOf(Repr) - @bitSizeOf(bool)),
    flag: packed union {
        indented: bool,
        @"comptime": bool,
        use_kind: Loader.LoadOptions.Kind,
    } = .{ .indented = false },

    pub fn init(index: Lexer.Pos) Pos {
        return .{ .index = @intCast(index) };
    }
};

pub fn init(gpa: std.mem.Allocator, current: Types.File, path: []const u8, code: []const u8, loader: Parser.Loader) !Ast {
    var lexer = Lexer.init(code, 0);

    var parser = Parser{
        .path = path,
        .current = current,
        .loader = loader,
        .cur = lexer.next(),
        .lexer = lexer,
        .arena = std.heap.ArenaAllocator.init(gpa),
        .gpa = gpa,
    };
    defer {
        parser.arena.deinit();
        parser.active_syms.deinit(gpa);
        parser.captures.deinit(gpa);
        parser.comptime_idents.deinit(gpa);
    }
    errdefer {
        parser.store.deinit(gpa);
    }

    return .{
        .items = try parser.parse(),
        .exprs = parser.store,
        .source = code,
        .path = path,
    };
}

pub fn findDecl(self: *const Ast, slice: Slice, id: anytype) ?Id {
    return for (self.exprs.view(slice)) |d| {
        if (d.tag() != .BinOp) continue;
        const decl = self.exprs.get(d).BinOp.lhs;
        if (decl.tag() == .Tag) continue;
        const ident = self.exprs.get(decl).Ident.id;
        switch (@TypeOf(id)) {
            Ident => if (ident == id) break d,
            else => if (cmpLow(ident.pos(), self.source, id)) break d,
        }
    } else null;
}

pub fn cmpIdent(self: *const Ast, id: Ident, to: []const u8) bool {
    return cmpLow(id.pos(), self.source, to);
}

pub fn tokenSrc(self: *const Ast, pos: u32) []const u8 {
    return Lexer.peekStr(self.source, pos);
}

pub fn posOf(self: *const Ast, origin: anytype) Pos {
    return switch (@TypeOf(origin)) {
        Id => switch (self.exprs.get(origin)) {
            inline else => |v| self.posOfPayload(v),
        },
        else => self.posOfPayload(origin),
    };
}

fn posOfPayload(self: *const Ast, v: anytype) Pos {
    return switch (@TypeOf(v)) {
        void => .init(0),
        Ident => .init(v.pos()),
        Pos => v,
        Id => self.posOf(v),
        else => |Vt| if (@hasField(Vt, "pos"))
            v.pos
        else
            self.posOf(@field(v, std.meta.fields(Vt)[0].name)),
    };
}

pub fn deinit(self: *Ast, gpa: std.mem.Allocator) void {
    self.exprs.deinit(gpa);
    self.* = undefined;
}

pub fn fmtExpr(self: *const Ast, buf: *std.ArrayList(u8), expr: Ast.Id) !void {
    var ft = Fmt{ .buf = buf, .ast = self };
    try ft.fmtExpr(expr);
}

pub fn fmt(self: *const Ast, buf: *std.ArrayList(u8)) !void {
    var ft = Fmt{ .buf = buf, .ast = self };
    try ft.fmt();
}

pub const CodePointer = struct {
    source: []const u8,
    index: usize,

    pub fn format(slf: *const @This(), comptime _: anytype, _: anytype, writer: anytype) !void {
        try pointToCode(slf.source, slf.index, writer);
    }
};

pub fn codePointer(self: *const Ast, index: usize) CodePointer {
    return .{ .source = self.source, .index = index };
}

pub fn lineCol(source: []const u8, index: isize) struct { usize, usize } {
    var line: usize = 0;
    var last_nline: isize = -1;
    for (source[0..@intCast(index)], 0..) |c, i| if (c == '\n') {
        line += 1;
        last_nline = @intCast(i);
    };
    return .{ line + 1, @intCast(index - last_nline) };
}

fn pointToCode(source: []const u8, index: usize, writer: anytype) !void {
    const line_start = if (std.mem.lastIndexOfScalar(u8, source[0..index], '\n')) |l| l + 1 else 0;
    const line_end = if (std.mem.indexOfScalar(u8, source[index..], '\n')) |l| l + index else source.len;
    const the_line = source[line_start..line_end];

    var buf: [256]u8 = undefined;
    var i: usize = 0;

    var extra_bytes: usize = 0;
    const code_start = for (the_line, 0..) |c, j| {
        if (c == ' ') {
            buf[i] = ' ';
            i += 1;
        } else if (c == '\t') {
            @memset(buf[i..][0 .. 4 - i % 4], ' ');
            i += 4 - i % 4;
            extra_bytes += 3 - i % 4;
        } else break j;
    } else the_line.len;

    const remining = @min(buf.len - i, the_line.len - code_start);
    @memcpy(buf[i..][0..remining], the_line[code_start..][0..remining]);
    i += remining;
    buf[i] = '\n';
    i += 1;
    try writer.writeAll(buf[0..i]);

    const col = index - line_start + extra_bytes;
    @memset(buf[0..col], ' ');
    buf[col] = '^';
    try writer.writeAll(buf[0 .. col + 1]);
}
