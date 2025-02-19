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

pub var colors: std.io.tty.Config = .no_color;

pub const Ident = enum(u32) {
    _,

    pub fn init(token: Lexer.Token) Ident {
        return @enumFromInt(token.pos);
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
    Ident,
    Buty,
    Fn,
    Struct,
    Arg,
    Directive,
    Call,
    Field,
    Ctor,
    CtorField,
    Tupl,
    If,
    Loop,
    Break,
    Continue,
    Return,
    Block,
    UnOp,
    BinOp,
    Use,
    Integer,
    Bool,
};

pub const Expr = union(Kind) {
    Void,
    Comment: Pos,
    Wildcard: Pos,
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
        args: Slice,
        ret: Id,
        body: Id,
    },
    Struct: struct {
        pos: Pos,
        fields: Slice,
    },
    Arg: struct {
        bindings: Id,
        ty: Id,
    },
    Directive: struct {
        pos: Pos,
        args: Slice,
    },
    Call: struct {
        called: Id,
        arg_pos: Pos,
        args: Slice,
    },
    Field: struct {
        base: Id,
        field: Pos,
    },
    Ctor: struct {
        pos: Pos,
        ty: Id,
        fields: Slice,
    },
    CtorField: struct {
        pos: Pos,
        value: Id,
    },
    Tupl: struct {
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
};

pub const Pos = packed struct(Pos.Repr) {
    const Repr = u32;

    index: std.meta.Int(.unsigned, @bitSizeOf(Repr) - @bitSizeOf(bool)),
    indented: bool = false,

    pub fn init(index: Lexer.Pos) Pos {
        return .{ .index = @intCast(index) };
    }
};

pub fn init(gpa: std.mem.Allocator, current: Types.File, path: []const u8, code: []const u8, loader: Parser.Loader) !Ast {
    var lexer = Lexer.init(code, 0);

    var parser = Parser{
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

pub fn findDecl(self: *const Ast, id: anytype) ?Id {
    return for (self.exprs.view(self.items)) |d| {
        if (d.tag() != .BinOp) continue;
        const ident = self.exprs.get(self.exprs.get(d).BinOp.lhs).Ident.id;
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
        void => Pos.init(0),
        Pos => v,
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
    self: *const Ast,
    index: usize,

    pub fn format(slf: *const @This(), comptime _: anytype, _: anytype, writer: anytype) !void {
        try slf.self.pointToCode(slf.index, writer);
    }
};

pub fn codePointer(self: *const Ast, index: usize) CodePointer {
    return .{ .self = self, .index = index };
}

pub fn lineCol(self: *const Ast, index: isize) struct { usize, usize } {
    var line: usize = 0;
    var last_nline: isize = -1;
    for (self.source[0..@intCast(index)], 0..) |c, i| if (c == '\n') {
        line += 1;
        last_nline = @intCast(i);
    };
    return .{ line + 1, @intCast(index - last_nline) };
}

fn pointToCode(self: *const Ast, index: usize, writer: anytype) !void {
    const line_start = if (std.mem.lastIndexOfScalar(u8, self.source[0..index], '\n')) |l| l + 1 else 0;
    const line_end = if (std.mem.indexOfScalar(u8, self.source[index..], '\n')) |l| l + index else self.source.len;
    const the_line = self.source[line_start..line_end];

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
