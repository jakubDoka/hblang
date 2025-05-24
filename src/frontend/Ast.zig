exprs: Store,
path: []const u8,
source: [:0]const u8,
items: Slice,
root_struct: Id,

const std = @import("std");
const root = @import("hb");
const utils = root.utils;
const Lexer = root.frontend.Lexer;
const Fmt = root.frontend.Fmt;
const Parser = root.frontend.Parser;
const Types = root.frontend.Types;
const Ast = @This();
pub const Loader = Parser.Loader;
pub const Store = utils.EnumStore(Expr);

pub const Id = Store.Id;
pub const Slice = utils.EnumSlice(Id);
pub const Idents = utils.EnumSlice(Ident);

pub const Ident = enum(u32) {
    _,

    pub fn init(token: Lexer.Token) Ident {
        return @enumFromInt(token.pos + @intFromBool(token.kind == .@"$"));
    }

    pub inline fn pos(self: Ident) u32 {
        return @intFromEnum(self);
    }
};

pub fn cmpLow(pos: u32, source: [:0]const u8, repr: []const u8) bool {
    var str = Lexer.peekStr(source, pos);
    if (str[0] == '$') str = str[1..];
    return std.mem.eql(u8, str, repr);
}

pub const Arg = struct {
    bindings: Id,
    ty: Id,
};

pub const CtorField = struct {
    pos: Pos,
    value: Id,
};

pub const Ctor = struct {
    pos: Pos,
    ty: Id,
    fields: utils.EnumSlice(CtorField),
};

pub const MatchArm = struct {
    pat: Id,
    body: Id,
};

pub const Expr = union(enum) {
    Void,
    Comment: Pos,
    Wildcard: Pos,
    Idk: Pos,
    Die: Pos,
    Ident: struct {
        pos: Pos = Pos.init(0),
        id: Ident = Ident.init(Lexer.Token.init(0, 0, .Eof)),
    },
    Buty: struct {
        pos: Pos,
        bt: Lexer.Lexeme.Type,
    },
    Fn: struct {
        pos: Pos,
        comptime_args: Idents,
        captures: Idents,
        args: utils.EnumSlice(Arg),
        ret: Id,
        body: Id,
    },
    Enum: Type,
    Union: Type,
    Struct: Type,
    Directive: struct {
        pos: Pos,
        kind: Lexer.Lexeme.Directive,
        args: Slice,
    },
    Range: struct {
        start: Id,
        end: Id,
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
    Defer: Id,
    Unwrap: Id,
    Deref: Id,
    Field: struct {
        base: Id,
        field: Pos,
    },
    Ctor: Ctor,
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
    Match: struct {
        pos: Pos,
        value: Id,
        arms: utils.EnumSlice(MatchArm),
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
    Decl: struct {
        bindings: Id,
        ty: Id = .zeroSized(.Void),
        value: Id,
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
    Integer: struct {
        pos: Pos,
        base: u8,
    },
    Float: Pos,
    Bool: struct {
        pos: Pos,
        value: bool,
    },
    Null: Pos,
    String: struct {
        pos: Pos,
        end: u32,
    },
    Quotes: struct {
        pos: Pos,
        end: u32,
    },

    pub const Type = struct {
        pos: Pos,
        alignment: Id,
        captures: utils.EnumSlice(Ident),
        fields: Slice,
    };
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

pub const InitOptions = struct {
    current: Types.File = .root,
    path: []const u8,
    code: [:0]const u8,
    loader: Parser.Loader = .noop,
    diagnostics: std.io.AnyWriter = std.io.null_writer.any(),
    ignore_errors: bool = false,
};

pub fn init(
    arena: *utils.Arena,
    opts: InitOptions,
) !Ast {
    var lexer = Lexer.init(opts.code, 0);

    var parser = Parser{
        .stack_base = @frameAddress(),
        .arena = arena,
        .path = opts.path,
        .current = opts.current,
        .loader = opts.loader,
        .cur = lexer.next(),
        .lexer = lexer,
        .diagnostics = opts.diagnostics,
    };

    const source_to_ast_ratio = 5;
    try parser.store.store.ensureTotalCapacity(arena.allocator(), opts.code.len * source_to_ast_ratio);

    const items: Slice = parser.parse() catch |err| switch (err) {
        error.UnexpectedToken, error.StackOverflow => .{},
        error.OutOfMemory => return err,
    };

    if (parser.errored and !opts.ignore_errors) {
        return error.ParsingFailed;
    }

    return .{
        .items = items,
        .path = opts.path,
        .source = opts.code,
        .root_struct = try parser.store.alloc(arena.allocator(), .Struct, .{
            .pos = .init(0),
            .alignment = .zeroSized(.Void),
            .fields = items,
            .captures = .{},
        }),
        .exprs = parser.store,
    };
}

pub fn searchBinding(self: *const Ast, cur: Ast.Id, id: anytype, fseq: *std.ArrayList(Pos)) bool {
    switch (cur.tag()) {
        .Ident => switch (@TypeOf(id)) {
            Ident => if (self.exprs.getTyped(.Ident, cur).?.id == id) return true,
            else => if (cmpLow(self.exprs.getTyped(.Ident, cur).?.id.pos(), self.source, id)) return true,
        },
        .Ctor => {
            const c = self.exprs.getTyped(.Ctor, cur).?;
            if (self.searchBinding(c.ty, id, fseq)) return true;

            for (self.exprs.view(c.fields)) |f| {
                fseq.append(f.pos) catch unreachable;
                if (self.searchBinding(f.value, id, fseq)) return true;
                _ = fseq.pop().?;
            }
        },
        else => {},
    }
    return false;
}

pub fn findDecl(
    self: *const Ast,
    slice: Slice,
    id: anytype,
    arena: std.mem.Allocator,
) ?struct { Id, []Pos } {
    var fseq = std.ArrayList(Pos).init(arena);
    return for (self.exprs.view(slice)) |d| {
        const decl = self.exprs.getTyped(.Decl, d) orelse continue;
        if (self.searchBinding(decl.bindings, id, &fseq)) return .{ d, fseq.items };
    } else null;
}

pub fn tokenSrc(self: *const Ast, pos: u32) []const u8 {
    return Lexer.peekStr(self.source, pos);
}

pub fn posOf(self: *const Ast, origin: anytype) Pos {
    return switch (@TypeOf(origin)) {
        Id => switch (origin.tag()) {
            inline else => |v| self.posOfPayload(self.exprs.getTyped(v, origin).?.*),
        },
        else => self.posOfPayload(origin),
    };
}

fn posOfPayload(self: *const Ast, v: anytype) Pos {
    if (@typeInfo(@TypeOf(v)) == .pointer) return self.posOfPayload(v.*);
    return switch (@TypeOf(v)) {
        void => .init(0),
        Ident => .init(v.pos()),
        Pos => v,
        u32 => .init(v),
        Id => self.posOf(v),
        Ctor => if (v.ty.tag() != .Void) self.posOf(v.ty) else v.pos,
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

pub fn report(path: []const u8, file: []const u8, pos: u32, comptime fmt_str: []const u8, args: anytype, out: anytype) void {
    const line, const col = Ast.lineCol(file, pos);
    out.print(
        "{s}:{}:{}: " ++ fmt_str ++ "\n{}\n",
        .{ path, line, col } ++ args ++ .{CodePointer{ .source = file, .index = pos }},
    ) catch unreachable;
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

pub fn lineCol(source: []const u8, index: usize) struct { usize, usize } {
    var line: usize = 0;
    var last_nline: isize = -1;
    for (source[0..@min(@as(usize, @intCast(index)), source.len)], 0..) |c, i| if (c == '\n') {
        line += 1;
        last_nline = @intCast(i);
    };
    return .{ line + 1, @intCast(@as(isize, @bitCast(index)) - last_nline) };
}

pub fn pointToCode(source: []const u8, index_m: usize, writer: anytype) !void {
    const index = @min(index_m, source.len -| 1); // might be an empty file
    const line_start = if (std.mem.lastIndexOfScalar(u8, source[0..index], '\n')) |l| l + 1 else 0;
    const line_end = if (std.mem.indexOfScalar(u8, source[index..], '\n')) |l| l + index else source.len;
    const the_line = source[line_start..line_end];

    var i: usize = 0;

    var extra_bytes: usize = 0;
    const code_start = for (the_line, 0..) |c, j| {
        if (c == ' ') {
            try writer.writeAll(" ");
            i += 1;
        } else if (c == '\t') {
            try writer.writeAll("    "[0 .. 4 - i % 4]);
            i += 4 - i % 4;
            extra_bytes += 3 - i % 4;
        } else break j;
    } else the_line.len;

    try writer.writeAll(the_line[code_start..][0 .. the_line.len - code_start]);
    try writer.writeAll("\n");

    const col = index - line_start + extra_bytes;
    for (0..col) |_| {
        try writer.writeAll(" ");
    }
    try writer.writeAll("^");
}
