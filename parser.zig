exprs: Store,
path: []const u8,
source: []const u8,
items: Slice,

const std = @import("std");
const root = @import("utils.zig");
const Lexer = @import("Lexer.zig");
const Fmt = @import("Fmt.zig");
const Ast = @This();
const Store = root.EnumStore(Id, Expr);

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

fn cmpLow(pos: u32, source: []const u8, repr: []const u8) bool {
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

pub const Decl = struct {
    name: Ident,
    expr: Id,
};

const Parser = struct {
    store: Store = .{},

    gpa: std.mem.Allocator,
    arena: std.heap.ArenaAllocator,

    active_syms: std.ArrayListUnmanaged(Sym) = .{},

    lexer: Lexer,
    cur: Lexer.Token,
    list_pos: Pos = undefined,
    undeclared_count: u32 = 0,

    const Error = error{UnexpectedToken} || std.mem.Allocator.Error;

    const Sym = struct {
        id: Ident,
        declared: bool = false,
        decl: Id = Id.zeroSized(.Void),
    };

    fn parse(self: *Parser) !Slice {
        var itemBuf = std.ArrayListUnmanaged(Id){};
        while (self.cur.kind != .Eof) {
            try itemBuf.append(self.arena.allocator(), try self.parseExpr());
            _ = self.tryAdvance(.@";");
        }

        self.undeclared_count = 0;
        const remining = self.finalizeVariablesLow(0);
        for (self.active_syms.items[0..remining]) |s| {
            std.debug.print(
                "undefined identifier: {s}\n",
                .{Lexer.peekStr(self.lexer.source, s.id.pos())},
            );
        }
        std.debug.assert(remining == 0);

        return self.store.allocSlice(Id, self.gpa, itemBuf.items);
    }

    fn parseExpr(self: *Parser) Error!Id {
        return self.parseBinExpr(try self.parseUnit(), 254);
    }

    fn parseBinExpr(self: *Parser, lhs: Id, prevPrec: u8) Error!Id {
        var acum = lhs;
        while (true) {
            const op = self.cur.kind;
            const prec = op.precedence();
            if (prec >= prevPrec) break;

            const decl = if (op == .@":=" or op == .@":") self.declareExpr(acum) else null;

            self.cur = self.lexer.next();
            const rhs = try self.parseBinExpr(try self.parseUnit(), prec);
            if (op.innerOp()) |iop| {
                acum = try self.store.alloc(self.gpa, .BinOp, .{
                    .lhs = acum,
                    .op = .@"=",
                    .rhs = try self.store.alloc(
                        self.gpa,
                        .BinOp,
                        .{ .lhs = acum, .op = iop, .rhs = rhs },
                    ),
                });
            } else {
                acum = try self.store.alloc(
                    self.gpa,
                    .BinOp,
                    .{ .lhs = acum, .op = op, .rhs = rhs },
                );
            }

            if (decl) |d| {
                self.active_syms.items[d].decl = acum;
            }
        }
        return acum;
    }

    fn declareExpr(self: *Parser, id: Id) usize {
        const ident: Ident = self.store.getTypedPtr(.Ident, id).?.id;
        var iter = std.mem.reverseIterator(self.active_syms.items);
        const sym = while (iter.nextPtr()) |s| {
            if (s.id == ident) break s;
        } else unreachable;
        if (sym.decl.tag() != .Void) {
            std.debug.panic("redeclaration of identifier", .{});
        }
        sym.declared = true;
        return (@intFromPtr(sym) - @intFromPtr(self.active_syms.items.ptr)) / @sizeOf(Sym);
    }

    fn parseUnit(self: *Parser) Error!Id {
        var base = try self.parseUnitWithoutTail();
        while (true) base = try self.store.allocDyn(self.gpa, switch (self.cur.kind) {
            .@"." => .{ .Field = .{
                .base = base,
                .field = b: {
                    _ = self.advance();
                    break :b Pos.init((try self.expectAdvance(.Ident)).pos);
                },
            } },
            .@"(" => .{ .Call = .{
                .called = base,
                .args = try self.parseList(.@"(", .@",", .@")", parseExpr),
                .arg_pos = self.list_pos,
            } },
            .@".{" => .{ .Ctor = .{
                .ty = base,
                .fields = try self.parseList(.@".{", .@",", .@"}", parseCtorField),
                .pos = self.list_pos,
            } },
            .@".(" => .{ .Tupl = .{
                .ty = base,
                .fields = try self.parseList(.@".(", .@",", .@")", parseExpr),
                .pos = self.list_pos,
            } },
            else => break,
        });
        return base;
    }

    fn parseUnitWithoutTail(self: *Parser) Error!Id {
        const token = self.advance();
        const scope_frame = self.active_syms.items.len;
        return try self.store.allocDyn(self.gpa, switch (token.kind) {
            .Comment => .{ .Comment = Pos.init(token.pos) },
            ._ => .{ .Wildcard = Pos.init(token.pos) },
            .Ident => return try self.resolveIdent(token),
            .@"fn" => .{ .Fn = .{
                .args = try self.parseList(.@"(", .@",", .@")", parseArg),
                .pos = self.list_pos,
                .ret = b: {
                    _ = try self.expectAdvance(.@":");
                    break :b try self.parseExpr();
                },
                .body = b: {
                    defer self.finalizeVariables(scope_frame);
                    break :b try self.parseExpr();
                },
            } },
            .@"struct" => .{ .Struct = .{
                .fields = try self.parseList(.@"{", .@",", .@"}", parseField),
                .pos = self.list_pos,
            } },
            .@".{" => .{ .Ctor = .{
                .ty = Id.zeroSized(.Void),
                .fields = try self.parseList(null, .@",", .@"}", parseCtorField),
                .pos = self.list_pos,
            } },
            .@".(" => .{ .Tupl = .{
                .ty = Id.zeroSized(.Void),
                .fields = try self.parseList(null, .@",", .@")", parseExpr),
                .pos = self.list_pos,
            } },
            .@"{" => .{ .Block = .{
                .pos = Pos.init(token.pos),
                .stmts = b: {
                    var buf = std.ArrayListUnmanaged(Id){};
                    while (!self.tryAdvance(.@"}")) {
                        try buf.append(self.arena.allocator(), try self.parseExpr());
                        _ = self.tryAdvance(.@";");
                    }
                    self.finalizeVariables(scope_frame);
                    break :b try self.store.allocSlice(Id, self.gpa, buf.items);
                },
            } },
            .@"(" => {
                const expr = try self.parseExpr();
                _ = try self.expectAdvance(.@")");
                return expr;
            },
            .bool,
            .u8,
            .u16,
            .u32,
            .uint,
            .i8,
            .i16,
            .i32,
            .int,
            .void,
            => .{ .Buty = .{ .pos = Pos.init(token.pos), .bt = token.kind } },
            .@"&", .@"*", .@"^", .@"-" => |op| .{ .UnOp = .{
                .pos = Pos.init(token.pos),
                .op = op,
                .oper = try self.parseUnit(),
            } },
            .@"if" => .{ .If = .{
                .pos = Pos.init(token.pos),
                .cond = try self.parseExpr(),
                .then = try self.parseExpr(),
                .else_ = if (self.tryAdvance(.@"else"))
                    try self.parseExpr()
                else
                    Id.zeroSized(.Void),
            } },
            .loop => .{ .Loop = .{
                .pos = Pos.init(token.pos),
                .body = try self.parseExpr(),
            } },
            .@"break" => .{ .Break = Pos.init(token.pos) },
            .@"continue" => .{ .Continue = Pos.init(token.pos) },
            .@"return" => .{ .Return = .{
                .pos = Pos.init(token.pos),
                .value = if (self.cur.kind.cantStartExpression())
                    Id.zeroSized(.Void)
                else
                    try self.parseExpr(),
            } },
            .Integer => .{ .Integer = Pos.init(token.pos) },
            .true => .{ .Bool = .{ .value = true, .pos = Pos.init(token.pos) } },
            .false => .{ .Bool = .{ .value = false, .pos = Pos.init(token.pos) } },
            else => |k| std.debug.panic("{any}", .{k}),
        });
    }

    fn finalizeVariablesLow(self: *Parser, start: usize) usize {
        var new_len = start;
        for (self.active_syms.items[start..]) |*s| {
            if (!s.declared) {
                self.active_syms.items[new_len] = s.*;
                new_len += 1;
            }
        }
        return new_len;
    }

    fn finalizeVariables(self: *Parser, start: usize) void {
        self.active_syms.items.len = self.finalizeVariablesLow(start);
    }

    fn resolveIdent(self: *Parser, token: Lexer.Token) !Id {
        const repr = token.view(self.lexer.source);

        for (self.active_syms.items) |*s| if (cmpLow(s.id.pos(), self.lexer.source, repr)) {
            return try self.store.alloc(self.gpa, .Ident, .{
                .pos = Pos.init(token.pos),
                .id = s.id,
            });
        };

        const id = Ident.init(token);
        const alloc = try self.store.alloc(self.gpa, .Ident, .{
            .pos = Pos.init(token.pos),
            .id = id,
        });
        try self.active_syms.append(self.gpa, .{
            .id = id,
        });
        self.undeclared_count += 1;
        return alloc;
    }

    fn parseList(
        self: *Parser,
        start: ?Lexer.Lexeme,
        sep: ?Lexer.Lexeme,
        end: Lexer.Lexeme,
        comptime parser: fn (*Parser) Error!Id,
    ) Error!Slice {
        if (start) |s| _ = try self.expectAdvance(s);
        self.list_pos = .{ .index = @intCast(self.cur.pos) };
        var buf = std.ArrayListUnmanaged(Id){};
        while (!self.tryAdvance(end)) {
            try buf.append(self.arena.allocator(), try parser(self));
            if (self.tryAdvance(end)) {
                self.list_pos.indented = sep == null;
                break;
            }
            if (sep) |s| _ = try self.expectAdvance(s);
            self.list_pos.indented = true;
        }
        return try self.store.allocSlice(Id, self.gpa, buf.items);
    }

    fn parseArg(self: *Parser) Error!Id {
        const bindings = try self.parseUnitWithoutTail();
        _ = self.declareExpr(bindings);
        _ = try self.expectAdvance(.@":");
        return try self.store.alloc(self.gpa, .Arg, .{
            .bindings = bindings,
            .ty = try self.parseExpr(),
        });
    }

    fn parseField(self: *Parser) Error!Id {
        const name = try self.expectAdvance(.Ident);
        _ = try self.expectAdvance(.@":");
        return try self.store.alloc(self.gpa, .CtorField, .{
            .pos = Pos.init(name.pos),
            .value = try self.parseExpr(),
        });
    }

    fn parseCtorField(self: *Parser) Error!Id {
        const name_tok = try self.expectAdvance(.Ident);
        const value = if (self.tryAdvance(.@":"))
            try self.parseExpr()
        else
            try self.resolveIdent(name_tok);
        return try self.store.alloc(self.gpa, .CtorField, .{
            .pos = Pos.init(name_tok.pos),
            .value = value,
        });
    }

    inline fn tryAdvance(self: *Parser, expected: Lexer.Lexeme) bool {
        if (self.cur.kind != expected) return false;
        _ = self.advance();
        return true;
    }

    fn expectAdvance(self: *Parser, expected: Lexer.Lexeme) !Lexer.Token {
        if (self.cur.kind != expected) {
            std.debug.panic("expected {s}, got {s}", .{ @tagName(expected), @tagName(self.cur.kind) });
        }
        return self.advance();
    }

    inline fn advance(self: *Parser) Lexer.Token {
        defer self.cur = self.lexer.next();
        return self.cur;
    }

    fn catchSynErr(expr: anytype) ?@TypeOf(expr) {
        return expr catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return null,
        };
    }
};

pub fn init(path: []const u8, code: []const u8, gpa: std.mem.Allocator) !Ast {
    var lexer = Lexer.init(code, 0);

    var parser = Parser{
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
