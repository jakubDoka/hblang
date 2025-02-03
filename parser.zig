exprs: Store,
path: []const u8,
source: []const u8,
items: Slice,
decls: []const Decl,

const std = @import("std");
const root = @import("main.zig");
const Lexer = @import("lexer.zig");
const Ast = @This();
const Store = root.EnumStore(Id, Expr);
pub const Id = root.EnumId(Kind);
pub const Slice = root.EnumSlice(Id);

pub const Ident = packed struct(Ident.Repr) {
    const Repr = u32;
    index: u29,
    mutated: bool = false,
    referenced: bool = false,
    last: bool = false,

    pub fn init(token: Lexer.Token) Ident {
        return .{ .index = @intCast(token.pos) };
    }
};

pub fn cmp(pos: u32, source: []const u8, repr: []const u8) bool {
    return std.mem.eql(u8, Lexer.peekStr(source, pos), repr);
}

pub fn Payload(comptime kind: Kind) type {
    return std.meta.TagPayload(Expr, kind);
}

pub const Kind = enum {
    Void,
    Comment,
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
};

pub const Expr = union(Kind) {
    Void,
    Comment: Pos,
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
        mutates: root.EnumSlice(Ident),
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
    decls: []Decl = &.{},

    gpa: std.mem.Allocator,
    arena: std.heap.ArenaAllocator,

    active_syms: std.ArrayListUnmanaged(Sym) = .{},
    all_sym_decls: std.ArrayListUnmanaged(u16) = .{},
    all_sym_occurences: std.ArrayListUnmanaged(Id) = .{},
    mutated_syms: std.ArrayListUnmanaged(Ident) = .{},
    mutated_slices: std.ArrayListUnmanaged(root.EnumSlice(Ident)) = .{},

    lexer: Lexer,
    cur: Lexer.Token,
    list_pos: Pos = undefined,
    undeclared_count: u32 = 0,
    block_depth: u32 = 0,

    const Error = error{UnexpectedToken} || std.mem.Allocator.Error;

    const Sym = struct {
        id: Ident,
        undeclared_count: u32,
        sym_decl: u32,
        first: Id,
        last: Id,
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
        self.decls = try self.gpa.alloc(Decl, self.active_syms.items.len);
        for (self.active_syms.items, self.decls) |s, *d| d.* = .{
            .name = s.id,
            .expr = s.decl,
        };
        for (self.all_sym_occurences.items) |id| {
            const ident = self.store.getTypedPtr(.Ident, id).?;
            ident.id.index = self.all_sym_decls.items[ident.id.index];
        }
        for (self.mutated_slices.items) |slice| {
            for (self.store.view(slice)) |*ident| {
                ident.index = self.all_sym_decls.items[ident.index];
            }
        }
        for (self.active_syms.items[0..remining]) |s| {
            std.debug.print(
                "undefined identifier: {s}\n",
                .{Lexer.peekStr(self.lexer.source, s.id.index)},
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

            const to_decl = if (op == .@":=") self.declareExpr(acum) else null;
            if (op.isAssignment()) try self.markIdent(acum, "mutated");

            self.cur = self.lexer.next();
            const rhs = try self.parseBinExpr(try self.parseUnit(), prec);
            acum = try self.store.alloc(
                self.gpa,
                .BinOp,
                .{ .lhs = acum, .op = op, .rhs = rhs },
            );
            if (to_decl) |decl| self.active_syms.items[decl].decl = acum;
        }
        return acum;
    }

    fn declareExpr(self: *Parser, id: Id) u32 {
        const ident = self.store.getTypedPtr(.Ident, id).?;
        const sym_idx = self.all_sym_decls.items[ident.id.index];
        const sym = &self.active_syms.items[sym_idx];
        if (!std.mem.eql(
            u8,
            Lexer.peekStr(self.lexer.source, ident.pos.index),
            Lexer.peekStr(self.lexer.source, sym.id.index),
        )) {
            std.debug.panic(
                "somehow the identifier and sym do not match: {s} {s}",
                .{
                    Lexer.peekStr(self.lexer.source, ident.pos.index),
                    Lexer.peekStr(self.lexer.source, sym.id.index),
                },
            );
        }
        if (self.block_depth != 0) {
            self.undeclared_count -= 1;
            sym.undeclared_count = self.undeclared_count;
            if (!sym.id.last and !std.meta.eql(id, sym.first))
                std.debug.panic("out of order local variable", .{});
        }
        sym.id.last = true;
        return sym_idx;
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
        const mutated_scope_frame = self.mutated_syms.items.len;
        return try self.store.allocDyn(self.gpa, switch (token.kind) {
            .Comment => .{ .Comment = Pos.init(token.pos) },
            .Ident => return try self.resolveIdent(token),
            .@"fn" => .{ .Fn = .{
                .args = p: {
                    self.block_depth += 1;
                    defer self.block_depth -= 1;
                    break :p try self.parseList(.@"(", .@",", .@")", parseArg);
                },
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
                .fields = try self.parseList(.@".{", .@",", .@"}", parseCtorField),
                .pos = self.list_pos,
            } },
            .@".(" => .{ .Tupl = .{
                .ty = Id.zeroSized(.Void),
                .fields = try self.parseList(.@".(", .@",", .@")", parseExpr),
                .pos = self.list_pos,
            } },
            .@"{" => .{ .Block = .{
                .pos = Pos.init(token.pos),
                .stmts = b: {
                    self.block_depth += 1;
                    defer self.block_depth -= 1;
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
            .int, .void => .{ .Buty = .{ .pos = Pos.init(token.pos), .bt = token.kind } },
            .@"&", .@"*", .@"^" => |op| .{ .UnOp = .{
                .pos = Pos.init(token.pos),
                .op = op,
                .oper = b: {
                    const oper = try self.parseUnit();
                    if (op == .@"&") try self.markIdent(oper, "referenced");
                    break :b oper;
                },
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
                .mutates = b: {
                    const list = self.mutated_syms.items[mutated_scope_frame..];
                    if (list.len == 0) break :b .{};
                    const mutated = try self.store.allocSlice(Ident, self.gpa, list);
                    self.mutated_syms.items.len = mutated_scope_frame;
                    try self.mutated_slices.append(self.gpa, mutated);
                    break :b mutated;
                },
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
            else => |k| std.debug.panic("{any}", .{k}),
        });
    }

    fn markIdent(self: *Parser, expr: Id, comptime flag: []const u8) !void {
        switch (self.store.get(expr)) {
            .Ident => |i| {
                const sym_idx = self.all_sym_decls.items[i.id.index];
                @field(self.active_syms.items[sym_idx].id, flag) = true;
                if (comptime std.mem.eql(u8, flag, "mutated")) {
                    try self.mutated_syms.append(self.gpa, i.id);
                }
            },
            else => {},
        }
    }

    fn finalizeVariablesLow(self: *Parser, start: usize) usize {
        var new_len = start;
        for (self.active_syms.items[start..], start..) |*s, i| {
            if (s.id.last) {
                self.all_sym_decls.items[s.sym_decl] = @intCast(i - s.undeclared_count);
                const first_ident = self.store.getTypedPtr(.Ident, s.first).?;
                var first_ident_id = s.id;
                first_ident_id.last = false;
                first_ident_id.index = @intCast(s.sym_decl);
                first_ident.id = first_ident_id;
                self.store.getTypedPtr(.Ident, s.last).?.id.last = true;
            } else {
                self.all_sym_decls.items[s.sym_decl] = @intCast(new_len);
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

        for (self.active_syms.items) |*s| if (cmp(s.id.index, self.lexer.source, repr)) {
            s.last = try self.store.alloc(self.gpa, .Ident, .{
                .pos = Pos.init(token.pos),
                .id = .{ .index = @intCast(s.sym_decl) },
            });
            try self.all_sym_occurences.append(self.gpa, s.last);
            return s.last;
        };

        const id = Ident{ .index = @intCast(token.pos) };
        const alloc = try self.store.alloc(self.gpa, .Ident, .{
            .pos = Pos.init(token.pos),
            .id = .{ .index = @intCast(self.all_sym_decls.items.len) },
        });
        try self.all_sym_occurences.append(self.gpa, alloc);
        try self.all_sym_decls.append(self.gpa, @intCast(self.active_syms.items.len));
        try self.active_syms.append(self.gpa, .{
            .id = id,
            .undeclared_count = 0,
            .first = alloc,
            .last = alloc,
            .sym_decl = @intCast(self.all_sym_decls.items.len - 1),
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
        self.active_syms.items[self.declareExpr(bindings)].decl = bindings;
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

const Fmt = struct {
    buf: *std.ArrayList(u8),
    indent: u32,
    ast: *const Ast,

    const Error = std.mem.Allocator.Error;

    fn fmt(self: *Fmt) Error!void {
        const items = self.ast.exprs.view(self.ast.items);
        for (items, 1..) |id, i| {
            try self.fmtExpr(id);
            if (items.len > i) {
                try self.autoInsertSemi(items[i]);
                try self.preserveSpace(items[i]);
            }
            try self.buf.appendSlice("\n");
        }
    }

    fn preserveSpace(self: *Fmt, id: Id) Error!void {
        const pos = self.ast.posOf(id);
        const preceding = self.ast.source[0..pos.index];
        const preceding_whitespace = preceding[std.mem.trimRight(u8, preceding, " \t\r\n").len..];
        const nline_count = std.mem.count(u8, preceding_whitespace, "\n");
        if (nline_count > 1) try self.buf.appendSlice("\n");
    }

    fn autoInsertSemi(self: *Fmt, id: Id) Error!void {
        const pos = self.ast.posOf(id);
        const starting_token = Lexer.peek(self.ast.source, pos.index);
        if (starting_token.kind.precedence() < 255) try self.buf.appendSlice(";");
    }

    fn fmtExpr(self: *Fmt, id: Id) Error!void {
        return self.fmtExprPrec(id, 255);
    }

    fn fmtExprPrec(self: *Fmt, id: Id, prec: u8) Error!void {
        switch (self.ast.exprs.get(id)) {
            .Void => {},
            .Comment => |c| {
                const comment_token = Lexer.peek(self.ast.source, c.index);
                const content = std.mem.trimRight(u8, comment_token.view(self.ast.source), "\n");
                try self.buf.appendSlice(content);
            },
            .Ident => |i| try self.buf.appendSlice(Lexer.peekStr(self.ast.source, i.pos.index)),
            .Fn => |f| {
                try self.buf.appendSlice("fn");
                try self.fmtSlice(f.pos.indented, f.args, .@"(", .@",", .@")");
                try self.buf.appendSlice(": ");
                try self.fmtExpr(f.ret);
                try self.buf.appendSlice(" ");
                try self.fmtExpr(f.body);
            },
            .Struct => |s| {
                try self.buf.appendSlice("struct");
                if (s.pos.indented) try self.buf.appendSlice(" ");
                try self.fmtSlice(s.pos.indented, s.fields, .@"{", .@",", .@"}");
            },
            .Arg => |a| {
                try self.fmtExpr(a.bindings);
                try self.buf.appendSlice(": ");
                try self.fmtExpr(a.ty);
            },
            .Call => |c| {
                try self.fmtExpr(c.called);
                try self.fmtSlice(c.arg_pos.indented, c.args, .@"(", .@",", .@")");
            },
            .Field => |f| {
                try self.fmtExpr(f.base);
                try self.buf.appendSlice(".");
                try self.buf.appendSlice(Lexer.peekStr(self.ast.source, f.field.index));
            },
            inline .Ctor, .Tupl => |v, t| {
                try self.fmtExpr(v.ty);
                const start = if (t == .Ctor) .@".{" else .@".(";
                const end = if (t == .Ctor) .@"}" else .@")";
                try self.fmtSlice(v.pos.indented, v.fields, start, .@",", end);
            },
            .CtorField => |f| {
                try self.buf.appendSlice(Lexer.peekStr(self.ast.source, f.pos.index));
                if (self.ast.exprs.getTyped(.Ident, f.value)) |ident|
                    if (std.mem.eql(
                        u8,
                        Lexer.peekStr(self.ast.source, ident.pos.index),
                        Lexer.peekStr(self.ast.source, f.pos.index),
                    )) return;
                try self.buf.appendSlice(": ");
                try self.fmtExpr(f.value);
            },
            .Buty => |b| try self.buf.appendSlice(b.bt.repr()),
            .Block => |b| {
                const view = self.ast.exprs.view(b.stmts);

                try self.buf.appendSlice("{\n");
                self.indent += 1;
                for (view, 1..) |stmt, i| {
                    for (0..self.indent) |_| try self.buf.appendSlice("    ");
                    try self.fmtExpr(stmt);
                    if (view.len > i) {
                        try self.autoInsertSemi(view[i]);
                        try self.preserveSpace(view[i]);
                    }
                    try self.buf.appendSlice("\n");
                }
                self.indent -= 1;
                for (0..self.indent) |_| try self.buf.appendSlice("    ");
                try self.buf.appendSlice("}");
            },
            .If => |i| {
                try self.buf.appendSlice("if ");
                try self.fmtExpr(i.cond);
                try self.buf.appendSlice(" ");
                try self.fmtExpr(i.then);
                if (i.else_.tag() != .Void) {
                    try self.buf.appendSlice(" else ");
                    try self.fmtExpr(i.else_);
                }
            },
            .Loop => |l| {
                try self.buf.appendSlice("loop ");
                try self.fmtExpr(l.body);
            },
            .Break => try self.buf.appendSlice("break"),
            .Continue => try self.buf.appendSlice("continue"),
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
            .BinOp => |o| {
                if (prec < o.op.precedence()) try self.buf.appendSlice("(");
                try self.fmtExprPrec(o.lhs, o.op.precedence());
                // TODO: linebreaks
                try self.buf.appendSlice(" ");
                try self.buf.appendSlice(o.op.repr());
                try self.buf.appendSlice(" ");
                try self.fmtExprPrec(o.rhs, o.op.precedence());
                if (prec < o.op.precedence()) try self.buf.appendSlice(")");
            },
            .Integer => |i| {
                const int_token = Lexer.peek(self.ast.source, i.index);
                try self.buf.appendSlice(self.ast.source[int_token.pos..int_token.end]);
            },
        }
    }

    fn fmtSlice(
        self: *Fmt,
        indent: bool,
        slice: Slice,
        start: Lexer.Lexeme,
        sep: Lexer.Lexeme,
        end: Lexer.Lexeme,
    ) Error!void {
        try self.buf.appendSlice(start.repr());

        if (indent) {
            self.indent += 1;
            try self.buf.appendSlice("\n");
        }

        const view = self.ast.exprs.view(slice);
        for (view, 0..) |id, i| {
            if (indent) for (0..self.indent) |_| try self.buf.appendSlice("    ");
            try self.fmtExpr(id);
            if (indent or i != view.len - 1) {
                try self.buf.appendSlice(sep.repr());
                if (!indent) try self.buf.appendSlice(" ");
            }
            if (indent) try self.buf.appendSlice("\n");
        }

        if (indent) {
            self.indent -= 1;
            for (0..self.indent) |_| try self.buf.appendSlice("    ");
        }

        try self.buf.appendSlice(end.repr());
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
        parser.all_sym_decls.deinit(gpa);
        parser.all_sym_occurences.deinit(gpa);
        parser.mutated_slices.deinit(gpa);
        parser.mutated_syms.deinit(gpa);
    }
    errdefer {
        parser.store.deinit(gpa);
        gpa.free(parser.decls);
    }

    return .{
        .items = try parser.parse(),
        .decls = parser.decls,
        .exprs = parser.store,
        .source = code,
        .path = path,
    };
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
    gpa.free(self.decls);
}

pub fn fmt(self: *const Ast, buf: *std.ArrayList(u8)) !void {
    var ft = Fmt{
        .buf = buf,
        .indent = 0,
        .ast = self,
    };
    try ft.fmt();
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
