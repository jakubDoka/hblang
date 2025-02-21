store: Ast.Store = .{},
path: []const u8,
current: Types.File,
gpa: std.mem.Allocator,
arena: std.heap.ArenaAllocator,
active_syms: std.ArrayListUnmanaged(Sym) = .{},
capture_boundary: usize = 0,
captures: std.ArrayListUnmanaged(Ident) = .{},
lexer: Lexer,
cur: Lexer.Token,
list_pos: Ast.Pos = undefined,
loader: Loader,

const std = @import("std");
const Lexer = @import("Lexer.zig");
const Ast = @import("Ast.zig");
const Types = @import("Types.zig");
const root = @import("utils.zig");
const Ident = Ast.Ident;
const Id = Ast.Id;
const Parser = @This();
const Error = error{UnexpectedToken} || std.mem.Allocator.Error;

const Sym = struct {
    id: Ident,
    declared: bool = false,
    unordered: bool = false,
};

pub const Loader = struct {
    data: *anyopaque,
    _load: *const fn (*anyopaque, LoadOptions) Types.File,

    var noop_state = struct {
        pub fn load(_: *@This(), _: LoadOptions) Types.File {
            return @enumFromInt(0);
        }
    }{};
    pub const noop = Loader.init(&noop_state);

    pub const LoadOptions = struct {
        path: []const u8,
        from: Types.File,
    };

    pub fn init(value: anytype) Loader {
        const Ty = @TypeOf(value.*);
        return .{
            .data = value,
            ._load = struct {
                fn load(self: *anyopaque, opts: LoadOptions) Types.File {
                    const slf: *Ty = @alignCast(@ptrCast(self));
                    return slf.load(opts);
                }
            }.load,
        };
    }

    pub fn load(self: Loader, opts: LoadOptions) Types.File {
        return self._load(self.data, opts);
    }
};

pub fn parse(self: *Parser) !Ast.Slice {
    var itemBuf = std.ArrayListUnmanaged(Id){};
    while (self.cur.kind != .Eof) {
        try itemBuf.append(self.arena.allocator(), try self.parseUnorderedExpr());
        _ = self.tryAdvance(.@";");
    }

    const remining = self.finalizeVariablesLow(0);
    for (self.active_syms.items[0..remining]) |s| {
        self.report(s.id.pos(), "undeclared identifier", .{});
    }
    std.debug.assert(remining == 0);

    return self.store.allocSlice(Id, self.gpa, itemBuf.items);
}

fn parseExpr(self: *Parser) Error!Id {
    return self.parseBinExpr(try self.parseUnit(), 254, false);
}

fn parseUnorderedExpr(self: *Parser) Error!Id {
    return self.parseBinExpr(try self.parseUnit(), 254, true);
}

fn parseBinExpr(self: *Parser, lhs: Id, prevPrec: u8, unordered: bool) Error!Id {
    if (lhs.tag() == .Comment) return lhs;
    var acum = lhs;
    while (true) {
        const op = self.cur.kind;
        const prec = op.precedence();
        if (prec >= prevPrec) break;

        if (op == .@":=" or op == .@":") _ = self.declareExpr(acum, unordered);

        self.cur = self.lexer.next();
        const rhs = try self.parseBinExpr(try self.parseUnit(), prec, false);
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
    }
    return acum;
}

fn declareExpr(self: *Parser, id: Id, unordered: bool) void {
    const ident: Ident = (self.store.getTypedPtr(.Ident, id) orelse return).id;
    var iter = std.mem.reverseIterator(self.active_syms.items);
    const sym = while (iter.nextPtr()) |s| {
        if (s.id == ident) break s;
    } else unreachable;
    if (sym.declared and self.loader.data != Loader.noop.data) {
        self.report(ident.pos(), "redeclaration of identifier", .{});
    }
    sym.declared = true;
    sym.unordered = unordered;
}

fn parseUnit(self: *Parser) Error!Id {
    var base = try self.parseUnitWithoutTail();
    if (base.tag() == .Comment) {
        return base;
    }

    while (true) base = try self.store.allocDyn(self.gpa, switch (self.cur.kind) {
        .@"." => .{ .Field = .{
            .base = base,
            .field = b: {
                _ = self.advance();
                break :b .init((try self.expectAdvance(.Ident)).pos);
            },
        } },
        .@"(" => .{ .Call = .{
            .called = base,
            .args = try self.parseList(.@"(", .@",", .@")", parseExpr),
            .arg_pos = self.list_pos,
        } },
        .@".{" => .{ .Ctor = .{
            .ty = base,
            .fields = try self.parseList(.@".{", .@";", .@"}", parseExpr),
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

fn report(self: *Parser, pos: u32, comptime msg: []const u8, args: anytype) void {
    const line, const col = Ast.lineCol(self.lexer.source, pos);
    std.debug.panic(
        "{s}:{}:{}: " ++ msg ++ "\n{}\n",
        .{ self.path, line, col } ++ args ++ .{self.codePointer(pos)},
    );
}

fn codePointer(self: *const Parser, pos: usize) Ast.CodePointer {
    return .{ .source = self.lexer.source, .index = pos };
}

fn popCaptures(self: *Parser, scope: usize) []const Ident {
    const slc = self.captures.items[scope..];
    self.captures.items.len = scope;
    if (slc.len > 1) {
        std.sort.pdq(u32, @ptrCast(slc), {}, std.sort.asc(u32));
        var i: usize = 0;
        for (slc[1..]) |s| {
            if (s != slc[i]) {
                i += 1;
                slc[i] = s;
            }
        }
        return slc[0 .. i + 1];
    }
    return slc;
}

fn parseUnitWithoutTail(self: *Parser) Error!Id {
    var token = self.advance();
    const scope_frame = self.active_syms.items.len;
    return try self.store.allocDyn(self.gpa, switch (token.kind) {
        .Comment => .{ .Comment = .init(token.pos) },
        ._ => .{ .Wildcard = .init(token.pos) },
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
        .@"@" => if (Ast.cmpLow(token.pos, self.lexer.source, "@use")) .{ .Use = .{
            .file = b: {
                _ = try self.expectAdvance(.@"(");
                token = try self.expectAdvance(.@"\"");
                const path = token.view(self.lexer.source);
                _ = try self.expectAdvance(.@")");
                break :b self.loader.load(.{ .from = self.current, .path = path[1 .. path.len - 1] });
            },
            .pos = .init(token.pos),
        } } else .{ .Directive = .{
            .args = try self.parseList(.@"(", .@",", .@")", parseExpr),
            .pos = .{ .index = @intCast(token.pos), .indented = self.list_pos.indented },
        } },
        .@"struct" => b: {
            const prev_capture_boundary = self.capture_boundary;
            self.capture_boundary = self.active_syms.items.len;
            defer self.capture_boundary = prev_capture_boundary;

            const capture_scope = self.captures.items.len;
            break :b .{ .Struct = .{
                .fields = try self.parseList(.@"{", .@";", .@"}", parseUnorderedExpr),
                .captures = try self.store.allocSlice(Ident, self.gpa, self.popCaptures(capture_scope)),
                .pos = self.list_pos,
            } };
        },
        .@"." => b: {
            break :b .{ .Tag = .init((try self.expectAdvance(.Ident)).pos - 1) };
        },
        .@".{" => .{ .Ctor = .{
            .ty = .zeroSized(.Void),
            .fields = try self.parseList(null, .@";", .@"}", parseExpr),
            .pos = self.list_pos,
        } },
        .@".(" => .{ .Tupl = .{
            .ty = .zeroSized(.Void),
            .fields = try self.parseList(null, .@",", .@")", parseExpr),
            .pos = self.list_pos,
        } },
        .@"{" => .{ .Block = .{
            .pos = .{ .index = @intCast(token.pos), .indented = true },
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
        .void, .bool, .u8, .u16, .u32, .uint, .i8, .i16, .i32, .int, .type => .{
            .Buty = .{ .pos = .init(token.pos), .bt = token.kind },
        },
        .@"&", .@"*", .@"^", .@"-" => |op| .{ .UnOp = .{
            .pos = .init(token.pos),
            .op = op,
            .oper = try self.parseUnit(),
        } },
        .@"if" => .{ .If = .{
            .pos = .init(token.pos),
            .cond = try self.parseExpr(),
            .then = try self.parseExpr(),
            .else_ = if (self.tryAdvance(.@"else"))
                try self.parseExpr()
            else
                .zeroSized(.Void),
        } },
        .loop => .{ .Loop = .{
            .pos = .init(token.pos),
            .body = try self.parseExpr(),
        } },
        .@"break" => .{ .Break = .init(token.pos) },
        .@"continue" => .{ .Continue = .init(token.pos) },
        .@"return" => .{ .Return = .{
            .pos = .init(token.pos),
            .value = if (self.cur.kind.cantStartExpression())
                .zeroSized(.Void)
            else
                try self.parseExpr(),
        } },
        .Integer => .{ .Integer = .init(token.pos) },
        .true => .{ .Bool = .{ .value = true, .pos = .init(token.pos) } },
        .false => .{ .Bool = .{ .value = false, .pos = .init(token.pos) } },
        else => |k| {
            self.report(token.pos, "no idea how to handle this: {s}", .{@tagName(k)});
            unreachable;
        },
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

    for (self.active_syms.items, 0..) |*s, i| if (Ast.cmpLow(s.id.pos(), self.lexer.source, repr)) {
        if (i < self.capture_boundary and !s.unordered) try self.captures.append(self.gpa, s.id);
        return try self.store.alloc(self.gpa, .Ident, .{
            .pos = .init(token.pos),
            .id = s.id,
        });
    };

    const id = Ident.init(token);
    const alloc = try self.store.alloc(self.gpa, .Ident, .{
        .pos = .init(token.pos),
        .id = id,
    });
    try self.active_syms.append(self.gpa, .{
        .id = id,
    });
    return alloc;
}

fn parseList(
    self: *Parser,
    start: ?Lexer.Lexeme,
    sep: ?Lexer.Lexeme,
    end: Lexer.Lexeme,
    comptime parser: fn (*Parser) Error!Id,
) Error!Ast.Slice {
    if (start) |s| _ = try self.expectAdvance(s);
    self.list_pos = .{ .index = @intCast(self.cur.pos) };
    var buf = std.ArrayListUnmanaged(Id){};
    while (!self.tryAdvance(end)) {
        try buf.append(self.arena.allocator(), try parser(self));
        if (self.tryAdvance(end)) {
            self.list_pos.indented = sep == null;
            break;
        }
        if (sep) |s| _ = self.tryAdvance(s);
        self.list_pos.indented = true;
    }
    return try self.store.allocSlice(Id, self.gpa, buf.items);
}

fn parseArg(self: *Parser) Error!Id {
    const bindings = try self.parseUnitWithoutTail();
    _ = self.declareExpr(bindings, false);
    _ = try self.expectAdvance(.@":");
    return try self.store.alloc(self.gpa, .Arg, .{
        .bindings = bindings,
        .ty = try self.parseExpr(),
    });
}

inline fn tryAdvance(self: *Parser, expected: Lexer.Lexeme) bool {
    if (self.cur.kind != expected) return false;
    _ = self.advance();
    return true;
}

fn expectAdvance(self: *Parser, expected: Lexer.Lexeme) !Lexer.Token {
    if (self.cur.kind != expected) {
        self.report(self.cur.pos, "expected {s}, got {s}", .{ @tagName(expected), @tagName(self.cur.kind) });
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
