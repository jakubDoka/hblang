store: Ast.Store = .{},
path: []const u8,
current: Types.File,
gpa: std.mem.Allocator,
arena: std.heap.ArenaAllocator,
active_syms: std.ArrayListUnmanaged(Sym) = .{},
capture_boundary: usize = 0,
captures: std.ArrayListUnmanaged(Ident) = .{},
comptime_idents: std.ArrayListUnmanaged(Ident) = .{},
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
        type: Kind,

        pub const Kind = enum(u1) { use, embed };
    };

    pub fn isNoop(self: Loader) bool {
        return self._load == noop._load;
    }

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
    if (!self.loader.isNoop()) {
        for (self.active_syms.items[0..remining]) |s| {
            self.report(s.id.pos(), "undeclared identifier", .{});
        }
        std.debug.assert(remining == 0);
    }

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
    if (sym.declared and !self.loader.isNoop()) {
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
        .@"." => b: {
            _ = self.advance();
            break :b if (self.tryAdvance(.@"!")) .{
                .Unwrap = base,
            } else .{ .Field = .{
                .base = base,
                .field = .init((try self.expectAdvance(.Ident)).pos),
            } };
        },
        .@"[" => .{ .Index = .{
            .base = base,
            .subscript = b: {
                _ = self.advance();
                if (self.tryAdvance(.@"]")) break :b .zeroSized(.Void);
                const expr = try self.parseExpr();
                _ = try self.expectAdvance(.@"]");
                break :b expr;
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
        .@".[" => .{ .Arry = .{
            .ty = base,
            .fields = try self.parseList(.@".[", .@",", .@"]", parseExpr),
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

fn popCaptures(self: *Parser, scope: usize, preserve: bool) []const Ident {
    const slc = self.captures.items[scope..];
    if (!preserve) self.captures.items.len = scope;
    if (slc.len > 1) {
        std.sort.pdq(u32, @ptrCast(slc), {}, std.sort.asc(u32));
        var i: usize = 0;
        for (slc[1..]) |s| {
            if (s != slc[i]) {
                i += 1;
                slc[i] = s;
            }
        }
        if (preserve) self.captures.items.len = scope + i + 1;
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
        .idk => .{ .Idk = .init(token.pos) },
        .null => .{ .Null = .init(token.pos) },
        .@"$", .Ident => return try self.resolveIdent(token),
        .@"fn" => b: {
            const prev_capture_boundary = self.capture_boundary;
            self.capture_boundary = self.active_syms.items.len;
            defer self.capture_boundary = prev_capture_boundary;

            const comptime_arg_start = self.comptime_idents.items.len;
            defer self.comptime_idents.items.len = comptime_arg_start;
            const args = try self.parseListTyped(.@"(", .@",", .@")", Ast.Arg, parseArg);
            const indented_args = self.list_pos.flag;
            _ = try self.expectAdvance(.@":");
            const ret = try self.parseExpr();

            const capture_scope = self.captures.items.len;
            const body = body: {
                defer self.finalizeVariables(scope_frame);
                break :body try self.parseExpr();
            };

            const comptime_args = try self.store.allocSlice(Ident, self.gpa, self.comptime_idents.items[comptime_arg_start..]);
            const captures = try self.store.allocSlice(Ident, self.gpa, self.popCaptures(capture_scope, prev_capture_boundary != 0));
            std.debug.assert(comptime_args.end == captures.start);

            break :b .{ .Fn = .{
                .args = args,
                .comptime_args = comptime_args,
                .captures = captures,
                .pos = .{ .index = @intCast(token.pos), .flag = indented_args },
                .ret = ret,
                .body = body,
            } };
        },
        .@"@" => if (Ast.cmpLow(token.pos, self.lexer.source, "@use") or
            Ast.cmpLow(token.pos, self.lexer.source, "@embed"))
        b: {
            const embed: Loader.LoadOptions.Kind =
                if (Ast.cmpLow(token.pos, self.lexer.source, "@embed")) .embed else .use;

            _ = try self.expectAdvance(.@"(");
            token = try self.expectAdvance(.@"\"");
            const path = token.view(self.lexer.source);
            _ = try self.expectAdvance(.@")");

            break :b .{ .Use = .{
                .file = self.loader.load(.{
                    .from = self.current,
                    .path = path[1 .. path.len - 1],
                    .type = embed,
                }),
                .pos = .{
                    .index = @intCast(token.pos),
                    .flag = .{ .use_kind = embed },
                },
            } };
        } else .{ .Directive = .{
            .args = try self.parseList(.@"(", .@",", .@")", parseExpr),
            .pos = .{ .index = @intCast(token.pos), .flag = self.list_pos.flag },
        } },
        .@"struct" => b: {
            const prev_capture_boundary = self.capture_boundary;
            self.capture_boundary = self.active_syms.items.len;
            defer self.capture_boundary = prev_capture_boundary;

            const capture_scope = self.captures.items.len;
            const fields = try self.parseList(.@"{", .@";", .@"}", parseUnorderedExpr);
            const captures = self.popCaptures(capture_scope, prev_capture_boundary != 0);
            break :b .{ .Struct = .{
                .fields = fields,
                .captures = try self.store.allocSlice(Ident, self.gpa, captures),
                .pos = .{ .index = @intCast(token.pos), .flag = self.list_pos.flag },
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
        .@".[" => .{ .Arry = .{
            .ty = .zeroSized(.Void),
            .fields = try self.parseList(null, .@",", .@"]", parseExpr),
            .pos = self.list_pos,
        } },
        .@"{" => .{ .Block = .{
            .pos = .{ .index = @intCast(token.pos), .flag = .{ .indented = true } },
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
        .@"&", .@"^", .@"-", .@"?" => |op| .{ .UnOp = .{
            .pos = .init(token.pos),
            .op = op,
            .oper = try self.parseUnit(),
        } },
        .@"[" => .{ .SliceTy = .{
            .pos = .init(token.pos),
            .len = if (self.tryAdvance(.@"]")) .zeroSized(.Void) else b: {
                const expr = try self.parseExpr();
                _ = try self.expectAdvance(.@"]");
                break :b expr;
            },
            .elem = try self.parseUnit(),
        } },
        .@"if", .@"$if" => .{ .If = .{
            .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind == .@"$if" } },
            .cond = try self.parseExpr(),
            .then = try self.parseExpr(),
            .else_ = if (self.tryAdvance(.@"else"))
                try self.parseExpr()
            else
                .zeroSized(.Void),
        } },
        .loop, .@"$loop" => .{ .Loop = .{
            .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind != .loop } },
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
        .@"\"" => .{ .String = .{ .pos = .init(token.pos), .end = token.end } },
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
        } else {
            while (std.mem.indexOfScalar(Ident, self.captures.items, s.id)) |idx| {
                _ = self.captures.swapRemove(idx);
            }
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
        if (i < self.capture_boundary and !s.unordered) {
            try self.captures.append(self.gpa, s.id);
        }
        return try self.store.alloc(self.gpa, .Ident, .{
            .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind == .@"$" } },
            .id = s.id,
        });
    };

    const id = Ident.init(token);
    const alloc = try self.store.alloc(self.gpa, .Ident, .{
        .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind == .@"$" } },
        .id = id,
    });
    if (token.kind == .@"$") self.comptime_idents.append(self.gpa, id) catch unreachable;
    try self.active_syms.append(self.gpa, .{ .id = id });
    return alloc;
}

fn parseList(
    self: *Parser,
    start: ?Lexer.Lexeme,
    sep: ?Lexer.Lexeme,
    end: Lexer.Lexeme,
    comptime parser: fn (*Parser) Error!Id,
) Error!Ast.Slice {
    return self.parseListTyped(start, sep, end, Id, parser);
}

fn parseListTyped(
    self: *Parser,
    start: ?Lexer.Lexeme,
    sep: ?Lexer.Lexeme,
    end: Lexer.Lexeme,
    comptime Elem: type,
    comptime parser: fn (*Parser) Error!Elem,
) Error!root.EnumSlice(Elem) {
    const pos = self.cur.pos;
    if (start) |s| _ = try self.expectAdvance(s);
    var buf = std.ArrayListUnmanaged(Elem){};
    var indented = false;
    while (!self.tryAdvance(end)) {
        try buf.append(self.arena.allocator(), try parser(self));
        if (sep) |s| indented = self.tryAdvance(s);
    }
    self.list_pos = .{ .index = @intCast(pos), .flag = .{ .indented = indented } };
    return try self.store.allocSlice(Elem, self.gpa, buf.items);
}

fn parseArg(self: *Parser) Error!Ast.Arg {
    const bindings = try self.parseUnitWithoutTail();
    _ = self.declareExpr(bindings, false);
    _ = try self.expectAdvance(.@":");
    return .{
        .bindings = bindings,
        .ty = try self.parseExpr(),
    };
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
