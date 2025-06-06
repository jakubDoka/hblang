const std = @import("std");

const root = @import("hb");
const utils = root.utils;
const Lexer = root.frontend.Lexer;
const Fmt = root.frontend.Fmt;
const Types = root.frontend.Types;
const Arena = utils.Arena;
const Ast = root.frontend.Ast;
const Ident = Ast.Ident;
const Id = Ast.Id;

store: Ast.Store = .{},
arena: *utils.Arena,
active_syms: std.ArrayListUnmanaged(Sym) = .{},
capture_boundary: usize = 0,
captures: std.ArrayListUnmanaged(Ident) = .{},
comptime_idents: std.ArrayListUnmanaged(Ident) = .{},
lexer: Lexer,
cur: Lexer.Token,
current: Types.File,
path: []const u8,
loader: Loader,
diagnostics: std.io.AnyWriter,
list_pos: Ast.Pos = undefined,
deferring: bool = false,
errored: bool = false,
stack_base: usize,
func_stats: FuncStats = .{},

pub const stack_limit = 1024 * 1024;

const Parser = @This();
const Error = error{ UnexpectedToken, StackOverflow } || std.mem.Allocator.Error;

const FuncStats = struct {
    loop_depth: u16 = 0,
    max_loop_depth: u16 = 0,
    max_variable_count: u16 = 0,
    variable_count: u16 = 0,
};

const Sym = struct {
    name: []const u8,
    id: Ident,
    declared: bool = false,
    unordered: bool = true,
    used: bool = false,
};

pub const Loader = struct {
    data: *anyopaque,
    _load: *const fn (*anyopaque, LoadOptions) ?Types.File,

    var noop_state = struct {
        pub fn load(_: *@This(), _: LoadOptions) ?Types.File {
            return @enumFromInt(0);
        }
    }{};
    pub const noop = Loader.init(&noop_state);

    pub const LoadOptions = struct {
        path: []const u8,
        from: Types.File,
        pos: u32,
        diagnostics: std.io.AnyWriter,
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
                fn load(self: *anyopaque, opts: LoadOptions) ?Types.File {
                    const slf: *Ty = @alignCast(@ptrCast(self));
                    return slf.load(opts);
                }
            }.load,
        };
    }

    pub fn load(self: Loader, opts: LoadOptions) ?Types.File {
        return self._load(self.data, opts);
    }
};

pub fn parse(self: *Parser) !Ast.Slice {
    var tmp = Arena.scrath(self.arena);
    defer tmp.deinit();

    var itemBuf = std.ArrayListUnmanaged(Id){};
    while (self.cur.kind != .Eof) {
        try itemBuf.append(tmp.arena.allocator(), try self.parseUnorderedExpr());
        _ = self.tryAdvance(.@";");
    }

    const remining = self.finalizeVariablesLow(0);
    if (!self.loader.isNoop()) {
        for (self.active_syms.items[0..remining]) |s| {
            self.report(s.id.pos(), "undeclared identifier", .{});
        }
    }

    return self.store.allocSlice(Id, self.arena.allocator(), itemBuf.items);
}

fn parseExpr(self: *Parser) Error!Id {
    return self.parseBinExpr(try self.parseUnit(), 254, false);
}

fn parseScopedExpr(self: *Parser) !Id {
    const scope = self.active_syms.items.len;
    defer self.finalizeVariables(scope);
    return self.parseExpr();
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

        self.cur = self.lexer.next();
        if (op == .@":=") {
            _ = self.declareExpr(acum, unordered);
            return try self.store.alloc(self.arena.allocator(), .Decl, .{
                .bindings = acum,
                .value = try self.parseExpr(),
            });
        } else if (op == .@":") {
            const lover_prec = comptime Lexer.Lexeme.@"=".precedence() - 1;
            const ty = try self.parseBinExpr(try self.parseUnit(), lover_prec, false);
            _ = self.declareExpr(acum, unordered);

            return try self.store.alloc(self.arena.allocator(), .Decl, .{
                .bindings = acum,
                .ty = ty,
                .value = if (self.tryAdvance(.@"="))
                    try self.parseExpr()
                else
                    .zeroSized(.Void),
            });
        }

        const rhs = try self.parseBinExpr(try self.parseUnit(), prec, false);
        if (op.innerOp()) |iop| {
            acum = try self.store.alloc(self.arena.allocator(), .BinOp, .{
                .lhs = acum,
                .op = .@"=",
                .rhs = try self.store.alloc(
                    self.arena.allocator(),
                    .BinOp,
                    .{ .lhs = acum, .op = iop, .rhs = rhs },
                ),
            });
        } else {
            acum = try self.store.alloc(
                self.arena.allocator(),
                .BinOp,
                .{ .lhs = acum, .op = op, .rhs = rhs },
            );
        }
    }
    return acum;
}

fn declareExpr(self: *Parser, id: Id, unordered: bool) void {
    const ident = switch (id.tag()) {
        .Ident => self.store.getTyped(.Ident, id).?.*,
        .Ctor => {
            const c = self.store.getTyped(.Ctor, id).?;
            if (c.ty.tag() != .Void) self.declareExpr(c.ty, unordered);
            for (self.store.view(c.fields)) |f| self.declareExpr(f.value, unordered);
            return;
        },
        else => return,
    };
    var iter = std.mem.reverseIterator(self.active_syms.items);
    const sym = while (iter.nextPtr()) |s| {
        if (s.id == ident.id) break s;
    } else unreachable;
    if (sym.declared and !self.loader.isNoop()) {
        self.report(ident.pos.index, "redeclaration of identifier", .{});
    } else if (!unordered and ident.pos.index > ident.id.pos()) {
        self.report(ident.pos.index, "out of order declaration in ordered scope", .{});
    } else if (!unordered and sym.used) {
        self.report(ident.pos.index, "ordered declaration is used recursively", .{});
    }
    sym.declared = true;
    sym.unordered = unordered;

    self.func_stats.variable_count += 1;
    self.func_stats.max_variable_count =
        @max(self.func_stats.max_variable_count, self.func_stats.variable_count);
}

fn parseUnit(self: *Parser) Error!Id {
    var base = try self.parseUnitWithoutTail();
    if (base.tag() == .Comment) {
        return base;
    }

    while (true) base = try self.store.allocDyn(self.arena.allocator(), switch (self.cur.kind) {
        .@"." => b: {
            _ = self.advance();
            break :b if (self.tryAdvance(.@"?")) .{
                .Unwrap = base,
            } else if (self.tryAdvance(.@"*")) .{
                .Deref = base,
            } else .{ .Field = .{
                .base = base,
                .field = .init((try self.expectAdvance(.Ident)).pos),
            } };
        },
        .@"[" => .{ .Index = .{
            .base = base,
            .subscript = b: {
                _ = self.advance();
                const start: Id = if (self.cur.kind == .@"..") .zeroSized(.Void) else try self.parseExpr();
                const is_range = self.tryAdvance(.@"..");
                const end: Id = if (self.cur.kind == .@"]") .zeroSized(.Void) else try self.parseExpr();
                _ = try self.expectAdvance(.@"]");
                break :b if (is_range)
                    try self.store.allocDyn(self.arena.allocator(), .{ .Range = .{ .start = start, .end = end } })
                else
                    start;
            },
        } },
        .@"(" => .{ .Call = .{
            .called = base,
            .args = try self.parseList(.@"(", .@",", .@")", parseExpr),
            .arg_pos = self.list_pos,
        } },
        .@".{" => .{ .Ctor = .{
            .ty = base,
            .fields = try self.parseListTyped(.@".{", .@",", .@"}", Ast.CtorField, parseCtorField),
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
    self.errored = true;
    Ast.report(self.path, self.lexer.source, pos, msg, args, self.diagnostics);
}

fn codePointer(self: *const Parser, pos: usize) Ast.CodePointer {
    return .{ .source = self.lexer.source, .index = pos };
}

fn popCaptures(self: *Parser, scope: usize, preserve: bool) []const Ident {
    const slc = self.captures.items[@min(scope, self.captures.items.len)..];
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

fn parseCtorField(self: *Parser) Error!Ast.CtorField {
    const id = try self.expectAdvance(.Ident);
    return .{
        .pos = .init(id.pos),
        .value = if (self.tryAdvance(.@":"))
            try self.parseExpr()
        else
            try self.resolveIdent(id),
    };
}

fn checkStack(self: *Parser) !void {
    const distance = @abs(@as(isize, @bitCast(@frameAddress() -% self.stack_base)));
    if (distance > stack_limit) {
        self.report(self.cur.pos, "the tree is too deep", .{});
        return error.StackOverflow;
    }
}

fn parseUnitWithoutTail(self: *Parser) Error!Id {
    try self.checkStack();

    var token = self.advance();
    const scope_frame = self.active_syms.items.len;
    return try self.store.allocDyn(self.arena.allocator(), switch (token.kind.expand()) {
        .Comment => .{ .Comment = .init(token.pos) },
        ._ => .{ .Wildcard = .init(token.pos) },
        .idk => .{ .Idk = .init(token.pos) },
        .die => .{ .Die = .init(token.pos) },
        .null => .{ .Null = .init(token.pos) },
        .@"$", .Ident => return try self.resolveIdent(token),
        .@"fn" => b: {
            const prev_func_stats = self.func_stats;
            defer self.func_stats = prev_func_stats;
            self.func_stats = .{};

            const prev_capture_boundary = self.capture_boundary;
            self.capture_boundary = self.active_syms.items.len;
            defer self.capture_boundary = prev_capture_boundary;

            const capture_scope = self.captures.items.len;
            const comptime_arg_start = self.comptime_idents.items.len;
            defer self.comptime_idents.items.len = comptime_arg_start;
            const args = try self.parseListTyped(.@"(", .@",", .@")", Ast.Arg, parseArg);
            const comptime_idents_end = self.comptime_idents.items.len;
            const indented_args = self.list_pos.flag;
            _ = try self.expectAdvance(.@":");
            const ret = try self.parseExpr();

            const body = body: {
                defer self.finalizeVariables(scope_frame);
                break :body try self.parseExpr();
            };

            const comptime_args = try self.store.allocSlice(Ident, self.arena.allocator(), self.comptime_idents.items[comptime_arg_start..comptime_idents_end]);
            const captures = try self.store.allocSlice(Ident, self.arena.allocator(), self.popCaptures(capture_scope, prev_capture_boundary != 0));
            std.debug.assert(comptime_args.end == captures.start);

            break :b .{ .Fn = .{
                .args = args,
                .comptime_args = comptime_args,
                .captures = captures,
                .pos = .{ .index = @intCast(token.pos), .flag = indented_args },
                .ret = ret,
                .body = body,
                .peak_vars = self.func_stats.max_variable_count,
                .peak_loops = self.func_stats.max_loop_depth,
            } };
        },

        .Directive => |k| switch (k) {
            inline .use, .embed => |t| b: {
                const ty = @field(Loader.LoadOptions.Kind, @tagName(t));

                _ = try self.expectAdvance(.@"(");
                token = try self.expectAdvance(.@"\"");
                const path = token.view(self.lexer.source);
                _ = try self.expectAdvance(.@")");

                break :b .{ .Use = .{
                    .file = self.loader.load(.{
                        .from = self.current,
                        .path = path[1 .. path.len - 1],
                        .type = ty,
                        .pos = token.pos,
                        .diagnostics = self.diagnostics,
                    }) orelse c: {
                        self.errored = true;
                        break :c .root;
                    },
                    .pos = .{
                        .index = @intCast(token.pos),
                        .flag = .{ .use_kind = ty },
                    },
                } };
            },
            else => .{ .Directive = .{
                .kind = k,
                .args = try self.parseList(.@"(", .@",", .@")", parseExpr),
                .pos = .{ .index = @intCast(token.pos), .flag = self.list_pos.flag },
            } },
        },
        inline .@"enum", .@"union", .@"struct" => |_, t| b: {
            const name = comptime nm: {
                var nm = @tagName(t)[0..].*;
                nm[0] = std.ascii.toUpper(nm[0]);
                break :nm nm[0..] ++ "";
            };

            const prev_func_stats = self.func_stats;
            defer self.func_stats = prev_func_stats;

            const prev_capture_boundary = self.capture_boundary;
            self.capture_boundary = self.active_syms.items.len;
            defer self.capture_boundary = prev_capture_boundary;

            var alignment: Id = .zeroSized(.Void);
            if (self.tryAdvance(.@"align")) {
                _ = try self.expectAdvance(.@"(");
                alignment = try self.parseExpr();
                _ = try self.expectAdvance(.@")");
            }

            const capture_scope = self.captures.items.len;
            const fields = try self.parseList(.@"{", .@";", .@"}", parseUnorderedExpr);
            self.finalizeVariables(scope_frame);
            const captures = self.popCaptures(capture_scope, prev_capture_boundary != 0);
            break :b @unionInit(Ast.Expr, name, .{
                .fields = fields,
                .alignment = alignment,
                .captures = try self.store.allocSlice(Ident, self.arena.allocator(), captures),
                .pos = .{ .index = @intCast(token.pos), .flag = self.list_pos.flag },
            });
        },
        .@"." => .{ .Tag = .init((try self.expectAdvance(.Ident)).pos - 1) },
        .@"defer" => .{ .Defer = b: {
            self.deferring = true;
            defer self.deferring = false;
            break :b try self.parseExpr();
        } },
        .@".{" => .{ .Ctor = .{
            .ty = .zeroSized(.Void),
            .fields = try self.parseListTyped(null, .@",", .@"}", Ast.CtorField, parseCtorField),
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
                var tmp = Arena.scrath(self.arena);
                defer tmp.deinit();
                var buf = std.ArrayListUnmanaged(Id){};
                while (!self.tryAdvance(.@"}")) {
                    try buf.append(tmp.arena.allocator(), try self.parseExpr());
                    _ = self.tryAdvance(.@";");
                }
                self.finalizeVariables(scope_frame);
                break :b try self.store.allocSlice(Id, self.arena.allocator(), buf.items);
            },
        } },
        .@"(" => {
            const expr = try self.parseExpr();
            _ = try self.expectAdvance(.@")");
            return expr;
        },
        .Type => |t| .{ .Buty = .{ .pos = .init(token.pos), .bt = t } },
        .@"&", .@"^", .@"-", .@"~", .@"!", .@"?" => .{ .UnOp = .{
            .pos = .init(token.pos),
            .op = token.kind,
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
            .cond = try self.parseScopedExpr(),
            .then = try self.parseScopedExpr(),
            .else_ = if (self.tryAdvance(.@"else"))
                try self.parseScopedExpr()
            else
                .zeroSized(.Void),
        } },
        .match, .@"$match" => .{ .Match = .{
            .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind == .@"$match" } },
            .value = try self.parseExpr(),
            .arms = try self.parseListTyped(.@"{", .@",", .@"}", Ast.MatchArm, parseMatchArm),
        } },
        .loop, .@"$loop" => .{ .Loop = .{
            .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind != .loop } },
            .body = b: {
                self.func_stats.loop_depth += 1;
                self.func_stats.max_loop_depth =
                    @max(self.func_stats.max_loop_depth, self.func_stats.loop_depth);
                defer self.func_stats.loop_depth -= 1;
                break :b try self.parseScopedExpr();
            },
        } },
        .@"break" => b: {
            if (self.deferring) self.report(token.pos, "can not break from a defer", .{});
            break :b .{ .Break = .init(token.pos) };
        },
        .@"continue" => b: {
            if (self.deferring) self.report(token.pos, "can not continue from a defer", .{});
            break :b .{ .Continue = .init(token.pos) };
        },
        .@"return" => .{ .Return = .{
            .pos = .init(token.pos),
            .value = b: {
                if (self.deferring) self.report(token.pos, "can not return from a defer", .{});

                break :b if (self.cur.kind.cantStartExpression())
                    .zeroSized(.Void)
                else
                    try self.parseExpr();
            },
        } },
        .BinInteger, .OctInteger, .DecInteger, .HexInteger => .{ .Integer = .{ .pos = .init(token.pos), .base = @intCast(@intFromEnum(token.kind) & ~@as(u8, 128)) } },
        .Float => .{ .Float = .init(token.pos) },
        .true => .{ .Bool = .{ .value = true, .pos = .init(token.pos) } },
        .@"\"" => .{ .String = .{ .pos = .init(token.pos), .end = token.end } },
        .@"'" => .{ .Quotes = .{ .pos = .init(token.pos), .end = token.end } },
        .false => .{ .Bool = .{ .value = false, .pos = .init(token.pos) } },
        else => |k| {
            self.report(token.pos, "no idea how to handle this: {s}", .{@tagName(k)});
            return error.UnexpectedToken;
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
    self.func_stats.variable_count -|= @intCast(self.active_syms.items.len - new_len);
    return new_len;
}

fn finalizeVariables(self: *Parser, start: usize) void {
    self.active_syms.items.len = self.finalizeVariablesLow(start);
}

fn resolveIdent(self: *Parser, token: Lexer.Token) !Id {
    var repr = token.view(self.lexer.source);
    if (token.kind == .@"$") repr = repr[1..];

    var iter = std.mem.reverseIterator(self.active_syms.items);
    var i = self.active_syms.items.len;
    while (iter.nextPtr()) |s| {
        i -= 1;
        if (std.mem.eql(u8, s.name, repr)) {
            s.used = true;
            if (i < self.capture_boundary and !s.unordered) {
                try self.captures.append(self.arena.allocator(), s.id);
            }
            return try self.store.alloc(self.arena.allocator(), .Ident, .{
                .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind == .@"$" } },
                .id = s.id,
            });
        }
    }

    const id = Ident.init(token);
    const alloc = try self.store.alloc(self.arena.allocator(), .Ident, .{
        .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind == .@"$" } },
        .id = id,
    });
    if (token.kind == .@"$") try self.comptime_idents.append(self.arena.allocator(), id);
    try self.active_syms.append(self.arena.allocator(), .{ .name = repr, .id = id });
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
) Error!utils.EnumSlice(Elem) {
    var tmp = Arena.scrath(self.arena);
    defer tmp.deinit();

    const pos = self.cur.pos;
    if (start) |s| _ = try self.expectAdvance(s);
    var buf = std.ArrayListUnmanaged(Elem){};
    var indented = false;
    while (!self.tryAdvance(end)) {
        try buf.append(tmp.arena.allocator(), try parser(self));
        if (sep) |s| indented = self.tryAdvance(s);
    }
    self.list_pos = .{ .index = @intCast(pos), .flag = .{ .indented = indented } };
    return try self.store.allocSlice(Elem, self.arena.allocator(), buf.items);
}

fn parseMatchArm(self: *Parser) Error!Ast.MatchArm {
    const pat = try self.parseExpr();
    _ = try self.expectAdvance(.@"=>");
    return .{
        .pat = pat,
        .body = try self.parseExpr(),
    };
}

fn parseArg(self: *Parser) Error!Ast.Arg {
    const pos = self.cur.pos;
    const bindings = try self.parseUnitWithoutTail();
    if (bindings.tag() != .Ident) {
        self.report(pos, "expected ident", .{});
    }
    _ = self.declareExpr(bindings, false);
    _ = try self.expectAdvance(.@":");

    const prev = self.comptime_idents.items.len;
    defer self.comptime_idents.items.len = prev;
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
        return error.UnexpectedToken;
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
