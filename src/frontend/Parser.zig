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
const Capture = Ast.Capture;

arena: *utils.Arena,
lexer: Lexer,
cur: Lexer.Token,
current: Types.File,
path: []const u8,
loader: Loader,
diagnostics: std.io.AnyWriter,
colors: std.io.tty.Config,
stack_base: usize,
store: Ast.Store = .{},
active_sym_table: std.HashMapUnmanaged(
    u32,
    void,
    Hasher,
    std.hash_map.default_max_load_percentage,
) = .{},
active_syms: std.ArrayListUnmanaged(Sym) = .{},
capture_boundary: usize = 0,
captures: std.ArrayListUnmanaged(Capture) = .{},
comptime_idents: std.ArrayListUnmanaged(Ident) = .{},
mode: Ast.InitOptions.Mode,
list_pos: Ast.Pos = undefined,
deferring: bool = false,
errored: bool = false,
in_if_or_while: bool = false,
func_stats: FuncStats = .{},
scope_depth: u8 = 0,

const Hasher = struct {
    syms: []const Sym,

    pub fn hash(h: Hasher, vl: u32) u64 {
        return std.hash.Fnv1a_64.hash(h.syms[vl].name);
    }

    pub fn eql(h: Hasher, a: u32, b: u32) bool {
        return std.mem.eql(u8, h.syms[a].name, h.syms[b].name);
    }
};

pub const stack_limit = @import("options").stack_size - 1024 * 16;
pub const sym_bloom_fns = 3;

const Parser = @This();
const Error = error{ UnexpectedToken, StackOverflow } || std.mem.Allocator.Error;

const FuncStats = struct {
    loop_depth: u8 = 0,
    max_loop_depth: u8 = 0,
    max_variable_count: u16 = 0,
    variable_count: u16 = 0,
};

const Sym = struct {
    name: []const u8,
    id: Ident,
    declared: bool = false,
    unordered: bool = true,
    used: bool = false,
    shadows: ?u31 = null,
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
        colors: std.io.tty.Config,
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

    var item_buf = std.ArrayListUnmanaged(Id){};
    while (self.cur.kind != .Eof) {
        try item_buf.append(tmp.arena.allocator(), try self.parseUnorderedExpr());
        _ = self.tryAdvance(.@";");
    }

    const remining = self.finalizeVariablesLow(0);
    if (!self.loader.isNoop()) {
        for (self.active_syms.items[0..remining]) |s| {
            self.report(s.id.pos(), "undeclared identifier", .{});
        }
    }

    return self.store.allocSlice(Id, self.arena.allocator(), item_buf.items);
}

fn parseExpr(self: *Parser) Error!Id {
    return self.parseExprPrec(254);
}

fn parseExprPrec(self: *Parser, prec: u8) Error!Id {
    return self.parseBinExpr(try self.parseUnit(), prec, false);
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
        const prec = op.precedence(self.in_if_or_while);
        if (prec >= prevPrec) break;

        self.cur = self.lexer.next();
        if (op == .@":") {
            const lover_prec = comptime Lexer.Lexeme.@"=".precedence(false) - 1;
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

        if (op == .@".." and (self.cur.kind == .@"," or
            self.cur.kind == .@")" or self.cur.kind == .@"]"))
        {
            return try self.store.alloc(self.arena.allocator(), .Range, .{
                .start = acum,
                .end = .zeroSized(.Void),
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
        } else if (op == .@":=") {
            _ = self.declareExpr(acum, unordered);
            acum = try self.store.alloc(self.arena.allocator(), .Decl, .{
                .bindings = acum,
                .value = rhs,
            });
        } else if (op == .@"..") {
            acum = try self.store.alloc(self.arena.allocator(), .Range, .{
                .start = acum,
                .end = rhs,
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

    // stuff beyond capture boundary can not be declared here
    const search_scpace = self.active_syms.items[self.capture_boundary..];
    var iter = std.mem.reverseIterator(search_scpace);
    const sym: *Sym = while (iter.nextPtr()) |s| {
        if (s.id == ident.id) break s;
    } else if (unordered) {
        // shadow

        const repr = Lexer.peekStr(self.lexer.source, ident.pos.index);
        const slot = self.active_sym_table.getEntryAdapted(
            repr,
            InsertCtx{ .syms = self.active_syms.items },
        ).?;

        var sym = self.active_syms.items[slot.key_ptr.*];
        sym.shadows = @intCast(slot.key_ptr.*);
        sym.declared = true;
        self.active_syms.append(self.arena.allocator(), sym) catch unreachable;

        return;
    } else {
        self.report(ident.pos.index, "out of order declaration in ordered scope", .{});
        return;
    };

    if (sym.declared and !self.loader.isNoop()) {
        self.report(ident.pos.index, "redeclaration of identifier", .{});
        self.report(sym.id.pos(), "...first declaration here", .{});
    } else if (!unordered and ident.pos.index > ident.id.pos()) {
        self.report(ident.pos.index, "out of order declaration in ordered scope", .{});
    } else if (!unordered and sym.used) {
        self.report(ident.pos.index, "ordered declaration is used recursively", .{});
    }
    sym.declared = true;
    sym.unordered = unordered;

    if (!unordered) {
        self.func_stats.variable_count += 1;
        self.func_stats.max_variable_count =
            @max(self.func_stats.max_variable_count, self.func_stats.variable_count);
    }
}

fn parseUnit(self: *Parser) Error!Id {
    var base = try self.parseUnitWithoutTail();
    if (base.tag() == .Comment) {
        return base;
    }

    while (true) base = try self.store.allocDyn(self.arena.allocator(), switch (self.cur.kind) {
        .@"." => b: {
            _ = self.advance();
            break :b .{ .Field = .{
                .base = base,
                .field = .init((try self.expectAdvance(.Ident)).pos),
            } };
        },
        .@"[" => .{ .Index = .{
            .base = base,
            .subscript = b: {
                _ = self.advance();
                const start: Id = if (self.cur.kind == .@"..")
                    .zeroSized(.Void)
                else
                    try self.parseExpr();
                const is_range = self.tryAdvance(.@"..");
                const end: Id = if (self.cur.kind == .@"]")
                    .zeroSized(.Void)
                else
                    try self.parseExpr();
                _ = try self.expectAdvance(.@"]");
                break :b if (is_range)
                    try self.store.allocDyn(
                        self.arena.allocator(),
                        .{ .Range = .{ .start = start, .end = end } },
                    )
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
        .@".?" => b: {
            _ = self.advance();
            break :b .{ .Unwrap = base };
        },
        .@".*" => b: {
            _ = self.advance();
            break :b .{ .Deref = base };
        },
        else => break,
    });
    return base;
}

fn report(self: *Parser, pos: u32, msg: []const u8, args: anytype) void {
    self.errored = true;
    const file = Ast{
        .path = self.path,
        .source = self.lexer.source,
        .exprs = undefined,
        .items = undefined,
        .root_struct = undefined,
    };

    file.report(self, pos, msg, args);
}

fn codePointer(self: *const Parser, pos: usize) Ast.CodePointer {
    return .{ .source = self.lexer.source, .index = pos };
}

fn popCaptures(self: *Parser, scope: usize, preserve: bool) []const Capture {
    const slc = self.captures.items[@min(scope, self.captures.items.len)..];
    if (!preserve) self.captures.items.len = scope;
    if (slc.len > 1) {
        std.sort.pdq(Capture, slc, {}, struct {
            pub fn inner(_: void, a: Capture, b: Capture) bool {
                return a.id.pos() < b.id.pos();
            }
        }.inner);
        var i: usize = 0;
        for (slc[1..]) |s| {
            if (s.id != slc[i].id) {
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

            const comptime_args = try self.store.allocSlice(
                Ident,
                self.arena.allocator(),
                self.comptime_idents.items[comptime_arg_start..comptime_idents_end],
            );
            const captures = try self.store.allocSlice(
                Capture,
                self.arena.allocator(),
                self.popCaptures(capture_scope, prev_capture_boundary != 0),
            );
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
                        .colors = self.colors,
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
        .@"enum", .@"union", .@"struct" => b: {
            const prev_func_stats = self.func_stats;
            defer self.func_stats = prev_func_stats;

            const prev_capture_boundary = self.capture_boundary;
            self.capture_boundary = self.active_syms.items.len;
            defer self.capture_boundary = prev_capture_boundary;

            var tag: Id = .zeroSized(.Void);
            if (self.tryAdvance(.@"(")) {
                tag = try self.parseExpr();
                _ = try self.expectAdvance(.@")");
            }

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
            break :b .{ .Type = .{
                .fields = fields,
                .tag = tag,
                .alignment = alignment,
                .captures = try self.store.allocSlice(Capture, self.arena.allocator(), captures),
                .pos = .{ .index = @intCast(token.pos), .flag = self.list_pos.flag },
                .kind = token.kind,
            } };
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
            .pos = .{ .index = @intCast(token.pos), .flag = self.list_pos.flag },
        } },
        .@".(" => .{ .Tupl = .{
            .ty = .zeroSized(.Void),
            .fields = try self.parseList(null, .@",", .@")", parseExpr),
            .pos = .{ .index = @intCast(token.pos), .flag = self.list_pos.flag },
        } },
        .@".[" => .{ .Arry = .{
            .ty = .zeroSized(.Void),
            .fields = try self.parseList(null, .@",", .@"]", parseExpr),
            .pos = .{ .index = @intCast(token.pos), .flag = self.list_pos.flag },
        } },
        .@"{" => .{ .Block = .{
            .pos = .{ .index = @intCast(token.pos), .flag = .{ .indented = true } },
            .stmts = b: {
                const prev_in_if_or_while = self.in_if_or_while;
                defer self.in_if_or_while = prev_in_if_or_while;
                self.in_if_or_while = false;

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
        .@"*" => switch (self.mode) {
            .legacy => .{ .Deref = try self.parseUnit() },
            .latest => {
                self.report(token.pos, "this is legacy defer syntax," ++
                    " use `<expr>.*` instead", .{});
                return error.UnexpectedToken;
            },
        },
        .@"^" => if (self.tryAdvance(.@"fn")) .{ .FnPtr = .{
            .args = try self.parseList(.@"(", .@",", .@")", parseScopedExpr),
            .ret = b: {
                _ = try self.expectAdvance(.@":");
                break :b try self.parseExpr();
            },
            .pos = .{ .index = @intCast(token.pos), .flag = self.list_pos.flag },
        } } else .{ .UnOp = .{
            .pos = .init(token.pos),
            .op = token.kind,
            .oper = try self.parseUnit(),
        } },
        .@"&", .@"-", .@"~", .@"!", .@"?" => .{ .UnOp = .{
            .pos = .init(token.pos),
            .op = token.kind,
            .oper = try self.parseUnit(),
        } },
        .@"[" => switch (self.mode) {
            .legacy => slice: {
                const pos = Ast.Pos.init(token.pos);
                var is_legacy = false;
                const len_or_legacy_elem: Ast.Id = if (self.tryAdvance(.@"]"))
                    .zeroSized(.Void)
                else b: {
                    const expr = try self.parseExpr();
                    if (self.tryAdvance(.@";")) {
                        is_legacy = true;
                    } else _ = try self.expectAdvance(.@"]");
                    break :b expr;
                };

                if (is_legacy) {
                    const res: Ast.Expr = .{ .SliceTy = .{
                        .pos = pos,
                        .elem = len_or_legacy_elem,
                        .len = try self.parseExpr(),
                    } };
                    _ = try self.expectAdvance(.@"]");
                    break :slice res;
                } else {
                    break :slice .{ .SliceTy = .{
                        .pos = pos,
                        .elem = try self.parseUnit(),
                        .len = len_or_legacy_elem,
                    } };
                }
            },
            .latest => .{ .SliceTy = .{
                .pos = .init(token.pos),
                .len = if (self.tryAdvance(.@"]")) .zeroSized(.Void) else b: {
                    const expr = try self.parseExpr();
                    _ = try self.expectAdvance(.@"]");
                    break :b expr;
                },
                .elem = try self.parseUnit(),
            } },
        },
        .@"if", .@"$if" => .{ .If = .{
            .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind == .@"$if" } },
            .cond = b: {
                const prev_in_if_or_while = self.in_if_or_while;
                defer self.in_if_or_while = prev_in_if_or_while;
                self.in_if_or_while = true;
                break :b try self.parseExpr();
            },
            .then = b: {
                defer self.finalizeVariables(scope_frame);
                break :b try self.parseScopedExpr();
            },
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
        .@"for", .@"$for" => for_loop: {
            const pos = Ast.Pos{
                .index = @intCast(token.pos),
                .flag = .{ .@"comptime" = token.kind != .@"for" },
            };

            const label: Ast.Id = try self.parseLabel();

            defer self.finalizeVariables(scope_frame);
            break :for_loop .{ .For = .{
                .pos = pos,
                .label = label,
                .iters = b: {
                    var tmp = Arena.scrath(self.arena);
                    defer tmp.deinit();

                    var buf = std.ArrayListUnmanaged(Ast.Decl){};
                    while (true) {
                        const ps = self.cur.pos;
                        const vl = self.store.get(try self.parseExpr());
                        if (vl != .Decl) {
                            self.report(ps, "expected a declaration", .{});
                        }
                        try buf.append(tmp.arena.allocator(), vl.Decl.*);
                        if (!self.tryAdvance(.@",")) break;
                    }
                    break :b try self.store.allocSlice(Ast.Decl, self.arena.allocator(), buf.items);
                },
                .body = body: {
                    self.func_stats.loop_depth += 1;
                    self.func_stats.max_loop_depth =
                        @max(self.func_stats.max_loop_depth, self.func_stats.loop_depth);
                    defer self.func_stats.loop_depth -= 1;
                    break :body try self.parseExpr();
                },
            } };
        },
        .@"while", .@"$while" => while_loop: {
            const pos = Ast.Pos{
                .index = @intCast(token.pos),
                .flag = .{ .@"comptime" = token.kind != .@"while" },
            };

            const label: Ast.Id = try self.parseLabel();

            const body = try self.store.alloc(self.arena.allocator(), .If, .{
                .pos = pos,
                .cond = b: {
                    const prev_in_if_or_while = self.in_if_or_while;
                    defer self.in_if_or_while = prev_in_if_or_while;
                    self.in_if_or_while = true;
                    break :b try self.parseExpr();
                },
                .then = b: {
                    self.func_stats.loop_depth += 1;
                    self.func_stats.max_loop_depth =
                        @max(self.func_stats.max_loop_depth, self.func_stats.loop_depth);
                    defer self.func_stats.loop_depth -= 1;
                    defer self.finalizeVariables(scope_frame);
                    break :b try self.parseExpr();
                },
                .else_ = try self.store.alloc(self.arena.allocator(), .Break, .{
                    .pos = pos,
                    .label = label,
                }),
            });

            break :while_loop .{ .Loop = .{ .pos = pos, .label = label, .body = body } };
        },
        .loop, .@"$loop" => .{ .Loop = .{
            .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind != .loop } },
            .label = try self.parseLabel(),
            .body = b: {
                self.func_stats.loop_depth += 1;
                self.func_stats.max_loop_depth =
                    @max(self.func_stats.max_loop_depth, self.func_stats.loop_depth);
                defer self.func_stats.loop_depth -= 1;
                defer self.finalizeVariables(scope_frame);
                break :b try self.parseScopedExpr();
            },
        } },
        .@"break" => b: {
            if (self.deferring) self.report(token.pos, "can not break from a defer", .{});
            break :b .{ .Break = .{
                .pos = .init(token.pos),
                .label = if (self.tryAdvance(.@":"))
                    try self.resolveIdent(try self.expectAdvance(.Ident))
                else
                    .zeroSized(.Void),
            } };
        },
        .@"continue" => b: {
            if (self.deferring) self.report(token.pos, "can not continue from a defer", .{});
            break :b .{ .Continue = .{
                .pos = .init(token.pos),
                .label = if (self.tryAdvance(.@":"))
                    try self.resolveIdent(try self.expectAdvance(.Ident))
                else
                    .zeroSized(.Void),
            } };
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
        .BinInteger, .OctInteger, .DecInteger, .HexInteger => .{ .Integer = .{
            .pos = .init(token.pos),
            .base = @intCast(@intFromEnum(token.kind) & ~@as(u8, 128)),
        } },
        .Float => .{ .Float = .init(token.pos) },
        .true => .{ .Bool = .{ .value = true, .pos = .init(token.pos) } },
        .@"\"" => .{ .String = .{ .pos = .init(token.pos), .end = token.end } },
        .@"'" => .{ .Quotes = .{ .pos = .init(token.pos), .end = token.end } },
        .false => .{ .Bool = .{ .value = false, .pos = .init(token.pos) } },
        else => |k| {
            self.report(token.pos, "no idea how to handle this: {}", .{@tagName(k)});
            return error.UnexpectedToken;
        },
    });
}

fn parseLabel(self: *Parser) Error!Ast.Id {
    return if (self.tryAdvance(.@":")) b: {
        const label = try self.resolveIdent(try self.expectAdvance(.Ident));
        self.declareExpr(label, false);
        break :b label;
    } else .zeroSized(.Void);
}

fn finalizeVariablesLow(self: *Parser, start: usize) usize {
    var new_len = start;
    for (self.active_syms.items[start..], start..) |s, j| {
        if (!s.declared) {
            if (new_len != j) {
                self.active_sym_table.getEntryContext(@intCast(j), .{
                    .syms = self.active_syms.items,
                }).?.key_ptr.* = @intCast(new_len);
                self.active_syms.items[new_len] = s;
            }
            new_len += 1;
        } else {
            while (for (self.captures.items, 0..) |c, i| {
                if (c.id == s.id) break i;
            } else null) |idx| {
                _ = self.captures.swapRemove(idx);
            }
            if (s.shadows) |shadows| {
                self.active_sym_table.getEntryContext(@intCast(j), .{
                    .syms = self.active_syms.items,
                }).?.key_ptr.* = shadows;
            } else {
                std.debug.assert(self.active_sym_table.removeContext(@intCast(j), .{
                    .syms = self.active_syms.items,
                }));
            }
        }
    }
    if (new_len != 0) self.func_stats.variable_count -|=
        @intCast(self.active_syms.items.len - new_len);
    return new_len;
}

fn finalizeVariables(self: *Parser, start: usize) void {
    self.active_syms.items.len = self.finalizeVariablesLow(start);
}

const InsertCtx = struct {
    syms: []const Sym,

    pub fn hash(_: @This(), vl: []const u8) u64 {
        return std.hash.Fnv1a_64.hash(vl);
    }

    pub fn eql(h: @This(), a: []const u8, b: u32) bool {
        return std.mem.eql(u8, a, h.syms[b].name);
    }
};

fn resolveIdent(self: *Parser, token: Lexer.Token) !Id {
    var repr = token.view(self.lexer.source);
    if (token.kind == .@"$") repr = repr[1..];

    const slot = self.active_sym_table.getOrPutContextAdapted(
        self.arena.allocator(),
        repr,
        InsertCtx{ .syms = self.active_syms.items },
        .{ .syms = self.active_syms.items },
    ) catch unreachable;
    if (slot.found_existing) {
        const i = slot.key_ptr.*;
        const s = &self.active_syms.items[i];
        s.used = true;

        if (i < self.capture_boundary and !s.unordered) {
            try self.captures.append(self.arena.allocator(), .{ .id = s.id, .pos = .init(token.pos) });
        }

        return try self.store.alloc(self.arena.allocator(), .Ident, .{
            .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind == .@"$" } },
            .id = s.id,
        });
    }

    const id = Ident.init(token);
    const alloc = try self.store.alloc(self.arena.allocator(), .Ident, .{
        .pos = .{ .index = @intCast(token.pos), .flag = .{ .@"comptime" = token.kind == .@"$" } },
        .id = id,
    });
    if (token.kind == .@"$") try self.comptime_idents.append(self.arena.allocator(), id);
    slot.key_ptr.* = @intCast(self.active_syms.items.len);
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
