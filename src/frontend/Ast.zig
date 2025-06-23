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
pub const Captures = utils.EnumSlice(Capture);

pub const Capture = struct { id: Ident, pos: Pos };

pub const Ident = enum(u32) {
    invalid = std.math.maxInt(u32),
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
        captures: Captures,
        args: utils.EnumSlice(Arg),
        ret: Id,
        body: Id,
        peak_vars: u16,
        peak_loops: u16,
    },
    Struct: Type,
    Union: Type,
    Enum: Type,
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
        label: Id,
        body: Id,
    },
    Break: struct {
        pos: Pos,
        label: Id,
    },
    Continue: struct {
        pos: Pos,
        label: Id,
    },
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
        captures: Captures,
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
    mode: Mode = .latest,
    colors: std.io.tty.Config = .no_color,

    pub const Mode = enum { legacy, latest };
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
        .mode = opts.mode,
        .cur = lexer.next(),
        .lexer = lexer,
        .diagnostics = opts.diagnostics,
        .colors = opts.colors,
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

pub const Index = struct {
    linear: std.MultiArrayList(Entry),
    map: HashMap,

    pub const empty = Index{ .linear = .empty, .map = .empty };

    const HashMap = std.HashMapUnmanaged(u32, void, Hasher, 70);

    const Hasher = struct {
        syms: []const Entry.Meta,

        pub fn hash(h: Hasher, vl: u32) u64 {
            return std.hash.Fnv1a_64.hash(h.syms[vl].name);
        }

        pub fn eql(h: Hasher, a: u32, b: u32) bool {
            return std.mem.eql(u8, h.syms[a].name, h.syms[b].name);
        }
    };

    pub const Entry = struct {
        id: Ident,
        meta: Meta,

        pub const Meta = struct {
            name: []const u8,
            path: []Pos,
            decl: Id,
        };
    };

    pub fn collectBindings(
        ast: *const Ast,
        bindings: Ast.Id,
        value: Ast.Id,
        pos_stack: *std.ArrayListUnmanaged(Pos),
        into: *std.ArrayListUnmanaged(Entry),
        arena: std.mem.Allocator,
        scratch: *utils.Arena,
    ) void {
        errdefer unreachable;
        switch (bindings.tag()) {
            .Ident => {
                const name = ast.tokenSrc(ast.exprs.get(bindings).Ident.id.pos());
                try into.append(scratch.allocator(), .{
                    .id = ast.exprs.get(bindings).Ident.id,
                    .meta = .{
                        .name = name,
                        .path = try arena.dupe(Pos, pos_stack.items),
                        .decl = value,
                    },
                });
            },
            .Ctor => {
                const c = ast.exprs.get(bindings).Ctor;
                collectBindings(ast, c.ty, value, pos_stack, into, arena, scratch);

                for (ast.exprs.view(c.fields)) |f| {
                    pos_stack.appendAssumeCapacity(f.pos);
                    collectBindings(ast, f.value, value, pos_stack, into, arena, scratch);
                    _ = pos_stack.pop().?;
                }
            },
            else => {},
        }
    }

    pub fn build(ast: *const Ast, slice: Slice, arena: std.mem.Allocator) Index {
        errdefer unreachable;

        var tmp = utils.Arena.scrathFromAlloc(arena);
        defer tmp.deinit();

        var fseq = std.ArrayListUnmanaged(Pos).initBuffer(tmp.arena.alloc(Pos, 128));
        var entries = std.ArrayListUnmanaged(Entry).initBuffer(tmp.arena.alloc(Entry, slice.len() * 5 / 4 + 3));
        for (ast.exprs.view(slice)) |d| {
            const decl = ast.exprs.getTyped(.Decl, d) orelse continue;
            collectBindings(ast, decl.bindings, d, &fseq, &entries, arena, tmp.arena);
        }

        std.sort.pdq(Entry, entries.items, {}, struct {
            fn lt(_: void, lhs: Entry, rhs: Entry) bool {
                return @intFromEnum(lhs.id) < @intFromEnum(rhs.id);
            }
        }.lt);

        var linear = std.MultiArrayList(Entry){};
        try linear.setCapacity(arena, entries.items.len);
        var map = HashMap{};
        try map.ensureTotalCapacityContext(arena, @intCast(entries.items.len), undefined);
        for (entries.items, 0..) |it, i| {
            linear.appendAssumeCapacity(it);

            const slot = map.getOrPutAssumeCapacityAdapted(it.meta.name, struct {
                syms: []const Entry,

                pub fn hash(_: @This(), vl: []const u8) u64 {
                    return std.hash.Fnv1a_64.hash(vl);
                }

                pub fn eql(h: @This(), a: []const u8, b: u32) bool {
                    return std.mem.eql(u8, a, h.syms[b].meta.name);
                }
            }{
                .syms = entries.items,
            });

            slot.key_ptr.* = @intCast(i);
        }

        return .{ .linear = linear, .map = map };
    }

    pub fn search(self: Index, id: anytype) ?struct { Id, []Pos, Ident } {
        switch (@TypeOf(id)) {
            Ident => {
                if (self.linear.len > 4096) {
                    if (std.sort.binarySearch(u32, @ptrCast(self.linear.items(.id)), @intFromEnum(id), struct {
                        fn ord(a: u32, b: u32) std.math.Order {
                            return std.math.order(a, b);
                        }
                    }.ord)) |pos|
                        return .{
                            self.linear.items(.meta)[pos].decl,
                            self.linear.items(.meta)[pos].path,
                            id,
                        };
                } else {
                    if (std.mem.indexOfScalar(Ident, self.linear.items(.id), id)) |pos|
                        return .{
                            self.linear.items(.meta)[pos].decl,
                            self.linear.items(.meta)[pos].path,
                            id,
                        };
                }
            },
            []const u8 => {
                if (self.map.getKeyAdapted(id, struct {
                    syms: []const Entry.Meta,

                    pub fn hash(_: @This(), vl: []const u8) u64 {
                        return std.hash.Fnv1a_64.hash(vl);
                    }

                    pub fn eql(h: @This(), a: []const u8, b: u32) bool {
                        return std.mem.eql(u8, a, h.syms[b].name);
                    }
                }{
                    .syms = self.linear.items(.meta),
                })) |pos| {
                    return .{
                        self.linear.items(.meta)[pos].decl,
                        self.linear.items(.meta)[pos].path,
                        self.linear.items(.id)[pos],
                    };
                }
            },
            else => comptime unreachable,
        }

        return null;
    }
};

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

pub fn report(self: *const Ast, types: anytype, pos: u32, msg: []const u8, args: anytype) void {
    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const fields = std.meta.fields(@TypeOf(args));
    var argss: [fields.len + 1][]const u8 = undefined;
    inline for (0..fields.len) |i| {
        if (fields[i].type == Types.Id) {
            argss[i] = try std.fmt.allocPrint(tmp.arena.allocator(), "{}", .{args[i].fmt(types)});
        } else if (@typeInfo(fields[i].type) == .pointer) {
            argss[i] = try std.fmt.allocPrint(tmp.arena.allocator(), "{s}", .{args[i]});
        } else {
            argss[i] = try std.fmt.allocPrint(tmp.arena.allocator(), "{}", .{args[i]});
        }
    }
    argss[fields.len] = "";

    Ast.reportLow(self.path, self.source, pos, msg, &argss, types.colors, types.diagnostics);
}

pub fn reportLow(
    path: []const u8,
    file: []const u8,
    pos: u32,
    fmt_str: []const u8,
    args: []const []const u8,
    colors: std.io.tty.Config,
    out: std.io.AnyWriter,
) void {
    errdefer unreachable;
    const line, const col = Ast.lineCol(file, pos);

    try colors.setColor(out, .bright_white);
    try colors.setColor(out, .bold);
    try out.print("{s}:{}:{}: ", .{ path, line, col });
    try colors.setColor(out, .reset);

    var iter = std.mem.splitSequence(u8, fmt_str, "{}");
    var idx: usize = 0;
    while (iter.next()) |chunk| {
        try out.writeAll(chunk);
        try out.writeAll(args[idx]);
        idx += 1;
    }

    try out.print("\n{}\n", .{CodePointer{
        .source = file,
        .index = pos,
        .colors = colors,
    }});
}

pub const CodePointer = struct {
    source: []const u8,
    index: usize,
    colors: std.io.tty.Config,

    pub fn format(slf: *const @This(), comptime _: anytype, _: anytype, writer: anytype) !void {
        try pointToCode(slf.source, slf.index, slf.colors, writer);
    }
};

pub fn codePointer(self: *const Ast, index: usize) CodePointer {
    return .{ .source = self.source, .index = index, .colors = .no_color };
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

pub fn highlightCode(
    source: []const u8,
    colors: std.io.tty.Config,
    writer: std.io.AnyWriter,
) !void {
    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var lexer = Lexer.init(try tmp.arena.allocator().dupeZ(u8, source), 0);
    var last: usize = 0;
    var token = lexer.next();
    while (token.kind != .Eof) : (token = lexer.next()) {
        if (token.kind.isKeyword()) {
            try colors.setColor(writer, .bright_white);
            try colors.setColor(writer, .bold);
        }

        try writer.writeAll(source[last..token.end]);
        last = token.end;

        if (token.kind.isKeyword()) {
            try colors.setColor(writer, .reset);
        }
    }
}

pub fn pointToCode(source: []const u8, index_m: usize, colors: std.io.tty.Config, writer: std.io.AnyWriter) !void {
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

    try colors.setColor(writer, .white);
    try highlightCode(the_line[code_start..][0 .. the_line.len - code_start], colors, writer);
    try writer.writeAll("\n");

    const col = index - line_start + extra_bytes;
    for (0..col) |_| {
        try writer.writeAll(" ");
    }
    try colors.setColor(writer, .green);
    try writer.writeAll("^");
    try colors.setColor(writer, .reset);
}
