const std = @import("std");
const hb = @import("hb");
const utils = hb.utils;
const Lexer = hb.frontend.Lexer;
const Types = hb.frontend.Types;

entries: std.MultiArrayList(Entry),
sub_scopes: std.MultiArrayList(Child),
imports: std.MultiArrayList(Import),

const DeclIndex = @This();

pub const Child = struct {
    offset: u32,
    index: DeclIndex,
};

pub const Entry = struct {
    prefix: u8,
    offset: Decl,
};

pub const Decl = struct {
    offset: u32,
    root: u32,
};

pub const Import = struct {
    offset: u32,
    file: File.Id,
};

pub const Builder = struct {
    lexer: Lexer,
    depth: u32 = 0,
    loader: *Loader,
};

pub const File = struct {
    path: []const u8,
    source: [:0]const u8,
    decls: DeclIndex,
    lines: hb.LineIndex,
    root_sope: Types.Id = undefined,

    pub const Id = enum(u32) {
        root,
        _,

        pub fn index(self: Id) u32 {
            return @intFromEnum(self);
        }

        pub fn get(self: Id, pool: *Types) *File {
            return &pool.files[self.index()];
        }
    };

    pub fn init(source: [:0]const u8, loader: *Loader, scratch: *utils.Arena) !File {
        return .{
            .path = loader.path,
            .source = source,
            .decls = try .build(source, loader, scratch),
            .lines = .init(source, scratch),
        };
    }

    pub fn isComptime(self: File, offset: u32) bool {
        return offset != 0 and self.source[offset - 1] == '$';
    }

    pub fn tokenStr(self: File, offset: u32) []const u8 {
        return Lexer.peekStr(self.source, offset);
    }
};

pub const Loader = struct {
    path: []const u8 = "main.hb",
    from: File.Id = .root,
    colors: std.io.tty.Config = .no_color,
    diagnostics: ?*std.Io.Writer = null,

    _load: *const fn (*Loader, LoadOptions) ?File.Id,
    _load_embed: *const fn (*Loader, LoadOptions) ?[:0]const u8,

    var noop_state = struct {
        loader: Loader = .init(@This()),

        pub fn load(_: *@This(), _: LoadOptions) ?File.Id {
            return null;
        }

        pub fn loadEmbed(_: *@This(), _: LoadOptions) ?[:0]const u8 {
            return null;
        }
    }{};

    pub const noop = &noop_state.loader;

    pub const LoadOptions = struct {
        pos: u32,

        path: []const u8,
    };

    pub fn init(comptime T: type) Loader {
        return .{
            ._load = struct {
                fn load(self: *Loader, opts: LoadOptions) ?File.Id {
                    const slf: *T = @fieldParentPtr("loader", self);
                    return slf.load(opts);
                }
            }.load,
            ._load_embed = struct {
                fn load(self: *Loader, opts: LoadOptions) ?[:0]const u8 {
                    const slf: *T = @fieldParentPtr("loader", self);
                    return slf.loadEmbed(opts);
                }
            }.load,
        };
    }

    pub fn load(self: *Loader, opts: LoadOptions) ?File.Id {
        return self._load(self, opts);
    }
};

pub fn build(source: [:0]const u8, loader: *Loader, scratch: *utils.Arena) !DeclIndex {
    var bl = Builder{ .lexer = .init(source, 0), .loader = loader };
    const res = try buildLow(&bl, scratch);
    std.debug.assert(bl.depth == 0);
    return res;
}

// NOTE: this assumes that `.Ident := <expr>` expr never contains the
// assignment without enclosing parentheses, there is a very low likelyhood
// of error that relates to nesting the scope in the scope suffixes (.eg
// struct align(enum{}) {}) which is just prohibited for simplicity reasons
pub fn buildLow(
    bl: *Builder,
    scratch: *utils.Arena,
) error{StupidNesting}!DeclIndex {
    var tmp = utils.Arena.scrath(scratch);
    defer tmp.deinit();

    const init_depth = bl.depth;

    var decls = std.ArrayList(Decl).empty;
    var sub_scopes = std.ArrayList(Child).empty;
    var imports = std.ArrayList(Import).empty;
    var subscope: struct { start: u32, depth: u32 } = .{
        .start = 0,
        .depth = std.math.maxInt(u32),
    };

    // NOTE: this is small because its very unlikely for someone to nest
    // scopes so much in the scope arguments
    var buf: [16]@TypeOf(subscope) = undefined;
    var scope_nesting_stack = std.ArrayList(@TypeOf(subscope))
        .initBuffer(&buf);

    while (true) {
        const tok = bl.lexer.next();
        switch (tok.kind) {
            .Eof => {
                bl.depth = init_depth;
                break;
            },
            .@".(", .@".[", .@"(", .@"[" => bl.depth += 1,
            .@"{" => {
                bl.depth += 1;

                // NOTE: every expression between keyword and '{' is in
                // parentheses
                if (subscope.depth == bl.depth - 1) {
                    const prev_depth = bl.depth;
                    const sub = try buildLow(bl, scratch);
                    sub_scopes.append(
                        tmp.arena.allocator(),
                        .{ .index = sub, .offset = subscope.start },
                    ) catch unreachable;

                    std.debug.assert(subscope.start < tok.pos);
                    std.debug.assert(bl.depth == prev_depth);

                    subscope = scope_nesting_stack.pop().?;
                    bl.depth -= 1;
                }
            },
            .@"}", .@")", .@"]" => {
                if (bl.depth == init_depth) break;
                bl.depth -= 1;

                if (subscope.depth != std.math.maxInt(u32) and
                    subscope.depth > bl.depth)
                {
                    subscope = scope_nesting_stack.pop().?;
                }
            },
            .@"struct", .@"enum", .@"union" => {
                scope_nesting_stack
                    .appendAssumeCapacity(subscope);
                subscope = .{ .depth = bl.depth, .start = tok.pos };
            },
            .@"@use" => {
                if (bl.lexer.next().kind != .@"(") continue;
                const path = bl.lexer.next();
                if (bl.lexer.next().kind != .@")") continue;
                if (path.kind != .@"\"") continue;
                var path_str = path.view(bl.lexer.source);
                path_str = path_str[1 .. path_str.len - 1];

                const file = bl.loader.load(.{
                    .pos = tok.pos,
                    .path = path_str,
                }) orelse continue;

                imports.append(tmp.arena.allocator(), .{
                    .offset = tok.pos,
                    .file = file,
                }) catch unreachable;
            },
            .@".{" => {
                if (bl.depth != init_depth) {
                    bl.depth += 1;
                    continue;
                }

                bl.lexer.cursor = tok.pos;

                const checkpoint = decls.items.len;
                addPattern(bl, tok.pos, &decls, scratch);

                switch (bl.lexer.peekNext().kind) {
                    .@":", .@":=" => {},
                    else => {
                        // NOTE: this is a struct decl, bail
                        decls.items.len = checkpoint;
                    },
                }
            },
            .@"$", .Ident => {
                if (bl.depth != init_depth) continue;

                const off = tok.pos + @intFromBool(tok.kind == .@"$");

                const next = bl.lexer.peekNext();
                switch (next.kind) {
                    .@":", .@":=" => {
                        decls.append(
                            tmp.arena.allocator(),
                            .{ .offset = off, .root = off },
                        ) catch unreachable;
                    },
                    .@".{" => {
                        bl.lexer.cursor = tok.pos;
                        const checkpoint = decls.items.len;
                        addPattern(bl, off, &decls, tmp.arena);

                        switch (bl.lexer.peekNext().kind) {
                            .@":", .@":=" => {},
                            else => {
                                // NOTE: this is a struct decl, bail
                                decls.items.len = checkpoint;
                            },
                        }
                    },
                    else => continue,
                }
            },
            else => {},
        }
    }

    errdefer unreachable;

    var entries = std.MultiArrayList(Entry).empty;
    {
        try entries.setCapacity(scratch.allocator(), decls.items.len);
        entries.len = decls.items.len;

        const slice = entries.slice();

        for (
            decls.items,
            slice.items(.prefix),
            slice.items(.offset),
        ) |i, *prefix, *offset| {
            prefix.* = bl.lexer.source[i.offset];
            offset.* = i;
        }
    }

    var sub_scopes_arr = std.MultiArrayList(Child).empty;
    {
        try sub_scopes_arr.setCapacity(
            scratch.allocator(),
            sub_scopes.items.len,
        );
        sub_scopes_arr.len = sub_scopes.items.len;

        const slice = sub_scopes_arr.slice();

        for (
            sub_scopes.items,
            slice.items(.offset),
            slice.items(.index),
        ) |c, *off, *idx| {
            off.* = c.offset;
            idx.* = c.index;
        }
    }

    var import_arr = std.MultiArrayList(Import).empty;
    {
        try import_arr.setCapacity(
            scratch.allocator(),
            imports.items.len,
        );
        import_arr.len = imports.items.len;

        const slice = import_arr.slice();

        for (
            imports.items,
            slice.items(.offset),
            slice.items(.file),
        ) |c, *off, *idx| {
            off.* = c.offset;
            idx.* = c.file;
        }
    }

    return .{
        .entries = entries,
        .sub_scopes = sub_scopes_arr,
        .imports = import_arr,
    };
}

pub fn addPattern(
    bl: *Builder,
    root: u32,
    entries: *std.ArrayList(Decl),
    scrath: *utils.Arena,
) void {
    errdefer unreachable;

    const tok = bl.lexer.next();

    switch (tok.kind) {
        .Ident => {
            try entries.append(scrath.allocator(), .{
                .offset = tok.pos,
                .root = root,
            });

            if (bl.lexer.peekNext().kind == .@".{") {
                addPattern(bl, root, entries, scrath);
            }
        },
        .@".{" => {
            bl.depth += 1;

            var iter = bl.lexer.list(.@",", .@"}");
            while (iter.next()) {
                const ident = bl.lexer.next();
                if (ident.kind != .Ident) {
                    break;
                }

                const suffix = bl.lexer.next();
                switch (suffix.kind) {
                    .@":" => {},
                    .@".{", .@",", .@"}" => {
                        bl.lexer.cursor = ident.pos;
                    },
                    else => {
                        break;
                    },
                }

                addPattern(bl, root, entries, scrath);
            }

            if (bl.lexer.source[bl.lexer.cursor - 1] == '}') {
                // NOTE: this means we were uninterrupted
                bl.depth -= 1;
            }
        },
        else => {
            // NOTE: this should recover any closing/opening delimeter to
            // keep the depth balance, this does not happen often, not
            // including syntax errors
            bl.lexer.cursor = tok.pos;
            return;
        },
    }
}

pub fn lookup(
    self: DeclIndex,
    source: [:0]const u8,
    name: []const u8,
) ?Decl {
    // TODO: handrolling this might help since we expect multiple matches
    var cursor: usize = 0;
    return while (std.mem.indexOfScalarPos(
        u8,
        self.entries.items(.prefix),
        cursor,
        name[0],
    )) |index| : (cursor = index + 1) {
        const decl = self.entries.items(.offset)[index];
        if (Lexer.compareIdent(source, decl.offset, name)) {
            return decl;
        }
    } else null;
}

pub fn lookupScope(self: *DeclIndex, source_offset: u32) ?*DeclIndex {
    // TODO: add binary search since we are always sorted
    const offs = self.sub_scopes.items(.offset);
    const idx = std.mem.indexOfScalar(u32, offs, source_offset) orelse
        return null;
    return &self.sub_scopes.items(.index)[idx];
}

pub fn lookupImport(self: *DeclIndex, source_offset: u32) ?File.Id {
    // TODO: add binary search since we are always sorted
    const offs = self.imports.items(.offset);
    const idx = std.mem.indexOfScalar(u32, offs, source_offset) orelse
        return null;
    return self.imports.items(.file)[idx];
}

pub fn log(self: DeclIndex, depth: usize, out: *std.Io.Writer) !void {
    for (
        self.entries.items(.offset),
        self.entries.items(.prefix),
    ) |v, p| {
        for (0..depth) |_| try out.print(" ", .{});
        try out.print("{}:{} {s}\n", .{ v.root, v.offset, &[_]u8{p} });
    }

    for (
        self.sub_scopes.items(.offset),
        self.sub_scopes.items(.index),
    ) |o, *v| {
        for (0..depth) |_| try out.print(" ", .{});
        try out.print("{} {{\n", .{o});
        try v.log(depth + 1, out);
        for (0..depth) |_| try out.print(" ", .{});
        try out.print("}}\n", .{});
    }
}

test {
    utils.Arena.initScratch(1024 * 4);

    const source =
        \\foo := struct {}
        \\bar := struct {
        \\   voo := struct(struct {}) {}
        \\   koo := struct {}
        \\   $loo := fn(): void {
        \\       a := 0
        \\       a := 0
        \\   }
        \\}
        \\foo.{boo, loo: .{coo}, koo.{kla}, soo: noo.{pa}} := mam
        \\
    ;

    const result =
        \\0:0 f
        \\17:17 b
        \\143:143 f
        \\143:148 b
        \\143:160 c
        \\143:166 k
        \\143:171 k
        \\143:182 n
        \\143:187 p
        \\7 {
        \\}
        \\24 {
        \\ 36:36 v
        \\ 67:67 k
        \\ 88:88 l
        \\ 50 {
        \\ }
        \\ 43 {
        \\ }
        \\ 74 {
        \\ }
        \\}
        \\
    ;

    var tmp = utils.Arena.init(1024 * 4);

    const idx = try DeclIndex.build(source, .noop, &tmp);

    var buf: [1024]u8 = undefined;
    var out = std.Io.Writer.fixed(&buf);

    try idx.log(0, &out);

    try std.testing.expectEqualSlices(u8, result, out.buffered());
}
