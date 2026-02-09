const std = @import("std");

var arena: std.mem.Allocator = undefined;

pub fn main() !void {
    var arena_state = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    arena = arena_state.allocator();

    const args = try std.process.argsAlloc(arena);
    const in_file, const out_file = args[1..3].*;

    const in = try std.fs.cwd().readFileAllocOptions(arena, in_file, 1024 * 1024, null, .of(u8), 0);

    const ast = try Ast.init(in_file, in);

    _ = try std.fs.cwd().makePath(std.fs.path.dirname(out_file) orelse ".");
    const out = try std.fs.cwd().createFile(out_file, .{});
    defer out.close();

    var buffer: [1024 * 4]u8 = undefined;
    var writer = out.writer(&buffer);

    try writer.interface.writeAll(
        \\const hb = @import("hb");
        \\const std = @import("std");
        \\const Graph = hb.backend.graph.Func;
        \\
        \\
        \\pub fn idealize(
        \\    self: anytype,
        \\    func: *Graph(@TypeOf(self.*)),
        \\    node: *Graph(@TypeOf(self.*)).Node,
        \\    worklist: *Graph(@TypeOf(self.*)).WorkList
        \\) ?*Graph(@TypeOf(self.*)).Node {
        \\    const Backend = @TypeOf(self.*);
        \\    const Func = Graph(@TypeOf(self.*));
        \\    const Node = Func.Node;
        \\    _ = .{Backend, Func, Node};
        \\    if (false) idealize(self, func, node, worklist);
        \\
    );

    for (ast.rules) |rule| {
        try writer.interface.writeAll("    rule: {\n");
        try writer.interface.writeAll("        if (false) break :rule;\n");
        try formatPattern("node", "", rule.pattern, &writer.interface);
        maybe_id = 0;

        if (rule.postprocess) |postprocess| {
            try writer.interface.writeAll("        const res = ");
            try formatReplacement(rule.replacement, &writer.interface);
            try writer.interface.writeAll(";\n");
            try writer.interface.writeAll(postprocess);
            try writer.interface.writeAll("return res;\n");
        } else {
            try writer.interface.writeAll("        return ");
            try formatReplacement(rule.replacement, &writer.interface);
            try writer.interface.writeAll(";\n");
        }

        try writer.interface.writeAll("    }\n");
    }

    try writer.interface.writeAll("    return null;\n");
    try writer.interface.writeAll("}\n");

    try writer.interface.flush();
}

var maybe_id: usize = 0;

pub fn formatPattern(root_node: []const u8, tag: []const u8, pattern: *Ast.Expr, writer: *std.Io.Writer) anyerror!void {
    const p = "        ";
    switch (pattern.*) {
        .Atom => |pat| {
            try writer.writeAll("\n");
            const name = try std.fmt.allocPrint(arena, "mabye_{s}_{}", .{ pat.name, maybe_id });
            maybe_id += 1;
            try writer.print(p ++ "const {s} = {s};\n", .{ name, root_node });
            if (!std.mem.eql(u8, pat.name, "_")) {
                try writer.print(p ++ "if ({s}.kind != .{s}) break :rule;\n", .{ name, pat.name });
            }
            if (pat.binding) |binding| {
                try writer.print(p ++ "const {s} = {s};\n", .{ binding, name });
            }

            var i: usize = 0;
            for (pat.args) |arg| {
                if (arg.* == .Field) {
                    try formatPattern(name, pat.name, arg, writer);
                } else {
                    const postfix = if (arg.* == .Binding and arg.Binding.optional) "" else " orelse break :rule";
                    const arg_name = try std.fmt.allocPrint(arena, "{s}.inputs()[{}]{s}", .{ name, i, postfix });
                    try formatPattern(arg_name, pat.name, arg, writer);
                    i += 1;
                }
                continue;
            }
        },
        .Binding => |b| {
            if (!std.mem.eql(u8, b.name, "_")) {
                try writer.print(p ++ "const {s} = {s};\n", .{ b.name, root_node });
            }
            if (b.pattern) |pa| try formatPattern(b.name, tag, pa, writer);
            if (b.predicate) |pred| {
                try writer.print(p ++ "if (!({s})) break :rule;\n", .{pred.ZixExpr.source});
            }
            if (b.extra) |ex| {
                try writer.writeAll(p);
                var first = true;
                const maybe_base = maybe_id;
                for (ex.bindings) |_| {
                    if (!first) try writer.writeAll(", ");
                    first = false;
                    try writer.print(p ++ "const tmp{}", .{maybe_id});
                    maybe_id += 1;
                }
                try writer.print(" = {s};", .{ex.zig_expr.ZixExpr.source});

                for (ex.bindings, maybe_base..) |binding, i| {
                    try formatPattern(try std.fmt.allocPrint(arena, "tmp{}", .{i}), tag, binding, writer);
                }
            }
        },
        .Field => |f| {
            const is_builtin = for (builtin_fields) |bf| {
                if (std.mem.eql(u8, f.name, bf)) break true;
            } else false;

            const access = try if (is_builtin)
                std.fmt.allocPrint(arena, "{s}.{s}", .{ root_node, f.name })
            else
                std.fmt.allocPrint(arena, "{s}.extra(.{s}).{s}", .{ root_node, tag, f.name });

            const name = if (f.expr == null)
                f.name
            else
                try std.fmt.allocPrint(arena, "{s}_{}", .{ f.name, maybe_id });
            maybe_id += 1;

            try writer.print(p ++ "const {s} = {s};\n", .{ name, access });
            if (f.expr) |expr| {
                try formatPattern(name, tag, expr, writer);
            }
        },
        .Or => {
            try writer.writeAll(p ++ "if (");

            var cursor = pattern;
            while (cursor.* == .Or) {
                try writer.print("{s} != {s} and ", .{ root_node, cursor.Or.left.ZixExpr.source });
                cursor = cursor.Or.right;
            }

            try writer.print("{s} != {s}) break :rule;\n", .{
                root_node,
                cursor.ZixExpr.source,
            });
        },
        .ZixExpr => |i| {
            try writer.print(p ++ "if ({s} != {s}) break :rule;\n", .{ root_node, i.source });
        },
        .Range => |r| {
            try writer.print(
                p ++ "if ({s} > {s} or {s} > {s}) break :rule;\n",
                .{ r.start.ZixExpr.source, root_node, root_node, r.end.ZixExpr.source },
            );
        },
        .Ref => |r| {
            try writer.print(p ++ "if ({s} != {s}) break :rule;\n", .{ root_node, r.name });
        },
    }
}

var indent: usize = 2;

pub fn doIndent(writer: *std.io.Writer) anyerror!void {
    for (0..indent) |_| {
        try writer.writeAll("    ");
    }
}

const builtin_fields = [_][]const u8{ "sloc", "data_type" };

pub fn formatReplacement(replacement: *Ast.Expr, writer: *std.Io.Writer) anyerror!void {
    switch (replacement.*) {
        .Atom => |a| {
            try writer.print(
                "func.addNode(.{s}, ",
                .{a.name},
            );
            inline for (builtin_fields) |name| {
                for (a.args) |arg| {
                    if (arg.* != .Field) continue;
                    if (!std.mem.eql(u8, arg.Field.name, name)) continue;
                    if (arg.Field.expr) |expr| {
                        try formatReplacement(expr, writer);
                    } else {
                        try writer.writeAll(name);
                    }
                    break;
                } else {
                    try writer.writeAll("node." ++ name);
                }
                try writer.writeAll(",");
            }
            try writer.writeAll("&.{\n");
            indent += 1;
            var i: usize = 0;
            for (a.args) |arg| {
                if (arg.* == .Field) continue;
                try doIndent(writer);
                try formatReplacement(arg, writer);
                try writer.writeAll(",\n");
                i += 1;
            }
            indent -= 1;
            try doIndent(writer);
            try writer.writeAll("}, .{\n");
            i = 0;
            indent += 1;
            o: for (a.args) |arg| {
                if (arg.* != .Field) continue;
                for (builtin_fields) |name| {
                    if (std.mem.eql(u8, arg.Field.name, name)) continue :o;
                }
                try doIndent(writer);
                try formatReplacement(arg, writer);
                try writer.writeAll(",\n");
                i += 1;
            }
            indent -= 1;
            try doIndent(writer);
            try writer.writeAll("})");
        },
        .Field => |f| {
            try writer.print(".{s} = ", .{f.name});
            if (f.expr) |expr| {
                try formatReplacement(expr, writer);
            } else {
                try writer.writeAll(f.name);
            }
        },
        .ZixExpr => |i| {
            try writer.writeAll(i.source);
        },
        .Binding => |b| {
            try writer.writeAll(b.name);
        },
        .Ref, .Or, .Range => unreachable,
    }
}

pub const Ast = struct {
    rules: []const Rule,

    pub const Rule = struct {
        pattern: *Expr,
        replacement: *Expr,
        postprocess: ?[]const u8,
    };

    pub const Expr = union(enum) {
        Atom: struct {
            name: []const u8,
            binding: ?[]const u8,
            args: []const *Expr,
        },
        Field: struct {
            name: []const u8,
            expr: ?*Expr,
        },
        ZixExpr: struct {
            source: []const u8,
        },
        Range: struct {
            start: *Expr,
            end: *Expr,
        },
        Or: struct {
            left: *Expr,
            right: *Expr,
        },
        Ref: struct {
            name: []const u8,
        },
        Binding: struct {
            name: []const u8,
            optional: bool,
            pattern: ?*Expr,
            predicate: ?*Expr,
            extra: ?struct {
                bindings: []const *Expr,
                zig_expr: *Expr,
            },
        },
    };

    pub fn init(file_name: []const u8, in: [:0]const u8) !Ast {
        var parser = Parser.init(file_name, in);

        var rules = std.ArrayList(Rule).empty;

        while (parser.lexer.peek().kind != .eof) {
            const rule = try parser.parseRule();
            try rules.append(arena, rule);
        }

        return Ast{ .rules = rules.items };
    }
};

pub const Parser = struct {
    file_name: []const u8,
    lexer: Lexer,

    pub fn init(file_name: []const u8, source: [:0]const u8) Parser {
        return .{
            .file_name = file_name,
            .lexer = .{ .source = source },
        };
    }

    const Error = anyerror;

    pub fn parseRule(self: *Parser) !Ast.Rule {
        const pattern = try self.parseExpr();
        _ = try self.expect(.@":");
        const replacement = try self.parseExpr();
        const postprocess = if (self.lexer.peek().kind == .@"&&") blk: {
            _ = self.lexer.next();
            const tok = self.lexer.peek();
            _ = try self.expect(.zix_expr);
            break :blk tok.source;
        } else null;
        return .{
            .pattern = pattern,
            .replacement = replacement,
            .postprocess = postprocess,
        };
    }

    pub fn expect(self: *Parser, kind: Token.Kind) Error!void {
        const token = self.lexer.next();
        if (token.kind != kind) {
            return self.reportError(token.pos, "expected {s}, found {s}", .{ @tagName(kind), @tagName(token.kind) });
        }
    }

    pub fn parseExpr(self: *Parser) Error!*Ast.Expr {
        const token = self.lexer.next();
        var expr = try self.spill(switch (token.kind) {
            .atom_name => .{
                .Atom = .{
                    .name = token.source,
                    .binding = try self.parseBinding(),
                    .args = &.{},
                },
            },
            .field_name => .{
                .Field = .{
                    .name = token.source[1..],
                    .expr = null,
                },
            },
            .binding_name, .opt_binding_name => .{
                .Binding = .{
                    .name = token.source[@intFromBool(token.kind == .opt_binding_name)..],
                    .optional = token.kind == .opt_binding_name,
                    .pattern = if (self.lexer.peek().kind == .@"&") blk: {
                        _ = self.lexer.next();
                        break :blk try self.parseExpr();
                    } else null,
                    .predicate = if (self.lexer.peek().kind == .@"&&") blk: {
                        _ = self.lexer.next();
                        break :blk try self.parseExpr();
                    } else null,
                    .extra = if (self.lexer.peek().kind == .@"@") blk: {
                        _ = self.lexer.next();
                        var bindings = std.ArrayList(*Ast.Expr).empty;

                        while (true) {
                            const binding = try self.parseExpr();
                            try bindings.append(arena, binding);

                            if (self.lexer.peek().kind == .@"=") break;
                        }

                        _ = self.lexer.next();

                        const zig_expr = try self.parseExpr();

                        break :blk .{
                            .bindings = bindings.items,
                            .zig_expr = zig_expr,
                        };
                    } else null,
                },
            },
            .@"&" => .{
                .Ref = .{
                    .name = self.lexer.next().source,
                },
            },
            .@"(" => b: {
                const prefix = self.lexer.next();
                break :b switch (prefix.kind) {
                    .atom_name, .binding_name => .{
                        .Atom = .{
                            .name = prefix.source,
                            .binding = try self.parseBinding(),
                            .args = try self.parseExprList(),
                        },
                    },
                    .field_name => .{
                        .Field = .{
                            .name = prefix.source[1..],
                            .expr = try self.parseOptExpr(),
                        },
                    },
                    .@"&" => .{
                        .Ref = .{
                            .name = br: {
                                const name = self.lexer.next().source;
                                try self.expect(.@")");
                                break :br name;
                            },
                        },
                    },
                    else => return self.reportError(
                        prefix.pos,
                        "expected atom or field, found {s}",
                        .{@tagName(prefix.kind)},
                    ),
                };
            },
            .tag, .integer, .hex_integer => .{
                .ZixExpr = .{
                    .source = token.source,
                },
            },
            .zix_expr => .{
                .ZixExpr = .{
                    .source = token.source[1 .. token.source.len - 1],
                },
            },
            else => return self.reportError(
                token.pos,
                "expected Atom or :field or binding, found {s}",
                .{@tagName(token.kind)},
            ),
        });

        while (true) {
            switch (self.lexer.peek().kind) {
                .@".." => {
                    _ = self.lexer.next();
                    expr = try self.spill(.{
                        .Range = .{
                            .start = expr,
                            .end = try self.parseExpr(),
                        },
                    });
                },
                .@"|" => {
                    _ = self.lexer.next();
                    expr = try self.spill(.{
                        .Or = .{
                            .left = expr,
                            .right = try self.parseExpr(),
                        },
                    });
                },
                else => break,
            }
        }

        return expr;
    }

    pub fn spill(_: *Parser, expr: Ast.Expr) !*Ast.Expr {
        const slot = try arena.create(Ast.Expr);
        slot.* = expr;
        return slot;
    }

    pub fn parseOptExpr(self: *Parser) !?*Ast.Expr {
        if (self.lexer.peek().kind == .@")") {
            _ = self.lexer.next();
            return null;
        }
        const expr = try self.parseExpr();
        _ = try self.expect(.@")");
        return expr;
    }

    pub fn parseBinding(self: *Parser) !?[]const u8 {
        if (self.lexer.peek().kind != .field_name) return null;
        return self.lexer.next().source[1..];
    }

    pub fn parseExprList(self: *Parser) ![]*Ast.Expr {
        var list = std.ArrayList(*Ast.Expr).empty;

        while (self.lexer.peek().kind != .@")") {
            if (self.lexer.peek().kind == .eof) {
                return self.reportError(null, "expected end of atom, found eof", .{});
            }
            const expr = try self.parseExpr();
            try list.append(arena, expr);
        }

        _ = self.lexer.next();

        return list.items;
    }

    pub fn reportError(self: *Parser, pos: ?usize, comptime fmt: []const u8, args: anytype) Error {
        var buffer: [1024 * 4]u8 = undefined;
        var output = std.fs.File.stderr().writer(&buffer);

        const line, const col = lineCol(self.lexer.source, pos orelse self.lexer.pos);
        try output.interface.print(
            "error: {s}:{}:{}: " ++ fmt ++ "\n",
            .{ self.file_name, line, col } ++ args,
        );

        try pointToCode(self.lexer.source, self.lexer.pos, &output.interface);
        try output.interface.print("\n", .{});
        try output.interface.flush();
        return error.InvalidToken;
    }
};

pub fn lineCol(source: []const u8, index: usize) struct { usize, usize } {
    var line: usize = 0;
    var last_nline: isize = -1;
    for (source[0..@min(@as(usize, @intCast(index)), source.len)], 0..) |c, i| if (c == '\n') {
        line += 1;
        last_nline = @intCast(i);
    };
    return .{ line + 1, @intCast(@as(isize, @bitCast(index)) - last_nline) };
}

pub fn pointToCode(source: []const u8, index_m: usize, writer: *std.Io.Writer) !void {
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

pub const Token = struct {
    kind: Kind,
    pos: usize,
    end: usize,
    source: []const u8,

    pub const Kind = enum {
        atom_name,
        field_name,
        binding_name,
        opt_binding_name,
        integer,
        hex_integer,
        zix_expr,
        tag,
        @"(",
        @")",
        @":",
        @"..",
        @"&",
        @"&&",
        @"@",
        @"=",
        @"|",
        eof,
        unknown,
    };
};

pub const Lexer = struct {
    source: [:0]const u8,
    pos: usize = 0,

    pub fn peek(self: *Lexer) Token {
        const prev = self.pos;
        defer self.pos = prev;
        return self.next();
    }

    pub fn next(self: *Lexer) Token {
        var start = self.pos;
        const kind = while (true) {
            break switch (self.source[self.pos]) {
                0 => break .eof,
                1...32 => {
                    self.pos += 1;
                    start = self.pos;
                    continue;
                },
                '{' => {
                    self.pos += 1;
                    var depth: usize = 1;
                    while (depth > 0) : (self.pos += 1) {
                        if (self.source[self.pos] == '{') depth += 1;
                        if (self.source[self.pos] == '}') depth -= 1;
                    }

                    break .zix_expr;
                },
                ':' => {
                    self.pos += 1;
                    var is_field = false;
                    while (true) switch (self.source[self.pos]) {
                        'a'...'z', '_' => {
                            self.pos += 1;
                            is_field = true;
                        },
                        else => break,
                    };

                    if (is_field) {
                        break .field_name;
                    } else {
                        break .@":";
                    }
                },
                '0'...'9' => {
                    self.pos += 1;
                    var is_hex = false;
                    while (true) switch (self.source[self.pos]) {
                        'x' => {
                            std.debug.assert(self.pos - start == 1);
                            self.pos += 1;
                            is_hex = true;
                        },
                        '0'...'9', 'a'...'f', 'A'...'F' => {
                            self.pos += 1;
                        },
                        else => break,
                    };

                    if (is_hex) {
                        break .hex_integer;
                    }
                    break .integer;
                },
                '?' => {
                    self.pos += 1;
                    while (true) switch (self.source[self.pos]) {
                        'a'...'z', 'A'...'Z', '0'...'9', '_' => {
                            self.pos += 1;
                        },
                        else => break,
                    };
                    break .opt_binding_name;
                },
                '&' => {
                    self.pos += 1;
                    if (self.source[self.pos] == '&') {
                        self.pos += 1;
                        break .@"&&";
                    }
                    break .@"&";
                },
                '@' => {
                    self.pos += 1;
                    break .@"@";
                },
                '=' => {
                    self.pos += 1;
                    break .@"=";
                },
                '|' => {
                    self.pos += 1;
                    break .@"|";
                },
                'a'...'z', '_' => {
                    self.pos += 1;
                    while (true) switch (self.source[self.pos]) {
                        'a'...'z', '0'...'9', '_' => {
                            self.pos += 1;
                        },
                        else => break,
                    };
                    break .binding_name;
                },
                'A'...'Z' => {
                    self.pos += 1;
                    while (true) switch (self.source[self.pos]) {
                        'a'...'z', 'A'...'Z', '0'...'9', '_' => {
                            self.pos += 1;
                        },
                        else => break,
                    };
                    break .atom_name;
                },
                '(' => {
                    self.pos += 1;
                    break .@"(";
                },
                ')' => {
                    self.pos += 1;
                    break .@")";
                },
                ';' => {
                    while (self.source[self.pos] != '\n') : (self.pos += 1) {}
                    continue;
                },
                '.' => {
                    self.pos += 1;
                    var is_atom = false;
                    break while (true) switch (self.source[self.pos]) {
                        'a'...'z', '0'...'9', '_', 'A'...'Z' => {
                            self.pos += 1;
                            is_atom = true;
                        },
                        '.' => {
                            std.debug.assert(!is_atom);
                            if (self.source[self.pos] == '.') {
                                self.pos += 1;
                                break .@"..";
                            }
                        },
                        else => break if (is_atom) Token.Kind.tag else .unknown,
                    };
                },
                else => .unknown,
            };
        };

        return .{
            .kind = kind,
            .pos = start,
            .end = self.pos,
            .source = self.source[start..self.pos],
        };
    }
};
