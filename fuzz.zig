const std = @import("std");
const Types = @import("Types.zig");
const Lexer = @import("Lexer.zig");
const tests = @import("tests.zig");

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    //var arena = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = arena.deinit();
    for (2513..10000) |i| {
        _ = arena.reset(.retain_capacity);
        try fuzz(i, arena.allocator());
    }
    std.debug.print("top mem: {}", .{arena.queryCapacity()});
}

const names = [_][]const u8{
    "main",       "well",      "apple",     "banana",     "cherry",      "developer", "eager",         "fluent",
    "grace",      "harmony",   "insight",   "jovial",     "keen",        "luminous",  "momentum",      "notable",
    "optimistic", "precise",   "quaint",    "resilient",  "sincere",     "tenacious", "uplift",        "vibrant",
    "wholesome",  "xenial",    "youthful",  "zealous",    "abstract",    "brilliant", "creative",      "dedicated",
    "efficient",  "fearless",  "generous",  "honest",     "intuitive",   "joyful",    "knowledgeable", "limitless",
    "meticulous", "nurturing", "objective", "perceptive", "questioning", "radiant",   "strategic",     "trustworthy",
    "unique",     "versatile", "wise",      "xenophobic", "yearning",    "zenith",
};

const func_count = 1;
const max_depth = 6;
const max_arg_count = 5;
const return_types = [_]Types.Id{ .void, .uint };
const arguments = [_]Types.Id{ .uint, .ptr };
const variable_types = [_]Types.Id{.uint};
const binops = [_]Lexer.Lexeme{ .@"+", .@"-", .@"*", .@"==", .@"!=" };

fn fuzz(seed: usize, arena: std.mem.Allocator) !void {
    std.debug.print("seed: {}\n", .{seed});

    var pcg = std.Random.Pcg.init(seed);
    const rng = pcg.random();

    const funcs = try arena.alloc(FuncData, func_count);
    defer {
        for (funcs) |*f| arena.free(f.args);
        arena.free(funcs);
    }

    for (funcs) |*f| {
        f.* = .{
            .args = try arena.alloc(Types.Id, rng.intRangeAtMost(usize, 0, max_arg_count)),
            .ret = return_types[rng.intRangeLessThan(usize, 0, return_types.len)],
        };

        for (f.args) |*a| {
            a.* = arguments[rng.intRangeLessThan(usize, 0, arguments.len)];
        }
    }

    var file = try std.ArrayList(u8).initCapacity(arena, 1024 * 16);
    defer file.deinit();
    var writer = file.writer();

    for (funcs, 0..) |f, i| {
        try writer.print("{s}:=fn(", .{names[i]});
        for (f.args, 0..) |a, j| {
            if (j != 0) try writer.writeAll(", ");
            try writer.print("{s}:{}", .{ names[func_count + j], a });
        }
        try writer.print("):{}", .{f.ret});

        var gen = ExprGen{ .func = i, .funcs = funcs, .rng = rng, .out = writer };
        defer gen.variables.deinit();
        try gen.generate();
    }

    if (false) {
        try tests.testBuilder("smh", file.items, arena, std.io.getStdErr().writer(), .escape_codes);
    } else {
        try tests.testBuilder("smh", file.items, arena, std.io.null_writer, .no_color);
    }
}

const FuncData = struct {
    args: []Types.Id,
    ret: Types.Id,
};

const ExprGen = struct {
    funcs: []const FuncData,
    func: usize,
    rng: std.Random,
    out: std.ArrayList(u8).Writer,
    variables: std.ArrayList(Types.Id) = undefined,
    depth: usize = 0,

    const Error = std.ArrayList(u8).Writer.Error;

    fn generate(self: *ExprGen) !void {
        self.variables = .init(self.out.context.allocator);
        try self.variables.appendSlice(self.funcs[self.func].args);
        try self.genBlockLow(true);
    }

    fn genExpr(self: *ExprGen, ty: Types.Id) Error!void {
        const Entry = struct { usize, *const fn (*ExprGen) Error!void, ?Types.Id, usize };

        self.depth += 1;
        defer self.depth -= 1;
        const reservoar = max_depth - self.depth;

        const table = [_]Entry{
            .{ 40, genConst, .uint, 0 },
            .{ 30, genBinOp, .uint, 1 },
            .{ 10, genVariable, .void, 1 },
            .{ 10, genIdent, .uint, 0 },
            .{ 10, genPtrIdent, .ptr, 0 },
            .{ 10, genBlock, .void, 2 },
            .{ 10, genAssignment, .void, 1 },
            .{ 10, genIf, .void, 2 },
            .{ 5, genReturn, .void, 1 },
        };

        var space_limit: usize = 0;
        for (table) |e| if (e[2] == ty and e[3] <= reservoar) {
            space_limit += e[0];
        };

        if (space_limit == 0) {
            try self.out.writeAll("{}");
            return;
        }

        const choice = self.rng.intRangeLessThan(usize, 0, space_limit);
        var range: usize = 0;
        for (table) |e| {
            if (e[2] != ty or e[3] > reservoar) continue;

            if (range <= choice and choice <= range + e[0]) {
                try e[1](self);
                break;
            }

            range += e[0];
        }
    }

    fn genVariable(self: *ExprGen) !void {
        const ty = variable_types[self.rng.intRangeLessThan(usize, 0, variable_types.len)];
        const name = self.funcs.len + self.variables.items.len;
        try self.out.print("{s}:=", .{names[name]});
        try self.genExpr(ty);
        try self.variables.append(ty);
    }

    fn genIf(self: *ExprGen) !void {
        try self.out.writeAll("if ");
        try self.genExpr(.uint);
        try self.genBlock();
        if (self.rng.boolean()) {
            try self.out.writeAll("else");
            try self.genBlock();
        }
    }

    fn genAssignment(self: *ExprGen) !void {
        if (self.variables.items.len == 0) {
            try self.genConst();
            return;
        }

        const index = self.rng.intRangeLessThan(usize, 0, self.variables.items.len);
        try self.out.writeAll(names[self.funcs.len + index]);
        try self.out.writeAll("=");
        try self.genExpr(self.variables.items[index]);
    }

    fn genIdent(self: *ExprGen) !void {
        if (self.variables.items.len == 0) {
            try self.genConst();
            return;
        }

        const index = self.rng.intRangeLessThan(usize, 0, self.variables.items.len);
        try self.out.writeAll(names[self.funcs.len + index]);
    }

    fn genPtrIdent(self: *ExprGen) !void {
        if (self.variables.items.len == 0) {
            try self.out.writeAll("&0");
            return;
        }

        var to_select: Types.Id = .ptr;
        var ptr_count: usize = 0;
        for (self.variables.items) |v| ptr_count += @intFromBool(v == to_select);

        if (ptr_count == 0) {
            to_select = .uint;
            for (self.variables.items) |v| ptr_count += @intFromBool(v == to_select);
        }

        var index = self.rng.intRangeLessThan(usize, 0, ptr_count);
        for (self.variables.items, 0..) |v, i| {
            if (v == to_select) {
                if (index == 0) {
                    if (to_select != .ptr) try self.out.writeAll("&");
                    try self.out.writeAll(names[i + self.funcs.len]);
                    break;
                }
                index -= 1;
            }
        }
    }

    fn genConst(self: *ExprGen) !void {
        try self.out.print("{}", .{self.rng.intRangeLessThan(usize, 0, 10)});
    }

    fn genBinOp(self: *ExprGen) !void {
        try self.genExpr(.uint);
        try self.out.writeAll(@tagName(binops[self.rng.intRangeLessThan(usize, 0, binops.len)]));
        try self.genExpr(.uint);
    }

    fn genBlock(self: *ExprGen) !void {
        try self.genBlockLow(false);
    }

    fn genReturn(self: *ExprGen) !void {
        try self.out.writeAll("return ");
        if (self.funcs[self.func].ret == .void) return;
        try self.genExpr(self.funcs[self.func].ret);
    }

    fn genBlockLow(self: *ExprGen, force_return: bool) !void {
        try self.out.writeAll("{");

        const prev_vars = self.variables.items.len;
        defer self.variables.items.len = prev_vars;

        for (0..self.rng.intRangeLessThan(usize, 1, 7)) |_| {
            try self.genExpr(.void);
            try self.out.writeAll(";");
        }
        if (force_return) try self.genReturn();

        try self.out.writeAll("}");
    }
};
