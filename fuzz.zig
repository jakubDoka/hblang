const std = @import("std");
const Types = @import("src/Types.zig");
const Lexer = @import("src/Lexer.zig");
const Ast = @import("src/Ast.zig");
const utils = @import("src/utils.zig");
const tests = @import("tests.zig");

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    //var arena = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = arena.deinit();
    for (14..10000) |i| {
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
const struct_count = 2;
const max_depth = 6;
const max_arg_count = 5;
const return_types = [_]Types.Id{ .void, .uint };
const arguments = [_]Types.Id{.uint};

fn fuzz(seed: usize, arena: std.mem.Allocator) !void {
    std.debug.print("seed: {}\n", .{seed});

    var pcg = std.Random.Pcg.init(seed);
    const rng = pcg.random();

    const funcs = try arena.alloc(Types.Func, func_count);
    defer {
        for (funcs) |*f| arena.free(f.args);
        arena.free(funcs);
    }

    for (funcs, 0..) |*f, i| {
        f.* = .{
            .id = @intCast(i),
            .key = .dummy,
            .name = "",
            .args = try arena.alloc(Types.Id, rng.intRangeAtMost(usize, 0, max_arg_count)),
            .ret = return_types[rng.intRangeLessThan(usize, 0, return_types.len)],
        };

        for (f.args) |*a| {
            a.* = arguments[rng.intRangeLessThan(usize, 0, arguments.len)];
        }
    }

    const structs = try arena.alloc(Types.Struct, struct_count);
    std.debug.assert(structs.len == 2);
    structs[0] = .{
        .key = .dummy,
        .name = "foo",
        .fields = b: {
            const mem = try arena.alloc(Types.Struct.Field, 2);
            mem[0] = .{
                .name = "",
                .ty = .uint,
            };
            mem[1] = .{
                .name = "",
                .ty = .uint,
            };
            break :b mem;
        },
        .ast_fields = .{},
    };
    structs[1] = .{
        .key = .dummy,
        .name = "bar",
        .fields = b: {
            const mem = try arena.alloc(Types.Struct.Field, 2);
            mem[0] = .{
                .name = "",
                .ty = Types.Id.init(.Struct, @intFromPtr(&structs[0])),
            };
            mem[1] = .{
                .name = "",
                .ty = .uint,
            };
            break :b mem;
        },
        .ast_fields = .{},
    };

    for (structs, 0..) |*s, i| s.key.file = @enumFromInt(i);

    var file = try std.ArrayList(u8).initCapacity(arena, 1024 * 16);
    defer file.deinit();
    var writer = file.writer();

    for (structs, 0..) |s, i| {
        try writer.print("{s}:=struct{{", .{names[i + funcs.len]});
        for (s.fields.?, 0..) |*f, j| {
            try writer.print("{s}:", .{names[j]});
            if (f.ty.data() == .Struct) {
                try writer.writeAll(names[funcs.len + @intFromEnum(f.ty.file())]);
            } else {
                try writer.print("{}", .{f.ty});
            }
            try writer.writeAll(",");
        }
        try writer.writeAll("}");
    }

    for (funcs, 0..) |f, i| {
        try writer.print("{s}:=fn(", .{names[i]});
        for (f.args, 0..) |a, j| {
            if (j != 0) try writer.writeAll(", ");
            try writer.print("{s}:{}", .{ names[funcs.len + structs.len + j], a });
        }
        try writer.print("):{}", .{f.ret});

        var gen = ExprGen{
            .func = i,
            .structs = structs,
            .funcs = funcs,
            .rng = rng,
            .out = writer,
        };
        defer gen.variables.deinit();
        try gen.generate();
    }

    //std.debug.print("\n{s}\n", .{file.items});

    if (false) {
        tests.testBuilder("smh", file.items, arena, std.io.getStdErr().writer().any(), std.io.tty.detectConfig(std.io.getStdErr()), true) catch |err| switch (err) {
            error.TestExpectedEqual => {},
            else => return err,
        };
    } else {
        tests.testBuilder("smh", file.items, arena, std.io.null_writer.any(), .no_color, false) catch |err| switch (err) {
            error.TestExpectedEqual => {},
            else => return err,
        };
    }
}

const generators = enum {
    fn hardwireType(comptime like: Types.Id) fn (*ExprGen, Types.Id) bool {
        return enum {
            fn ht(_: *ExprGen, ty: Types.Id) bool {
                return ty == like;
            }
        }.ht;
    }

    fn requredDepth(ty: Types.Id) usize {
        return switch (ty.data()) {
            .Builtin => 0,
            .Ptr => 1,
            .Struct => |s| {
                var depth_requirement: usize = 0;
                for (s.fields.?) |f| {
                    depth_requirement = @max(depth_requirement, 1 + requredDepth(f.ty));
                }
                return depth_requirement;
            },
            else => unreachable,
        };
    }

    pub const Const = enum {
        pub const depth_requirement = 0;

        pub fn gen(self: *ExprGen, ty: Types.Id) ExprGen.Error!void {
            if (ty == .bool) {
                try self.out.print("{}", .{self.rng.boolean()});
            } else {
                try self.out.print("{}", .{self.rng.intRangeLessThan(usize, 0, 10)});
            }
        }

        pub fn compatible(_: *ExprGen, ty: Types.Id) bool {
            return ty.isInteger() or ty == .bool;
        }
    };

    pub const Variable = enum {
        pub const depth_requirement = 1;
        const variable_types = [_]Types.Id{.uint};

        pub fn gen(self: *ExprGen, _: Types.Id) !void {
            const reservoar = max_depth - self.depth - 1;
            var affordable_struct_count: usize = 0;
            for (self.structs) |*s| affordable_struct_count += @intFromBool(requredDepth(s.asTy()) <= reservoar);

            const ty = if (self.rng.boolean() and affordable_struct_count != 0) b: {
                var idx = self.rng.intRangeLessThan(usize, 0, affordable_struct_count);
                for (self.structs) |*s| {
                    if (requredDepth(s.asTy()) <= reservoar) {
                        if (idx == 0) break :b s.asTy();
                        idx -= 1;
                    }
                }
                unreachable;
            } else variable_types[self.rng.intRangeLessThan(usize, 0, variable_types.len)];
            const name = self.funcs.len + self.structs.len + self.variables.items.len;
            try self.out.print("{s}:=", .{names[name]});
            try self.genExpr(ty);
            try self.variables.append(ty);
        }

        pub const compatible = hardwireType(.void);
    };

    pub const Ctor = enum {
        pub const depth_requirement = 0;

        pub fn gen(self: *ExprGen, ty: Types.Id) ExprGen.Error!void {
            try self.out.print("{s}.{{", .{names[self.funcs.len + @intFromEnum(ty.file())]});
            for (ty.data().Struct.fields.?, 0..) |f, i| {
                try self.out.print("{s}:", .{names[i]});
                try self.genExpr(f.ty);
                try self.out.writeAll(",\n");
            }
            try self.out.writeAll("}");
        }

        pub fn compatible(self: *ExprGen, ty: Types.Id) bool {
            if (ty.data() != .Struct) return false;
            const d_reqirement: usize = requredDepth(ty);
            const reservoar = max_depth - self.depth;
            return reservoar >= d_reqirement;
        }
    };

    pub const If = enum {
        pub const depth_requirement = 3;

        pub fn gen(self: *ExprGen, _: Types.Id) !void {
            try self.out.writeAll("if ");
            try self.genExpr(.bool);
            try self.gen(Block, .void);
            if (self.rng.boolean()) {
                try self.out.writeAll("else");
                try self.gen(Block, .void);
            }
        }

        pub const compatible = hardwireType(.void);
    };

    pub const Assignment = enum {
        pub const depth_requirement = 1;

        fn gen(self: *ExprGen, _: Types.Id) !void {
            const index = self.rng.intRangeLessThan(usize, 0, self.variables.items.len);
            try self.out.writeAll(names[self.funcs.len + self.structs.len + index]);
            try self.out.writeAll("=");
            try self.genExpr(self.variables.items[index]);
        }

        pub fn compatible(self: *ExprGen, ty: Types.Id) bool {
            return ty == .void and self.variables.items.len != 0;
        }
    };

    pub const Ident = enum {
        pub const depth_requirement = 0;

        pub fn gen(self: *ExprGen, ty: Types.Id) !void {
            var count: usize = 0;
            for (self.variables.items) |v| count += @intFromBool(v == ty);
            var index = self.rng.intRangeLessThan(usize, 0, count);
            for (names[self.funcs.len + self.structs.len ..][0..self.variables.items.len], self.variables.items) |name, vty| {
                if (vty == ty) {
                    if (index == 0) {
                        try self.out.writeAll(name);
                        return;
                    }
                    index -= 1;
                }
            }
        }

        pub fn compatible(self: *ExprGen, ty: Types.Id) bool {
            return std.mem.indexOfScalar(Types.Id, self.variables.items, ty) != null;
        }
    };

    pub const Block = enum {
        pub const depth_requirement = 2;

        pub fn gen(self: *ExprGen, _: Types.Id) !void {
            try genLow(self, false);
        }

        pub const compatible = hardwireType(.void);

        fn genLow(self: *ExprGen, force_return: bool) !void {
            try self.out.writeAll("{");

            const prev_vars = self.variables.items.len;
            defer self.variables.items.len = prev_vars;

            for (0..self.rng.intRangeLessThan(usize, 1, 7)) |_| {
                try self.genExpr(.void);
                try self.out.writeAll(";\n");
            }
            if (force_return) try Return.gen(self, .void);

            try self.out.writeAll("}");
        }
    };

    pub const BinOp = enum {
        pub const depth_requirement = 1;

        const binops = [_]Lexer.Lexeme{ .@"+", .@"-", .@"*" };
        const cmps = [_]Lexer.Lexeme{ .@"==", .@"!=" };

        pub fn gen(self: *ExprGen, ty: Types.Id) !void {
            try self.genExpr(.uint);
            const ops = switch (ty) {
                .bool => &cmps,
                .uint => &binops,
                else => unreachable,
            };
            try self.out.writeAll(@tagName(ops[self.rng.intRangeLessThan(usize, 0, ops.len)]));
            try self.genExpr(.uint);
        }

        pub fn compatible(_: *ExprGen, ty: Types.Id) bool {
            return ty == .uint or ty == .bool;
        }
    };

    pub const Return = enum {
        pub const depth_requirement = 1;

        pub fn gen(self: *ExprGen, _: Types.Id) !void {
            try self.out.writeAll("return ");
            if (self.funcs[self.func].ret == .void) return;
            try self.genExpr(self.funcs[self.func].ret);
        }

        pub const compatible = hardwireType(.void);
    };
};

const ExprGen = struct {
    structs: []Types.Struct,
    funcs: []Types.Func,
    func: usize,
    rng: std.Random,
    out: std.ArrayList(u8).Writer,
    variables: std.ArrayList(Types.Id) = undefined,
    depth: usize = 0,

    const Error = std.ArrayList(u8).Writer.Error;

    fn generate(self: *ExprGen) !void {
        self.variables = .init(self.out.context.allocator);
        try self.variables.appendSlice(self.funcs[self.func].args);
        try generators.Block.genLow(self, true);
    }

    const Entry = struct {
        gen: *const fn (*ExprGen, Types.Id) Error!void,
        compatible: *const fn (*ExprGen, Types.Id) bool,
        depth_requirement: usize,
        comptime weight: usize = 1,

        pub fn canGenerate(e: @This(), self: *ExprGen, ty: Types.Id, reservoar: usize) bool {
            return e.compatible(self, ty) and e.depth_requirement <= reservoar;
        }
    };

    fn gen(self: *ExprGen, comptime Gen: type, ty: Types.Id) Error!void {
        try Gen.gen(self, ty);
    }

    fn genExpr(self: *ExprGen, ty: Types.Id) Error!void {
        self.depth += 1;
        defer self.depth -= 1;
        const reservoar = max_depth - self.depth;

        const decls = @typeInfo(generators).@"enum".decls;
        var table: [decls.len]Entry = undefined;
        inline for (&table, decls) |*entry, decl| {
            const Gen = @field(generators, decl.name);
            entry.* = .{
                .gen = Gen.gen,
                .compatible = Gen.compatible,
                .depth_requirement = Gen.depth_requirement,
            };
        }

        var space_limit: usize = 0;
        for (table) |e| space_limit += @intFromBool(e.canGenerate(self, ty, reservoar)) * e.weight;

        if (space_limit == 0) {
            std.debug.panic("{}", .{ty});
        }

        const choice = self.rng.intRangeLessThan(usize, 0, space_limit);
        var range: usize = 0;
        for (table) |e| {
            if (!e.canGenerate(self, ty, reservoar)) continue;

            if (range <= choice and choice <= range + e.weight) {
                try e.gen(self, ty);
                break;
            }

            range += e.weight;
        }
    }
};
