funcs: std.ArrayListUnmanaged(FuncData) = .{},
arena: std.heap.ArenaAllocator,
func_worklist: std.ArrayListUnmanaged(Func) = .{},
source: []const Ast,

const std = @import("std");
const Ast = @import("parser.zig");
const graph = @import("Func.zig");
const Types = @This();

pub const Func = enum(u32) {
    main,
    _,
    const Data = FuncData;
    const field = "funcs";

    pub fn format(self: *const @This(), comptime _: anytype, _: anytype, writer: anytype) !void {
        try writer.print("fn{}", .{@intFromEnum(self.*)});
    }
};

pub const File = enum(u16) { root, _ };

pub const Id = enum {
    void,
    uint,
    ptr,

    pub fn size(self: Id) usize {
        return switch (self) {
            .void => 0,
            .uint, .ptr => 8,
        };
    }

    pub fn asDataType(self: Id) graph.DataType {
        return switch (self) {
            .void => unreachable,
            .uint, .ptr => .int,
        };
    }

    pub fn fromStr(str: []const u8) ?Id {
        return std.meta.stringToEnum(Id, str);
    }

    pub fn format(self: *const Id, comptime _: anytype, _: anytype, writer: anytype) !void {
        try switch (self.*) {
            .ptr => writer.writeAll("^uint"),
            else => writer.writeAll(@tagName(self.*)),
        };
    }
};

pub const FuncData = struct {
    args: []Id,
    ret: Id,
    file: File,
    name: Ast.Pos,
    ast: Ast.Id,
};

pub fn init(gpa: std.mem.Allocator, source: []const Ast) Types {
    return .{
        .source = source,
        .arena = .init(gpa),
    };
}

pub fn deinit(self: *Types) void {
    self.funcs.deinit(self.arena.child_allocator);
    self.func_worklist.deinit(self.arena.child_allocator);
    self.arena.deinit();
    self.* = undefined;
}

pub fn get(self: *Types, id: anytype) *@TypeOf(id).Data {
    return &@field(self, @TypeOf(id).field).items[@intFromEnum(id)];
}

pub fn getAst(self: *Types, file: File, expr: Ast.Id) Ast.Expr {
    return self.getFile(file).exprs.get(expr);
}

pub fn getFile(self: *Types, file: File) *const Ast {
    return &self.source[@intFromEnum(file)];
}

pub fn resolveTy(self: *Types, file: File, expr: Ast.Id) Id {
    const ast = self.getFile(file);
    return switch (ast.exprs.get(expr)) {
        .Buty => |e| switch (e.bt) {
            .uint => .uint,
            .void => .void,
            else => std.debug.panic("{any}", .{e.bt}),
        },
        .UnOp => |e| switch (e.op) {
            .@"^" => b: {
                const v = self.resolveTy(file, e.oper);
                std.debug.assert(v == .uint);
                break :b .ptr;
            },
            else => std.debug.panic("{any}", .{e.op}),
        },
        else => std.debug.panic("{any}", .{expr.tag()}),
    };
}

pub fn resolveFunc(self: *Types, file: File, called: Ast.Id) Func {
    const ast = self.getFile(file);
    const id = ast.exprs.get(called).Ident.id;
    const fn_ast = ast.exprs.get(ast.decls[id.index].expr).BinOp.rhs;

    for (self.funcs.items, 0..) |f, i| {
        if (f.ast == fn_ast) return @enumFromInt(i);
    }

    return self.addFunc(file, ast.posOf(ast.decls[id.index].expr), fn_ast);
}

pub fn addFunc(self: *Types, file: File, name: Ast.Pos, func: Ast.Id) Func {
    const ast = self.getFile(file);
    const fn_ast = self.getAst(file, func).Fn;

    const args = self.arena.allocator().alloc(Id, fn_ast.args.len()) catch unreachable;
    for (ast.exprs.view(fn_ast.args), args) |argid, *arg| {
        const ty = ast.exprs.get(argid).Arg.ty;
        arg.* = self.resolveTy(file, ty);
    }

    self.funcs.append(self.arena.child_allocator, .{
        .args = args,
        .name = name,
        .file = file,
        .ret = self.resolveTy(file, fn_ast.ret),
        .ast = func,
    }) catch unreachable;

    self.func_worklist.append(
        self.arena.child_allocator,
        @enumFromInt(self.funcs.items.len - 1),
    ) catch unreachable;

    return @enumFromInt(self.funcs.items.len - 1);
}
