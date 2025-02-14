funcs: std.ArrayListUnmanaged(FuncData) = .{},
arena: std.heap.ArenaAllocator,
func_worklist: std.ArrayListUnmanaged(Func) = .{},
interner: std.hash_map.HashMapUnmanaged(Id, void, TypeCtx, 70) = .{},
source: []const Ast,

const std = @import("std");
const Ast = @import("parser.zig");
const graph = @import("Func.zig");
const Lexer = @import("Lexer.zig");
const Types = @This();

pub const TypeCtx = struct {
    pub fn eql(_: @This(), a: Id, b: Id) bool {
        return std.meta.eql(a.data(), b.data());
    }

    pub fn hash(_: @This(), adapted_key: Id) u64 {
        var hasher = std.hash.Fnv1a_64.init();
        std.hash.autoHash(&hasher, adapted_key.data());
        return hasher.final();
    }
};

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

pub const Data = union(enum) {
    Builtin: b: {
        var enm = @typeInfo(Id);
        enm.@"enum".is_exhaustive = true;
        enm.@"enum".decls = &.{};
        break :b @Type(enm);
    },
    Ptr: Id,
};

pub const Id = enum(usize) {
    never,
    void,
    bool,
    u8,
    u16,
    u32,
    uint,
    i8,
    i16,
    i32,
    int,
    _,

    const Repr = packed struct(usize) {
        data: std.meta.Int(.unsigned, @bitSizeOf(usize) - @bitSizeOf(std.meta.Tag(Data))),
        flag: std.meta.Tag(std.meta.Tag(Data)),

        inline fn tag(self: Repr) std.meta.Tag(Data) {
            return @enumFromInt(self.flag);
        }
    };

    pub fn fromLexeme(lexeme: Lexer.Lexeme) Id {
        const off = comptime @as(isize, @intFromEnum(Id.void)) - @intFromEnum(Lexer.Lexeme.void);
        return @enumFromInt(@as(isize, @intFromEnum(lexeme)) + off);
    }

    inline fn init(flg: std.meta.Tag(Data), dt: usize) Id {
        comptime {
            std.debug.assert(fromLexeme(.i8) == .i8);
        }
        return @enumFromInt(@as(usize, @bitCast(Repr{ .flag = @intFromEnum(flg), .data = @intCast(dt) })));
    }

    pub fn isUnsigned(self: Id) bool {
        return @intFromEnum(Id.u8) <= @intFromEnum(self) and @intFromEnum(self) <= @intFromEnum(Id.uint);
    }

    pub fn isSigned(self: Id) bool {
        return @intFromEnum(Id.i8) <= @intFromEnum(self) and @intFromEnum(self) <= @intFromEnum(Id.int);
    }

    pub fn data(self: Id) Data {
        const repr: Repr = @bitCast(@intFromEnum(self));
        return switch (repr.tag()) {
            .Builtin => .{ .Builtin = @enumFromInt(repr.data) },
            .Ptr => .{ .Ptr = @as(*const Id, @ptrFromInt(repr.data)).* },
        };
    }

    pub fn size(self: Id) usize {
        return switch (self.data()) {
            .Builtin => |b| switch (b) {
                .never => unreachable,
                .void => 0,
                .u8, .i8, .bool => 1,
                .u16, .i16 => 2,
                .u32, .i32 => 4,
                .uint, .int => 8,
            },
            .Ptr => 8,
        };
    }

    pub fn asDataType(self: Id) graph.DataType {
        return switch (self.data()) {
            .Builtin => |b| switch (b) {
                .never => unreachable,
                .void => unreachable,
                .u8, .i8, .bool => .i8,
                .u16, .i16 => .i16,
                .u32, .i32 => .i32,
                .uint, .int => .int,
            },
            .Ptr => .int,
        };
    }

    pub fn max(lhs: Id, rhs: Id) Id {
        return @enumFromInt(@max(@intFromEnum(lhs), @intFromEnum(rhs)));
    }

    pub fn canUpcast(from: Id, to: Id) bool {
        if (from == .never) return true;
        if (from == to) return true;
        const is_bigger = from.size() < to.size();
        if (from.isUnsigned() and to.isUnsigned()) return is_bigger;
        if (from.isSigned() and to.isSigned()) return is_bigger;
        if (from.isUnsigned() and to.isSigned()) return is_bigger;

        return false;
    }

    pub fn binOpUpcast(lhs: Id, rhs: Id) !Id {
        if (lhs == rhs) return lhs;
        if (lhs.data() == .Ptr and rhs.data() == .Ptr) return .uint;
        if (lhs.data() == .Ptr) return lhs;
        if (rhs.data() == .Ptr) return error.@"pointer must be on the left";

        if (lhs.canUpcast(rhs)) return rhs;
        if (rhs.canUpcast(lhs)) return lhs;

        return error.@"incompatible types";
    }

    pub fn format(self: *const Id, comptime _: anytype, _: anytype, writer: anytype) !void {
        try switch (self.data()) {
            .Ptr => |b| writer.print("^{}", .{b}),
            .Builtin => |b| writer.writeAll(@tagName(b)),
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
    self.interner.deinit(self.arena.child_allocator);
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

pub fn makePtr(self: *Types, v: Id) Id {
    const ptr = Id.init(.Ptr, @intFromPtr(&v));
    const slot = self.interner.getOrPut(self.arena.child_allocator, ptr) catch unreachable;
    if (slot.found_existing) return slot.key_ptr.*;
    const ptr_slot = self.arena.allocator().create(Id) catch unreachable;
    ptr_slot.* = v;
    slot.key_ptr.* = Id.init(.Ptr, @intFromPtr(ptr_slot));
    return slot.key_ptr.*;
}

pub fn resolveTy(self: *Types, file: File, expr: Ast.Id) Id {
    const ast = self.getFile(file);
    return switch (ast.exprs.get(expr)) {
        .Buty => |e| .fromLexeme(e.bt),
        .UnOp => |e| switch (e.op) {
            .@"^" => self.makePtr(self.resolveTy(file, e.oper)),
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
