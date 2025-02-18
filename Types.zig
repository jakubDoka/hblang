funcs: std.ArrayListUnmanaged(FuncData) = .{},
arena: std.heap.ArenaAllocator,
interner: std.hash_map.HashMapUnmanaged(Id, void, TypeCtx, 70) = .{},
source: []const Ast,

const std = @import("std");
const Ast = @import("parser.zig");
const graph = @import("graph.zig");
const Lexer = @import("Lexer.zig");
const Types = @This();

pub const TypeCtx = struct {
    pub fn eql(_: @This(), a: Id, b: Id) bool {
        const ad, const bd = .{ a.data(), b.data() };
        if (std.meta.fields(@TypeOf(ad.Struct.*)).len != 4) @compileError("maybe we are capturing already");
        if (ad == .Struct and bd == .Struct) {
            return ad.Struct.file == bd.Struct.file and ad.Struct.pos == bd.Struct.pos;
        }

        return std.meta.eql(ad, bd);
    }

    pub fn hash(_: @This(), adapted_key: Id) u64 {
        var hasher = std.hash.Fnv1a_64.init();
        const adk = adapted_key.data();
        if (adk == .Struct) {
            std.hash.autoHashStrat(&hasher, adk.Struct.file, .Deep);
            std.hash.autoHashStrat(&hasher, adk.Struct.pos, .Deep);
        } else {
            std.hash.autoHashStrat(&hasher, adk, .Deep);
        }
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
    Struct: *const Struct,
};

pub const Struct = struct {
    file: File,
    pos: Ast.Pos,
    name: []const u8,
    fields: []const Field,

    pub const Field = struct {
        name: Ast.Pos,
        ty: Id,
    };

    pub fn asTy(self: *const Struct) Id {
        return Id.init(.Struct, @intFromPtr(self));
    }
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

    pub inline fn init(flg: std.meta.Tag(Data), dt: usize) Id {
        comptime {
            std.debug.assert(fromLexeme(.i8) == .i8);
        }
        return @enumFromInt(@as(usize, @bitCast(Repr{ .flag = @intFromEnum(flg), .data = @intCast(dt) })));
    }

    pub fn isInteger(self: Id) bool {
        return self.isUnsigned() or self.isSigned();
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
            .Struct => .{ .Struct = @ptrFromInt(repr.data) },
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
            .Struct => |s| {
                var siz: usize = 0;
                var alignm: usize = 1;
                for (s.fields) |f| {
                    alignm = @max(alignm, f.ty.alignment());
                    siz = std.mem.alignForward(usize, siz, f.ty.alignment());
                    siz += f.ty.size();
                }
                siz = std.mem.alignForward(usize, siz, alignm);
                return siz;
            },
        };
    }

    pub fn alignment(self: Id) usize {
        return switch (self.data()) {
            .Builtin => self.size(),
            .Ptr => 8,
            .Struct => |s| {
                var alignm: usize = 1;
                for (s.fields) |f| {
                    alignm = @max(alignm, f.ty.alignment());
                }
                return alignm;
            },
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
            .Struct => |b| writer.writeAll(b.name),
        };
    }
};

pub const Abi = enum {
    ableos,

    pub const Spec = union(enum) {
        ByValue: graph.DataType,
        ByValuePair: struct {
            types: [2]graph.DataType,
            padding: u16,

            pub fn offsets(self: @This()) [2]usize {
                return .{ 0, self.types[0].size() + self.padding };
            }
        },
        ByRef,
        Imaginary,

        const max_subtypes = 2;

        pub const Field = struct {
            offset: usize = 0,
            dt: graph.DataType,
        };

        const Dts = std.BoundedArray(graph.DataType, max_subtypes);
        const Offs = std.BoundedArray(usize, max_subtypes);

        pub fn types(self: Spec, buf: []graph.DataType) void {
            switch (self) {
                .Imaginary => {},
                .ByValue => |d| buf[0] = d,
                .ByValuePair => |pair| buf[0..2].* = pair.types,
                .ByRef => buf[0] = .int,
            }
        }

        pub fn len(self: Spec, is_ret: bool) usize {
            return switch (self) {
                .Imaginary => 0,
                .ByValue => 1,
                .ByValuePair => 2,
                .ByRef => 1 - @intFromBool(is_ret),
            };
        }
    };

    pub fn categorize(self: Abi, ty: Id) Spec {
        return switch (ty.data()) {
            .Builtin => |b| .{ .ByValue = switch (b) {
                .never => unreachable,
                .void => return .Imaginary,
                .u8, .i8, .bool => .i8,
                .u16, .i16 => .i16,
                .u32, .i32 => .i32,
                .uint, .int => .int,
            } },
            .Ptr => .{ .ByValue = .int },
            .Struct => |s| switch (self) {
                .ableos => categorizeAbleosStruct(s),
            },
        };
    }

    pub fn categorizeAbleosStruct(stru: *const Struct) Spec {
        var res: Spec = .Imaginary;
        var offset: usize = 0;
        for (stru.fields) |f| {
            const fspec = Abi.ableos.categorize(f.ty);
            if (fspec == .Imaginary) continue;
            if (res == .Imaginary) {
                res = fspec;
                offset += f.ty.size();
                continue;
            }

            if (fspec == .ByRef) return fspec;
            if (fspec == .ByValuePair) return .ByRef;
            if (res == .ByValuePair) return .ByRef;
            std.debug.assert(res != .ByRef);

            const off = std.mem.alignForward(usize, offset, f.ty.alignment());
            res = .{ .ByValuePair = .{
                .types = .{ res.ByValue, fspec.ByValue },
                .padding = @intCast(off - offset),
            } };

            offset = off + f.ty.size();
        }
        return res;
    }
};

pub const FuncData = struct {
    args: []Id,
    ret: Id,
    file: File,
    name: Ast.Pos,
    ast: Ast.Id,
    completion: std.EnumArray(Target, CompileState) = .{ .values = .{ .queued, .queued } },

    pub const Target = enum { @"comptime", runtime };
    pub const CompileState = enum { queued, compiled };

    pub fn computeAbiSize(self: FuncData, abi: Abi) struct { usize, usize, Abi.Spec } {
        const ret_abi = abi.categorize(self.ret);
        var param_count: usize = @intFromBool(ret_abi == .ByRef);
        for (self.args) |ty| param_count += abi.categorize(ty).len(false);
        const return_count: usize = ret_abi.len(true);
        return .{ param_count, return_count, ret_abi };
    }
};

pub fn init(gpa: std.mem.Allocator, source: []const Ast) Types {
    return .{
        .source = source,
        .arena = .init(gpa),
    };
}

pub fn deinit(self: *Types) void {
    self.funcs.deinit(self.arena.child_allocator);
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

const Ctx = struct {
    name: []const u8 = &.{},
    file: File,

    pub fn init(fl: File) Ctx {
        return .{ .file = fl };
    }
};

pub fn resolveTy(self: *Types, ctx: Ctx, expr: Ast.Id) Id {
    const ast = self.getFile(ctx.file);
    return switch (ast.exprs.get(expr)) {
        .Buty => |e| .fromLexeme(e.bt),
        .UnOp => |e| switch (e.op) {
            .@"^" => self.makePtr(self.resolveTy(ctx, e.oper)),
            else => std.debug.panic("{any}", .{e.op}),
        },
        .Ident => |e| {
            const decl = ast.decls[e.id.index];
            return self.resolveTy(.{ .file = ctx.file, .name = ast.tokenSrc(decl.name.index) }, ast.exprs.get(decl.expr).BinOp.rhs);
        },
        .Struct => |e| {
            var v: Struct = undefined;
            v.file = ctx.file;
            v.pos = e.pos;
            const stru = Id.init(.Struct, @intFromPtr(&v));
            const slot = self.interner.getOrPut(self.arena.child_allocator, stru) catch unreachable;
            if (slot.found_existing) return slot.key_ptr.*;
            const struct_slot = self.arena.allocator().create(Struct) catch unreachable;
            struct_slot.* = .{
                .file = ctx.file,
                .pos = e.pos,
                .name = ctx.name,
                .fields = b: {
                    const fields = self.arena.allocator().alloc(Struct.Field, e.fields.len()) catch unreachable;
                    for (fields, ast.exprs.view(e.fields)) |*fslot, fast| {
                        const field = ast.exprs.get(fast).CtorField;
                        fslot.* = .{
                            .name = field.pos,
                            .ty = self.resolveTy(.{ .file = ctx.file }, field.value),
                        };
                    }
                    break :b fields;
                },
            };
            slot.key_ptr.* = Id.init(.Struct, @intFromPtr(struct_slot));
            return slot.key_ptr.*;
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
        arg.* = self.resolveTy(.init(file), ty);
    }

    self.funcs.append(self.arena.child_allocator, .{
        .args = args,
        .name = name,
        .file = file,
        .ret = self.resolveTy(.init(file), fn_ast.ret),
        .ast = func,
    }) catch unreachable;

    return @enumFromInt(self.funcs.items.len - 1);
}
