next_struct: u32 = 0,
funcs: std.ArrayListUnmanaged(*Func) = .{},
next_global: u32 = 0,
arena: Arena,
interner: Map = .{},
file_scopes: []Id,
ct: Comptime,
diagnostics: std.io.AnyWriter,
files: []const Ast,

const std = @import("std");
const Ast = @import("Ast.zig");
const Arena = @import("utils.zig").Arena;
const Codegen = @import("Codegen.zig");
const Comptime = @import("Comptime.zig");
const graph = @import("graph.zig");
const Lexer = @import("Lexer.zig");
const HbvmGen = @import("HbvmGen.zig");
const Vm = @import("Vm.zig");
const Types = @This();
const Map = std.hash_map.HashMapUnmanaged(Id, void, TypeCtx, 70);

pub const TypeCtx = struct {
    pub fn eql(_: @This(), a: Id, b: Id) bool {
        const ad, const bd = .{ a.data(), b.data() };
        if (std.meta.activeTag(ad) != std.meta.activeTag(bd)) return false;

        return switch (ad) {
            .Builtin => std.meta.eql(ad, bd),
            inline .Ptr, .Nullable, .Slice => |v, t| std.meta.eql(v.*, @field(bd, @tagName(t)).*),
            .Tuple => |v| std.mem.eql(Id, @ptrCast(v.fields), @ptrCast(bd.Tuple.fields)),
            inline else => |v, t| return v.key.eql(@field(bd, @tagName(t)).key),
        };
    }

    pub fn hash(_: @This(), adapted_key: Id) u64 {
        var hasher = std.hash.Fnv1a_64.init();
        const adk = adapted_key.data();
        switch (adk) {
            inline .Builtin, .Ptr, .Slice, .Nullable, .Tuple => |v| std.hash.autoHashStrat(&hasher, v, .Deep),
            inline else => |v| std.hash.autoHashStrat(&hasher, v.key, .Deep),
        }
        return hasher.final();
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
    Ptr: *Id,
    Slice: *Slice,
    Nullable: *Id,
    Tuple: *Tuple,
    Enum: *Enum,
    Union: *Union,
    Struct: *Struct,
    Template: *Template,
    Func: *Func,
    Global: *Global,
};

pub const Key = struct {
    file: File,
    scope: Id,
    ast: Ast.Id,
    name: []const u8,
    captures: []const Capture,

    pub const Capture = struct {
        id: Ast.Ident,
        ty: Id,
        value: u64 = 0,
    };

    pub const dummy = Key{
        .file = .root,
        .scope = .void,
        .ast = .zeroSized(.Void),
        .name = "",
        .captures = &.{},
    };

    pub fn eql(self: Key, other: Key) bool {
        return self.file == other.file and self.scope == other.scope and self.ast == other.ast and
            self.captures.len == other.captures.len and
            for (self.captures, other.captures) |a, b|
        {
            if (!std.meta.eql(a, b)) return false;
        } else true;
    }
};

pub const Slice = struct {
    len: ?usize,
    elem: Id,

    pub const ptr_offset = 0;
    pub const len_offset = 8;
};

pub const Tuple = struct {
    fields: []Field,

    pub const Field = struct {
        ty: Id,
    };

    pub fn getFields(self: *Tuple, _: anytype) []Field {
        return self.fields;
    }
};

pub const Enum = struct {
    key: Key,

    fields: ?[]const Field = null,

    pub const Field = struct {
        name: []const u8,
    };

    pub fn asTy(self: *Enum) Id {
        return Id.init(.{ .Enum = self });
    }

    pub fn getFields(self: *Enum, types: *Types) []const Field {
        if (self.fields) |f| return f;
        const ast = types.getFile(self.key.file);
        const enum_ast = ast.exprs.get(self.key.ast).Enum;

        var count: usize = 0;
        for (ast.exprs.view(enum_ast.fields)) |f| count += @intFromBool(f.tag() == .Tag);

        const fields = types.arena.alloc(Field, count);
        var i: usize = 0;
        for (ast.exprs.view(enum_ast.fields)) |fast| {
            if (fast.tag() != .Tag) continue;
            fields[i] = .{ .name = ast.tokenSrc(ast.exprs.get(fast).Tag.index + 1) };
            i += 1;
        }
        self.fields = fields;
        return fields;
    }
};

pub const Union = struct {
    key: Key,

    fields: ?[]const Field = null,
    size: ?usize = null,
    alignment: ?usize = null,

    pub const Field = struct {
        name: []const u8,
        ty: Id,
    };

    pub fn asTy(self: *Union) Id {
        return Id.init(.{ .Union = self });
    }

    pub fn getFields(self: *Union, types: *Types) []const Field {
        if (self.fields) |f| return f;
        const ast = types.getFile(self.key.file);
        const union_ast = ast.exprs.get(self.key.ast).Union;

        var count: usize = 0;
        for (ast.exprs.view(union_ast.fields)) |f| count += @intFromBool(if (ast.exprs.getTyped(.BinOp, f)) |b| b.lhs.tag() == .Tag else false);

        const fields = types.arena.alloc(Field, count);
        var i: usize = 0;
        for (ast.exprs.view(union_ast.fields)) |fast| {
            const field = ast.exprs.getTyped(.BinOp, fast) orelse continue;
            if (field.lhs.tag() != .Tag) continue;
            fields[i] = .{
                .name = ast.tokenSrc(ast.exprs.get(field.lhs).Tag.index + 1),
                .ty = types.ct.evalTy("", .{ .Perm = self.asTy() }, field.rhs) catch .never,
            };
            i += 1;
        }
        self.fields = fields;
        return fields;
    }
};

pub const Struct = struct {
    key: Key,

    fields: ?[]const Field = null,
    size: ?usize = null,
    alignment: ?usize = null,

    pub const Field = struct {
        name: []const u8,
        ty: Id,
        defalut_value: ?*Global = null,
    };

    pub fn asTy(self: *Struct) Id {
        return Id.init(.{ .Struct = self });
    }

    pub fn getSize(self: *Struct, types: *Types) usize {
        if (self.size) |a| return a;

        if (@hasField(Field, "alignment")) @compileError("");
        const max_alignment = self.getAlignment(types);

        var siz: usize = 0;
        for (self.getFields(types)) |f| {
            siz = std.mem.alignForward(usize, siz, @min(max_alignment, f.ty.alignment(types)));
            siz += f.ty.size(types);
        }
        siz = std.mem.alignForward(usize, siz, max_alignment);
        return siz;
    }

    pub fn getAlignment(self: *Struct, types: *Types) usize {
        if (self.alignment) |a| return a;

        const ast = types.getFile(self.key.file);
        const struct_ast = ast.exprs.get(self.key.ast).Struct;

        if (struct_ast.alignment.tag() != .Void) {
            if (@hasField(Field, "alignment")) @compileError("assert fields <= alignment then base alignment");
            self.alignment = @bitCast(types.ct.evalIntConst(.{ .Perm = self.asTy() }, struct_ast.alignment) catch 1);
            return self.alignment.?;
        }

        var alignm: usize = 1;
        for (self.getFields(types)) |f| {
            alignm = @max(alignm, f.ty.alignment(types));
        }
        return alignm;
    }

    pub fn getFields(self: *Struct, types: *Types) []const Field {
        if (self.fields) |f| return f;
        const ast = types.getFile(self.key.file);
        const struct_ast = ast.exprs.get(self.key.ast).Struct;

        var count: usize = 0;
        for (ast.exprs.view(struct_ast.fields)) |f| count += @intFromBool(if (ast.exprs.getTyped(.BinOp, f)) |b| b.lhs.tag() == .Tag else false);

        const fields = types.arena.alloc(Field, count);
        var i: usize = 0;
        for (ast.exprs.view(struct_ast.fields)) |fast| {
            const field = ast.exprs.getTyped(.BinOp, fast) orelse continue;
            if (field.lhs.tag() != .Tag) continue;
            if (field.rhs.tag() == .BinOp and ast.exprs.get(field.rhs).BinOp.op == .@"=") {
                const field_meta = ast.exprs.get(field.rhs).BinOp;
                const name = ast.tokenSrc(ast.exprs.get(field.lhs).Tag.index + 1);
                const ty = types.ct.evalTy("", .{ .Perm = self.asTy() }, field_meta.lhs) catch .never;

                const value = types.arena.create(Global);
                value.* = .{
                    .id = types.next_global,
                    .key = .{
                        .file = self.key.file,
                        .name = name,
                        .scope = self.asTy(),
                        .ast = field_meta.rhs,
                        .captures = &.{},
                    },
                };
                types.ct.evalGlobal(name, value, ty, field_meta.rhs) catch {};
                types.next_global += 1;

                fields[i] = .{ .name = name, .ty = ty, .defalut_value = value };
            } else {
                fields[i] = .{
                    .name = ast.tokenSrc(ast.exprs.get(field.lhs).Tag.index + 1),
                    .ty = types.ct.evalTy("", .{ .Perm = self.asTy() }, field.rhs) catch .never,
                };
            }
            i += 1;
        }
        self.fields = fields;
        return fields;
    }
};

pub const Template = struct {
    key: Key,
};

pub const Func = struct {
    key: Key,
    id: u32,
    args: []Id,
    ret: Id,
    completion: std.EnumArray(Target, CompileState) = .{ .values = .{ .queued, .queued } },

    pub const CompileState = enum { queued, compiled };

    pub fn computeAbiSize(self: Func, abi: Abi, types: *Types) struct { usize, usize, Abi.Spec } {
        const ret_abi = abi.categorize(self.ret, types);
        var param_count: usize = @intFromBool(ret_abi == .ByRef);
        for (self.args) |ty| param_count += abi.categorize(ty, types).len(false);
        const return_count: usize = ret_abi.len(true);
        return .{ param_count, return_count, ret_abi };
    }
};

pub const Global = struct {
    // captures are extra but whatever for now
    key: Key,
    id: u32,
    ty: Id = .void,
    data: []const u8 = &.{},
    completion: std.EnumArray(Target, CompileState) = .{ .values = .{ .queued, .queued } },

    pub const CompileState = enum { queued, staged, compiled };
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
    type,
    any,
    _,

    const Repr = packed struct(usize) {
        data: std.meta.Int(.unsigned, @bitSizeOf(usize) - @bitSizeOf(std.meta.Tag(Data))),
        flag: std.meta.Tag(std.meta.Tag(Data)),

        inline fn tag(self: Repr) std.meta.Tag(Data) {
            return @enumFromInt(self.flag);
        }
    };

    pub fn fromLexeme(lexeme: Lexer.Lexeme.Type) Id {
        comptime {
            std.debug.assert(@intFromEnum(Lexer.Lexeme.Type.never) == @intFromEnum(Id.never));
        }
        return @enumFromInt(@intFromEnum(lexeme));
    }

    pub inline fn init(dt: Data) Id {
        return @enumFromInt(@as(u64, @bitCast(Repr{
            .flag = @intFromEnum(dt),
            .data = @intCast(switch (dt) {
                .Builtin => |b| @intFromEnum(b),
                inline else => |b| @intFromPtr(b),
            }),
        })));
    }

    pub fn file(self: Id) ?File {
        return switch (self.data()) {
            .Builtin, .Ptr, .Slice, .Nullable, .Tuple => null,
            inline else => |v| v.key.file,
        };
    }

    pub fn items(self: Id, ast: *const Ast) Ast.Slice {
        return switch (self.data()) {
            .Global, .Builtin, .Ptr, .Slice, .Nullable, .Tuple => std.debug.panic("{s}", .{@tagName(self.data())}),
            .Template, .Func => .{},
            inline else => |v, t| @field(ast.exprs.get(v.key.ast), @tagName(t)).fields,
        };
    }

    pub fn captures(self: Id) []const Key.Capture {
        return switch (self.data()) {
            .Global, .Builtin, .Ptr, .Slice, .Nullable, .Tuple => std.debug.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| v.key.captures,
        };
    }

    pub fn findCapture(self: Id, id: Ast.Ident) ?Key.Capture {
        return switch (self.data()) {
            .Global, .Builtin, .Ptr, .Slice, .Nullable, .Tuple => std.debug.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| for (v.key.captures) |cp| {
                if (cp.id == id) break cp;
            } else null,
        };
    }

    pub fn parent(self: Id) Id {
        return switch (self.data()) {
            .Global, .Builtin, .Ptr, .Slice, .Nullable, .Tuple => std.debug.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| v.key.scope,
        };
    }

    pub fn isBinaryOperand(self: Id) bool {
        return switch (self.data()) {
            .Builtin => self.isInteger() or self == .bool,
            .Struct, .Ptr, .Enum => true,
            .Global, .Func, .Template, .Slice, .Nullable, .Union, .Tuple => false,
        };
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
            inline else => |t| @unionInit(Data, @tagName(t), @ptrFromInt(repr.data)),
        };
    }

    pub fn child(self: Id, _: *Types) ?Id {
        return switch (self.data()) {
            .Ptr => |p| p.*,
            .Slice => |s| s.elem,
            else => null,
        };
    }

    pub fn len(self: Id, types: *Types) ?usize {
        return switch (self.data()) {
            inline .Struct, .Union => |s| s.getFields(types).len,
            .Slice => |s| s.len,
            else => null,
        };
    }

    pub fn size(self: Id, types: *Types) usize {
        return switch (self.data()) {
            .Builtin => |b| switch (b) {
                .never, .any => 0,
                .void => 0,
                .u8, .i8, .bool => 1,
                .u16, .i16 => 2,
                .u32, .i32 => 4,
                .uint, .int, .type => 8,
            },
            .Ptr => 8,
            .Enum => |e| {
                const var_count = e.getFields(types).len;
                return std.math.ceilPowerOfTwo(usize, std.mem.alignForward(usize, std.math.log2_int(usize, var_count), 8) / 8) catch unreachable;
            },
            .Tuple => |t| {
                var total_size: usize = 0;
                var alignm: usize = 1;
                for (t.fields) |f| {
                    alignm = @max(alignm, f.ty.alignment(types));
                    total_size = std.mem.alignForward(usize, total_size, f.ty.alignment(types));
                    total_size += f.ty.size(types);
                }
                total_size = std.mem.alignForward(usize, total_size, alignm);
                return total_size;
            },
            .Union => |u| {
                var max_size: usize = 0;
                var alignm: usize = 1;
                for (u.getFields(types)) |f| {
                    alignm = @max(alignm, f.ty.alignment(types));
                    max_size = @max(max_size, f.ty.size(types));
                }
                max_size = std.mem.alignForward(usize, max_size, alignm);
                return max_size;
            },
            .Struct => |s| s.getSize(types),
            .Slice => |s| if (s.len) |l| l * s.elem.size(types) else 16,
            .Nullable => |n| n.alignment(types) + n.size(types),
            .Global, .Func, .Template => 0,
        };
    }

    pub fn alignment(self: Id, types: *Types) usize {
        return switch (self.data()) {
            .Builtin, .Enum => @max(1, self.size(types)),
            .Ptr => 8,
            .Nullable => |n| n.alignment(types),
            .Struct => |s| s.getAlignment(types),
            inline .Union, .Tuple => |s| {
                var alignm: usize = 1;
                for (s.getFields(types)) |f| {
                    alignm = @max(alignm, f.ty.alignment(types));
                }
                return alignm;
            },
            .Slice => |s| if (s.len == null) 8 else s.elem.alignment(types),
            .Global, .Func, .Template => 1,
        };
    }

    pub fn max(lhs: Id, rhs: Id) Id {
        return @enumFromInt(@max(@intFromEnum(lhs), @intFromEnum(rhs)));
    }

    pub fn canUpcast(from: Id, to: Id, types: *Types) bool {
        if (from == .never) return true;
        if (from == to) return true;
        const is_bigger = from.size(types) < to.size(types);
        if (from.isUnsigned() and to.isUnsigned()) return is_bigger;
        if (from.isSigned() and to.isSigned()) return is_bigger;
        if (from.isUnsigned() and to.isSigned()) return is_bigger;
        if (from.data() == .Enum and to.isUnsigned()) return from.size(types) <= to.size(types);
        if (from.data() == .Enum and to.isSigned()) return is_bigger;
        if (from == .bool and to.isInteger()) return true;

        return false;
    }

    pub fn binOpUpcast(lhs: Id, rhs: Id, types: *Types) !Id {
        if (lhs == rhs) return lhs;
        if (lhs.data() == .Ptr and rhs.data() == .Ptr) return .uint;
        if (lhs.data() == .Ptr) return lhs;
        if (rhs.data() == .Ptr) return error.@"pointer must be on the left";

        if (lhs.canUpcast(rhs, types)) return rhs;
        if (rhs.canUpcast(lhs, types)) return lhs;

        return error.@"incompatible types";
    }

    pub const Fmt = struct {
        self: Id,
        tys: *Types,

        pub fn format(self: *const Fmt, comptime opts: []const u8, _: anytype, writer: anytype) !void {
            try switch (self.self.data()) {
                .Ptr => |b| writer.print("^{" ++ opts ++ "}", .{b.fmt(self.tys)}),
                .Nullable => |b| writer.print("?{" ++ opts ++ "}", .{b.fmt(self.tys)}),
                .Slice => |b| {
                    try writer.writeAll("[");
                    if (b.len) |l| try writer.print("{d}", .{l});
                    try writer.writeAll("]");
                    try writer.print("{" ++ opts ++ "}", .{b.elem.fmt(self.tys)});
                    return;
                },
                .Tuple => |b| {
                    try writer.writeAll("(");
                    for (b.fields, 0..) |f, i| {
                        if (i != 0) try writer.writeAll(", ");
                        try writer.print("{" ++ opts ++ "}", .{f.ty.fmt(self.tys)});
                    }
                    try writer.writeAll(")");
                    return;
                },
                .Builtin => |b| writer.writeAll(@tagName(b)),
                inline .Func, .Global, .Template, .Struct, .Union, .Enum => |b| {
                    if (b.key.scope != .void) {
                        try writer.print("{" ++ opts ++ "}", .{b.key.scope.fmt(self.tys)});
                    }
                    if (b.key.name.len != 0) {
                        if (b.key.scope != .void and (b.key.scope.data() != .Struct or b.key.scope.data().Struct.key.scope != .void or
                            comptime !std.mem.eql(u8, opts, "test"))) try writer.writeAll(".");
                        if (b.key.scope != .void) {
                            try writer.print("{s}", .{b.key.name});
                        } else {
                            if (comptime !std.mem.eql(u8, opts, "test")) {
                                try writer.print("\"{s}\"", .{b.key.name});
                            }
                        }
                    }
                    if (b.key.captures.len != 0) {
                        var written_paren = false;
                        o: for (b.key.captures) |capture| {
                            var cursor = b.key.scope;
                            while (cursor != .void and cursor.data() != .Ptr and cursor.data() != .Builtin) {
                                if (cursor.findCapture(capture.id) != null) continue :o;
                                cursor = cursor.parent();
                            }

                            if (written_paren) try writer.writeAll(", ");
                            if (!written_paren) {
                                try writer.writeAll("(");
                                written_paren = true;
                            }
                            const finty: Types.Id = if (capture.ty == .type) @enumFromInt(capture.value) else capture.ty;
                            const op = if (capture.ty == .type) " =" else ":";
                            try writer.print(
                                "{s}{s} {" ++ opts ++ "}",
                                .{ self.tys.getFile(b.key.file).tokenSrc(capture.id.pos()), op, finty.fmt(self.tys) },
                            );
                        }
                        if (written_paren) try writer.writeAll(")");
                    }
                    return;
                },
            };
        }
    };

    pub fn fmt(self: Id, tys: *Types) Fmt {
        return .{ .self = self, .tys = tys };
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

    pub fn categorize(self: Abi, ty: Id, types: *Types) Spec {
        return switch (ty.data()) {
            .Builtin => |b| .{ .ByValue = switch (b) {
                .never, .any => .bot,
                .void => return .Imaginary,
                .u8, .i8, .bool => .i8,
                .u16, .i16 => .i16,
                .u32, .i32 => .i32,
                .uint, .int, .type => .int,
            } },
            .Ptr => .{ .ByValue = .int },
            .Enum => .{ .ByValue = switch (ty.size(types)) {
                0 => return .Imaginary,
                1 => .i8,
                2 => .i16,
                4 => .i32,
                8 => .int,
                else => unreachable,
            } },
            .Union => |s| switch (self) {
                .ableos => categorizeAbleosUnion(s, types),
            },
            inline .Struct, .Tuple => |s| switch (self) {
                .ableos => categorizeAbleosRecord(s, types),
            },
            .Slice => |s| switch (self) {
                .ableos => categorizeAbleosSlice(s, types),
            },
            .Nullable => |n| switch (self) {
                .ableos => categorizeAbleosNullable(n, types),
            },
            .Global, .Func, .Template => .Imaginary,
        };
    }

    pub fn categorizeAbleosNullable(nullable: *Id, types: *Types) Spec {
        const base_abi = Abi.ableos.categorize(nullable.*, types);
        if (base_abi == .Imaginary) return .{ .ByValue = .i8 };
        if (base_abi == .ByValue) return .{ .ByValuePair = .{
            .types = .{ .i8, base_abi.ByValue },
            .padding = @intCast(base_abi.ByValue.size() - 1),
        } };
        return .ByRef;
    }

    pub fn categorizeAbleosSlice(slice: *Slice, types: *Types) Spec {
        if (slice.len == null) return .{ .ByValuePair = .{ .types = .{ .int, .int }, .padding = 0 } };
        if (slice.len == 0) return .Imaginary;
        const elem_abi = Abi.ableos.categorize(slice.elem, types);
        if (elem_abi == .Imaginary) return .Imaginary;
        if (slice.len == 1) return elem_abi;
        if (slice.len == 2 and elem_abi == .ByValue) return .{ .ByValuePair = .{ .types = .{elem_abi.ByValue} ** 2, .padding = 0 } };
        return .ByRef;
    }

    pub fn categorizeAbleosUnion(unio: *Union, types: *Types) Spec {
        const fields = unio.getFields(types);
        if (fields.len == 0) return .Imaginary; // TODO: add .Impossible
        const res = Abi.ableos.categorize(fields[0].ty, types);
        for (fields[1..]) |f| {
            const fspec = Abi.ableos.categorize(f.ty, types);
            if (!std.meta.eql(res, fspec)) return .ByRef;
        }
        return res;
    }

    pub fn categorizeAbleosRecord(stru: anytype, types: *Types) Spec {
        var res: Spec = .Imaginary;
        var offset: usize = 0;
        for (stru.getFields(types)) |f| {
            const fspec = Abi.ableos.categorize(f.ty, types);
            if (fspec == .Imaginary) continue;
            if (res == .Imaginary) {
                res = fspec;
                offset += f.ty.size(types);
                continue;
            }

            if (fspec == .ByRef) return fspec;
            if (fspec == .ByValuePair) return .ByRef;
            if (res == .ByValuePair) return .ByRef;
            std.debug.assert(res != .ByRef);

            const off = std.mem.alignForward(usize, offset, f.ty.alignment(types));
            res = .{ .ByValuePair = .{
                .types = .{ res.ByValue, fspec.ByValue },
                .padding = @intCast(off - offset),
            } };

            offset = off + f.ty.size(types);
        }
        return res;
    }
};

pub const Target = enum { @"comptime", runtime };

pub fn init(gpa: std.mem.Allocator, source: []const Ast, diagnostics: std.io.AnyWriter) Types {
    var arena = Arena.init(1024 * 1024);
    const scopes = arena.alloc(Id, source.len);
    @memset(scopes, .void);
    return .{
        .files = source,
        .file_scopes = scopes,
        .arena = arena,
        .ct = .init(gpa),
        .diagnostics = diagnostics,
    };
}

pub fn deinit(self: *Types) void {
    self.arena.deinit();
    self.ct.in_progress.deinit(self.ct.comptime_code.out.allocator);
    self.ct.comptime_code.out.deinit();
    self.ct.comptime_code.deinit();
    self.* = undefined;
}

pub fn report(self: *Types, file_id: File, expr: anytype, comptime fmt: []const u8, args: anytype) void {
    const file = self.getFile(file_id);
    const line, const col = Ast.lineCol(file.source, file.posOf(expr).index);

    const RemapedArgs = comptime b: {
        var tupl = @typeInfo(@TypeOf(args)).@"struct";
        var fields = tupl.fields[0..tupl.fields.len].*;
        for (&fields) |*f| if (f.type == Types.Id) {
            f.type = Types.Id.Fmt;
        };
        tupl.fields = &fields;
        break :b @Type(.{ .@"struct" = tupl });
    };

    var rargs: RemapedArgs = undefined;
    inline for (args, 0..) |v, i| {
        if (@TypeOf(v) == Types.Id) {
            rargs[i] = v.fmt(self);
        } else {
            rargs[i] = v;
        }
    }
    self.diagnostics.print(
        "{s}:{}:{}: " ++ fmt ++ "\n{}\n",
        .{ file.path, line, col } ++ rargs ++ .{file.codePointer(file.posOf(expr).index)},
    ) catch unreachable;
}

pub fn getAst(self: *Types, file: File, expr: Ast.Id) Ast.Expr {
    return self.getFile(file).exprs.get(expr);
}

pub fn getFile(self: *Types, file: File) *const Ast {
    return &self.files[@intFromEnum(file)];
}

pub fn getScope(self: *Types, file: File) Id {
    if (self.file_scopes[@intFromEnum(file)] == .void) {
        self.file_scopes[@intFromEnum(file)] = self.resolveFielded(
            .Struct,
            .void,
            file,
            self.getFile(file).path,
            self.getFile(file).root_struct,
            &.{},
        );
    }

    return self.file_scopes[@intFromEnum(file)];
}

pub fn internPtr(self: *Types, comptime tag: std.meta.Tag(Data), payload: std.meta.Child(std.meta.TagPayload(Data, tag))) Id {
    var vl = payload;
    const id = Id.init(@unionInit(Data, @tagName(tag), &vl));
    const slot = self.interner.getOrPut(self.arena.allocator(), id) catch unreachable;
    if (slot.found_existing) return slot.key_ptr.*;
    const alloc = self.arena.create(@TypeOf(payload));
    if (@TypeOf(payload) == Tuple) {
        alloc.fields = self.arena.dupe(Tuple.Field, payload.fields);
    } else alloc.* = payload;
    slot.key_ptr.* = .init(@unionInit(Data, @tagName(tag), alloc));
    return slot.key_ptr.*;
}

pub fn makeSlice(self: *Types, len: ?usize, elem: Id) Id {
    return self.internPtr(.Slice, .{ .len = len, .elem = elem });
}

pub fn makePtr(self: *Types, v: Id) Id {
    return self.internPtr(.Ptr, v);
}

pub fn makeNullable(self: *Types, v: Id) Id {
    return self.internPtr(.Nullable, v);
}

pub fn makeTuple(self: *Types, v: []Id) Id {
    return self.internPtr(.Tuple, .{ .fields = @ptrCast(v) });
}

pub fn intern(self: *Types, comptime kind: std.meta.Tag(Data), key: Key) struct { Map.GetOrPutResult, std.meta.TagPayload(Data, kind) } {
    var ty: std.meta.Child(std.meta.TagPayload(Data, kind)) = undefined;
    ty.key = key;
    const id = Id.init(@unionInit(Data, @tagName(kind), &ty));
    const slot = self.interner.getOrPut(self.arena.allocator(), id) catch unreachable;
    if (slot.found_existing) {
        std.debug.assert(slot.key_ptr.data() == kind);
        return .{ slot, @field(slot.key_ptr.data(), @tagName(kind)) };
    }
    const alloc = self.arena.create(@TypeOf(ty));
    alloc.* = ty;
    slot.key_ptr.* = Id.init(@unionInit(Data, @tagName(kind), alloc));
    return .{ slot, alloc };
}

pub fn resolveFielded(
    self: *Types,
    comptime tag: std.meta.Tag(Data),
    scope: Id,
    file: File,
    name: []const u8,
    ast: Ast.Id,
    captures: []const Key.Capture,
) Id {
    const slot, const alloc = self.intern(tag, .{
        .scope = scope,
        .file = file,
        .ast = ast,
        .name = name,
        .captures = captures,
    });
    if (!slot.found_existing) {
        alloc.* = .{
            .key = alloc.key,
        };
    }
    return slot.key_ptr.*;
}

pub fn resolveGlobal(self: *Types, scope: Id, name: []const u8, ast: Ast.Id) struct { Id, bool } {
    const slot, const alloc = self.intern(.Global, .{
        .scope = scope,
        .file = scope.file().?,
        .ast = ast,
        .name = name,
        .captures = &.{},
    });
    if (!slot.found_existing) {
        alloc.* = .{
            .key = alloc.key,
            .id = self.next_global,
        };
        self.next_global += 1;
    }
    return .{ slot.key_ptr.*, !slot.found_existing };
}
