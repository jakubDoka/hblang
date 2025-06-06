const root = @import("hb");
const Types = root.frontend.Types;
const Ast = root.frontend.Ast;
const graph = root.backend.graph;
const utils = root.utils;
const TyId = Types.Id;
const std = @import("std");
const Scope = Types.Scope;

pub const Builtin = enum(Types.IdRepr) {
    never,
    void,
    bool,
    u8,
    u16,
    u32,
    u64,
    uint,
    i8,
    i16,
    i32,
    i64,
    int,
    f32,
    f64,
    type,
    any,

    pub const identity = {};
};

pub const Pointer = TyId;

pub const Slice = struct {
    len: ?usize,
    elem: TyId,

    pub const ptr_offset = 0;
    pub const len_offset = 8;
};

pub const Nullable = struct {
    inner: TyId,
    nieche: enum(u64) {
        unresolved = std.math.maxInt(u64) - 1,
        explicit,
        _,

        pub fn offset(self: *@This(), types: *Types) ?NiecheSpec {
            if (self.* == .unresolved) {
                const nullable: *Nullable = @fieldParentPtr("nieche", self);
                self.* = if (nullable.inner.findNieche(types)) |n| @enumFromInt(@as(u64, @bitCast(n))) else .explicit;
            }

            return switch (self.*) {
                .explicit => null,
                .unresolved => unreachable,
                else => |v| @bitCast(@intFromEnum(v)),
            };
        }
    } = .unresolved,

    pub const Id = enum(u32) {
        _,

        pub const Data = Nullable;

        pub fn isCompact(id: Id, types: *Types) bool {
            const self = types.store.get(id);

            return self.nieche.offset(types) != null;
        }

        pub fn size(id: Id, types: *Types) u64 {
            const self = types.store.get(id);

            return self.inner.size(types) +
                if (id.isCompact(types)) 0 else self.inner.alignment(types);
        }
    };

    pub const NiecheSpec = packed struct(u64) {
        kind: enum(u1) {
            bool,
            ptr,
            pub fn abi(self: @This()) graph.DataType {
                return switch (self) {
                    .bool => .i8,
                    .ptr => .int,
                };
            }
        },
        offset: std.meta.Int(.unsigned, @bitSizeOf(u64) - 1),
    };
};

pub const Tuple = struct {
    fields: []Field,

    pub const Field = struct {
        ty: TyId,
    };

    pub const Id = enum(u32) {
        _,

        pub const Data = Tuple;

        pub fn getFields(id: Id, types: *Types) []Field {
            return types.store.get(id).fields;
        }

        pub fn offsetIter(id: Id, types: *Types) OffIter {
            return .{
                .types = types,
                .fields = getFields(id, types),
            };
        }
    };

    pub const OffIter = struct {
        types: *Types,
        fields: []const Field,
        offset: u64 = 0,

        pub const Elem = struct { field: *const Field, offset: u64 };

        pub fn next(self: *OffIter) ?Elem {
            if (self.fields.len == 0) return null;
            self.offset = std.mem.alignForward(u64, self.offset, self.fields[0].ty.alignment(self.types));
            const elem = Elem{ .field = &self.fields[0], .offset = self.offset };
            self.fields = self.fields[1..];
            self.offset += elem.field.ty.size(self.types);
            return elem;
        }
    };
};

pub const Enum = struct {
    key: Scope,

    fields: ?[]const Field = null,

    pub const Field = struct {
        name: []const u8,
    };

    pub const Id = enum(u32) {
        _,

        pub const Data = Enum;

        pub fn getFields(id: Id, types: *Types) []const Field {
            const self = types.store.get(id);

            if (self.fields) |f| return f;
            const ast = types.getFile(self.key.file);
            const enum_ast = ast.exprs.getTyped(.Enum, self.key.ast).?;

            var count: usize = 0;
            for (ast.exprs.view(enum_ast.fields)) |f| count += @intFromBool(f.tag() == .Tag);

            const fields = types.arena.alloc(Field, count);
            var i: usize = 0;
            for (ast.exprs.view(enum_ast.fields)) |fast| {
                if (fast.tag() == .Comment) continue;
                if (fast.tag() != .Tag) {
                    if (fast.tag() != .Decl) {
                        types.report(self.key.file, fast, "unexpected item," ++
                            " only field declarations (.variant_name)," ++
                            " and declarations (decl_name := expr)", .{});
                    }
                    continue;
                }
                fields[i] = .{ .name = ast.tokenSrc(ast.exprs.getTyped(.Tag, fast).?.index + 1) };
                i += 1;
            }
            self.fields = fields;
            return fields;
        }
    };
};

pub const Union = struct {
    key: Scope,

    fields: ?[]const Field = null,

    pub const Field = struct {
        name: []const u8,
        ty: TyId,
    };

    pub const Id = enum(u32) {
        _,

        pub const Data = Union;

        pub fn getFields(id: Id, types: *Types) []const Field {
            const self: *Union = types.store.get(id);

            if (self.fields) |f| return f;
            const ast = types.getFile(self.key.file);
            const union_ast = ast.exprs.getTyped(.Union, self.key.ast).?;

            var count: usize = 0;
            for (ast.exprs.view(union_ast.fields)) |f| count +=
                @intFromBool(if (ast.exprs.getTyped(.Decl, f)) |b| b.bindings.tag() == .Tag else false);

            const fields = types.arena.alloc(Field, count);
            var i: usize = 0;
            for (ast.exprs.view(union_ast.fields)) |fast| {
                if (fast.tag() == .Comment) continue;
                const field = ast.exprs.getTyped(.Decl, fast) orelse {
                    types.report(self.key.file, fast, "unexpected item," ++
                        " only field declarations (.field_name: field_type)," ++
                        " and declarations (decl_name := expr)", .{});
                    continue;
                };
                if (field.bindings.tag() != .Tag) continue;
                fields[i] = .{
                    .name = ast.tokenSrc(ast.exprs.getTyped(.Tag, field.bindings).?.index + 1),
                    .ty = types.ct.evalTy("", .{ .Perm = .init(.{ .Union = id }) }, field.ty) catch .never,
                };
                i += 1;
            }
            self.fields = fields;
            return fields;
        }
    };
};

pub const Struct = struct {
    key: Scope,

    fields: ?[]const Field = null,
    size: ?u64 = null,
    alignment: ?u64 = null,
    recursion_lock: bool = false,

    pub const Field = struct {
        name: []const u8,
        ty: TyId,
        defalut_value: ?utils.EntId(Global) = null,
    };

    pub const Id = enum(u32) {
        _,

        pub const Data = Struct;

        pub fn getSize(id: Id, types: *Types) u64 {
            var self = types.store.get(id);

            if (self.size) |a| return a;

            const max_alignment = getAlignment(id, types);

            if (self.recursion_lock) {
                types.report(self.key.file, self.key.ast, "the struct has infinite size", .{});
                return 0;
            }
            self.recursion_lock = true;
            defer self.recursion_lock = false;

            if (@hasField(Field, "alignment")) @compileError("");

            var siz: u64 = 0;
            for (id.getFields(types)) |f| {
                siz = std.mem.alignForward(u64, siz, @min(max_alignment, f.ty.alignment(types)));
                siz += f.ty.size(types);
            }
            siz = std.mem.alignForward(u64, siz, max_alignment);

            self = types.store.get(id);
            self.size = siz;
            return siz;
        }

        pub fn getAlignment(id: Id, types: *Types) u64 {
            var self = types.store.get(id);

            if (self.alignment) |a| return a;

            if (self.recursion_lock) {
                types.report(self.key.file, self.key.ast, "the struct has undecidable alignment (cycle)", .{});
                return 1;
            }
            self.recursion_lock = true;
            defer self.recursion_lock = false;

            const ast = types.getFile(self.key.file);
            const struct_ast = ast.exprs.getTyped(.Struct, self.key.ast).?;

            if (struct_ast.alignment.tag() != .Void) {
                if (@hasField(Field, "alignment")) @compileError("assert fields <= alignment then base alignment");
                self.alignment = @bitCast(types.ct.evalIntConst(.{ .Perm = .init(.{ .Struct = id }) }, struct_ast.alignment) catch 1);
                if (self.alignment == 0 or !std.math.isPowerOfTwo(self.alignment.?)) {
                    self = types.store.get(id);
                    types.report(self.key.file, struct_ast.alignment, "the alignment needs to be power of 2, got {}", .{self.alignment.?});
                    self.alignment = 1;
                    return 1;
                }
                return @max(self.alignment.?, 1);
            }

            var alignm: u64 = 1;
            for (id.getFields(types)) |f| {
                alignm = @max(alignm, f.ty.alignment(types));
            }

            self = types.store.get(id);
            self.alignment = alignm;
            return alignm;
        }

        pub const OffIter = struct {
            types: *Types,
            max_align: u64,
            fields: []const Field,
            offset: u64 = 0,

            pub const Elem = struct { field: *const Field, offset: u64 };

            pub fn next(self: *OffIter) ?Elem {
                if (self.fields.len == 0) return null;
                self.offset = std.mem.alignForward(u64, self.offset, @min(self.max_align, self.fields[0].ty.alignment(self.types)));
                const elem = Elem{ .field = &self.fields[0], .offset = self.offset };
                self.fields = self.fields[1..];
                self.offset += elem.field.ty.size(self.types);
                return elem;
            }
        };

        pub fn offsetIter(id: Id, types: *Types) OffIter {
            return .{ .types = types, .fields = getFields(id, types), .max_align = getAlignment(id, types) };
        }

        pub fn getFields(id: Id, types: *Types) []const Field {
            const self = types.store.get(id);

            if (self.fields) |f| return f;
            const ast = types.getFile(self.key.file);
            const struct_ast = ast.exprs.getTyped(.Struct, self.key.ast).?;

            var count: usize = 0;
            for (ast.exprs.view(struct_ast.fields)) |f| count += @intFromBool(if (ast.exprs.getTyped(.Decl, f)) |b| b.bindings.tag() == .Tag else false);

            const fields = types.arena.alloc(Field, count);
            var i: usize = 0;
            for (ast.exprs.view(struct_ast.fields)) |fast| {
                if (fast.tag() == .Comment) continue;
                const field = ast.exprs.getTyped(.Decl, fast) orelse {
                    types.report(self.key.file, fast, "unexpected item," ++
                        " only field declarations (.field_name: field_type [= default_value])," ++
                        " and declarations (decl_name := expr)", .{});
                    continue;
                };
                if (field.bindings.tag() != .Tag) continue;
                const name = ast.tokenSrc(ast.exprs.getTyped(.Tag, field.bindings).?.index + 1);
                const ty = types.ct.evalTy("", .{ .Perm = .init(.{ .Struct = id }) }, field.ty) catch .never;
                fields[i] = .{ .name = name, .ty = ty };
                if (field.value.tag() != .Void) {
                    const value = types.store.add(types.arena.allocator(), Global{
                        .key = .{
                            .file = self.key.file,
                            .name = name,
                            .scope = .init(.{ .Struct = id }),
                            .ast = field.value,
                            .captures = &.{},
                        },
                    });

                    types.ct.evalGlobal(name, value, ty, field.value) catch {};

                    fields[i].defalut_value = value;
                }
                i += 1;
            }
            self.fields = fields;
            return fields;
        }
    };
};

pub const Template = struct {
    key: Scope,
    temporary: bool = false,
};

pub const Func = struct {
    key: Scope,
    args: []TyId,
    ret: TyId,
    errored: bool = false,
    recursion_lock: bool = false,
    visibility: root.backend.Machine.Data.Linkage = .local,
    completion: std.EnumArray(Types.Target, CompileState) = .{ .values = .{ .queued, .queued } },

    pub const CompileState = enum { queued, compiled };

    pub fn computeAbiSize(self: Func, abi: Types.Abi, types: *Types) struct { usize, usize, Types.Abi.Spec } {
        const ret_abi = @as(Types.Abi.TmpSpec, abi.categorize(self.ret, types) orelse .Imaginary)
            .toPerm(self.ret, types);
        var param_count: usize = @intFromBool(ret_abi.isByRefRet(abi));
        for (self.args) |ty| param_count += (abi.categorize(ty, types) orelse continue)
            .toPerm(self.ret, types).len(false, abi);
        const return_count: usize = ret_abi.len(true, abi);
        return .{ param_count, return_count, ret_abi };
    }
};

pub const Global = struct {
    key: Scope,
    ty: TyId = .void,
    data: []const u8 = &.{},
    completion: std.EnumArray(Types.Target, CompileState) = .{ .values = .{ .queued, .queued } },

    pub const CompileState = enum { queued, staged, compiled };
};
