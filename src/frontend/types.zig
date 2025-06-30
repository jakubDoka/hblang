const root = @import("hb");
const Types = root.frontend.Types;
const Ast = root.frontend.Ast;
const graph = root.backend.graph;
const utils = root.utils;
const TyId = Types.Id;
const std = @import("std");
const Scope = Types.Scope;

pub const Builtin = Types.Id.Builtin;
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
        kind: enum(u2) {
            bool,
            ptr,
            impossible,
            pub fn abi(self: @This()) graph.DataType {
                return switch (self) {
                    .bool => .i8,
                    .ptr => .i64,
                    .impossible => .bot,
                };
            }
        },
        offset: std.meta.Int(.unsigned, @bitSizeOf(u64) - 2),
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
    index: Ast.Index,

    pub const Field = struct {
        name: []const u8,
    };

    pub const Id = enum(u32) {
        _,

        pub const Data = Enum;

        pub fn getFields(id: Id, types: *Types) []const Field {
            const self = types.store.get(id);

            if (self.fields) |f| return f;
            const ast = types.getFile(self.key.loc.file);
            const enum_ast = ast.exprs.getTyped(.Enum, self.key.loc.ast).?;

            var count: usize = 0;
            for (ast.exprs.view(enum_ast.fields)) |f| count += @intFromBool(f.tag() == .Tag);

            const fields = types.pool.arena.alloc(Field, count);
            var i: usize = 0;
            for (ast.exprs.view(enum_ast.fields)) |fast| {
                if (fast.tag() == .Comment) continue;
                if (fast.tag() != .Tag) {
                    if (fast.tag() != .Decl) {
                        types.report(self.key.loc.file, fast, "unexpected item," ++
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
    index: Ast.Index,

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
            const ast = types.getFile(self.key.loc.file);
            const union_ast = ast.exprs.getTyped(.Union, self.key.loc.ast).?;

            var count: usize = 0;
            for (ast.exprs.view(union_ast.fields)) |f| count +=
                @intFromBool(if (ast.exprs.getTyped(.Decl, f)) |b| b.bindings.tag() == .Tag else false);

            const fields = types.pool.arena.alloc(Field, count);
            var i: usize = 0;
            for (ast.exprs.view(union_ast.fields)) |fast| {
                if (fast.tag() == .Comment) continue;
                const field = ast.exprs.getTyped(.Decl, fast) orelse {
                    types.report(self.key.loc.file, fast, "unexpected item," ++
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

    index: Ast.Index,

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
                types.report(self.key.loc.file, self.key.loc.ast, "the struct has infinite size", .{});
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
                types.report(self.key.loc.file, self.key.loc.ast, "the struct has undecidable alignment (cycle)", .{});
                return 1;
            }
            self.recursion_lock = true;
            defer self.recursion_lock = false;

            const ast = types.getFile(self.key.loc.file);
            const struct_ast = ast.exprs.getTyped(.Struct, self.key.loc.ast).?;

            if (struct_ast.alignment.tag() != .Void) {
                if (@hasField(Field, "alignment")) @compileError("assert fields <= alignment then base alignment");
                self.alignment = @bitCast(types.ct.evalIntConst(.{ .Perm = .init(.{ .Struct = id }) }, struct_ast.alignment) catch 1);
                if (self.alignment == 0 or !std.math.isPowerOfTwo(self.alignment.?)) {
                    self = types.store.get(id);
                    types.report(self.key.loc.file, struct_ast.alignment, "the alignment needs to be power of 2, got {}", .{self.alignment.?});
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
            const ast = types.getFile(self.key.loc.file);
            const struct_ast = ast.exprs.getTyped(.Struct, self.key.loc.ast).?;

            var count: usize = 0;
            for (ast.exprs.view(struct_ast.fields)) |f| count += @intFromBool(if (ast.exprs.getTyped(.Decl, f)) |b| b.bindings.tag() == .Tag else false);

            const fields = types.pool.arena.alloc(Field, count);
            var i: usize = 0;
            for (ast.exprs.view(struct_ast.fields)) |fast| {
                if (fast.tag() == .Comment) continue;
                const field = ast.exprs.getTyped(.Decl, fast) orelse {
                    types.report(self.key.loc.file, fast, "unexpected item," ++
                        " only field declarations (.field_name: field_type [= default_value])," ++
                        " and declarations (decl_name := expr)", .{});
                    continue;
                };
                if (field.bindings.tag() != .Tag) continue;
                const name = ast.tokenSrc(ast.exprs.getTyped(.Tag, field.bindings).?.index + 1);
                const ty = types.ct.evalTy("", .{ .Perm = .init(.{ .Struct = id }) }, field.ty) catch .never;
                fields[i] = .{ .name = name, .ty = ty };
                if (field.value.tag() != .Void) {
                    const value = types.store.add(types.pool.allocator(), Global{
                        .key = .{
                            .loc = .{
                                .file = self.key.loc.file,
                                .scope = .init(.{ .Struct = id }),
                                .ast = field.value,
                            },
                            .name = name,
                            .captures = &.{},
                        },
                        .readonly = true,
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
    is_inline: bool = false,
};

pub const Func = struct {
    key: Scope,
    args: []TyId,
    ret: TyId,
    errored: bool = false,
    recursion_lock: bool = false,
    is_inline: bool = false,
    visibility: root.backend.Machine.Data.Linkage = .local,
    special: ?root.backend.Machine.EmitOptions.Special = null,
    completion: std.EnumArray(Types.Target, CompileState) = .{ .values = .{ .queued, .queued } },

    pub const CompileState = enum { queued, compiled };

    pub fn computeAbi(
        self: Func,
        abi: Types.Abi,
        types: *Types,
        scratch: *utils.Arena,
    ) ?struct {
        []const graph.AbiParam,
        ?[]const graph.AbiParam,
        Types.Abi.Spec,
    } {
        errdefer unreachable;
        var builder = abi.builder();

        const max_elems = Types.Abi.Builder.max_elems;

        const ret_abi = @as(Types.Abi.TmpSpec, abi.categorize(self.ret, types))
            .toPerm(self.ret, types);

        var params = scratch.alloc(graph.AbiParam, self.args.len * max_elems + 1);
        var cursor: usize = 0;

        const returns = if (ret_abi != .Impossible)
            if (abi.isByRefRet(ret_abi)) b: {
                cursor += builder.types(params, true, ret_abi).len;
                break :b &.{};
            } else builder.types(scratch.alloc(graph.AbiParam, max_elems), true, ret_abi)
        else
            null;

        for (self.args) |ty| {
            const arg_abi = abi.categorize(ty, types).toPerm(ty, types);
            if (arg_abi == .Impossible) return null;
            cursor += builder.types(params[cursor..], false, arg_abi).len;
        }

        return .{ params[0..cursor], returns, ret_abi };
    }
};

pub const Global = struct {
    key: Scope,
    ty: TyId = .void,
    data: []const u8 = &.{},
    readonly: bool,
    completion: std.EnumArray(Types.Target, CompileState) = .{ .values = .{ .queued, .queued } },

    pub const CompileState = enum { queued, staged, compiled };
};
