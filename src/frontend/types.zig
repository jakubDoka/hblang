const root = @import("hb");
const Types = root.frontend.Types;
const Comptime = root.frontend.Comptime;
const Ast = root.frontend.Ast;
const graph = root.backend.graph;
const Abi = root.frontend.Abi;
const utils = root.utils;
const TyId = Types.Id;
const std = @import("std");
const Scope = Types.Scope;

pub const Builtin = Types.Id.Builtin;
pub const Pointer = TyId;

pub const Slice = extern struct {
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

        pub fn get(self: @This(), cont: anytype) *Data {
            return cont.store.get(self);
        }

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

        pub fn get(self: @This(), cont: anytype) *Data {
            return cont.store.get(self);
        }

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

    backing_int: ?TyId = null,
    fields: ?[]const Field = null,
    index: Ast.Index,

    pub const Field = struct {
        name: []const u8,
        value: i64,
    };

    pub const Id = enum(u32) {
        _,

        pub const Data = Enum;

        pub fn get(self: @This(), cont: anytype) *Data {
            return cont.store.get(self);
        }

        pub const getFields = Enum.getFields;
        pub const getBackingInt = Enum.getBackingInt;

        pub fn deepEqual(lsh: Id, types: *Types, rhs: Id) bool {
            const lhs_data: *Enum = types.store.get(lsh);
            const rhs_data: *Enum = types.store.get(rhs);

            if (!lhs_data.key.eql(rhs_data.key)) return false;

            if (lhs_data.backing_int != rhs_data.backing_int) return false;

            for (lhs_data.fields.?, rhs_data.fields.?) |lhsf, rhsf| {
                if (!std.mem.eql(u8, lhsf.name, rhsf.name)) return false;
                if (lhsf.value != rhsf.value) return false;
            }

            return true;
        }

        pub fn deepHash(id: Id, types: *Types, hasher: anytype) void {
            const data: *Enum = types.store.get(id);

            data.key.hash(hasher);

            std.hash.autoHash(hasher, data.backing_int);

            for (data.fields.?) |f| {
                hasher.update(f.name);
                std.hash.autoHash(hasher, f.value);
            }
        }
    };

    pub fn getBackingInt(id: Id, types: *Types) TyId {
        if (types.store.get(id).backing_int) |b| return b;
        _ = id.getFields(types);
        return types.store.get(id).backing_int.?;
    }

    pub fn getFields(id: Id, types: *Types) []const Field {
        const self: *Enum = types.store.get(id);

        if (self.fields) |f| return f;

        const ast = types.getFile(self.key.loc.file);
        const enum_ast = ast.exprs.get(self.key.loc.ast).Type;

        self.backing_int = if (enum_ast.tag.tag() != .Void)
            types.ct.evalTy("", .{ .Perm = .init(.{ .Enum = id }) }, enum_ast.tag) catch null
        else
            null;

        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        var fields = std.ArrayListUnmanaged(Field){};

        var value: i64 = 0;
        for (ast.exprs.view(enum_ast.fields)) |fast| {
            if (fast.tag() == .Comment) continue;
            const name = b: switch (ast.exprs.get(fast)) {
                .Tag => |t| {
                    break :b ast.tokenSrc(t.index + 1);
                },
                .Decl => |d| {
                    if (d.bindings.tag() == .Tag) {
                        const t = ast.exprs.get(d.bindings).Tag;
                        value = types.ct.evalIntConst(
                            .{ .Perm = .init(.{ .Enum = id }) },
                            d.value,
                        ) catch continue;
                        break :b ast.tokenSrc(t.index + 1);
                    }
                    continue;
                },
                else => {
                    types.report(self.key.loc.file, fast, "unexpected item," ++
                        " only field declarations (.variant_name)," ++
                        " and declarations (decl_name := expr)", .{});
                    continue;
                },
            };

            fields.append(
                tmp.arena.allocator(),
                .{ .name = name, .value = value },
            ) catch unreachable;
            value += 1;
        }

        std.sort.pdq(Field, fields.items, {}, enum {
            fn lessThenFn(_: void, lhs: Field, rhs: Field) bool {
                return lhs.value < rhs.value;
            }
        }.lessThenFn);

        if (self.backing_int == null) {
            if (fields.items.len == 0)
                self.backing_int = .never
            else
                self.backing_int = .smallestIntFor(@bitCast(fields.getLast().value));
        }

        self.fields = types.pool.arena.dupe(Field, fields.items);

        return self.fields.?;
    }
};

pub const Union = struct {
    key: Scope,

    tag: TyId = .void,
    fields: ?[]const Field = null,
    abi: ?Abi.TmpSpec = null,
    payload_size: ?u64 = null,
    payload_align: ?u64 = null,
    index: Ast.Index,

    pub const Field = struct {
        name: []const u8,
        ty: TyId,
    };

    pub const Id = enum(u32) {
        _,

        pub const Data = Union;

        pub fn get(self: @This(), cont: anytype) *Data {
            return cont.store.get(self);
        }

        pub fn deepEqual(lsh: Id, types: *Types, rhs: Id) bool {
            const lhs_data: *Union = types.store.get(lsh);
            const rhs_data: *Union = types.store.get(rhs);

            if (!lhs_data.key.eql(rhs_data.key)) return false;

            if (lhs_data.tag != rhs_data.tag) return false;

            for (lhs_data.fields.?, rhs_data.fields.?) |lhsf, rhsf| {
                if (!std.mem.eql(u8, lhsf.name, rhsf.name)) return false;
                if (lhsf.ty != rhsf.ty) return false;
            }

            return true;
        }

        pub fn deepHash(id: Id, types: *Types, hasher: anytype) void {
            const data: *Union = types.store.get(id);

            data.key.hash(hasher);

            std.hash.autoHash(hasher, data.tag);

            for (data.fields.?) |f| {
                hasher.update(f.name);
                std.hash.autoHash(hasher, f.ty);
            }
        }

        pub fn tagOffset(id: Id, types: *Types) u64 {
            const self: *Union = types.store.get(id);
            if (self.payload_size == null) {
                id.computeLayout(types);
            }
            return self.payload_size.?;
        }

        pub fn size(id: Id, types: *Types) u64 {
            const self: *Union = types.store.get(id);

            if (self.payload_size == null) {
                id.computeLayout(types);
            }

            return self.payload_size.? + if (id.getTag(types) != .void) self.payload_align.? else 0;
        }

        pub fn alignment(id: Id, types: *Types) u64 {
            const self: *Union = types.store.get(id);

            if (self.payload_align == null) {
                id.computeLayout(types);
            }

            return @max(self.payload_align.?, self.tag.alignment(types));
        }

        fn computeLayout(id: Id, types: *Types) void {
            const self: *Union = types.store.get(id);

            var max_size: u64 = 0;
            var alignm: u64 = 1;
            for (id.getFields(types)) |f| {
                alignm = @max(alignm, f.ty.alignment(types));
                max_size = @max(max_size, f.ty.size(types));
            }
            max_size = std.mem.alignForward(u64, max_size, alignm);

            self.payload_size = max_size;
            self.payload_align = alignm;
        }

        pub fn getTag(id: Id, types: *Types) TyId {
            const self: *Union = types.store.get(id);

            if (self.tag != .void) {
                return self.tag;
            }

            const ast = types.getFile(self.key.loc.file);
            if (self.key.loc.ast.tag() == .Directive) return .void;
            const union_ast = ast.exprs.get(self.key.loc.ast).Type;
            if (union_ast.tag.tag() == .Void) return .void;

            if (union_ast.tag.tag() == .EnumWildcard) {
                const rfields = id.getFields(types);
                const fields = types.pool.arena.alloc(Enum.Field, rfields.len);
                for (rfields, fields, 0..) |ref, *slot, i| {
                    slot.* = .{ .name = ref.name, .value = @intCast(i) };
                }

                const slot, const ty = types.intern(.Enum, .{
                    .loc = .{
                        .scope = .init(.{ .Union = id }),
                        .file = self.key.loc.file,
                        .ast = .zeroSized(.Void),
                        .capture_len = 0,
                    },
                    .name_pos = self.key.name_pos,
                    .captures_ptr = undefined,
                });

                std.debug.assert(!slot.found_existing);

                const enm: *Enum = types.store.get(ty);
                enm.fields = fields;
                enm.index = .empty;
                enm.backing_int = .u8; // todo

                self.tag = .init(.{ .Enum = ty });
            } else {
                self.tag = types.ct.evalTy("", .init(.{ .Union = id }), union_ast.tag) catch .never;
            }

            return self.tag;
        }

        pub fn getFields(id: Id, types: *Types) []const Field {
            const self: *Union = types.store.get(id);

            if (self.fields) |f| return f;
            const ast = types.getFile(self.key.loc.file);
            const union_ast = ast.exprs.get(self.key.loc.ast).Type;

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
    abi: ?Abi.TmpSpec = null,
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

        pub fn get(self: @This(), cont: anytype) *Data {
            return cont.store.get(self);
        }

        pub fn deepEqual(lsh: Id, types: *Types, rhs: Id) bool {
            const lhs_data: *Struct = types.store.get(lsh);
            const rhs_data: *Struct = types.store.get(rhs);

            if (!lhs_data.key.eql(rhs_data.key)) return false;

            if (lhs_data.alignment.? != rhs_data.alignment.?) return false;

            for (lhs_data.fields.?, rhs_data.fields.?) |lhsf, rhsf| {
                if (!std.mem.eql(u8, lhsf.name, rhsf.name)) return false;
                if (lhsf.ty != rhsf.ty) return false;
            }

            return true;
        }

        pub fn deepHash(id: Id, types: *Types, hasher: anytype) void {
            const data: *Struct = types.store.get(id);

            data.key.hash(hasher);

            std.hash.autoHash(hasher, data.alignment.?);

            for (data.fields.?) |f| {
                hasher.update(f.name);
                std.hash.autoHash(hasher, f.ty);
            }
        }

        pub fn getSize(id: Id, types: *Types) u64 {
            const self = types.store.get(id);

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

            self.size = siz;
            return siz;
        }

        pub fn getAlignment(id: Id, types: *Types) u64 {
            const self = types.store.get(id);

            if (self.alignment) |a| return a;

            if (self.recursion_lock) {
                types.report(self.key.loc.file, self.key.loc.ast, "the struct has undecidable alignment (cycle)", .{});
                //std.debug.dumpCurrentStackTrace(@returnAddress());
                return 1;
            }
            self.recursion_lock = true;
            defer self.recursion_lock = false;

            const ast = types.getFile(self.key.loc.file);
            const struct_ast = ast.exprs.get(self.key.loc.ast).Type;

            if (struct_ast.alignment.tag() != .Void) {
                if (@hasField(Field, "alignment")) @compileError("assert fields <= alignment then base alignment");
                self.alignment = @bitCast(types.ct.evalIntConst(.{ .Perm = .init(.{ .Struct = id }) }, struct_ast.alignment) catch 1);
                if (self.alignment == 0 or !std.math.isPowerOfTwo(self.alignment.?)) {
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
            const struct_ast = ast.exprs.get(self.key.loc.ast).Type;

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
                    const value = types.store.add(&types.pool.arena, Global{
                        .key = .{
                            .loc = .{
                                .file = self.key.loc.file,
                                .scope = .init(.{ .Struct = id }),
                                .ast = field.value,
                                .capture_len = 0,
                            },
                            .name_pos = ast.strPos(name),
                            .captures_ptr = undefined,
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
    completion: std.EnumArray(Types.Target, CompileState) =
        .{ .values = @splat(.queued) },

    pub const RrmoteId = struct {
        // TODO: we can squeeze this into a single u64 if we want
        from_thread: u32,
        remote: utils.EntId(Func),
        local: utils.EntId(Func),
    };

    pub const CompileState = enum { queued, compiled };

    pub fn sig(self: Func) FnPtr {
        return .{ .ret = self.ret, .args = self.args };
    }
};

pub const Global = struct {
    key: Scope,
    ty: TyId = .void,
    data: union(enum) {
        @"comptime": struct {
            base: usize,
            len: usize,
        },
        mut: []u8,
        imm: []const u8,

        pub fn freeze(self: *@This()) void {
            const tmp = self.mut;
            self.* = .{ .imm = tmp };
        }

        pub fn slice(self: @This(), ct: *Comptime) []const u8 {
            return switch (self) {
                .@"comptime" => |s| ct.gen.mach.out.code.items[s.base..][0..s.len],
                .mut => |s| s,
                .imm => |s| s,
            };
        }

        pub fn mutSlice(self: @This(), ct: *Comptime) ?[]u8 {
            return switch (self) {
                .@"comptime" => |s| ct.gen.mach.out.code.items[s.base..][0..s.len],
                .mut => |s| s,
                .imm => null,
            };
        }
    } = .{ .imm = &.{} },
    relocs: []Reloc = &.{},
    readonly: bool,
    uninit: bool = false,
    thread_local: bool = false,
    completion: std.EnumArray(Types.Target, CompileState) =
        .{ .values = @splat(.queued) },

    pub const CompileState = enum { queued, compiled };

    pub const Reloc = root.backend.Machine.DataOptions.Reloc;
};

pub const FnPtr = struct {
    args: []TyId,
    ret: TyId,

    pub fn computeAbi(
        self: FnPtr,
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
            if (arg_abi == .Impossible) {
                return null;
            }
            cursor += builder.types(params[cursor..], false, arg_abi).len;
        }

        return .{ params[0..cursor], returns, ret_abi };
    }
};

pub const Simd = struct {
    elem: TyId,
    len: u32,
};

pub const Array = extern struct {
    elem: TyId,
    len: u64,
};
