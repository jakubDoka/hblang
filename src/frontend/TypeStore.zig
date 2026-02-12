const std = @import("std");
const hb = @import("hb");
const utils = hb.utils;
const graph = hb.backend.graph;
const Lexer = hb.frontend.Lexer;
const DeclIndex = hb.frontend.DeclIndex;
const File = DeclIndex.File;
const Loader = DeclIndex.Loader;
const Codegen = hb.frontend.Codegen;
const Abi = hb.frontend.Abi;
const Machine = hb.backend.Machine;
const HbvmGen = hb.hbvm.HbvmGen;
const isa = hb.hbvm.isa;

arena: utils.Arena,
tmp: utils.Arena,
tmp_depth: usize = 0,

// TDOD: remove indexes that are actually not used
structs: utils.SegmentedList(Struct, StructId, 1024, 1024 * 1024) = .empty,
struct_index: Interner(StructId) = .empty,
enums: utils.SegmentedList(Enum, EnumId, 1024, 1024 * 1024) = .empty,
enum_index: Interner(EnumId) = .empty,
unions: utils.SegmentedList(Union, UnionId, 1024, 1024 * 1024) = .empty,
union_index: Interner(UnionId) = .empty,
funcs: utils.SegmentedList(Func, FuncId, 1024, 1024 * 1024) = .empty,
func_index: Interner(FuncId) = .empty,
globals: utils.SegmentedList(Global, GlobalId, 1024, 1024 * 1024) = .empty,
global_index: Interner(GlobalId) = .empty,
func_tys: utils.SegmentedList(FuncTy, FuncTyId, 1024, 1024 * 1024) = .empty,
func_ty_index: Interner(FuncTyId) = .empty,
templates: utils.SegmentedList(Template, TemplateId, 1024, 1024 * 1024) = .empty,
template_index: Interner(TemplateId) = .empty,
pointers: utils.SegmentedList(Pointer, PointerId, 1024, 1024 * 1024) = .empty,
pointer_index: Interner(PointerId) = .empty,
arrays: utils.SegmentedList(Array, ArrayId, 1024, 1024 * 1024) = .empty,
array_index: Interner(ArrayId) = .empty,
slices: utils.SegmentedList(Slice, SliceId, 1024, 1024 * 1024) = .empty,
slice_index: Interner(SliceId) = .empty,
options: utils.SegmentedList(Option, OptionId, 1024, 1024 * 1024) = .empty,
option_index: Interner(OptionId) = .empty,

files: []const File,
roots: []StructId,
line_indexes: []const hb.LineIndex,
loader: *Loader,
backend: *Machine,
vm: hb.hbvm.Vm = .{},
target: []const u8,
abi: Abi = .systemv,
func_queue: std.EnumArray(Target, std.ArrayList(FuncId)) =
    .initFill(.empty),
errored: usize = 0,
builtins: struct {
    type_union: UnionId,
    enum_field: StructId,
    union_field: StructId,
    struct_field: StructId,
    source_loc: StructId,
},
handlers: std.EnumArray(Handler, FuncId) = .initFill(.invalid),
handler_signatures: std.EnumArray(Handler, FuncTyId),
ct_backend: HbvmGen,

pub const Handler = enum {
    slice_ioob,
    null_unwrap,
    memcpy,
    entry,
    for_loop_length_mismatch,
};

pub const ComptimeValue = extern union {
    spilled: extern struct { id: GlobalId, off: u32 },
    @"inline": i64,
};

pub const TmpCheckpoint = struct {
    types: *Types,

    pub fn allocator(self: *TmpCheckpoint) std.mem.Allocator {
        return self.types.tmp.allocator();
    }

    pub fn deinit(self: *TmpCheckpoint) void {
        self.types.tmp_depth -= 1;
        if (self.types.tmp_depth == 0) {
            self.types.tmp.reset();
        }
    }
};

const Types = @This();

pub const Size = u58;
pub const AlignPow = u6;

pub const stack_size = 1024 * 128;

pub fn EntId(comptime T: type, comptime field: []const u8) type {
    return enum(u32) {
        invalid = std.math.maxInt(u32),
        _,

        pub const data = .{ .ty = T, .field = field };

        pub fn get(self: @This(), types: *Types) *T {
            return @field(types, data.field).at(self);
        }

        pub fn asOpt(self: @This()) ?@This() {
            if (self == .invalid) return null;
            return self;
        }
    };
}

pub fn Interner(comptime I: type) type {
    return struct {
        map: Map,

        pub const empty = @This(){ .map = .empty };
        pub const interner = {};

        pub const Map = std.HashMapUnmanaged(I, void, Ctx, std.hash_map.default_max_load_percentage);

        pub const Ctx = struct {
            types: *Types,

            pub fn eql(_: Ctx, a: I, b: I) bool {
                return a == b;
            }

            pub fn hash(self: Ctx, key: I) u64 {
                return @field(self.types, I.data.field).at(key).hash(self.types);
            }
        };

        pub const InsertCtx = struct {
            types: *Types,

            pub fn eql(c: InsertCtx, a: *I.data.ty, b: I) bool {
                return a.eql(@field(c.types, I.data.field).at(b), c.types);
            }

            pub fn hash(self: InsertCtx, key: *I.data.ty) u64 {
                return key.hash(self.types);
            }
        };

        pub fn intern(
            self: *@This(),
            types: *Types,
            value: *I.data.ty,
        ) Map.GetOrPutResult {
            return self.map.getOrPutContextAdapted(
                types.allocator(),
                value,
                InsertCtx{ .types = types },
                Ctx{ .types = types },
            ) catch unreachable;
        }

        pub fn deinit(self: *@This(), types: *Types) void {
            self.map.deinit(types.allocator());
        }
    };
}

pub const Target = enum {
    runtime,
    cmptime,
};

pub const UnorderedScope = union(enum(u8)) {
    Struct: StructId = Data.scope_start,
    Enum: EnumId,
    Union: UnionId,

    pub const upcast = generic.upcast;
    pub const downcast = generic.downcast;
    pub const scope = generic.scope;

    pub fn decls(self: @This(), types: *Types) *const DeclIndex {
        return switch (self) {
            inline else => |v| v.get(types).decls,
        };
    }
};

pub const ParentRef = enum(u32) {
    _,

    pub const data = Parent.Conv.data;
    pub const nany = Parent.Conv.nany;
    pub const init = Parent.Conv.pack;
};

pub const Parent = union(enum(u8)) {
    Struct: StructId = Data.scope_start,
    Enum: EnumId,
    Union: UnionId,
    Func: FuncId,
    Template: TemplateId,
    Tail: enum(u32) { end },

    pub const Conv = IdConv(ParentRef, Parent);

    pub const upcast = generic.upcast;
    pub const downcast = generic.downcast;
    pub const scope = generic.scope;
    pub const pack = Conv.pack;
};

pub const AnyScopeRef = enum(u32) {
    _,

    pub const data = AnyScope.Conv.data;
    pub const nany = AnyScope.Conv.nany;
    pub const init = AnyScope.Conv.pack;
};

pub const AnyScope = union(enum(u8)) {
    Struct: StructId = Data.scope_start,
    Enum: EnumId,
    Union: UnionId,
    Func: FuncId,
    Template: TemplateId,

    pub const Conv = IdConv(AnyScopeRef, AnyScope);

    pub const upcast = generic.upcast;
    pub const downcast = generic.downcast;
    pub const scope = generic.scope;
    pub const captures = generic.captures;
    pub const format_ = generic.format_;
    pub const pack = Conv.pack;

    pub fn findCurrentScope(self: AnyScope, types: *Types) Id {
        return switch (self) {
            inline .Func, .Template => |f| f.get(types).scope.parent
                .data().downcast(AnyScope).?.findCurrentScope(types),
            inline else => |v| .nany(v),
        };
    }

    pub fn findCurrentFunc(self: AnyScope, types: *Types) ?FuncId {
        return switch (self) {
            .Func => |f| return f,
            inline else => |t| (t.get(types).scope.parent.data()
                .downcast(AnyScope) orelse return null).findCurrentFunc(types),
        };
    }

    pub fn decls(self: AnyScope, types: *Types) *const DeclIndex {
        return switch (self) {
            inline .Func, .Template => |f| f.get(types).scope.parent
                .data().downcast(AnyScope).?.decls(types),
            inline else => |v| v.get(types).decls,
        };
    }
};

pub const generic = struct {
    pub fn format_(self: anytype, types: *Types, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        return switch (self.*) {
            inline else => |t| t.get(types).format_(types, writer),
        };
    }

    pub fn lookupField(self: anytype, types: *Types, name: []const u8) ?usize {
        const field = self.decls
            .lookupField(self.scope.file.get(types).source, name) orelse return null;
        return utils.indexOfPtr(u32, self.decls.fields.items(.offset), field);
    }

    pub fn hashScope(self: anytype, _: *Types) u64 {
        return std.hash.Wyhash.hash(0, std.mem.asBytes(&self.scope));
    }

    pub fn eqlScope(self: anytype, other: anytype, _: *Types) bool {
        return std.meta.eql(self.scope, other.scope);
    }

    pub fn scope(self: anytype, types: *Types) *Types.Scope {
        return switch (self.*) {
            inline else => |v| &v.get(types).scope,
        };
    }

    pub fn captures(self: anytype, types: *Types) *Types.Captures {
        return switch (self.*) {
            inline else => |v| &v.get(types).captures,
        };
    }

    pub fn upcast(self: anytype, comptime T: type) T {
        const Dt = @TypeOf(self.*);

        comptime {
            for (std.meta.fields(std.meta.Tag(Dt))) |f| {
                for (std.meta.fields(std.meta.Tag(T))) |of| {
                    if (std.mem.eql(u8, f.name, of.name)) {
                        if (f.value != of.value) {
                            @compileError(std.fmt.comptimePrint(
                                "subset mismatch {s}.{s}({} != {})",
                                .{
                                    @typeName(T),
                                    f.name,
                                    f.value,
                                    of.value,
                                },
                            ));
                        }
                        break;
                    }
                } else {
                    @compileError(std.fmt.comptimePrint(
                        "missing field {s}.{s}",
                        .{
                            @typeName(T),
                            f.name,
                        },
                    ));
                }
            }
        }
        return @as(*const T, @ptrCast(self)).*;
    }

    pub fn downcast(self: anytype, comptime T: type) ?T {
        const Dt = @TypeOf(self.*);

        comptime var range_start = 0;
        comptime var range_end = 0;
        comptime {
            const to_fields = std.meta.fields(std.meta.Tag(T));

            for (std.meta.fields(std.meta.Tag(Dt))) |f| {
                for (to_fields) |of| {
                    if (std.mem.eql(u8, f.name, of.name)) {
                        if (f.value != of.value) {
                            @compileError(std.fmt.comptimePrint(
                                "subset mismatch {s}.{s}({} != {})",
                                .{
                                    @typeName(T),
                                    f.name,
                                    f.value,
                                    of.value,
                                },
                            ));
                        }
                    }
                }
            }

            var first = to_fields[0].value;
            range_start = first;
            for (to_fields[1..]) |v| {
                if (v.value != first + 1) {
                    @compileError(@typeName(T) ++ "is not continuous");
                }
                first += 1;
            }
            range_end = first;

            if (@sizeOf(T) != @sizeOf(Dt)) {
                @compileError("layout does not match for " ++ @typeName(T));
            }
        }

        if (range_start <= @intFromEnum(self.*) and
            @intFromEnum(self.*) <= range_end)
        {
            return @as(*const T, @ptrCast(self)).*;
        }

        return null;
    }
};

pub const Data = union(enum(u8)) {
    Builtin: Builtin,
    Option: OptionId,
    Pointer: PointerId,
    Slice: SliceId,
    Array: ArrayId,
    FuncTy: FuncTyId,
    Struct: StructId,
    Enum: EnumId,
    Union: UnionId,

    pub const scope_start = 6;
    pub const index_start = 2;

    pub const pack = Id.Conv.pack;
    pub const downcast = generic.downcast;

    pub fn size(self: Data, types: *Types) Size {
        return switch (self) {
            .Builtin => |b| b.size(types),
            .FuncTy => 4,
            .Pointer => 8,
            .Slice => 16,
            .Array => |a| a.get(types).elem.size(types) * a.get(types).len.s,
            inline .Option, .Struct, .Enum, .Union => |s| s.get(types)
                .getLayout(types).spec.size,
        };
    }

    pub fn alignment(self: Data, types: *Types) Size {
        return switch (self) {
            .Builtin => |b| b.alignment(types),
            .FuncTy => 4,
            .Pointer => 8,
            .Slice => 8,
            .Array => |a| a.get(types).elem.alignment(types),
            inline .Option, .Struct, .Enum, .Union => |e| e.get(types)
                .getLayout(types).spec.alignmentBytes(),
        };
    }
};

pub fn IdConv(comptime I: type, comptime D: type) type {
    return struct {
        pub const DRepr = extern struct {
            value: u32,
            tag: u8,
        };

        pub const IRepr = packed struct(u32) {
            index: std.meta.Int(.unsigned, 32 - @bitSizeOf(std.meta.Tag(D))),
            tag: std.meta.Tag(std.meta.Tag(D)),
        };

        pub fn repr(self: I) IRepr {
            return @bitCast(@intFromEnum(self));
        }

        pub fn data(self: I) D {
            const rpr: IRepr = @bitCast(@intFromEnum(self));
            return @as(*const D, @ptrCast(&DRepr{
                .value = rpr.index,
                .tag = rpr.tag,
            })).*;
        }

        pub fn nany(value: anytype) I {
            inline for (std.meta.fields(D)) |f| {
                if (f.type == @TypeOf(value)) {
                    return D.pack(@unionInit(D, f.name, value));
                }
            }
            @compileError(@typeName(@TypeOf(value)));
        }

        pub fn pack(dt: D) I {
            comptime std.debug.assert(@sizeOf(D) == @sizeOf(DRepr));
            const data_repr = @as(*const DRepr, @ptrCast(&dt)).*;
            const rpr = IRepr{
                .tag = @intCast(data_repr.tag),
                .index = @intCast(data_repr.value),
            };
            return @enumFromInt(@as(u32, @bitCast(rpr)));
        }
    };
}

pub const Id = enum(u32) {
    never,
    void,
    bool,
    u8,
    u16,
    u32,
    uint,
    u64,
    i8,
    i16,
    i32,
    int,
    i64,
    f32,
    f64,
    type,
    template,
    any,
    _,

    const Conv = IdConv(Id, Data);
    pub const data = Conv.data;
    pub const nany = Conv.nany;
    pub const init = Conv.pack;
    pub const repr = Conv.repr;

    pub fn raw(self: Id) u32 {
        return @intFromEnum(self);
    }

    pub fn size(self: Id, types: *Types) Size {
        return self.data().size(types);
    }

    pub fn child(self: Id, types: *Types) ?Id {
        return switch (self.data()) {
            .Pointer => |p| p.get(types).ty,
            .Option => |o| o.get(types).inner,
            inline .Slice, .Array => |a| a.get(types).elem,
            .Struct, .Enum, .Union, .FuncTy, .Builtin => null,
        };
    }

    pub fn isBuiltin(
        self: Id,
        comptime pred: enum { isInteger, isUnsigned, isSigned, isFloat },
    ) bool {
        return switch (self.data()) {
            .Builtin => |b| @field(Builtin, @tagName(pred))(b),
            else => false,
        };
    }

    pub fn category(self: Id, types: *Types) Abi.Category {
        var buf = Abi.Buf{};
        return .fromSpec(types.abi.categorize(self, types, &buf));
    }

    pub fn alignment(self: Id, types: *Types) Size {
        return self.data().alignment(types);
    }

    pub fn len(self: Id, types: *Types) Size {
        return @intCast(switch (self.data()) {
            .Slice, .Pointer, .Builtin, .Option => 0,
            .Array => |a| a.get(types).len.s,
            inline .Struct, .Enum, .Union => |s| s.get(types).decls.fields.len,
            .FuncTy => |f| f.get(types).args.len,
        });
    }

    pub fn alignmentPow(self: Id, types: *Types) u6 {
        return std.math.log2_int(u64, self.alignment(types));
    }

    pub fn stackSpec(self: Id, types: *Types) graph.AbiParam.StackSpec {
        return .fromByteUnits(self.size(types), self.alignment(types));
    }

    pub fn isScalar(ty: Types.Id, types: *Types) bool {
        return ty.category(types) == .Scalar;
    }

    pub fn format_(self: Id, types: *Types, writer: *std.io.Writer) !void {
        switch (self.data()) {
            .Builtin => |b| try writer.print("{s}", .{@tagName(b)}),
            .Option => |o| {
                try writer.writeByte('?');
                try o.get(types).inner.format_(types, writer);
            },
            .Pointer => |p| {
                try writer.writeByte('^');
                try p.get(types).ty.format_(types, writer);
            },
            .Array => |a| {
                try writer.writeByte('[');
                try writer.print("{}", .{a.get(types).len.s});
                try writer.writeByte(']');
                try a.get(types).elem.format_(types, writer);
            },
            .FuncTy => |f| {
                try writer.writeAll("fn(");
                for (f.get(types).args, 0..) |arg, i| {
                    try arg.format_(types, writer);
                    if (i != f.get(types).args.len - 1) try writer.writeAll(", ");
                }
                try writer.writeAll("): ");
                try f.get(types).ret.format_(types, writer);
            },
            .Slice => |s| {
                try writer.writeAll("[]");
                try s.get(types).elem.format_(types, writer);
            },
            inline .Enum, .Struct, .Union => |s| try s.get(types).format_(types, writer),
        }
    }

    pub const fmt = Fmt(Id).fmt;

    pub fn canUpcast(from: Id, to: Id, types: *Types) bool {
        if (from == .never) return true;
        if (from == to) return true;
        const is_bigger = from.size(types) < to.size(types);
        if (from.isBuiltin(.isUnsigned) and to.isBuiltin(.isUnsigned)) return is_bigger;
        if (from.isBuiltin(.isSigned) and to.isBuiltin(.isSigned)) return is_bigger;
        if (from.isBuiltin(.isUnsigned) and to.isBuiltin(.isSigned)) return is_bigger;
        if (from.data() == .Enum and to.isBuiltin(.isUnsigned)) return from.size(types) <= to.size(types);
        if (from.data() == .Enum and to.isBuiltin(.isSigned)) return is_bigger;
        if (from == .bool and to.isBuiltin(.isInteger)) return true;

        return false;
    }

    comptime {
        for (std.meta.fields(Id), std.meta.fields(Builtin)) |a, b| {
            if (!std.mem.eql(u8, a.name, b.name)) {
                @compileError("mismatched builtin '" ++ a.name ++ "' and '" ++ b.name ++ "'");
            }
        }

        for (
            std.meta.fields(Id)[0 .. std.meta.fields(Id).len - 1],
            std.meta.fields(Lexer.Lexeme.Type),
        ) |a, b| {
            if (!std.mem.eql(u8, a.name, b.name)) {
                @compileError("mismatched lexeme '" ++ a.name ++ "' and '" ++ b.name ++ "'");
            }
        }
    }
};

pub fn Fmt(comptime T: type) type {
    return struct {
        id: T,
        types: *Types,

        pub fn fmt(self: T, types: *Types) @This() {
            return .{ .types = types, .id = self };
        }

        pub fn format(self: @This(), writer: *std.io.Writer) !void {
            try self.id.format_(self.types, writer);
        }

        pub fn toString(self: @This(), arena: *utils.Arena) []u8 {
            var tmp = utils.Arena.scrath(arena);
            defer tmp.deinit();
            var arr = std.io.Writer.Allocating.init(tmp.arena.allocator());
            self.format(&arr.writer) catch unreachable;
            return arena.dupe(u8, arr.written());
        }
    };
}

pub const Builtin = enum(u32) {
    never,
    void,
    bool,
    u8,
    u16,
    u32,
    uint,
    u64,
    i8,
    i16,
    i32,
    int,
    i64,
    f32,
    f64,
    type,
    template,
    any,

    pub const identity = {};

    pub fn isInteger(self: Builtin) bool {
        return self.isUnsigned() or self.isSigned();
    }

    pub fn isUnsigned(self: Builtin) bool {
        return @intFromEnum(Builtin.u8) <= @intFromEnum(self) and
            @intFromEnum(self) <= @intFromEnum(Id.u64);
    }

    pub fn isSigned(self: Builtin) bool {
        return @intFromEnum(Builtin.i8) <= @intFromEnum(self) and
            @intFromEnum(self) <= @intFromEnum(Id.i64);
    }

    pub fn isFloat(self: Builtin) bool {
        return @intFromEnum(Builtin.f32) <= @intFromEnum(self) and
            @intFromEnum(self) <= @intFromEnum(Id.f64);
    }

    pub fn size(self: Builtin, _: *Types) Size {
        return switch (self) {
            .void, .never => 0,
            .bool, .u8, .i8 => 1,
            .u16, .i16 => 2,
            .u32, .i32, .f32, .type, .template => 4,
            .u64, .i64, .f64, .uint, .int => 8,
            .any => unreachable,
        };
    }

    pub fn alignment(self: Builtin, types: *Types) Size {
        return @max(self.size(types), 1);
    }
};

pub const Captures = struct {
    /// first byte in the name for each var
    prefixes: []const u8,
    variables: []const Variable,
    /// packed values for each comptime variable, index is comptuted when
    /// searching
    values: []const ComptimeValue,

    pub const empty = Captures{
        .values = &.{},
        .variables = &.{},
        .prefixes = &.{},
    };

    pub const Variable = struct {
        meta: packed struct(u32) {
            offset: u31,
            is_cmptime: bool,
        },
        ty: Id,
    };

    pub fn init(scope: *Codegen, scratch: *utils.Arena) Captures {
        var vars: []const Codegen.Variable = scope.vars.items(.variable);
        if (vars.len > 0 and vars[vars.len - 1].value == std.math.maxInt(u32)) {
            vars = vars[0 .. vars.len - 1];
        }
        const variables = scratch.alloc(Variable, vars.len);

        for (vars, variables) |vari, *variable| {
            variable.* = .{
                .meta = .{
                    .offset = vari.meta.pos,
                    .is_cmptime = vari.meta.kind == .cmptime,
                },
                .ty = vari.ty,
            };
        }

        const values = scratch.alloc(ComptimeValue, scope.cmptime_values.items.len);
        for (scope.cmptime_values.items, values) |v, *slot| slot.* = v;

        return .{
            .prefixes = scratch.dupe(u8, scope.vars.items(.prefix)[0..vars.len]),
            .variables = variables,
            .values = values,
        };
    }

    pub fn lookup(self: Captures, source: [:0]const u8, name: []const u8) ?struct { u32, Id, ?ComptimeValue } {
        // TODO: we can vectorize this

        var value_index: usize = 0;
        for (self.prefixes, self.variables) |prefix, variable| {
            if (prefix == name[0] and Lexer.compareIdent(source, variable.meta.offset, name)) {
                return .{ variable.meta.offset, variable.ty, if (variable.meta.is_cmptime)
                    self.values[value_index]
                else
                    null };
            }
            if (variable.meta.is_cmptime) {
                value_index += 1;
            }
        }

        return null;
    }
};

pub const Scope = extern struct {
    parent: ParentRef,
    name_pos: NamePos,
    file: File.Id,

    comptime {
        if (!std.meta.hasUniqueRepresentation(Scope)) {
            @compileError("Scope must have unique representation");
        }
    }

    pub const NamePos = enum(u32) {
        tuple = std.math.maxInt(u32) - 3,
        file,
        empty,
        _,

        pub fn sourcePos(self: NamePos) u32 {
            return switch (self) {
                .file => 0,
                .empty => 0,
                .tuple => 0,
                _ => |v| @intFromEnum(v),
            };
        }

        pub fn get(self: NamePos, file: File.Id, types: *Types) []const u8 {
            return switch (self) {
                .file => file.get(types).path,
                .empty => "",
                .tuple => "tuple",
                _ => |v| {
                    var str = file.get(types).tokenStr(@intFromEnum(v));
                    if (str[0] == '"') str = str[1 .. str.len - 1];
                    return str;
                },
            };
        }
    };

    pub const Param = extern struct {};

    pub fn name(self: Scope, types: *Types) []const u8 {
        return self.name_pos.get(self.file, types);
    }

    pub fn format_(self: *Scope, id: anytype, types: *Types, writer: *std.Io.Writer) !void {
        const nme = self.name(types);
        if (self.parent.data().downcast(AnyScope)) |as| {
            try as.format_(types, writer);
            try writer.writeByte('.');
        }

        if (nme.len == 0) {
            try writer.print(@TypeOf(id).data.field ++ "[{}]", .{@intFromEnum(id)});
        } else {
            try writer.writeAll(nme);
        }
    }
};

pub const OptionId = EntId(Option, "options");
pub const Option = struct {
    inner: Id,
    layout: Layout = .not_computed,

    pub const Layout = packed struct {
        storage: enum(u1) {
            bool,
            ptr,

            pub fn dataType(self: @This()) graph.DataType {
                return switch (self) {
                    .bool => .i8,
                    .ptr => .i64,
                };
            }

            pub fn ty(self: @This()) Id {
                return switch (self) {
                    .bool => .u8,
                    .ptr => .uint,
                };
            }
        },
        offset: u31,

        pub const empty = Layout{
            .storage = .bool,
            .offset = std.math.maxInt(u31),
        };

        pub const not_computed = Layout{
            .storage = .ptr,
            .offset = std.math.maxInt(u31),
        };
    };

    pub const ExpLayout = struct {
        spec: graph.AbiParam.StackSpec,
        inner: Layout,
        compact: bool,
    };

    pub fn hash(self: *Option, _: *Types) u64 {
        return std.hash.int(@intFromEnum(self.inner));
    }

    pub fn eql(self: *Option, other: *Option, _: *Types) bool {
        return self.inner == other.inner;
    }

    pub fn getLayout(self: *Option, types: *Types) ExpLayout {
        if (self.layout == Layout.not_computed) {
            self.layout = findNieche(types, self.inner, 0);

            if (self.layout == Layout.not_computed) {
                self.layout.offset = @intCast(self.inner.size(types));
                self.layout.storage = .bool;
            }
        }

        std.debug.assert(self.layout != Layout.not_computed);

        const min_size = self.layout.offset + self.inner.alignment(types);
        const inner_size = self.inner.size(types);

        return .{
            .spec = .fromByteUnits(
                if (self.layout == Layout.empty) 0 else @max(min_size, inner_size),
                self.inner.alignment(types),
            ),
            .inner = self.layout,
            .compact = min_size == inner_size,
        };
    }

    pub fn findNieche(types: *Types, ty: Id, offset: Size) Layout {
        switch (ty.data()) {
            .Builtin => |b| switch (b) {
                .never => return .empty,
                else => return .not_computed,
            },
            .Union => return .not_computed,
            .Enum => |e| return if (e.get(types).decls.fields.len == 0)
                .empty
            else
                .not_computed,
            .FuncTy, .Option => return .not_computed,
            .Pointer => return .{ .offset = @intCast(offset), .storage = .ptr },
            .Slice => return .{ .offset = @intCast(offset + Slice.ptr_offset), .storage = .ptr },
            .Array => |a| if (a.get(types).len.s == 0)
                return .not_computed
            else
                return findNieche(types, a.get(types).elem, offset),
            .Struct => |s| {
                for (s.get(types).getLayout(types).fields) |f| {
                    const nich = findNieche(types, f.ty, offset + f.offset);
                    if (nich != Layout.not_computed) return nich;
                }

                return .not_computed;
            },
        }
    }
};

pub const SliceId = EntId(Slice, "slices");
pub const Slice = extern struct {
    elem: Id,

    pub const len_offset = 8;
    pub const ptr_offset = 0;

    pub fn hash(self: Slice, _: *Types) u64 {
        return std.hash.int(@intFromEnum(self.elem));
    }

    pub fn eql(self: *Slice, other: *Slice, _: *Types) bool {
        return std.meta.eql(self.elem, other.elem);
    }
};

pub const ArrayId = EntId(Array, "arrays");
pub const Array = extern struct {
    elem: Id,
    _padd: u32 = 0,
    len: packed struct {
        s: Size,
        pad: u6 = 0,
    },

    pub fn hash(self: Array, _: *Types) u64 {
        return std.hash.Wyhash.hash(0, std.mem.asBytes(&self));
    }

    pub fn eql(self: *Array, other: *Array, _: *Types) bool {
        return std.meta.eql(self.elem, other.elem) and
            std.meta.eql(self.len, other.len);
    }
};

pub const StructId = EntId(Struct, "structs");
pub const Struct = struct {
    scope: Scope,
    captures: Captures,
    decls: *const DeclIndex,
    layout: ?Layout = null,

    pub const Layout = struct {
        spec: graph.AbiParam.StackSpec,
        fields: []Field,

        pub const Field = struct {
            ty: Id,
            default: GlobalId,
            offset: Size,
        };
    };

    pub fn format_(self: *Struct, types: *Types, writer: *std.Io.Writer) error{WriteFailed}!void {
        if (self.scope.name_pos == .tuple) {
            try writer.writeAll(".(");

            for (self.layout.?.fields, 0..) |f, i| {
                if (i != 0) try writer.writeAll(", ");
                try f.ty.format_(types, writer);
            }
            try writer.writeByte(')');

            return;
        }

        try self.scope.format_(types.structs.ptrToIndex(self), types, writer);
    }

    pub fn fieldName(self: *Struct, types: *Types, index: usize) []const u8 {
        return Lexer.peekStr(
            self.scope.file.get(types).source,
            self.decls.fields.items(.offset)[index],
        );
    }

    pub const lookupField = generic.lookupField;

    pub fn getLayout(self: *Struct, types: *Types) *Layout {
        if (self.layout) |*l| return l;

        const file = self.scope.file.get(types);

        self.layout = Layout{
            .spec = .{ .size = 0, .alignment = 0 },
            .fields = types.arena.alloc(Layout.Field, self.decls.fields.len),
        };
        const layout = &self.layout.?;

        var tmp = types.tmpCheckpoint();
        defer tmp.deinit();

        var gen: Codegen = undefined;
        gen.init(
            types,
            .nany(types.structs.ptrToIndex(self)),
            .never,
            tmp.allocator(),
        );

        _ = gen.bl.begin(.systemv, undefined);

        var hard_align: ?Size = null;
        haling: {
            if (self.decls.start == 0) break :haling;

            var lex = Lexer.init(file.source, self.decls.start);
            _ = lex.slit(.@"struct"); // maybe shift this after the keyword?

            if (lex.eatMatch(.@"align")) {
                _ = gen.expect(&lex, .@"(", "to open align definition") catch break :haling;
                const alignv = gen.typedExpr(.uint, .{}, &lex) catch break :haling;
                const alignc = gen.peval(lex.cursor, alignv, Size) catch break :haling;
                _ = gen.expect(&lex, .@")", "to close align definition") catch break :haling;
                hard_align = alignc;
            }
        }

        for (@as([]u32, self.decls.fields.items(.offset)), 0..) |o, i| {
            const slot = &layout.fields[i];
            var lex = Lexer.init(file.source, o);

            _ = lex.slit(.Ident);
            _ = lex.slit(.@":");

            slot.ty = gen.typ(&lex) catch .never;
            slot.default = .invalid;

            if (lex.eatMatch(.@"=")) {
                slot.default = types.globals.push(&types.arena, .{
                    .scope = gen.gatherScope(),
                    .ty = slot.ty,
                    .readonly = true,
                });

                var glob_gen: Codegen = undefined;
                glob_gen.init(
                    types,
                    .nany(types.structs.ptrToIndex(self)),
                    .never,
                    tmp.allocator(),
                );
                glob_gen.target = .cmptime;

                glob_gen.evalGlobal(&lex, slot.ty, slot.default);
            }

            layout.spec.alignment = @max(
                layout.spec.alignment,
                slot.ty.alignmentPow(types),
            );
            layout.spec.size = std.mem.alignForward(
                u58,
                layout.spec.size,
                @min(
                    slot.ty.alignment(types),
                    hard_align orelse layout.spec.alignmentBytes(),
                ),
            );

            slot.offset = layout.spec.size;

            layout.spec.size += slot.ty.size(types);
        }

        if (hard_align) |alignm| {
            layout.spec.alignment = std.math.log2_int(u64, alignm);
        }

        layout.spec.size = std.mem.alignForward(
            u58,
            layout.spec.size,
            layout.spec.alignmentBytes(),
        );

        return layout;
    }
};

pub const EnumId = EntId(Enum, "enums");
pub const Enum = struct {
    scope: Scope,
    captures: Captures,
    decls: *const DeclIndex,
    layout: ?Layout = null,

    pub const Layout = struct {
        spec: graph.AbiParam.StackSpec,
        fields: []i64,

        pub fn backingInteger(self: *Layout) Id {
            return @enumFromInt(@intFromEnum(Id.u8) + self.spec.alignment);
        }
    };

    pub fn format_(
        self: *@This(),
        types: *Types,
        writer: *std.Io.Writer,
    ) std.Io.Writer.Error!void {
        try self.scope.format_(types.enums.ptrToIndex(self), types, writer);
    }

    pub const lookupField = generic.lookupField;

    pub fn getLayout(self: *Enum, types: *Types) *Layout {
        if (self.layout) |*l| return l;

        const file = self.scope.file.get(types);

        self.layout = Layout{
            .spec = .{ .size = 0, .alignment = 1 },
            .fields = types.arena.alloc(i64, self.decls.fields.len),
        };
        const layout = &self.layout.?;

        var lex = Lexer.init(file.source, self.decls.start);

        if (lex.eatMatch(.@"union")) {
            _ = lex.slit(.@"(");
            _ = lex.slit(.@"enum");
            _ = lex.slit(.@")");
        } else {
            _ = lex.slit(.@"enum");

            if (lex.eatMatch(.@"(")) tag: {
                var gen: Codegen = undefined;
                gen.init(types, .nany(types.enums.ptrToIndex(self)), .never, types.tmp.allocator());

                const vl = gen.typ(&lex) catch break :tag;
                layout.spec = vl.stackSpec(types);
            }
        }

        var tmp = types.tmpCheckpoint();
        defer tmp.deinit();

        var max_value: i64 = 0;
        var value: i64 = 0;
        for (self.decls.fields.items(.offset), layout.fields) |f, *slt| {
            var flex = Lexer.init(file.source, f);

            _ = flex.slit(.Ident);
            if (flex.eatMatch(.@":=")) vl: {
                var gen: Codegen = undefined;
                gen.init(types, .nany(types.enums.ptrToIndex(self)), .never, tmp.allocator());

                const vl = gen.typedExpr(.i64, .{}, &flex) catch break :vl;
                value = gen.peval(flex.cursor, vl, i64) catch break :vl;
            }

            if (layout.spec.size != 0) {
                if ((@as(u64, 1) <<| layout.spec.size * 8) < value) {
                    types.report(
                        self.scope.file,
                        flex.cursor,
                        "enum value too large, does not fit in {} bits",
                        .{layout.spec.size * 8},
                    );
                }
            }

            slt.* = value;
            max_value = @max(max_value, value);
            value +%= 1;
        }

        if (layout.spec.size == 0) {
            layout.spec.size = @max(8, std.math.ceilPowerOfTwo(
                Size,
                @max(64 - @clz(max_value), 1),
            ) catch unreachable) / 8;
            layout.spec.alignment = std.math.log2_int(u64, @max(1, layout.spec.size));
        }

        return layout;
    }
};

pub const UnionId = EntId(Union, "unions");
pub const Union = struct {
    scope: Scope,
    captures: Captures,
    decls: *const DeclIndex,
    layout: ?Layout = null,

    pub const Layout = struct {
        tag: ?EnumId,
        spec: graph.AbiParam.StackSpec,
        fields: []Id,

        pub const TagLayout = struct { id: EnumId, offset: Size };

        pub fn tagLayout(self: *Layout) ?TagLayout {
            return if (self.tag) |tag|
                .{ .id = tag, .offset = self.spec.size - self.spec.alignmentBytes() }
            else
                null;
        }
    };

    pub const lookupField = generic.lookupField;

    pub fn format_(self: *Union, types: *Types, writer: *std.Io.Writer) error{WriteFailed}!void {
        try self.scope.format_(types.unions.ptrToIndex(self), types, writer);
    }

    pub fn getLayout(self: *Union, types: *Types) *Layout {
        if (self.layout) |*l| return l;

        const file = self.scope.file.get(types);

        self.layout = .{
            .tag = null,
            .spec = .{ .alignment = 1, .size = 0 },
            .fields = types.arena.alloc(Id, self.decls.fields.len),
        };
        const layout = &self.layout.?;

        var tmp = types.tmpCheckpoint();
        defer tmp.deinit();

        var gen: Codegen = undefined;
        gen.init(
            types,
            .nany(types.unions.ptrToIndex(self)),
            .never,
            tmp.allocator(),
        );
        _ = gen.bl.begin(.systemv, undefined);

        var lex = Lexer.init(file.source, self.decls.start);
        _ = lex.slit(.@"union");
        if (lex.eatMatch(.@"(")) tag: {
            const check_point = lex.cursor;
            if (lex.eatMatch(.@"enum") and lex.eatMatch(.@")")) {
                layout.tag = types.enums.push(&types.arena, .{
                    .scope = gen.gatherScope(),
                    .captures = .empty,
                    .decls = self.decls, // mabye, just mabye
                });
            } else {
                lex.cursor = check_point;
                const ty = gen.typ(&lex) catch break :tag;
                if (ty.data() != .Enum) {
                    gen.report(lex.cursor, "{} is not an enum", .{ty}) catch break :tag;
                }

                layout.tag = ty.data().Enum;
            }
        }

        for (self.decls.fields.items(.offset), layout.fields) |off, *slot| {
            var flex = Lexer.init(file.source, off);

            _ = flex.slit(.Ident);
            _ = gen.expect(&flex, .@":", "to start the field type declaration") catch {};

            slot.* = gen.typ(&flex) catch .never;

            layout.spec.size = @max(layout.spec.size, slot.size(types));
            layout.spec.alignment = @max(layout.spec.alignment, slot.alignmentPow(types));
        }

        if (layout.tag) |t| {
            layout.spec.alignment = @max(
                layout.spec.alignment,
                Id.nany(t).alignmentPow(types),
            );
            layout.spec.size += layout.spec.alignmentBytes();
        }

        return layout;
    }
};

pub const PointerId = EntId(Pointer, "pointers");
pub const Pointer = struct {
    ty: Id,

    comptime {
        if (std.meta.fields(Pointer).len != 1)
            @compileError("handle other fields");
    }

    pub fn hash(self: Pointer, _: *Types) u64 {
        return std.hash.int(@intFromEnum(self.ty));
    }

    pub fn eql(self: *Pointer, other: *Pointer, _: *Types) bool {
        return self.ty == other.ty;
    }
};

pub const FuncTyId = EntId(FuncTy, "func_tys");
pub const FuncTy = struct {
    args: []const Id,
    ret: Id,

    pub fn hash(self: FuncTy, _: *Types) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(@ptrCast(self.args));
        hasher.update(@ptrCast(&self.ret));
        return hasher.final();
    }

    pub fn eql(self: *FuncTy, other: *FuncTy, _: *Types) bool {
        return std.mem.eql(Id, self.args, other.args) and
            std.meta.eql(self.ret, other.ret);
    }
};

pub const FuncId = EntId(Func, "funcs");
pub const Func = struct {
    scope: Scope,
    captures: Captures,
    params: []Param,
    args: []Id,
    ret: Id,
    // NOTE: start at the first argument
    pos: u32,
    compiled: std.EnumSet(Target) = .initEmpty(),
    linkage: Machine.Data.Linkage = .local,

    pub const Param = extern struct {
        value: ComptimeValue,
    };

    pub fn sig(self: *Func) FuncTy {
        return .{ .args = self.args, .ret = self.ret };
    }

    pub fn queue(self: *Func, target: Target, types: *Types) void {
        types.func_queue.getPtr(target).append(
            types.arena.allocator(),
            types.funcs.ptrToIndex(self),
        ) catch unreachable;
    }

    pub fn eql(self: *Func, other: *Func, _: *Types) bool {
        return std.meta.eql(self.scope, other.scope) and
            std.mem.eql(Id, self.args, other.args) and
            self.ret == other.ret and
            std.mem.eql(u8, @ptrCast(self.params), @ptrCast(other.params));
    }

    pub fn hash(self: *Func, _: *Types) u64 {
        var hasher = std.hash.Wyhash.init(0);

        hasher.update(@ptrCast(&self.scope));
        // TODO: showe these into a single array
        hasher.update(@ptrCast(self.args));
        hasher.update(@ptrCast(&self.ret));
        hasher.update(@ptrCast(self.params));

        return hasher.final();
    }

    pub fn format_(self: *Func, types: *Types, writer: *std.Io.Writer) !void {
        const name = self.scope.name(types);
        if (self.linkage != .local) {
            std.debug.assert(name.len != 0);
            try writer.writeAll(name);
            return;
        }

        try self.scope.format_(types.funcs.ptrToIndex(self), types, writer);

        try writer.writeByte('[');

        var param_idx: usize = 0;
        var arg_idx: usize = 0;
        var lex = Lexer.init(self.scope.file.get(types).source, self.pos);
        var iter = lex.list(.@",", .@")");

        while (iter.next()) : (arg_idx += 1) {
            if (arg_idx != 0) try writer.writeAll(", ");

            _, const cmptime = lex.eatIdent().?;
            _ = lex.slit(.@":");
            lex.skipExpr() catch unreachable;

            const ty = self.args[arg_idx];
            try ty.format_(types, writer);

            if (cmptime) {
                try writer.writeByte('=');

                const p = self.params[param_idx];
                if (ty != .type) {
                    try writer.writeAll("(TODO)");
                } else {
                    const t: Id = @enumFromInt(p.value.@"inline");
                    try t.format_(types, writer);
                }

                param_idx += 1;
            }
        }

        try writer.writeAll("]:");
        try self.ret.format_(types, writer);
    }

    pub const fmt = Fmt(*Func).fmt;
};

pub const TemplateId = EntId(Template, "templates");
pub const Template = struct {
    scope: Scope,
    captures: Captures,
    pos: u32,

    pub fn format_(self: *Template, types: *Types, writer: *std.Io.Writer) !void {
        if (self.scope.parent.data().downcast(AnyScope)) |p| {
            try p.format_(types, writer);
        }
    }
};

pub const GlobalId = EntId(Global, "globals");
pub const Global = struct {
    scope: Scope,
    ty: Id,
    // NOTE: points to the vm memory
    data: struct {
        pub fn get(self: *@This(), types: *Types) []u8 {
            const sm = self.sym(types);
            return types.ct_backend.mach.out.code.items[sm.offset..][0..sm.size];
        }

        pub fn sym(self: *@This(), types: *Types) *Machine.Data.Sym {
            const parent: *Global = @alignCast(@fieldParentPtr("data", self));
            return types.ct_backend.mach.out.getGlobalSym(
                @intFromEnum(types.globals.ptrToIndex(parent)),
            ).?;
        }
    } = .{},
    readonly: bool,
    uninit: bool = false,
    runtime_emmited: bool = false,
    linkage: Machine.Data.Linkage = .local,

    pub const hash = generic.hashScope;
    pub const eql = generic.eqlScope;

    pub fn format_(self: *Global, types: *Types, writer: *std.Io.Writer) !void {
        const name = self.scope.name(types);
        if (self.linkage != .local) {
            std.debug.assert(name.len != 0);
            try writer.writeAll(name);
            return;
        }

        try self.scope.format_(types.globals.ptrToIndex(self), types, writer);
    }

    pub const fmt = Fmt(*Global).fmt;
};

pub fn init(
    files: []File,
    loader: *Loader,
    target: []const u8,
    backend: *Machine,
    arena: utils.Arena,
    gpa: std.mem.Allocator,
) Types {
    var self = Types{
        .files = files,
        .roots = undefined,
        .line_indexes = undefined,
        .ct_backend = HbvmGen{
            .gpa = gpa,
            .push_uninit_globals = true,
            .emit_global_reloc_offsets = true,
        },
        .loader = loader,
        .backend = backend,
        .target = target,
        .tmp = undefined,
        .arena = arena,
        .builtins = undefined,
        .handler_signatures = undefined,
    };

    self.roots = self.arena.alloc(StructId, files.len);

    self.tmp = self.arena.subslice(1024 * 1024);

    // NOTE: god for now, will be configured later
    self.ct_backend.mach.out.code = .initBuffer(self.arena.subslice(1024 * 1024 * 16).asSlice());

    self.ct_backend.mach.out.code.items.len = stack_size;
    self.ct_backend.mach.out.code.items[self.ct_backend.mach.out.code.items.len - 1] = @intFromEnum(isa.Op.tx);
    self.ct_backend.mach.out.code.items[self.ct_backend.mach.out.code.items.len - 2] = @intFromEnum(isa.Op.eca);
    self.vm.regs.set(.stack_addr, stack_size - 8);

    const line_indexes = self.arena.alloc(hb.LineIndex, self.files.len);
    for (self.files, line_indexes) |f, *li| li.* = f.lines;
    self.line_indexes = line_indexes;

    const out_files = self.arena.alloc(Machine.Data.File, self.files.len);
    for (self.files, out_files) |f, *of| {
        of.* = .{ .name = f.path, .size = @intCast(f.source.len) };
    }
    backend.out.files = out_files;

    for (self.files, self.roots, 0..) |*f, *r, i| {
        r.* = self.structs.push(
            &self.arena,
            Struct{
                .scope = .{
                    .parent = .init(.{ .Tail = .end }),
                    .file = @enumFromInt(i),
                    .name_pos = .file,
                },
                .captures = .empty,
                .decls = &f.decls,
            },
        );
    }

    const builtins: File.Id = @enumFromInt(self.files.len - 1);

    {
        var tmp = self.tmpCheckpoint();
        defer tmp.deinit();

        const fns = struct {
            fn getField(gen: *Codegen, type_union: Id, scope: []const u8) StructId {
                var value = gen.lookupIdent(
                    type_union.data().downcast(Types.AnyScope).?.pack(),
                    scope,
                ).?;
                const type_union_enum = gen.peval(0, value, Types.Id) catch unreachable;

                value = gen.lookupIdent(
                    type_union_enum.data().downcast(Types.AnyScope).?.pack(),
                    "Field",
                ).?;
                return (gen.peval(0, value, Types.Id) catch unreachable).data().Struct;
            }

            pub fn fnty(types: *Types, args: []const Id, ret: Id) FuncTyId {
                return types.funcTyOf(args, ret).data().FuncTy;
            }
        };

        var gen: Codegen = undefined;
        gen.init(&self, .nany(builtins.getScope(&self)), .never, tmp.allocator());
        _ = gen.bl.begin(.systemv, undefined);

        var value = gen.lookupIdent(gen.scope, "Type").?;
        const type_union = gen.peval(0, value, Types.Id) catch unreachable;

        value = gen.lookupIdent(gen.scope, "SrcLoc").?;
        const source_loc = gen.peval(0, value, Types.Id) catch unreachable;

        self.builtins = .{
            .type_union = type_union.data().Union,
            .enum_field = fns.getField(&gen, type_union, "Enum"),
            .union_field = fns.getField(&gen, type_union, "Union"),
            .struct_field = fns.getField(&gen, type_union, "Struct"),
            .source_loc = source_loc.data().Struct,
        };

        const @"^u8" = self.pointerTo(.u8);
        self.handler_signatures = .init(.{
            .slice_ioob = fns.fnty(&self, &.{ source_loc, .uint, .uint, .uint }, .never),
            .null_unwrap = fns.fnty(&self, &.{source_loc}, .never),
            .memcpy = fns.fnty(&self, &.{ @"^u8", @"^u8", .uint }, .void),
            .entry = .invalid,
            .for_loop_length_mismatch = fns.fnty(&self, &.{source_loc}, .never),
        });
    }

    return self;
}

pub fn deinit(self: *Types) void {
    self.ct_backend.mach.out.code = .empty;

    inline for (std.meta.fields(Types)) |f| {
        if (f.type == utils.Arena) continue;

        if (std.meta.hasMethod(f.type, "deinit")) {
            const base = if (@typeInfo(f.type) == .pointer)
                continue
            else
                f.type;

            const args = @typeInfo(@TypeOf(base.deinit)).@"fn".params;

            if (args.len == 2) {
                if (args[1].type == *Types) {
                    @field(self, f.name).deinit(self);
                } else if (args[1].type == std.mem.Allocator) {
                    @field(self, f.name).deinit(self.allocator());
                }
            } else {
                @field(self, f.name).deinit();
            }
        }
    }

    self.* = undefined;
}

pub fn reportSloc(self: *Types, slc: graph.Sloc, fmt: []const u8, args: anytype) void {
    if (slc == graph.Sloc.none) return;
    self.report(@enumFromInt(slc.namespace), slc.index, fmt, args);
}

pub fn report(
    self: *Types,
    file: File.Id,
    pos: u32,
    fmt: []const u8,
    args: anytype,
) void {
    const fl = file.get(self);
    Codegen.reportGeneric(fl.path, fl.source, self, pos, fmt, args);
    self.errored += 1;

    //std.debug.dumpCurrentStackTrace(@returnAddress());
}

pub fn allocator(self: *Types) std.mem.Allocator {
    return self.ct_backend.gpa;
}

pub fn tmpCheckpoint(self: *Types) TmpCheckpoint {
    self.tmp_depth += 1;
    return .{ .types = self };
}

pub fn pointerTo(self: *Types, ty: Id) Id {
    var pointer = Pointer{ .ty = ty };
    const slot = self.pointer_index.intern(self, &pointer);

    if (!slot.found_existing) {
        slot.key_ptr.* = self.pointers.push(&self.arena, pointer);
    }

    return .nany(slot.key_ptr.*);
}

pub fn arrayOf(self: *Types, elem: Id, len: Size) Id {
    var array = Array{ .elem = elem, .len = .{ .s = len } };
    const slot = self.array_index.intern(self, &array);

    if (!slot.found_existing) {
        slot.key_ptr.* = self.arrays.push(&self.arena, array);
    }

    return .nany(slot.key_ptr.*);
}

pub fn funcTyOf(self: *Types, args: []const Id, ret: Id) Id {
    var func_ty = FuncTy{ .args = args, .ret = ret };
    const slot = self.func_ty_index.intern(self, &func_ty);

    if (!slot.found_existing) {
        func_ty.args = self.arena.dupe(Id, args);
        slot.key_ptr.* = self.func_tys.push(&self.arena, func_ty);
    }

    return .nany(slot.key_ptr.*);
}

pub fn sliceOf(self: *Types, elem: Id) Id {
    var slice = Slice{ .elem = elem };
    const slot = self.slice_index.intern(self, &slice);

    if (!slot.found_existing) {
        slot.key_ptr.* = self.slices.push(&self.arena, slice);
    }

    return .nany(slot.key_ptr.*);
}

pub fn optionOf(self: *Types, inner: Id) Id {
    var option = Option{ .inner = inner };
    const slot = self.option_index.intern(self, &option);
    if (!slot.found_existing) {
        slot.key_ptr.* = self.options.push(&self.arena, option);
    }
    return .nany(slot.key_ptr.*);
}

pub fn collectAnalError(types: *anyopaque, err: hb.backend.static_anal.Error) void {
    const self: *Types = @ptrCast(@alignCast(types));

    switch (err) {
        .ReturningStack => |loc| {
            self.reportSloc(loc.slot, "stack location escapes the function", .{});
        },
        .StackOob => |loc| {
            self.reportSloc(loc.slot, "this slot has a out of bounds read/write", .{});
            self.reportSloc(loc.access, "...the access is here, stack slot has {} bytes," ++
                " while access is at {}..{}", .{ loc.size, loc.range.start, loc.range.end });
        },
        .LoopInvariantBreak => |loc| {
            self.reportSloc(loc.if_node, "the if condition is loop invariant but it" ++
                " decides wheter to break out ouf the loop", .{});
        },
        .InfiniteLoopWithBreak => |loc| {
            self.reportSloc(loc.loop, "the loop was declared with breaks or" ++
                " returns but they are all unreachable", .{});
        },
        .UsedPoison => |loc| {
            self.reportSloc(loc.loc, "reading from an uninitialized memory location", .{});
        },
    }
}

pub const CollectRelocCtx = struct {
    sloc: graph.Sloc,
    bytes: []const u8,
    relocs: *std.ArrayList(Machine.DataOptions.Reloc),
    scratch: *utils.Arena,
    allow_null: bool,
};

pub fn collectGlobalRelocs(
    self: *Types,
    id: GlobalId,
    relocs: *std.ArrayList(Machine.DataOptions.Reloc),
    scratch: *utils.Arena,
    allow_null: bool,
) void {
    self.collectRelocsRecur(.{
        .sloc = .{
            .index = id.get(self).scope.name_pos.sourcePos(),
            .namespace = id.get(self).scope.file.index(),
        },
        .bytes = id.get(self).data.get(self),
        .relocs = relocs,
        .scratch = scratch,
        .allow_null = allow_null,
    }, id.get(self).ty, 0);
}

pub fn collectRelocsRecur(
    self: *Types,
    ctx: CollectRelocCtx,
    ty: Id,
    offset: u32,
) void {
    switch (ty.data()) {
        .Builtin => {},
        .Enum => {},
        .FuncTy => {},
        .Option => |o| {
            const layout = o.get(self).getLayout(self);

            if (!std.mem.allEqual(
                u8,
                ctx.bytes[offset + layout.inner.offset ..][0..layout
                    .inner.storage.dataType().size()],
                0,
            )) {
                self.collectRelocsRecur(
                    ctx,
                    o.get(self).inner,
                    offset,
                );
            }
        },
        .Pointer => |p| {
            if (self.collectPointer(
                ctx.sloc,
                p.get(self).ty.data() == .FuncTy,
                offset,
                p.get(self).ty.size(self),
                ctx.bytes,
                ctx.allow_null,
            )) |reloc| {
                ctx.relocs.append(ctx.scratch.allocator(), reloc) catch unreachable;
            } else |_| {}
        },
        .Slice => |s| {
            const len: u64 = @bitCast(ctx.bytes[offset + Slice.len_offset ..][0..8].*);
            if (self.collectPointer(
                ctx.sloc,
                false,
                offset + Slice.ptr_offset,
                len * s.get(self).elem.size(self),
                ctx.bytes,
                ctx.allow_null,
            )) |reloc| {
                ctx.relocs.append(ctx.scratch.allocator(), reloc) catch unreachable;
            } else |_| {}
        },
        .Array => |a| {
            const elem_size = a.get(self).elem.size(self);
            for (0..a.get(self).len.s) |i| {
                const elem_offset = offset + elem_size * i;
                self.collectRelocsRecur(
                    ctx,
                    a.get(self).elem,
                    @intCast(elem_offset),
                );
            }
        },
        .Struct => |s| {
            for (s.get(self).getLayout(self).fields) |f| {
                self.collectRelocsRecur(
                    ctx,
                    f.ty,
                    @intCast(offset + f.offset),
                );
            }
        },
        .Union => |u| {
            const layout = u.get(self).getLayout(self);
            const tag = layout.tagLayout() orelse return;

            const tag_size = Id.nany(tag.id).size(self);
            var value: i64 = 0;
            @memcpy(
                std.mem.asBytes(&value)[0..tag_size],
                ctx.bytes[tag.offset..][0..tag_size],
            );

            const findex = std.mem.indexOfScalar(i64, tag.id.get(self)
                .getLayout(self).fields, value) orelse {
                self.reportSloc(ctx.sloc, "tagged union has an invalid tag", .{});
                return;
            };

            self.collectRelocsRecur(ctx, layout.fields[findex], offset);
        },
    }
}

pub fn collectPointer(
    self: *Types,
    sloc: graph.Sloc,
    is_func: bool,
    offset: u64,
    size: u64,
    bytes: []const u8,
    allow_null: bool,
) !Machine.DataOptions.Reloc {
    // TODO: if this becomes a bottleneck, optimize it
    const value: u64 = @bitCast(bytes[offset..][0..8].*);

    if (allow_null and value == 0) return .{
        .target = std.math.maxInt(u32),
        .offset = @intCast(offset),
        .is_func = is_func,
    };

    if (is_func) {
        for (0..self.funcs.meta.len) |i| {
            const sim = self.ct_backend.mach.out.getFuncSym(@intCast(i)) orelse continue;
            if (sim.offset == value) {
                std.debug.assert(size == 0);
                return .{
                    .target = @intCast(i),
                    .offset = @intCast(offset),
                    .is_func = true,
                };
            }
        } else {
            self.reportSloc(
                sloc,
                "global contains an invlaid function pointer",
                .{},
            );
        }
    } else {
        for (0..self.globals.meta.len) |i| {
            const sim = self.ct_backend.mach.out.getGlobalSym(@intCast(i)) orelse continue;
            if (sim.offset == value) {
                if (size > sim.size) {
                    self.reportSloc(
                        sloc,
                        "global contains an invlaid pointer (size overflow) (offset: {}) ({} > {})",
                        .{ sim.offset, size, sim.size },
                    );

                    break;
                }

                return .{
                    .target = @intCast(i),
                    .offset = @intCast(offset),
                    .is_func = false,
                };
            }
        } else {
            self.reportSloc(
                sloc,
                "global contains an invlaid pointer",
                .{},
            );
        }
    }

    return error.InvalidPointer;
}

pub fn nextFunc(self: *Types, target: Target, pop_until: usize) ?FuncId {
    const queue = self.func_queue.getPtr(target);
    while (queue.items.len > pop_until) {
        const func = queue.pop().?;
        if (!func.get(self).compiled.contains(target)) {
            func.get(self).compiled.insert(target);
            return func;
        }
    }

    return null;
}
