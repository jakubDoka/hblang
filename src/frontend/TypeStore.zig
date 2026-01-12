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
structs: utils.SegmentedList(Struct, StructId, 1024, 1024 * 1024) = .{},
struct_index: Interner(StructId) = .{},
funcs: utils.SegmentedList(Func, FuncId, 1024, 1024 * 1024) = .{},
func_index: Interner(FuncId) = .{},
globals: utils.SegmentedList(Global, GlobalId, 1024, 1024 * 1024) = .{},
global_index: Interner(GlobalId) = .{},
func_tys: utils.SegmentedList(FuncTy, FuncTyId, 1024, 1024 * 1024) = .{},
func_ty_index: Interner(FuncTyId) = .{},
templates: utils.SegmentedList(Template, TemplateId, 1024, 1024 * 1024) = .{},
template_index: Interner(TemplateId) = .{},

files: []File,
line_indexes: []const hb.LineIndex,
loader: *Loader,
backend: *Machine,
ct_backend: HbvmGen,
vm: hb.hbvm.Vm = .{},
abi: Abi = .systemv,
func_queue: std.EnumArray(Target, std.ArrayList(FuncId)) =
    .initFill(.empty),
errored: usize = 0,

const Types = @This();

pub const stack_size = 1024 * 128;

pub fn EntId(comptime T: type, comptime field: []const u8) type {
    return enum(u32) {
        _,

        pub const data = .{ .ty = T, .field = field };

        pub fn get(self: @This(), types: *Types) *T {
            return @field(types, data.field).at(self);
        }
    };
}

pub fn Interner(comptime I: type) type {
    return struct {
        map: Map = .empty,

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

    pub const upcast = generic.upcast;
    pub const downcast = generic.downcast;
    pub const scope = generic.scope;

    pub fn decls(self: @This(), types: *Types) *DeclIndex {
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
    Func: FuncId,
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
    Func: FuncId,

    pub const Conv = IdConv(AnyScopeRef, AnyScope);

    pub const upcast = generic.upcast;
    pub const downcast = generic.downcast;
    pub const scope = generic.scope;
    pub const pack = Conv.pack;
};

pub const generic = struct {
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
    FuncTy: FuncTyId,
    Struct: StructId,

    const scope_start = 2;

    pub const pack = Id.Conv.pack;

    pub fn size(self: Data, types: *Types) u64 {
        return switch (self) {
            .Builtin => |b| b.size(types),
            .FuncTy => 4,
            .Struct => |s| s.get(types).size(types),
        };
    }

    pub fn alignment(self: Data, types: *Types) u64 {
        return switch (self) {
            .Builtin => |b| b.alignment(types),
            .FuncTy => 4,
            .Struct => |s| s.get(types).alignment(types),
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

    pub fn size(self: Id, types: *Types) u64 {
        return self.data().size(types);
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

    pub fn alignment(self: Id, types: *Types) u64 {
        return self.data().alignment(types);
    }

    pub fn stackSpec(self: Id, types: *Types) graph.AbiParam.StackSpec {
        return .{
            .size = @intCast(self.size(types)),
            .alignment = @intCast(@min(4, std.math.log2_int(u64, self.alignment(types)))),
        };
    }

    pub fn format_(self: Id, types: *Types, writer: *std.io.Writer) !void {
        switch (self.data()) {
            .Builtin => |b| try writer.print("{s}", .{@tagName(b)}),
            .FuncTy => |f| {
                try writer.writeAll("fn(");
                for (f.get(types).args, 0..) |arg, i| {
                    try arg.format_(types, writer);
                    if (i != f.get(types).args.len - 1) try writer.writeAll(", ");
                }
                try writer.writeAll("): ");
                try f.get(types).ret.format_(types, writer);
            },
            .Struct => unreachable,
        }
    }

    pub fn fmt(self: Id, types: *Types) Fmt {
        return .{ .id = self, .types = types };
    }

    pub fn canUpcast(from: Id, to: Id, types: *Types) bool {
        if (from == .never) return true;
        if (from == to) return true;
        const is_bigger = from.size(types) < to.size(types);
        if (from.isBuiltin(.isUnsigned) and to.isBuiltin(.isUnsigned)) return is_bigger;
        if (from.isBuiltin(.isSigned) and to.isBuiltin(.isSigned)) return is_bigger;
        if (from.isBuiltin(.isUnsigned) and to.isBuiltin(.isSigned)) return is_bigger;
        //if (from.data() == .Enum and to.isBuiltin(.isUnsigned)) return from.size(types) <= to.size(types);
        //if (from.data() == .Enum and to.isBuiltin(.isSigned)) return is_bigger;
        if (from == .bool and to.isBuiltin(.isInteger)) return true;

        return false;
    }

    pub const Fmt = struct {
        id: Id,
        types: *Types,

        pub fn format(self: Fmt, writer: *std.io.Writer) !void {
            try self.id.format_(self.types, writer);
        }

        pub fn toString(self: Fmt, arena: *utils.Arena) []u8 {
            var tmp = utils.Arena.scrath(arena);
            defer tmp.deinit();
            var arr = std.io.Writer.Allocating.init(tmp.arena.allocator());
            self.format(&arr.writer) catch unreachable;
            return arena.dupe(u8, arr.written());
        }
    };

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

pub const Builtin = enum(u32) {
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
    template,
    any,

    pub const identity = {};

    pub fn isInteger(self: Builtin) bool {
        return self.isUnsigned() or self.isSigned();
    }

    pub fn isUnsigned(self: Builtin) bool {
        return @intFromEnum(Builtin.u8) <= @intFromEnum(self) and
            @intFromEnum(self) <= @intFromEnum(Id.uint);
    }

    pub fn isSigned(self: Builtin) bool {
        return @intFromEnum(Builtin.i8) <= @intFromEnum(self) and
            @intFromEnum(self) <= @intFromEnum(Id.int);
    }

    pub fn isFloat(self: Builtin) bool {
        return @intFromEnum(Builtin.f32) <= @intFromEnum(self) and
            @intFromEnum(self) <= @intFromEnum(Id.f64);
    }

    pub fn size(self: Builtin, _: *Types) u64 {
        return switch (self) {
            .void, .never => 0,
            .bool, .u8, .i8 => 1,
            .u16, .i16 => 2,
            .u32, .i32, .f32, .type, .template => 4,
            .u64, .i64, .f64, .uint, .int => 8,
            .any => unreachable,
        };
    }

    pub fn alignment(self: Builtin, types: *Types) u64 {
        return @max(self.size(types), 1);
    }
};

pub const Captures = struct {
    /// first byte in the name for each var
    prefixes: []const u8,
    variables: []const Variable,
    /// packed values for each comptime variable, index is comptuted when
    /// searching
    values: []const i64,

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

        const values = scratch.alloc(i64, scope.cmptime_values.items.len);
        for (scope.cmptime_values.items, values) |v, *slot| slot.* = v;

        return .{
            .prefixes = scratch.dupe(u8, scope.vars.items(.prefix)),
            .variables = variables,
            .values = values,
        };
    }

    pub fn lookup(self: Captures, source: [:0]const u8, name: []const u8) ?struct { Id, ?i64 } {
        // TODO: we can vectorize this

        var value_index: usize = 0;
        for (self.prefixes, self.variables) |prefix, variable| {
            if (prefix == name[0] and Lexer.compareIdent(source, variable.meta.offset, name)) {
                return .{ variable.ty, if (variable.meta.is_cmptime)
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
        file = std.math.maxInt(u32) - 1,
        empty,
        _,

        pub fn get(self: NamePos, file: File.Id, types: *Types) []const u8 {
            return switch (self) {
                .file => file.get(types).path,
                .empty => "",
                _ => |v| file.get(types).tokenStr(@intFromEnum(v)),
            };
        }
    };

    pub const Param = extern struct {};

    pub fn name(self: Scope, types: *Types) []const u8 {
        return self.name_pos.get(self.file, types);
    }
};

pub const StructId = EntId(Struct, "structs");
pub const Struct = struct {
    scope: Scope,
    captures: Captures,
    decls: *DeclIndex,

    pub fn size(self: Struct, types: *Types) u64 {
        _ = self; // autofix
        _ = types; // autofix
        unreachable;
    }

    pub fn alignment(self: Struct, types: *Types) u64 {
        _ = self; // autofix
        _ = types; // autofix
        unreachable;
    }
};

pub const FuncTyId = EntId(FuncTy, "func_tys");
pub const FuncTy = struct {
    args: []Id,
    ret: Id,

    pub fn hash(self: FuncTy, _: *Types) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(@ptrCast(self.args));
        hasher.update(@ptrCast(&self.ret));
        return hasher.final();
    }

    pub fn eql(self: *FuncTy, other: *FuncTy, _: *Types) bool {
        return std.meta.eql(self.args, other.args) and
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

    pub const Param = struct {
        name: u32,
        ty: Id,
        data: u64,
    };

    pub fn queue(self: *Func, target: Target, types: *Types) void {
        if (self.compiled.contains(target)) return;
        self.compiled.insert(target);
        types.func_queue.getPtr(target).append(
            types.arena.allocator(),
            types.funcs.ptrToIndex(self),
        ) catch unreachable;
    }
};

pub const TemplateId = EntId(Template, "templates");
pub const Template = struct {
    scope: Scope,
    captures: Captures,
};

pub const GlobalId = EntId(Global, "globals");
pub const Global = struct {
    scope: Scope,
    ty: Id,
    // NOTE: points to the vm memory
    data: struct {
        pos: u32,
        len: u32,

        pub fn get(self: @This(), types: *Types) []u8 {
            return types.ct_backend.mach.out.code.items[self.pos..][0..self.len];
        }
    },
    readonly: bool,
    runtime_emmited: bool = false,

    pub const hash = generic.hashScope;
    pub const eql = generic.eqlScope;
};

pub fn init(
    files: []File,
    loader: *Loader,
    backend: *Machine,
    arena: utils.Arena,
    gpa: std.mem.Allocator,
) Types {
    var self = Types{
        .files = files,
        .line_indexes = undefined,
        .ct_backend = HbvmGen{
            .gpa = gpa,
            .push_uninit_globals = true,
            .emit_global_reloc_offsets = true,
        },
        .loader = loader,
        .backend = backend,
        .arena = arena,
    };

    self.ct_backend.mach.out.code.resize(gpa, stack_size) catch unreachable;
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

    for (self.files, 0..) |*f, i| {
        f.root_sope = .nany(self.structs.push(
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
        ));
    }

    return self;
}

pub fn deinit(self: *Types) void {
    inline for (std.meta.fields(Types)) |f| {
        if (f.type == utils.Arena) continue;

        if (std.meta.hasMethod(f.type, "deinit")) {
            const base = if (@typeInfo(f.type) == .pointer)
                continue
            else
                f.type;

            if (@typeInfo(@TypeOf(base.deinit)).@"fn".params.len == 2) {
                @field(self, f.name).deinit(self);
            } else {
                @field(self, f.name).deinit();
            }
        }
    }

    self.* = undefined;
}

pub fn report(
    self: *Types,
    file: File.Id,
    pos: anytype,
    fmt: []const u8,
    args: anytype,
) void {
    const fl = file.get(self);
    Codegen.reportGeneric(fl.path, fl.source, self, pos, fmt, args);
}

pub fn allocator(self: *Types) std.mem.Allocator {
    return self.ct_backend.gpa;
}
