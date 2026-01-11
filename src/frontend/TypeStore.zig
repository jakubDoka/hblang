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

arena: utils.Arena,
store: utils.EntStore(Data) = .{},
files: []File,
line_indexes: []const hb.LineIndex,
loader: *Loader,
backend: *Machine,
ct_backend: HbvmGen,
vm: hb.hbvm.Vm = .{},
abi: Abi = .systemv,
func_queue: std.EnumArray(Target, std.ArrayList(utils.EntId(Func))) =
    .initFill(.empty),
errored: bool = false,
interner: std.HashMapUnmanaged(
    Id,
    void,
    InternerCtx,
    std.hash_map.default_max_load_percentage,
) = .{},

const Types = @This();

pub const InternerCtx = struct {
    types: *Types,

    pub fn eql(_: InternerCtx, a: Id, b: Id) bool {
        return a == b;
    }

    pub fn hash(self: InternerCtx, key: Id) u64 {
        return (InternerInsertCtx{ .types = self.types }).hash(switch (key.data()) {
            .Builtin => unreachable,
            inline .Struct,
            => |s, t| .{
                .scope = .{ t, &s.get(self.types).scope },
            },
            .Func => |f| .{ .func = f.get(self.types) },
        });
    }
};

pub const InternerInsertCtx = struct {
    types: *Types,

    pub const Entry = union(enum) {
        scope: struct { std.meta.Tag(Data), *Scope },
        func: *Func,
    };

    pub fn eql(self: @This(), a: Entry, b: Id) bool {
        switch (a) {
            .scope => |s| {
                if (b.data() != s[0]) return false;
                return std.meta.eql(s[1].*, b.data().downcast(Data.Scope).?.scope(self.types).*);
            },
            .func => |f| {
                if (b.data() != .Func) return false;
                const ofunc = b.data().Func.get(self.types);
                if (!std.meta.eql(f.scope, ofunc.scope)) return false;
                return std.mem.eql(u8, @ptrCast(f.params), @ptrCast(ofunc.params));
            },
        }
    }

    pub fn hash(_: @This(), key: Entry) u64 {
        var hasher = std.hash.Wyhash.init(0);

        switch (key) {
            .scope => |s| {
                hasher.update(std.mem.asBytes(&s[0]));
                hasher.update(std.mem.asBytes(s[1]));
            },
            .func => |f| {
                hasher.update(std.mem.asBytes(&std.meta.Tag(Data).Func));
                hasher.update(std.mem.asBytes(&f.scope));
                hasher.update(@ptrCast(f.params));
            },
        }

        return hasher.final();
    }
};

pub const Target = enum {
    runtime,
    cmptime,
};

pub const Data = union(enum(u8)) {
    Builtin: Builtin,
    Struct: utils.EntId(Struct),
    Func: utils.EntId(Func),

    pub const Repr = extern struct {
        tag: u32,
        value: u32,
    };

    pub const UnorderedScope = union(enum(u8)) {
        Struct: utils.EntId(Struct) = 1,

        pub const upcast = Data.upcast;
        pub const downcast = Data.downcast;
        pub const scope = Data.scope;

        pub fn decls(self: @This(), types: *Types) *DeclIndex {
            return switch (self) {
                inline else => |v| v.get(types).decls,
            };
        }
    };

    pub const Scope = union(enum(u8)) {
        Struct: utils.EntId(Struct) = 1,
        Func: utils.EntId(Func),

        pub const upcast = Data.upcast;
        pub const downcast = Data.downcast;
        pub const scope = Data.scope;

        pub fn parent(self: Data.Scope, types: *Types) ?Data.Scope {
            return self.scope(types).parent.data().downcast(Data.Scope);
        }
    };

    pub fn scope(self: anytype, types: *Types) *Types.Scope {
        return switch (self.*) {
            inline else => |v| &v.get(types).scope,
        };
    }

    pub fn size(self: Data, types: *Types) u64 {
        return switch (self) {
            .Builtin => |b| b.size(types),
            .Struct => |s| s.get(types).size(types),
            .Func,
            => unreachable,
        };
    }

    pub fn alignment(self: Data, types: *Types) u64 {
        return switch (self) {
            .Builtin => |b| b.alignment(types),
            .Struct => |s| s.get(types).alignment(types),
            .Func,
            => unreachable,
        };
    }

    pub fn upcast(self: anytype) Data {
        comptime std.debug.assert(@sizeOf(@TypeOf(self.*)) == @sizeOf(Data));
        return @as(*const Data, @ptrCast(self)).*;
    }

    pub fn downcast(self: anytype, comptime To: type) ?To {
        const Dt = @TypeOf(self.*);

        comptime var range_start = 0;
        comptime var range_end = 0;
        comptime {
            const to_fields = std.meta.fields(std.meta.Tag(To));

            for (std.meta.fields(std.meta.Tag(Dt))) |f| {
                for (to_fields) |of| {
                    if (std.mem.eql(u8, f.name, of.name)) {
                        if (f.value != of.value) {
                            @compileError(std.fmt.comptimePrint(
                                "subset mismatch {s}.{s}({} != {})",
                                .{
                                    @typeName(To),
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
                    @compileError(@typeName(To) ++ "is not continuous");
                }
                first += 1;
            }
            range_end = first;

            if (@sizeOf(To) != @sizeOf(Dt)) {
                @compileError("layout does not match for " ++ @typeName(To));
            }
        }

        if (range_start <= @intFromEnum(self.*) and
            @intFromEnum(self.*) <= range_end)
        {
            return @as(*const To, @ptrCast(self)).*;
        }

        return null;
    }

    comptime {
        var val = Data{ .Builtin = .int };
        std.debug.assert(val.downcast(Data.Scope) == null);
    }

    // assert that all the stuff in others is a subset of Data with the
    // matching tag values
};

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
    any,
    _,

    pub const Repr = packed struct(u32) {
        tag: std.meta.Tag(std.meta.Tag(Data)),
        index: std.meta.Int(.unsigned, 32 - @bitSizeOf(std.meta.Tag(Data))),
    };

    pub fn nany(value: anytype) Id {
        inline for (std.meta.fields(Data)) |f| {
            if (f.type == @TypeOf(value)) {
                return .init(@unionInit(Data, f.name, value));
            }
        }
        @compileError(@typeName(@TypeOf(value)));
    }

    pub fn init(dt: Data) Id {
        const data_repr = @as(*const Data.Repr, @ptrCast(&dt)).*;
        const repr = Repr{
            .tag = @intCast(data_repr.tag),
            .index = @intCast(data_repr.value),
        };
        return @enumFromInt(@as(u32, @bitCast(repr)));
    }

    pub fn data(self: Id) Data {
        const repr: Repr = @bitCast(@intFromEnum(self));
        return @as(*const Data, @ptrCast(&Data.Repr{
            .value = repr.index,
            .tag = repr.tag,
        })).*;
    }

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
        _ = types;
        switch (self.data()) {
            .Builtin => |b| try writer.print("{s}", .{@tagName(b)}),
            .Struct => unreachable,
            .Func => unreachable,
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
            std.debug.assert(std.mem.eql(u8, a.name, b.name));
        }

        for (
            std.meta.fields(Id)[0 .. std.meta.fields(Id).len - 1],
            std.meta.fields(Lexer.Lexeme.Type),
        ) |a, b| {
            std.debug.assert(std.mem.eql(u8, a.name, b.name));
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
            .u32, .i32, .f32, .type => 4,
            .u64, .i64, .f64, .uint, .int => 8,
            .any => unreachable,
        };
    }

    pub fn alignment(self: Builtin, types: *Types) u64 {
        return @max(self.size(types), 1);
    }
};

pub const Scope = extern struct {
    parent: Id,
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

pub const StructId = utils.EntId(Struct);
pub const Struct = struct {
    scope: Scope,
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

pub const FuncId = utils.EntId(Func);
pub const Func = struct {
    scope: Scope,
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
            types.store.ptrToId(self),
        ) catch unreachable;
    }
};

pub const Global = struct {
    scope: Scope,
    ty: Id,
    // NOTE: points to the vm memory
    data: struct {
        pos: u32,
        len: u32,
    },
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
        .ct_backend = HbvmGen{ .gpa = gpa },
        .loader = loader,
        .backend = backend,
        .arena = arena,
    };

    const line_indexes = self.arena.alloc(hb.LineIndex, self.files.len);
    for (self.files, line_indexes) |f, *li| li.* = f.lines;
    self.line_indexes = line_indexes;

    const out_files = self.arena.alloc(Machine.Data.File, self.files.len);
    for (self.files, out_files) |f, *of| {
        of.* = .{ .name = f.path, .size = @intCast(f.source.len) };
    }
    backend.out.files = out_files;

    for (self.files, 0..) |*f, i| {
        f.root_sope = .nany(self.store.add(
            &self.arena,
            Struct{
                .scope = .{
                    .parent = .void,
                    .file = @enumFromInt(i),
                    .name_pos = .file,
                },
                .decls = &f.decls,
            },
        ));
    }

    return self;
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
