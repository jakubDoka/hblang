const std = @import("std");

const root = @import("hb");
const graph = root.backend.graph;
const utils = root.utils;
const static_anal = root.backend.static_anal;
const Ast = root.frontend.Ast;
const Arena = utils.Arena;
const Codegen = root.frontend.Codegen;
const Comptime = root.frontend.Comptime;
const Lexer = root.frontend.Lexer;
const HbvmGen = root.hbvm.HbvmGen;
const Vm = root.hbvm.Vm;
const Machine = root.backend.Machine;
const tys = root.frontend.types;

pub const Abi = root.frontend.Abi;

pub const comptime_only_fn = Machine.max_func - 1;

errored: bool = false,
alignment: void align(std.atomic.cache_line) = {},
store: utils.EntStore(tys) = .{},
pool: utils.Pool,
interner: TypeIndex = .{},
string_globals: StringGlobalIndex = .{},
ct: Comptime,
diagnostics: ?*std.Io.Writer,
colors: std.io.tty.Config = .no_color,
files: []const Ast,
file_scopes: []Id,
line_indexes: []const utils.LineIndex,
stack_base: usize,
target: []const u8 = "hbvm-ableos",
func_work_list: std.EnumArray(Target, std.ArrayList(utils.EntId(tys.Func))),
global_work_list: std.EnumArray(Target, std.ArrayList(utils.EntId(tys.Global))),
remote_ids: std.ArrayList(tys.Func.RrmoteId) = .empty,
string: Id = undefined,
type_info: Id = undefined,
source_loc: Id = undefined,
handlers: Handlers = .{},
tmp_templates: ?utils.EntId(tys.Template) = null,
tmp_funcs: ?utils.EntId(tys.Func) = null,
handler_signatures: std.EnumArray(
    std.meta.FieldEnum(Handlers),
    ?Handlers.Signature,
) = undefined,
stats: struct {
    useless_ecas: u64 = 0,
    total_ecas: u64 = 0,
    full_jit_exprs: u64 = 0,
    skipped_global_jit_exprs: u64 = 0,
    skipped_constant_jit_exprs: u64 = 0,
    skipped_buty_jit_exprs: u64 = 0,
    unique_globals: u64 = 0,
} = .{},
metrics: Metrics,

const Metrics = utils.TimeMetrics(enum {
    exports,
    build,
    retain_globals,
    emit_func,
    dump_anal_errors,
    instantiate,
    jit,
    jit_emit_func,
    hbvm,
});

const Types = @This();
const TypeIndex = std.hash_map.HashMapUnmanaged(
    Id,
    void,
    TypeCtx,
    std.hash_map.default_max_load_percentage,
);
const StringGlobalIndex = std.hash_map.HashMapUnmanaged(
    utils.EntId(tys.Global),
    void,
    StringGlobalCtx,
    std.hash_map.default_max_load_percentage,
);

pub const TypeCtx = struct {
    types: *Types,

    pub fn eql(self: @This(), a: Id, b: Id) bool {
        const ad, const bd = .{ a.data(), b.data() };
        if (std.meta.activeTag(ad) != std.meta.activeTag(bd)) return false;

        return switch (ad) {
            .Builtin => |bl| bl == bd.Builtin,
            .FnPtr => |s| {
                return self.types.store.get(s).ret == self.types.store.get(bd.FnPtr).ret and
                    std.mem.eql(Id, self.types.store.get(s).args, self.types.store.get(bd.FnPtr).args);
            },
            inline .Slice, .Simd, .Pointer, .Array => |s, t| std.meta.eql(
                self.types.store.get(s).*,
                self.types.store.get(@field(bd, @tagName(t))).*,
            ),
            .Nullable => |n| std.meta.eql(self.types.store.get(n).inner, self.types.store.get(bd.Nullable).inner),
            .Tuple => |n| std.mem.eql(Id, @ptrCast(self.types.store.get(n).fields), @ptrCast(self.types.store.get(bd.Tuple).fields)),
            .Enum, .Union, .Struct, .Func, .Template, .Global => {
                const as = a.getKey(self.types);
                const bs = b.getKey(self.types);
                return as.eql(bs.*);
            },
        };
    }

    pub fn hash(self: @This(), key: Id) u64 {
        var hasher = std.hash.Fnv1a_64.init();
        const adk = key.data();
        std.hash.autoHash(&hasher, std.meta.activeTag(adk));
        switch (adk) {
            .Builtin => unreachable,
            inline .Pointer, .Slice, .Simd, .Array => |s| std.hash.autoHash(&hasher, self.types.store.get(s).*),
            .Nullable => |n| std.hash.autoHash(&hasher, self.types.store.get(n).inner),
            // its an array of integers, splat
            .Tuple => |n| hasher.update(@ptrCast(self.types.store.get(n).fields)),
            .FnPtr => |s| {
                hasher.update(std.mem.asBytes(&self.types.store.get(s).ret));
                hasher.update(@ptrCast(self.types.store.get(s).args));
            },
            .Enum, .Union, .Struct, .Func, .Template, .Global => {
                const scope = switch (adk) {
                    inline .Enum, .Union, .Struct, .Func, .Template, .Global => |v| &self.types.store.get(v).key,
                    else => unreachable,
                };

                scope.hash(&hasher);
            },
        }
        return hasher.final();
    }
};

pub const StringGlobalCtx = struct {
    types: *Types,

    pub fn eql(self: @This(), a: utils.EntId(tys.Global), b: utils.EntId(tys.Global)) bool {
        return std.mem.eql(
            u8,
            a.get(self.types).data.slice(&self.types.ct),
            b.get(self.types).data.slice(&self.types.ct),
        ) and std.mem.eql(
            tys.Global.Reloc,
            a.get(self.types).relocs,
            b.get(self.types).relocs,
        );
    }

    pub fn hash(self: @This(), adapted_key: utils.EntId(tys.Global)) u64 {
        var hasher = std.hash.Fnv1a_64.init();

        hasher.update(adapted_key.get(self.types).data.slice(&self.types.ct));
        hasher.update(@ptrCast(adapted_key.get(self.types).relocs));

        return hasher.final();
    }
};

pub const Handlers = struct {
    slice_ioob: ?utils.EntId(tys.Func) = null,
    null_unwrap: ?utils.EntId(tys.Func) = null,
    memcpy: ?utils.EntId(tys.Func) = null,
    entry: ?utils.EntId(tys.Func) = null,
    for_loop_length_mismatch: ?utils.EntId(tys.Func) = null,

    pub const Signature = struct { args: []const Id, ret: Id };
};

pub const Scope = struct {
    loc: struct {
        file: Types.File = .root,
        scope: Id = .void,
        ast: Ast.Id = .zeroSized(.Void),
        capture_len: u16 = 0,
    } = .{},
    name_pos: NamePos = .empty_name,
    captures_ptr: [*]const Capture = undefined,

    comptime {
        std.debug.assert(std.meta.hasUniqueRepresentation(Scope));
    }

    pub const NamePos = enum(u32) {
        string = std.math.maxInt(u32) - 4,
        main,
        file_name,
        generic_name,
        empty_name,
        _,
    };

    pub const Capture = struct {
        id: packed struct(u32) {
            index: u30,
            from_any: bool = false,
            has_value: bool,

            pub fn fromCapture(cap: Ast.Capture) @This() {
                return .{ .index = @intCast(cap.id.pos()), .has_value = cap.pos.flag.@"comptime" };
            }
        },
        ty: Id,
        value: i64 = 0,

        comptime {
            std.debug.assert(@sizeOf(@This()) == 16);
        }

        pub fn ident(self: Capture) Ast.Ident {
            return @enumFromInt(self.id.index);
        }
    };

    pub const dummy = Scope{};

    pub fn captures(self: Scope) []const Capture {
        return self.captures_ptr[0..self.loc.capture_len];
    }

    pub fn name(self: *const Scope, types: *Types) []const u8 {
        return switch (self.name_pos) {
            .empty_name => "",
            .generic_name => "-",
            .file_name => types.getFile(self.loc.file).path,
            .main => "main",
            .string => b: {
                const parent: *const tys.Global = @fieldParentPtr("key", self);
                break :b parent.data.slice(&types.ct);
            },
            else => types.getFile(self.loc.file).tokenSrc(@intFromEnum(self.name_pos)),
        };
    }

    pub fn setCaptures(self: *Scope, captres: []const Capture) void {
        self.loc.capture_len = @intCast(captres.len);
        self.captures_ptr = captres.ptr;
    }

    pub fn eql(self: Scope, other: Scope) bool {
        return self.loc.file == other.loc.file and
            self.loc.scope == other.loc.scope and
            self.loc.ast == other.loc.ast and
            std.mem.eql(u64, @ptrCast(self.captures()), @ptrCast(other.captures()));
    }

    pub fn hash(self: Scope, hasher: anytype) void {
        // we can safely hash the prefix as it contains
        // only integers
        hasher.update(std.mem.asBytes(&self.loc));

        // we skip the name and also splat the captures since they
        // have no padding bites
        hasher.update(@ptrCast(self.captures()));
    }
};

pub const File = enum(u16) { root, _ };

pub const IdRepr = u32;

pub const Data = utils.EntStore(root.frontend.types).Data;

pub const Id = enum(IdRepr) {
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

    comptime {
        std.debug.assert(std.meta.fields(Id).len == std.meta.fields(Builtin).len);
    }

    const Repr = packed struct(IdRepr) {
        data: std.meta.Int(.unsigned, @bitSizeOf(IdRepr) - @bitSizeOf(std.meta.Tag(Data))),
        flag: std.meta.Tag(std.meta.Tag(Data)),

        inline fn tag(self: Repr) std.meta.Tag(Data) {
            return @enumFromInt(self.flag);
        }
    };

    const RawData = extern struct {
        id: u32,
        tag: u32,
    };

    pub fn smallestIntFor(value: u64) Id {
        if (value == 0) return .void;
        return @enumFromInt(@intFromEnum(Id.u8) + std.math.log2_int_ceil(u64, value) / 8);
    }

    pub fn fromRaw(raw: i64, types: *Types) ?Id {
        const repr: Repr = @bitCast(std.math.cast(u32, raw) orelse return null);
        if (repr.flag >= std.meta.fields(Data).len) return null;

        switch (repr.tag()) {
            .Builtin => {
                if (repr.data >= std.meta.fields(tys.Builtin).len) return null;
            },
            inline else => |t| {
                if (!types.store.isValid(t, repr.data)) return null;
            },
        }

        return @enumFromInt(raw);
    }

    pub fn fromLexeme(lexeme: Lexer.Lexeme.Type) Id {
        comptime {
            std.debug.assert(@intFromEnum(Lexer.Lexeme.Type.never) == @intFromEnum(Id.never));
        }
        return @enumFromInt(@intFromEnum(lexeme));
    }

    pub fn init(dt: Data) Id {
        const raw: *const RawData = @ptrCast(&dt);
        const raw_id = Repr{ .flag = @intFromEnum(dt), .data = @intCast(raw.id) };
        return @enumFromInt(@as(IdRepr, @bitCast(raw_id)));
    }

    pub fn perm(self: Id, types: *Types) Id {
        switch (self.data()) {
            .Template => |t| if (types.store.get(t).temporary) return types.store.get(t).key.loc.scope,
            else => {},
        }

        return self;
    }

    pub fn needsTag(self: Id, types: *Types) bool {
        return self.data() == .Nullable and !self.data().Nullable.isCompact(types);
    }

    pub fn firstType(self: Id, types: *Types) Id {
        return switch (self.data()) {
            .Struct, .Union, .Enum => self,
            inline .Func, .Template, .Global => |t| types.store.get(t).key.loc.scope.firstType(types),
            .Builtin, .Tuple, .Pointer, .Nullable, .Slice, .FnPtr, .Simd, .Array => unreachable,
        };
    }

    pub fn file(self: Id, types: *Types) ?File {
        return switch (self.data()) {
            .Builtin, .Pointer, .Slice, .Nullable, .Tuple, .FnPtr, .Simd, .Array => null,
            inline else => |v| types.store.get(v).key.loc.file,
        };
    }

    pub fn index(self: Id, types: *Types) ?*Ast.Index {
        return switch (self.data()) {
            inline .Struct, .Union, .Enum => |v| &types.store.get(v).index,
            else => null,
        };
    }

    pub fn getKey(self: Id, types: *Types) *Scope {
        return switch (self.data()) {
            .Builtin, .Pointer, .Slice, .Nullable, .Tuple, .FnPtr, .Simd, .Array => utils.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| &types.store.get(v).key,
        };
    }

    pub fn getAst(self: Id, types: *Types) Ast.Id {
        return self.getKey(types).loc.ast;
    }

    pub fn items(self: Id, ast: *const Ast, types: *Types) Ast.Slice {
        return switch (self.data()) {
            .Global, .Builtin, .Pointer, .Slice, .Nullable, .Tuple, .FnPtr, .Simd, .Array => utils.panic("{s}", .{@tagName(self.data())}),
            .Template, .Func => .{},
            inline else => |v| ast.exprs.get(types.store.get(v).key.loc.ast).Type.fields,
        };
    }

    pub fn captures(self: Id, types: *Types) []const Scope.Capture {
        return self.getKey(types).captures();
    }

    pub fn findCapture(self: Id, id: Ast.Ident, types: *Types) ?*const Scope.Capture {
        return for (self.getKey(types).captures()) |*cp| {
            if (cp.id.index == @intFromEnum(id)) break cp;
        } else null;
    }

    pub fn parent(self: Id, types: *Types) Id {
        return self.getKey(types).loc.scope;
    }

    pub fn isInteger(self: Id) bool {
        return self.isUnsigned() or self.isSigned();
    }

    pub fn isFloat(self: Id) bool {
        return switch (self) {
            .f32, .f64 => true,
            else => false,
        };
    }

    pub fn isUnsigned(self: Id) bool {
        return @intFromEnum(Id.u8) <= @intFromEnum(self) and @intFromEnum(self) <= @intFromEnum(Id.uint);
    }

    pub fn isSigned(self: Id) bool {
        return @intFromEnum(Id.i8) <= @intFromEnum(self) and @intFromEnum(self) <= @intFromEnum(Id.int);
    }

    pub fn data(self: Id) Data {
        const repr: Repr = @bitCast(@intFromEnum(self));
        const raw = RawData{ .tag = repr.flag, .id = repr.data };
        return @as(*const Data, @ptrCast(&raw)).*;
    }

    pub fn child(self: Id, types: *Types) ?Id {
        return switch (self.data()) {
            .Pointer => |p| types.store.get(p).*,
            .Nullable => |n| types.store.get(n).inner,
            .Slice => |s| types.store.get(s).elem,
            .Array => |s| types.store.get(s).elem,
            else => null,
        };
    }

    pub fn len(self: Id, types: *Types) ?u64 {
        return switch (self.data()) {
            inline .Struct, .Union, .Enum, .Tuple => |s| s.getFields(types).len,
            .Array => |s| types.store.get(s).len,
            else => null,
        };
    }

    pub fn findNieche(self: Id, types: *Types) ?root.frontend.types.Nullable.NiecheSpec {
        return switch (self.data()) {
            .Builtin => |b| switch (b) {
                .never => .{ .offset = 0, .kind = .impossible },
                else => null,
            },
            .Enum => |u| if (u.getFields(types).len == 0)
                .{ .offset = 0, .kind = .impossible }
            else
                null,
            .Union => |u| if (u.getFields(types).len == 0)
                .{ .offset = 0, .kind = .impossible }
            else
                null,
            .Pointer => return .{ .offset = 0, .kind = .ptr },
            .Slice => return .{ .offset = tys.Slice.ptr_offset, .kind = .ptr },
            .Struct => |s| {
                var offs: tys.Struct.Id.OffIter = s.offsetIter(types);

                while (offs.next()) |o| {
                    if (o.field.ty.findNieche(types)) |n| return .{
                        .offset = @as(@TypeOf(n.offset), @intCast(o.offset)) + n.offset,
                        .kind = n.kind,
                    };
                }

                return null;
            },
            else => null,
        };
    }

    pub fn size(self: Id, types: *Types) u64 {
        return switch (self.data()) {
            .Builtin => |b| switch (b) {
                .never, .any => 0,
                .void => 0,
                .u8, .i8, .bool => 1,
                .u16, .i16 => 2,
                .type => @sizeOf(Id),
                .u32, .i32, .f32 => 4,
                .uint, .i64, .f64, .u64, .int => 8,
            },
            .Pointer, .FnPtr => 8,
            .Enum => |e| e.getBackingInt(types).size(types),
            .Tuple => |t| {
                var total_size: u64 = 0;
                var alignm: u64 = 1;
                for (t.getFields(types)) |f| {
                    alignm = @max(alignm, f.ty.alignment(types));
                    total_size = std.mem.alignForward(u64, total_size, f.ty.alignment(types));
                    total_size += f.ty.size(types);
                }
                total_size = std.mem.alignForward(u64, total_size, alignm);
                return total_size;
            },
            .Union => |u| u.size(types),
            .Struct => |s| s.getSize(types),
            .Array => |s| types.store.get(s).len * types.store.get(s).elem.size(types),
            .Slice => 16,
            .Nullable => |n| n.size(types),
            .Simd => |s| types.store.get(s).len * types.store.get(s).elem.size(types),
            .Global, .Func, .Template => 0,
        };
    }

    pub fn alignment(self: Id, types: *Types) u64 {
        return switch (self.data()) {
            .Builtin, .Enum => @max(1, self.size(types)),
            .Pointer, .FnPtr => 8,
            .Nullable => |n| types.store.get(n).inner.alignment(types),
            .Struct => |s| s.getAlignment(types),
            .Union => |u| u.alignment(types),
            .Tuple => |s| {
                var alignm: u64 = 1;
                for (s.getFields(types)) |f| {
                    alignm = @max(alignm, f.ty.alignment(types));
                }
                return alignm;
            },
            .Slice => 8,
            .Array => |s| types.store.get(s).elem.alignment(types),
            .Simd => |s| types.store.get(s).elem.alignment(types) *
                types.store.get(s).len,
            .Global, .Func, .Template => 1,
        };
    }

    pub fn stackSpec(self: Id, types: *Types) graph.AbiParam.StackSpec {
        return .{
            .size = @intCast(self.size(types)),
            .alignment = @intCast(@min(4, std.math.log2_int(u64, self.alignment(types)))),
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

    pub const Fmt = struct {
        self: Id,
        tys: *Types,
        root: Id = .void,

        const Task = union(enum) {
            Name: []const u8,
            Type: Id,
            Value: Val,
            PushScope: Id,
            PopScope: usize,

            const Val = struct {
                ty: Id,
                offset: u32 = 0,
                value: i64,

                pub fn normalize(slf: Val, ts: *Types) Val {
                    return .{ .value = switch (Abi.ableos.categorize(slf.ty, ts)) {
                        .Impossible, .Imaginary, .ByValue => readFromGlobal(ts, @enumFromInt(slf.value), slf.ty, slf.offset),
                        .ByRef, .ByValuePair => slf.value,
                    }, .ty = slf.ty, .offset = slf.offset };
                }
            };

            pub fn format(s: *const @This(), wrter: *std.Io.Writer) !void {
                switch (s.*) {
                    .Name => |n| try wrter.print("name: {s}", .{n}),
                    .Type => |t| try wrter.print("ty: {}", .{t.data()}),
                    .Value => |v| try wrter.print("v: {}", .{v}),
                    .PopScope => try wrter.writeAll("pop scope"),
                }
            }
        };

        pub fn toString(self: *const Fmt, arena: *utils.Arena) []u8 {
            var tmp = utils.Arena.scrath(arena);
            defer tmp.deinit();
            var arr = std.Io.Writer.Allocating.init(tmp.arena.allocator());
            self.fmt(&arr.writer, tmp.arena);
            return arena.dupe(u8, arr.written());
        }

        pub fn fmt(self: *const Fmt, writer: *std.Io.Writer, to: ?*utils.Arena) void {
            errdefer unreachable;

            var tmp = utils.Arena.scrath(to);
            defer tmp.deinit();

            var work_list = tmp.arena.makeArrayList(Task, 16);
            var scope_stack = std.ArrayList(Id).empty;

            work_list.appendAssumeCapacity(.{ .Type = self.self });

            while (work_list.pop()) |task| switch (task) {
                .PopScope => |v| scope_stack.items.len = v,
                .PushScope => |v| try scope_stack.append(tmp.arena.allocator(), v),
                .Type => |t| switch (t.data()) {
                    .Builtin => |b| try writer.writeAll(@tagName(b)),
                    .Pointer => |p| {
                        try writer.writeAll("^");
                        work_list.appendAssumeCapacity(.{ .Type = self.tys.store.get(p).* });
                    },
                    .FnPtr => |p| {
                        try writer.writeAll("^fn(");
                        const fp = self.tys.store.get(p);
                        work_list.ensureUnusedCapacity(
                            tmp.arena.allocator(),
                            fp.args.len + 3,
                        ) catch unreachable;
                        work_list.appendAssumeCapacity(.{ .Type = fp.ret });
                        work_list.appendAssumeCapacity(.{ .Name = "): " });
                        var iter = std.mem.reverseIterator(fp.args);
                        while (iter.next()) |arg| {
                            work_list.appendAssumeCapacity(.{ .Type = arg });
                            work_list.appendAssumeCapacity(.{ .Name = ", " });
                        }
                        _ = work_list.pop();
                    },
                    .Slice => |s| {
                        try writer.writeAll("[]");
                        work_list.appendAssumeCapacity(.{ .Type = self.tys.store.get(s).elem });
                    },
                    .Array => |s| {
                        try writer.print("[{d}]", .{self.tys.store.get(s).len});
                        work_list.appendAssumeCapacity(.{ .Type = self.tys.store.get(s).elem });
                    },
                    .Nullable => |n| {
                        try writer.writeAll("?");
                        work_list.appendAssumeCapacity(.{ .Type = self.tys.store.get(n).inner });
                    },
                    .Simd => |s| {
                        try writer.writeAll("@simd(");
                        try work_list.appendSlice(tmp.arena.allocator(), &.{
                            .{ .Name = ")" },
                            .{ .Value = .{ .ty = .uint, .value = @intCast(self.tys.store.get(s).len) } },
                            .{ .Name = ", " },
                            .{ .Type = self.tys.store.get(s).elem },
                        });
                    },
                    .Tuple => |tupl| {
                        try writer.writeAll("(");
                        var iter = std.mem.reverseIterator(self.tys.store.get(tupl).fields);
                        work_list.appendAssumeCapacity(.{ .Name = ")" });
                        if (iter.index != 0) {
                            work_list.ensureUnusedCapacity(
                                tmp.arena.allocator(),
                                iter.index * 2,
                            ) catch unreachable;
                            while (iter.next()) |elem| {
                                work_list.appendAssumeCapacity(.{ .Type = elem.ty });
                                work_list.appendAssumeCapacity(.{ .Name = ", " });
                            }
                            _ = work_list.pop();
                        }
                    },
                    .Func, .Global, .Template, .Struct, .Union, .Enum => {
                        std.debug.assert(t.data() != .Template or
                            self.tys.store.get(t.data().Template).temporary == false);

                        var cursor: Id = t;
                        var depth: usize = 0;
                        const frame = scope_stack.items.len;
                        work_list.appendAssumeCapacity(.{ .PopScope = frame });
                        while (cursor != .void) : (depth += 1) {
                            if (std.mem.indexOfScalar(Id, scope_stack.items, cursor) != null) {
                                try work_list.append(tmp.arena.allocator(), .{ .Name = "." });
                                break;
                            }
                            const key = cursor.getKey(self.tys);
                            cursor = key.loc.scope;

                            try work_list.ensureUnusedCapacity(tmp.arena.allocator(), key.captures().len * 2 + 4);
                            if (key.captures().len != 0) {
                                work_list.appendAssumeCapacity(.{ .Name = ")" });
                                for (key.captures()) |cap| {
                                    if (cap.id.from_any) {
                                        work_list.appendAssumeCapacity(.{ .Type = cap.ty });
                                    } else {
                                        work_list.appendAssumeCapacity(.{ .Value = .{ .ty = cap.ty, .value = cap.value } });
                                    }
                                    work_list.appendAssumeCapacity(.{ .Name = ", " });
                                }
                                work_list.items[work_list.items.len - 1] = .{ .Name = "(" };
                            }

                            work_list.appendAssumeCapacity(.{ .PushScope = cursor });
                            if (key.name_pos != .empty_name and key.name_pos != .generic_name) {
                                const name = key.name(self.tys);
                                if (key.loc.scope == .void) {
                                    const end = std.mem.lastIndexOfScalar(u8, name, '.') orelse name.len;
                                    work_list.appendAssumeCapacity(.{ .Name = name[0..end] });
                                } else {
                                    work_list.appendAssumeCapacity(.{ .Name = name });
                                }
                                work_list.appendAssumeCapacity(.{ .Name = "." });
                            }
                        }
                        _ = work_list.pop();
                    },
                },
                .Name => |n| try writer.writeAll(n),
                .Value => |v| switch (v.ty.data()) {
                    .Builtin => |b| switch (@as(Builtin, b)) {
                        .never, .any => try writer.writeAll("<invalid>"),
                        .void => try writer.writeAll(".()"),
                        .bool => try writer.writeAll(if (v.value != 0) "true" else "false"),
                        .u8, .u16, .u32, .u64, .uint => try writer.print("{d}", .{v.value}),
                        // FIXME: this will not display smaller ints correctly
                        .i8, .i16, .i32, .i64, .int => try writer.print("{d}", .{@as(i64, @bitCast(v.value))}),
                        .f32 => try writer.print("{}", .{@as(f32, @bitCast(@as(u32, @truncate(@as(u64, @bitCast(v.value))))))}),
                        .f64 => try writer.print("{}", .{@as(f64, @bitCast(@as(u64, @bitCast(v.value))))}),
                        .type => work_list.appendAssumeCapacity(.{ .Type = @enumFromInt(v.value) }),
                    },
                    .Array => |s| {
                        const arr: *tys.Array = self.tys.store.get(s);
                        const ln, const global = .{ arr.len, v.value };

                        try writer.writeAll(".[");

                        try self.formatSeq(&work_list, tmp.arena, arr.elem, ln, global);
                    },
                    .Slice => |s| {
                        const slc: tys.Slice = self.tys.store.get(s).*;
                        const ln, const global, const base = b: {
                            const ptr = readFromGlobal(self.tys, @enumFromInt(v.value), .uint, v.offset + tys.Slice.ptr_offset);
                            const ln = readFromGlobal(self.tys, @enumFromInt(v.value), .uint, v.offset + tys.Slice.len_offset);

                            const global = self.tys.findSymForPtr(@intCast(ptr));
                            break :b .{ ln, global catch |err| {
                                try writer.writeAll("<corrupted-slice>(");
                                try writer.writeAll(@errorName(err));
                                try writer.writeAll(")");
                                continue;
                            }, 0 };
                        };

                        if (slc.elem == .u8) {
                            const glb: utils.EntId(tys.Global) = @enumFromInt(global);
                            try writer.writeAll("\"");
                            try writer.writeAll(self.tys.store.get(glb).data
                                .slice(&self.tys.ct)[@intCast(base)..][0..@intCast(ln)]);
                            try writer.writeAll("\"");
                            continue;
                        }

                        try writer.writeAll("&.[");

                        try self.formatSeq(&work_list, tmp.arena, slc.elem, @intCast(ln), global);
                    },
                    .Struct => |s| {
                        var offsets = @as(tys.Struct.Id, s).offsetIter(self.tys);
                        try writer.writeAll(".{");
                        work_list.ensureUnusedCapacity(tmp.arena.allocator(), offsets.fields.len * 2) catch unreachable;
                        work_list.appendAssumeCapacity(.{ .Name = "}" });
                        const base = work_list.items.len;
                        while (offsets.next()) |elem| {
                            work_list.appendAssumeCapacity(.{ .Name = ", " });
                            work_list.appendAssumeCapacity(.{ .Name = elem.field.name });
                            work_list.appendAssumeCapacity(.{ .Name = ": " });
                            work_list.appendAssumeCapacity(.{ .Value = .normalize(.{
                                .ty = elem.field.ty,
                                .value = v.value,
                                .offset = @intCast(v.offset + elem.offset),
                            }, self.tys) });
                        }
                        std.mem.reverse(Task, work_list.items[base..]);
                        _ = work_list.pop();
                    },
                    .Pointer => |p| {
                        const ty: Id = self.tys.store.get(p).*;
                        const global = self.tys.findSymForPtr(@intCast(v.value)) catch |err| {
                            try writer.writeAll("<corrupted-pointer>(");
                            try writer.writeAll(@errorName(err));
                            try writer.writeAll(")");
                            return;
                        };

                        try writer.writeAll("&");
                        work_list.appendAssumeCapacity(.{
                            .Value = .normalize(.{ .ty = ty, .value = global }, self.tys),
                        });
                    },
                    .FnPtr, .Simd => {
                        unreachable;
                    },
                    .Tuple => |t| {
                        try writer.writeAll(".(");
                        var iter = @as(tys.Tuple.Id, t).offsetIter(self.tys);
                        while (iter.next()) |elem| {
                            work_list.appendAssumeCapacity(.{ .Name = ", " });
                            work_list.appendAssumeCapacity(.{ .Value = .normalize(.{
                                .ty = elem.field.ty,
                                .value = v.value,
                                .offset = @intCast(v.offset + elem.offset),
                            }, self.tys) });
                        }
                        std.mem.reverse(Task, work_list.items[work_list.items.len - 1 ..]);
                        _ = work_list.pop();
                    },
                    .Enum => |e| {
                        try writer.writeAll(".");
                        try writer.writeAll(e.getFields(self.tys)[@intCast(v.value)].name);
                    },
                    .Nullable => |n| {
                        const global = self.tys.store.get(@as(utils.EntId(tys.Global), @enumFromInt(v.value)));
                        if (self.tys.isNullablePresent(n, global.data.slice(&self.tys.ct), v.offset)) {
                            try writer.writeAll("null");
                            continue;
                        }

                        const dta: *tys.Nullable = self.tys.store.get(n);
                        const nieche: ?tys.Nullable.NiecheSpec = dta.nieche.offset(self.tys);
                        const next_offset = if (nieche != null) dta.inner.alignment(self.tys) else 0;
                        work_list.appendAssumeCapacity(.{ .Value = .normalize(.{
                            .ty = dta.inner,
                            .value = v.value,
                            .offset = @intCast(v.offset + next_offset),
                        }, self.tys) });
                    },
                    .Union => try writer.writeAll("<union: cant display>"),
                    .Template, .Global, .Func => unreachable,
                },
            };
        }

        pub fn formatSeq(self: *const Fmt, work_list: *std.ArrayList(Task), arena: *utils.Arena, elem: Types.Id, ln: u64, global: i64) !void {
            work_list.ensureUnusedCapacity(arena.allocator(), @intCast(ln * 2)) catch unreachable;
            try work_list.append(arena.allocator(), .{ .Name = "]" });
            for (0..@intCast(ln)) |i| {
                const off = i * elem.size(self.tys);
                work_list.appendAssumeCapacity(.{ .Value = .normalize(.{
                    .ty = elem,
                    .value = global,
                    .offset = @intCast(off),
                }, self.tys) });
                work_list.appendAssumeCapacity(.{ .Name = ", " });
            }
            _ = work_list.pop();
        }

        pub fn format(self: *const Fmt, writer: *std.Io.Writer) !void {
            self.fmt(writer, null);
        }
    };

    pub fn fmtLocal(self: Id, types: *Types, bound: Id) Fmt {
        return .{ .self = self, .tys = types, .root = bound };
    }

    pub fn fmt(self: Id, types: *Types) Fmt {
        return .{ .self = self, .tys = types };
    }
};

pub const Target = enum { @"comptime", runtime };

pub fn readFromGlobal(self: *Types, global: utils.EntId(tys.Global), ty: Id, offset: u64) i64 {
    const glob = global.get(self);
    var value: i64 = 0;
    @memcpy(
        @as([*]u8, @ptrCast(&value))[0..@intCast(ty.size(self))],
        glob.data.slice(&self.ct)[@intCast(offset)..][0..@intCast(ty.size(self))],
    );
    return value;
}

pub fn getBuiltins(self: *Types) Machine.Builtins {
    return .{
        .memcpy = if (self.handlers.memcpy) |m|
            @intFromEnum(m)
        else
            std.math.maxInt(u32),
    };
}

pub fn retainClonedGlobals(self: *Types, pop_until: usize) void {
    errdefer unreachable;

    const work_list = self.global_work_list.getPtr(.@"comptime");
    while (work_list.items.len > pop_until) {
        const global = work_list.pop().?;
        var scrath = utils.Arena.scrath(null);
        defer scrath.deinit();

        const glob: *tys.Global = global.get(self);
        if (glob.completion.get(.@"comptime") == .compiled) continue;
        glob.completion.getPtr(.@"comptime").* = .compiled;

        self.ct.gen.emitData(.{
            .id = @intFromEnum(global),
            .name = "",
            .value = .{ .init = glob.data.slice(&self.ct) },
            .relocs = &.{},
            .readonly = glob.readonly,
            .thread_local = glob.thread_local,
        });

        if (glob.relocs.len == 0) continue;
        const final_data = self.pool.arena.dupe(u8, glob.data.slice(&self.ct));
        for (glob.relocs) |reloc| {
            const sym = self.ct.gen.mach.out.globals.items[reloc.target];
            const offset: u64 = self.ct.gen.mach.out.syms.items[@intFromEnum(sym)].offset;

            @memcpy(final_data[reloc.offset..][0..8], @as(*const [8]u8, @ptrCast(&offset))[0..8]);
        }
        glob.data = .{ .imm = final_data };
    }
}

pub fn retainGlobals(self: *Types, target: Target, backend: *Machine, handle_errors: bool) bool {
    errdefer unreachable;

    const emit_names = target == .runtime;
    var errored = false;

    const work_list = self.global_work_list.getPtr(target);
    out: while (work_list.pop()) |global| {
        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        const glob: *tys.Global = global.get(self);
        if (glob.completion.get(target) == .compiled) {
            continue;
        }
        glob.completion.getPtr(target).* = .compiled;

        if (glob.relocs.len == 0 and !glob.uninit) {
            // TODO: add a flag that we did this
            var relocs = std.ArrayList(Machine.DataOptions.Reloc){};
            self.findPointerOffsets(&relocs, glob.data.slice(&self.ct), tmp.arena, glob.ty, 0);
            glob.relocs = self.pool.arena.dupe(Machine.DataOptions.Reloc, relocs.items);
        }

        for (glob.relocs) |*r| {
            const ptr_big: u64 = @bitCast(glob.data.slice(&self.ct)[r.offset..][0..8].*);
            const ptr: usize = @intCast(ptr_big);

            if (r.is_func) {
                if (target == .@"comptime") {
                    r.target = std.math.maxInt(u32);
                } else {
                    r.target = @intCast(ptr);
                    self.queue(target, .init(.{ .Func = @enumFromInt(ptr) }));
                }
            } else {
                r.target = self.findSymForPtr(ptr) catch |err| {
                    if (handle_errors) {
                        errored = true;
                        self.report(
                            glob.key.loc.file,
                            glob.key.loc.ast,
                            "global is corrupted (of type {}) (global_id: {}): contains a pointer {}, @alloc_global might help",
                            .{ glob.ty, @intFromEnum(global), @errorName(err) },
                        );
                        continue :out;
                    }
                    continue;
                };
            }
        }

        if (glob.data == .@"comptime" and target == .@"comptime") {
            continue;
        }

        backend.emitData(.{
            .id = @intFromEnum(global),
            .name = if (emit_names) root.frontend.Types.Id.init(.{ .Global = global })
                .fmt(self).toString(tmp.arena) else "",
            .value = if (glob.uninit)
                .{ .uninit = glob.data.slice(&self.ct).len }
            else
                .{ .init = glob.data.slice(&self.ct) },
            .alignment = glob.ty.alignment(self),
            .relocs = if (target == .runtime) glob.relocs else &.{},
            .readonly = glob.readonly,
            .thread_local = glob.thread_local,
        });

        if (target == .@"comptime") {
            const len = glob.data.slice(&self.ct).len;
            glob.data = .{ .@"comptime" = .{
                .base = backend.out.syms.items[@intFromEnum(backend.out.globals.items[@intFromEnum(global)])].offset,
                .len = len,
            } };
        }
    }

    return errored;
}

pub fn cloneFrom(self: *Types, from: *Types, id: Id) struct { Id, bool } {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();
    return .{
        switch (id.data()) {
            .Builtin => id,
            .Pointer => |p| self.makePtr(self.cloneFrom(from, from.store.get(p).*)[0]),
            .Slice => |s| self.makeSlice(self.cloneFrom(from, from.store.get(s).elem)[0]),
            .Array => |a| self.makeArray(from.store.get(a).len, self.cloneFrom(from, from.store.get(a).elem)[0]),
            .Nullable => |n| self.makeNullable(self.cloneFrom(from, from.store.get(n).inner)[0]),
            .Simd => |s| self.makeSimd(self.cloneFrom(from, from.store.get(s).elem)[0], from.store.get(s).len),
            .Tuple => |t| {
                const fields = from.store.get(t).fields;
                const new_fields = tmp.arena.alloc(Id, fields.len);
                for (fields, new_fields) |f, *nf| {
                    nf.* = self.cloneFrom(from, f.ty)[0];
                }
                return .{ self.makeTuple(new_fields), false };
            },
            .FnPtr => |f| {
                const fptr = from.store.get(f);
                const new_params = tmp.arena.alloc(Id, fptr.args.len);
                for (fptr.args, new_params) |a, *na| {
                    na.* = self.cloneFrom(from, a)[0];
                }
                return .{ self.internPtr(.FnPtr, .{
                    .args = new_params,
                    .ret = self.cloneFrom(from, fptr.ret)[0],
                }), false };
            },
            inline .Enum, .Union, .Struct, .Func, .Template, .Global => |v, t| {
                var key: Scope = from.store.get(v).key;
                const file = key.loc.file;
                if (key.loc.scope == .void) return .{ self.getScope(file), false };
                self.cloneKeyFrom(from, &key);
                const res, const alloc = self.intern(t, key);
                const nid = res.key_ptr.*;
                if (!res.found_existing) {
                    switch (t) {
                        inline .Enum, .Union, .Struct => {
                            alloc.get(self).* = .{
                                .key = alloc.get(self).key,
                                .index = Ast.Index.build(
                                    self.getFile(file),
                                    self.getFile(file).exprs.get(key.loc.ast).Type.fields,
                                    &self.pool.arena,
                                ),
                            };
                        },
                        .Func => {
                            const func: *tys.Func = alloc.get(self);
                            const other: *tys.Func = from.store.get(v);
                            const args = self.pool.arena.alloc(Types.Id, other.args.len);
                            for (other.args, args) |oa, *a| {
                                a.* = self.cloneFrom(from, oa)[0];
                            }
                            const ret = self.cloneFrom(from, other.ret)[0];
                            func.* = .{
                                .key = func.key,
                                .args = args,
                                .ret = ret,
                                .is_inline = func.is_inline,
                                .visibility = func.visibility,
                            };
                        },
                        .Template => {
                            const templ: *tys.Template = alloc.get(self);
                            templ.* = .{ .key = templ.key, .is_inline = templ.is_inline };
                        },
                        .Global => {
                            const glob: *tys.Global = alloc.get(self);
                            glob.* = .{ .key = glob.key, .data = glob.data, .readonly = glob.readonly };
                        },
                        else => comptime unreachable,
                    }
                }
                return .{ nid, !res.found_existing };
            },
        },
        false,
    };
}

pub fn cloneKeyFrom(self: *Types, from: *Types, key: *Scope) void {
    key.loc.scope = self.cloneFrom(from, key.loc.scope)[0];

    var tmp = utils.Arena.scrath(null);
    // NOTE: we leak on purpose

    const new_captures = tmp.arena.alloc(Scope.Capture, key.captures().len);
    for (key.captures(), new_captures) |c, *nc| {
        nc.* = self.cloneCaptureFrom(from, c);
    }

    key.captures_ptr = new_captures.ptr;
}

pub fn cloneCaptureFrom(self: *Types, from: *Types, capture: Scope.Capture) Scope.Capture {
    const ty = self.cloneFrom(from, capture.ty)[0];

    if (capture.id.from_any) return .{ .id = capture.id, .ty = ty };

    return switch (ty.data()) {
        .Builtin => |b| switch (b) {
            .type => .{
                .id = capture.id,
                .ty = .type,
                .value = @intFromEnum(self.cloneFrom(from, @enumFromInt(capture.value))[0]),
            },
            else => capture,
        },
        .Enum, .Union => .{
            .id = capture.id,
            .ty = ty,
            .value = capture.value,
        },
        .FnPtr => unreachable,
        .Slice => {
            var global: utils.EntId(tys.Global) = @enumFromInt(capture.value);
            const pop_until = self.global_work_list.get(.@"comptime").items.len;
            global = self.cloneGlobal(from, global);
            self.retainClonedGlobals(pop_until);

            return .{
                .id = capture.id,
                .ty = ty,
                .value = @intFromEnum(global),
            };
        },
        else => utils.panic("{f}", .{capture.ty.fmt(from)}),
    };
}

pub fn cloneGlobal(self: *Types, from: *Types, id: utils.EntId(tys.Global)) utils.EntId(tys.Global) {
    const global: *tys.Global = id.get(self);

    const new = self.store.add(&self.pool.arena, global.*);
    self.queue(.@"comptime", .init(.{ .Global = new }));

    const rels = self.pool.arena.alloc(Machine.DataOptions.Reloc, global.relocs.len);
    for (global.relocs, rels) |r, *dr| {
        dr.* = r;
        dr.target = @intFromEnum(self.cloneGlobal(from, @enumFromInt(r.target)));
    }

    return new;
}

pub fn findPointerOffsets(
    self: *Types,
    relocs: *std.ArrayList(Machine.DataOptions.Reloc),
    global: []const u8,
    scratch: *utils.Arena,
    ty: Id,
    offset_f: u64,
) void {
    const offset: usize = @intCast(offset_f);
    switch (ty.data()) {
        .Enum, .Builtin => {},
        .Union => |u| {
            const tag: Id = u.getTag(self);
            if (tag == .void) return;

            const tag_offset: u64 = u.tagOffset(self);

            var tag_value: u64 = 0;
            @memcpy(
                std.mem.asBytes(&tag_value)[0..@intCast(tag.size(self))],
                global[@intCast(offset_f + tag_offset)..][0..@intCast(tag.size(self))],
            );

            if (tag_value > u.getFields(self).len) return;

            const inner_repr: Id = u.getFields(self)[@intCast(tag_value)].ty;
            self.findPointerOffsets(relocs, global, scratch, inner_repr, offset_f);
        },
        .FnPtr => {
            relocs.append(scratch.allocator(), .{
                .offset = @intCast(offset),
                .target = undefined,
                .is_func = true,
            }) catch unreachable;
        },
        .Pointer => |p| {
            const base: Id = p.get(self).*;

            const cap = base.size(self);
            if (cap == 0) return;

            relocs.append(scratch.allocator(), .{
                .offset = @intCast(offset),
                .target = undefined,
            }) catch unreachable;
        },
        .Array => |a| {
            const arr: *tys.Array = a.get(self);
            const elem_size = arr.elem.size(self);
            for (0..@intCast(arr.len)) |idx| {
                self.findPointerOffsets(
                    relocs,
                    global,
                    scratch,
                    arr.elem,
                    offset + idx * elem_size,
                );
            }
        },
        .Slice => |s| {
            const slc: *tys.Slice = s.get(self);

            const len_big: u64 = @bitCast(global[offset + tys.Slice.len_offset ..][0..8].*);
            const len: usize = @intCast(len_big);

            const cap = len *% slc.elem.size(self);
            if (cap == 0) return;

            relocs.append(scratch.allocator(), .{
                .offset = @intCast(offset + tys.Slice.ptr_offset),
                .target = undefined,
            }) catch unreachable;
        },
        .Simd => |s| {
            const smd: *tys.Simd = s.get(self);

            const elem_size = smd.elem.size(self);
            for (0..smd.len) |idx| {
                self.findPointerOffsets(
                    relocs,
                    global,
                    scratch,
                    smd.elem,
                    offset + idx * elem_size,
                );
            }
        },
        inline .Struct, .Tuple => |t| {
            var fields_iter = t.offsetIter(self);
            while (fields_iter.next()) |elem| {
                self.findPointerOffsets(relocs, global, scratch, elem.field.ty, offset_f + elem.offset);
            }
        },
        .Nullable => |n| {
            if (!self.isNullablePresent(n, global, offset)) return;

            const data: *tys.Nullable = n.get(self);
            const nieche: ?tys.Nullable.NiecheSpec = data.nieche.offset(self);
            const next_offset = if (nieche != null) data.inner.alignment(self) else 0;
            self.findPointerOffsets(relocs, global, scratch, data.inner, offset + next_offset);
        },
        .Global, .Func, .Template => unreachable,
    }
}

pub fn isNullablePresent(self: *Types, n: utils.EntId(tys.Nullable), global: []const u8, offset: u64) bool {
    const data: *tys.Nullable = n.get(self);
    const nieche: ?tys.Nullable.NiecheSpec = data.nieche.offset(self);

    return if (nieche) |niche| b: {
        const abi = niche.kind.abi();
        if (abi == .bot) return false;
        const size = abi.size();

        var value: u64 = 0;
        @memcpy(
            @as(*[8]u8, @ptrCast(&value))[0..@intCast(size)],
            global[@intCast(offset + niche.offset)..][0..@intCast(size)],
        );

        break :b value != 0;
    } else global[@intCast(offset)] != 0;
}

pub fn findSymForPtr(
    self: *Types,
    ptr: u64,
) !u32 {
    const data = &self.ct.gen.mach.out;

    if (ptr < Comptime.stack_size)
        return error.@"to comptime stack";

    if (ptr > data.code.items.len) {
        return error.@"exceeding code section";
    }

    const id: utils.EntId(tys.Global) =
        @enumFromInt(@as(u32, @bitCast(data.code.items[@intCast(ptr - 4)..][0..4].*)));

    if (!self.store.isValid(.Global, @intFromEnum(id)))
        return error.@"to something thats not a global";

    self.queue(.runtime, .init(.{ .Global = id }));

    return @intFromEnum(id);
}

pub fn queue(self: *Types, target: Target, task: Id) void {
    errdefer unreachable;
    switch (task.data()) {
        .Func => |func| {
            if (func.get(self).completion.get(target) == .compiled) return;
            try self.func_work_list.getPtr(target).append(self.ct.getGpa(), func);
        },
        .Global => |global| {
            if (global.get(self).completion.get(target) == .compiled) return;
            try self.global_work_list.getPtr(target).append(self.ct.getGpa(), global);
        },
        else => unreachable,
    }
}

pub fn nextLocalTask(self: *Types, target: Target, pop_limit: usize) ?utils.EntId(tys.Func) {
    while (self.func_work_list.get(target).items.len > pop_limit) {
        const func = self.func_work_list.getPtr(target).pop() orelse return null;
        if (func.get(self).completion.get(target) == .compiled) continue;
        func.get(self).completion.set(target, .compiled);
        return func;
    }

    return null;
}

pub fn nextTask(self: *Types, target: Target, pop_limit: usize, q: ?*root.Queue) ?utils.EntId(tys.Func) {
    if (q) |qu| {
        std.debug.assert(target == .runtime);
        std.debug.assert(pop_limit == 0);
        while (qu.dequeue()) |task| {
            if (task.intoFunc(self)) |func| {
                // destribute work to others
                while (self.nextLocalTask(target, 0)) |other| {
                    qu.enque(&.{.fronFn(self, qu.self_id, other)});
                }
                return func;
            }
        }
    }

    const work = self.nextLocalTask(target, pop_limit);
    if (q) |qu| {
        std.debug.assert(target == .runtime);
        std.debug.assert(pop_limit == 0);
        while (self.nextLocalTask(target, 0)) |other| {
            qu.enque(&.{.fronFn(self, qu.self_id, other)});
        }
    }
    return work;
}

pub fn retryNextTask(self: *Types, target: Target, pop_limit: usize, q: ?*root.Queue) ?utils.EntId(tys.Func) {
    const qu = q orelse return null;

    std.debug.assert(target == .runtime);
    std.debug.assert(pop_limit == 0);

    while (true) {
        var task = qu.dequeueWait(5) orelse {
            return null;
        };
        if (task.intoFunc(self)) |func| {
            return func;
        }
    }
}

pub fn init(arena_: Arena, source: []const Ast, diagnostics: ?*std.Io.Writer, gpa: ?std.mem.Allocator) *Types {
    var arena = arena_;
    const scopes = arena.alloc(Id, source.len);
    @memset(scopes, .void);
    const slot = arena.create(Types);
    const line_indexes = arena.alloc(utils.LineIndex, source.len);
    for (source, 0..) |fl, i| {
        line_indexes[i] = utils.LineIndex.init(fl.source, &arena);
    }
    slot.* = .{
        .func_work_list = .{ .values = @splat(.empty) },
        .global_work_list = .{ .values = .{ .empty, .empty } },
        .stack_base = @frameAddress(),
        .files = source,
        .file_scopes = scopes,
        .line_indexes = line_indexes,
        .pool = .{ .arena = arena },
        .ct = undefined,
        .diagnostics = diagnostics,
        .metrics = .init(),
    };

    slot.ct = .init(gpa orelse slot.pool.allocator());

    slot.ct.gen.emit_global_reloc_offsets = true;
    slot.ct.gen.push_uninit_globals = true;
    slot.ct.gen.align_globlals = true;
    slot.ct.gen.comptime_only_fn = comptime_only_fn;

    slot.string = slot.makeSlice(.u8);
    slot.source_loc = slot.convertZigTypeToHbType(extern struct {
        file: Slice(u8),
        line: u32,
        col: u32,
    });

    slot.type_info = slot.convertZigTypeToHbType(TypeInfo);

    const u8_ptr = slot.makePtr(.u8);
    slot.handler_signatures = .{
        .values = .{
            .{
                // sloc, len, range start, range end
                .args = slot.pool.arena.dupe(Id, &.{ slot.source_loc, .uint, .uint, .uint }),
                .ret = .never,
            },
            .{
                // sloc
                .args = slot.pool.arena.dupe(Id, &.{slot.source_loc}),
                .ret = .never,
            },
            .{
                // dst, src, len
                .args = slot.pool.arena.dupe(Id, &.{ u8_ptr, u8_ptr, .uint }),
                .ret = .void,
            },
            null,
            .{
                // sloc
                .args = slot.pool.arena.dupe(Id, &.{slot.source_loc}),
                .ret = .never,
            },
        },
    };

    return slot;
}

pub const TypeInfo = extern struct {
    data: extern union {
        builtin: void,
        pointer: Id,
        slice: Id,
        nullable: Id,
        tuple: Slice(Id),
        @"@enum": extern struct {
            backing_int: Id,
            fields: Slice(extern struct {
                name: Slice(u8),
                value: i64,
            }),
            decls: Slice(Decl),
        },
        @"@union": extern struct {
            tag: Id,
            fields: Slice(extern struct {
                name: Slice(u8),
                ty: Id,
            }),
            decls: Slice(Decl),
        },
        @"@struct": extern struct {
            alignment: u64,
            fields: Slice(extern struct {
                name: Slice(u8),
                ty: Id,
                defalut_value: *anyopaque,
            }),
            decls: Slice(Decl),
        },
        template: extern struct {
            is_inline: bool,
        },
        @"@fn": extern struct {
            args: Slice(Id),
            ret: Id,
        },
        global: extern struct {
            ty: Id,
            readonly: bool,
        },
        fnptr: extern struct {
            args: Slice(Id),
            ret: Id,
        },
        simd: extern struct {
            elem: Id,
            len: u32,
        },
        array: tys.Array,
    },
    kind: enum(u8) {
        builtin,
        pointer,
        slice,
        nullable,
        tuple,
        @"@enum",
        @"@union",
        @"@struct",
        template,
        @"@fn",
        global,
        fnptr,
        simd,
        array,
    },

    pub const Decl = extern struct {
        name: Slice(u8),
    };

    pub const is_tagged_union = true;
};

pub fn Optional(comptime Elem: type) type {
    return extern struct {
        pub const is_optional = true;
        pub const elem = Elem;

        present: bool,
        ptr: Elem,
    };
}

pub fn CompactOptional(comptime Elem: type) type {
    return extern struct {
        pub const is_optional = true;
        pub const elem = Elem;

        ptr: Elem,
    };
}

pub fn Slice(comptime Elem: type) type {
    return extern struct {
        pub const is_slice = true;
        pub const elem = Elem;

        elem_ptr: u64,
        len: u64,

        pub fn alloc(ct: *Comptime, slce: []const Elem) @This() {
            const types = ct.getTypes();
            const global = types.addInternedGlobal(
                types.makeArray(slce.len, types.convertZigTypeToHbType(Elem)),
                @ptrCast(slce),
            );
            types.queue(.@"comptime", .init(.{ .Global = global }));
            std.debug.assert(!types.retainGlobals(.@"comptime", &ct.gen.mach, true));

            const off = ct.gen.mach.out.syms.items[@intFromEnum(ct.gen.mach.out.globals.items[@intFromEnum(global)])].offset;
            return .{ .elem_ptr = off, .len = slce.len };
        }

        pub fn slice(slf: @This(), ct: *Comptime) []Elem {
            return @as([*]Elem, @ptrCast(@alignCast(&ct.gen.mach.out.code.items[@intCast(slf.elem_ptr)])))[0..@intCast(slf.len)];
        }
    };
}

pub fn Pointer(comptime Elem: type) type {
    return extern struct {
        pub const is_pointer = true;
        pub const elem = Elem;

        ptr: [*c]Elem,
    };
}

pub fn convertZigTypeToHbType(self: *Types, comptime T: type) Id {
    if (T == Id) return .type;

    return switch (@typeInfo(T)) {
        .void => .void,
        .@"opaque" => .void,
        .bool => .bool,
        .noreturn => .never,
        .@"fn" => |f| {
            const args = self.pool.arena.alloc(Id, f.args.len) catch unreachable;
            inline for (f.args, args) |a, i| {
                args[i] = self.convertZigTypeToHbType(a);
            }

            return self.internPtr(.FnPtr, .{
                .args = args,
                .ret = self.convertZigTypeToHbType(f.return_type.?),
            });
        },
        .int => |t| switch (t.signedness) {
            .signed => switch (t.bits) {
                8 => .i8,
                16 => .i16,
                32 => .i32,
                64 => .i64,
                else => unreachable,
            },
            .unsigned => switch (t.bits) {
                8 => .u8,
                16 => .u16,
                32 => .u32,
                64 => .u64,
                else => unreachable,
            },
        },
        .float => |t| switch (t.bits) {
            32 => .f32,
            64 => .f64,
            else => unreachable,
        },
        .pointer => |t| {
            return self.makePtr(self.convertZigTypeToHbType(t.child));
        },
        .@"struct" => |t| {
            if (@hasDecl(T, "is_slice")) {
                return self.makeSlice(self.convertZigTypeToHbType(T.elem));
            }

            if (@hasDecl(T, "is_pointer")) {
                return self.makePtr(self.convertZigTypeToHbType(T.elem));
            }

            if (@hasDecl(T, "is_optional")) {
                return self.makeNullable(self.convertZigTypeToHbType(T.elem));
            }

            if (@hasDecl(T, "is_tagged_union")) {
                const tag = self.convertZigTypeToHbType(t.fields[1].type);

                const unon = self.convertZigTypeToHbType(t.fields[0].type);
                unon.data().Union.get(self).tag = tag;
                return unon;
            }

            comptime std.debug.assert(t.layout == .@"extern");

            var fields: [t.fields.len]tys.Struct.Field = undefined;
            inline for (t.fields, 0..) |f, i| {
                fields[i] = .{
                    .name = f.name,
                    .ty = self.convertZigTypeToHbType(f.type),
                };
            }

            return .init(.{ .Struct = self.store.add(&self.pool.arena, tys.Struct{
                .key = .{
                    .loc = .{
                        .scope = self.getScope(.root),
                    },
                },
                .index = .empty,
                .alignment = @alignOf(T),
                .size = @sizeOf(T),
                .fields = self.pool.arena.dupe(tys.Struct.Field, &fields),
            }) });
        },
        .@"enum" => |t| {
            var fields: [t.fields.len]tys.Enum.Field = undefined;
            inline for (t.fields, 0..) |f, i| {
                fields[i] = .{
                    .name = f.name,
                    .value = @intCast(f.value),
                };
            }

            return .init(.{ .Enum = self.store.add(&self.pool.arena, tys.Enum{
                .key = .{
                    .loc = .{
                        .scope = self.getScope(.root),
                    },
                },
                .index = .empty,
                .backing_int = self.convertZigTypeToHbType(t.tag_type),
                .fields = self.pool.arena.dupe(tys.Enum.Field, &fields),
            }) });
        },
        .@"union" => |t| {
            comptime std.debug.assert(t.layout == .@"extern");
            comptime std.debug.assert(t.tag_type == null);

            var fields: [t.fields.len]tys.Union.Field = undefined;
            inline for (t.fields, 0..) |f, i| {
                fields[i] = .{
                    .name = f.name,
                    .ty = self.convertZigTypeToHbType(f.type),
                };
            }

            return .init(.{ .Union = self.store.add(&self.pool.arena, tys.Union{
                .key = .{
                    .loc = .{
                        .scope = self.getScope(.root),
                    },
                },
                .index = .empty,
                .fields = self.pool.arena.dupe(tys.Union.Field, &fields),
            }) });
        },
        else => @compileError("TODO " ++ @typeName(T)),
    };
}

pub fn checkStack(self: *Types, file: File, pos: anytype) !void {
    const distance = @abs(@as(isize, @bitCast(@frameAddress() -% self.stack_base)));
    if (distance > root.frontend.Parser.stack_limit) {
        self.report(file, pos, "the comptime evaluation recurses too deep", .{});
        //std.debug.dumpCurrentStackTrace(@returnAddress());
        return error.StackOverflow;
    }
}

pub fn deinit(self: *Types) void {
    if (!std.debug.runtime_safety) return;

    for (&self.global_work_list.values) |*list| list.deinit(self.ct.getGpa());
    for (&self.func_work_list.values) |*list| list.deinit(self.ct.getGpa());
    self.interner.deinit(self.ct.getGpa());
    self.string_globals.deinit(self.ct.getGpa());
    self.remote_ids.deinit(self.ct.getGpa());

    self.ct.deinit();

    var arena = self.pool.arena;
    self.* = undefined;
    arena.deinit();
}

pub fn reportSloc(self: *Types, sloc: graph.Sloc, fmt: []const u8, args: anytype) void {
    std.debug.assert(sloc != graph.Sloc.none);
    self.report(@enumFromInt(sloc.namespace), sloc.index, fmt, args);
}

pub fn report(self: *Types, file_id: File, expr: anytype, msg: []const u8, args: anytype) void {
    self.getFile(file_id).report(self, self.getFile(file_id).posOf(expr).index, msg, args);
}

pub fn getFile(self: *Types, file: File) *const Ast {
    return &self.files[@intFromEnum(file)];
}

pub fn posOf(self: *Types, file: File, expr: anytype) Ast.Pos {
    return self.getFile(file).posOf(expr);
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

pub fn internPtr(self: *Types, comptime tag: std.meta.Tag(Data), payload: std.meta.TagPayload(Data, tag).Data) Id {
    const vl = self.store.add(&self.pool.arena, payload);
    const id = Id.init(@unionInit(Data, @tagName(tag), vl));
    const slot = self.interner.getOrPutContext(self.ct.getGpa(), id, .{ .types = self }) catch unreachable;
    if (slot.found_existing) {
        self.store.pop(vl);
        return slot.key_ptr.*;
    }
    if (@TypeOf(payload) == tys.Tuple) {
        vl.get(self).fields = self.pool.arena.dupe(tys.Tuple.Field, payload.fields);
    } else if (@TypeOf(payload) == tys.FnPtr) {
        vl.get(self).args = self.pool.arena.dupe(Id, payload.args);
    } else vl.get(self).* = payload;
    return slot.key_ptr.*;
}

pub fn makeSlice(self: *Types, elem: Id) Id {
    return self.internPtr(.Slice, .{ .elem = elem });
}

pub fn makeArray(self: *Types, len: u64, elem: Id) Id {
    return self.internPtr(.Array, .{ .len = len, .elem = elem });
}

pub fn makePtr(self: *Types, v: Id) Id {
    return self.internPtr(.Pointer, v);
}

pub fn makeNullable(self: *Types, v: Id) Id {
    return self.internPtr(.Nullable, .{ .inner = v });
}

pub fn makeTuple(self: *Types, v: []Id) Id {
    return self.internPtr(.Tuple, .{ .fields = @ptrCast(v) });
}

pub fn makeSimd(self: *Types, elem: Id, len: u32) Id {
    return self.internPtr(.Simd, .{ .elem = elem, .len = len });
}

pub fn intern(self: *Types, comptime kind: std.meta.Tag(Data), key: Scope) struct { TypeIndex.GetOrPutResult, std.meta.TagPayload(Data, kind) } {
    var mem: std.meta.TagPayload(Data, kind).Data = undefined;
    mem.key = key;
    const ty = self.store.add(&self.pool.arena, mem);
    const id = Id.init(@unionInit(Data, @tagName(kind), ty));
    const slot = self.interner.getOrPutContext(self.ct.getGpa(), id, .{ .types = self }) catch unreachable;
    if (slot.found_existing) {
        std.debug.assert(slot.key_ptr.data() == kind);
        self.store.pop(ty);
        return .{ slot, @field(slot.key_ptr.data(), @tagName(kind)) };
    } else {
        ty.get(self).key.captures_ptr =
            self.pool.arena.dupe(Types.Scope.Capture, ty.get(self).key.captures()).ptr;
    }
    return .{ slot, ty };
}

pub fn resolveFielded(
    self: *Types,
    comptime tag: std.meta.Tag(Data),
    scope: Id,
    file: File,
    name: []const u8,
    ast: Ast.Id,
    captures: []const Scope.Capture,
) Id {
    const slot, const alloc = self.intern(tag, .{
        .loc = .{
            .scope = scope,
            .file = file,
            .ast = ast,
            .capture_len = @intCast(captures.len),
        },
        .name_pos = self.getFile(file).strPos(name),
        .captures_ptr = captures.ptr,
    });
    if (!slot.found_existing) {
        alloc.get(self).* = .{
            .key = alloc.get(self).key,
            .index = Ast.Index.build(
                self.getFile(file),
                self.getFile(file).exprs.get(ast).Type.fields,
                &self.pool.arena,
            ),
        };
    }
    return slot.key_ptr.*;
}

pub fn dumpAnalErrors(self: *Types, anal_errors: *std.ArrayList(static_anal.Error)) bool {
    for (anal_errors.items) |err| switch (err) {
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
        .ReadUninit => |loc| {
            self.reportSloc(loc.loc, "reading from an uninitialized memory location", .{});
        },
    };
    defer anal_errors.items.len = 0;
    return anal_errors.items.len != 0;
}

pub fn addInternedGlobal(self: *Types, ty: Id, data: []const u8) utils.EntId(tys.Global) {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var relocs = std.ArrayList(Machine.DataOptions.Reloc).empty;
    self.findPointerOffsets(&relocs, data, tmp.arena, ty, 0);

    for (relocs.items) |*r| {
        const ptr_big: u64 = @bitCast(data[r.offset..][0..8].*);
        const ptr: usize = @intCast(ptr_big);
        std.debug.assert(!r.is_func);
        r.target = self.findSymForPtr(ptr) catch unreachable;
    }

    const glob = self.store.add(&self.pool.arena, tys.Global{
        .key = .{ .name_pos = if (ty.data() == .Array and
            ty.data().Array.get(self).elem == .u8) .string else .empty_name },
        .data = .{ .imm = data },
        .ty = ty,
        .readonly = true,
        .relocs = relocs.items,
    });

    const entry = self.string_globals.getOrPutContext(
        self.ct.getGpa(),
        glob,
        .{ .types = self },
    ) catch unreachable;
    if (!entry.found_existing) {
        glob.get(self).data = .{ .imm = self.pool.arena.dupe(u8, data) };
        glob.get(self).relocs = self.pool.arena.dupe(tys.Global.Reloc, relocs.items);
    } else {
        self.store.pop(glob);
    }

    return entry.key_ptr.*;
}

pub fn addUniqueGlobal(self: *Types, scope: Id) utils.EntId(tys.Global) {
    self.stats.unique_globals += 1;

    const glob = self.store.add(&self.pool.arena, tys.Global{
        .key = .{
            .loc = .{
                .file = scope.file(self) orelse .root,
                .scope = scope,
            },
        },
        .ty = .never,
        .readonly = true,
    });

    return glob;
}

pub fn resolveGlobal(
    self: *Types,
    scope: Id,
    name: []const u8,
    ast: Ast.Id,
    readonly: bool,
) struct { Id, bool } {
    const slot, const alloc = self.intern(.Global, .{
        .loc = .{
            .scope = scope,
            .file = scope.file(self).?,
            .ast = ast,
        },
        .name_pos = self.getFile(scope.file(self).?).strPos(name),
    });

    if (!slot.found_existing) {
        alloc.get(self).* = .{
            .key = alloc.get(self).key,
            .readonly = readonly,
        };
    }
    return .{ slot.key_ptr.*, !slot.found_existing };
}

// we keep linked list of these
pub fn allocTempType(self: *Types, comptime T: type) utils.EntId(T) {
    const field = switch (T) {
        tys.Template => &self.tmp_templates,
        tys.Func => &self.tmp_funcs,
        else => comptime unreachable,
    };
    const name = @TypeOf(self.store).fieldName(T).name;

    return if (field.*) |t| {
        const tl = t.get(self);
        field.* = if (tl.key.loc.scope == .void)
            null
        else
            @field(tl.key.loc.scope.data(), name);
        return t;
    } else self.store.add(&self.pool.arena, @as(T, undefined));
}

pub fn freeTempType(self: *Types, comptime T: type, scope: utils.EntId(T)) void {
    const field = switch (T) {
        tys.Template => &self.tmp_templates,
        tys.Func => &self.tmp_funcs,
        else => comptime unreachable,
    };
    const name = @TypeOf(self.store).fieldName(T).name;

    scope.get(self).key.loc.scope = if (field.*) |t|
        .init(@unionInit(@TypeOf(self.store).Data, name, t))
    else
        .void;
    field.* = scope;
}
