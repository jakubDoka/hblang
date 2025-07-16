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

store: utils.EntStore(tys) = .{},
pool: utils.Pool,
interner: Map = .{},
file_scopes: []Id,
ct: Comptime,
diagnostics: std.io.AnyWriter,
colors: std.io.tty.Config = .no_color,
files: []const Ast,
stack_base: usize,
target: []const u8 = "hbvm-ableos",
func_work_list: std.EnumArray(Target, std.ArrayListUnmanaged(utils.EntId(tys.Func))),
global_work_list: std.EnumArray(Target, std.ArrayListUnmanaged(utils.EntId(tys.Global))),
string: Id = undefined,
source_loc: Id = undefined,
handlers: Handlers = .{},
handler_signatures: std.EnumArray(
    std.meta.FieldEnum(Handlers),
    ?Handlers.Signature,
) = undefined,

const Types = @This();
const Map = std.hash_map.HashMapUnmanaged(
    Id,
    void,
    TypeCtx,
    std.hash_map.default_max_load_percentage,
);

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
        file: Types.File,
        scope: Id,
        ast: Ast.Id,
        unused2: u16 = 0,
        unused: u32 = 0,
    },
    name: []const u8,
    captures: []const Capture,

    pub const Capture = struct {
        id: packed struct(u32) {
            index: u31,
            from_any: bool = false,

            pub fn fromIdent(id: Ast.Ident) @This() {
                return .{ .index = @intCast(@intFromEnum(id)) };
            }
        },
        ty: Id,
        value: u64 = 0,

        comptime {
            std.debug.assert(@sizeOf(@This()) == 16);
        }

        pub fn ident(self: Capture) Ast.Ident {
            return @enumFromInt(self.id.index);
        }
    };

    pub const dummy = Scope{
        .loc = .{
            .file = .root,
            .scope = .void,
            .ast = .zeroSized(.Void),
        },
        .name = "",
        .captures = &.{},
    };

    pub fn eql(self: Scope, other: Scope) bool {
        return self.loc.file == other.loc.file and
            self.loc.scope == other.loc.scope and
            self.loc.ast == other.loc.ast and
            std.mem.eql(u64, @ptrCast(self.captures), @ptrCast(other.captures));
    }
};

pub const TypeCtx = struct {
    types: *Types,

    pub fn eql(self: @This(), a: Id, b: Id) bool {
        const ad, const bd = .{ a.data(), b.data() };
        if (std.meta.activeTag(ad) != std.meta.activeTag(bd)) return false;

        return switch (ad) {
            .Builtin => |bl| bl == bd.Builtin,
            .Pointer => |s| std.meta.eql(self.types.store.get(s).*, self.types.store.get(bd.Pointer).*),
            .Slice => |s| std.meta.eql(self.types.store.get(s).*, self.types.store.get(bd.Slice).*),
            .Nullable => |n| std.meta.eql(self.types.store.get(n).inner, self.types.store.get(bd.Nullable).inner),
            .Tuple => |n| std.mem.eql(Id, @ptrCast(self.types.store.get(n).fields), @ptrCast(self.types.store.get(bd.Tuple).fields)),
            .Enum, .Union, .Struct, .Func, .Template, .Global => {
                const as, const bs = switch (ad) {
                    inline .Enum, .Union, .Struct, .Func, .Template, .Global => |v, t| .{
                        &self.types.store.get(v).key,
                        &self.types.store.get(@field(bd, @tagName(t))).key,
                    },
                    else => unreachable,
                };

                return as.eql(bs.*);
            },
        };
    }

    pub fn hash(self: @This(), adapted_key: Id) u64 {
        var hasher = std.hash.Fnv1a_64.init();
        const adk = adapted_key.data();
        std.hash.autoHash(&hasher, std.meta.activeTag(adk));
        switch (adk) {
            .Builtin => unreachable,
            inline .Pointer, .Slice => |s| std.hash.autoHash(&hasher, self.types.store.get(s).*),
            .Nullable => |n| std.hash.autoHash(&hasher, self.types.store.get(n).inner),
            // its an array of integers, splat
            .Tuple => |n| hasher.update(@ptrCast(self.types.store.get(n).fields)),
            .Enum, .Union, .Struct, .Func, .Template, .Global => {
                const scope = switch (adk) {
                    inline .Enum, .Union, .Struct, .Func, .Template, .Global => |v| &self.types.store.get(v).key,
                    else => unreachable,
                };

                // we can safely hash the prefix as it contains
                // only integers
                hasher.update(std.mem.asBytes(&scope.loc));

                // we skip the name and also splat the captures since they
                // have no padding bites
                hasher.update(@ptrCast(scope.captures));
            },
        }
        return hasher.final();
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

    pub fn fromRaw(raw: u32, types: *Types) ?Id {
        const repr: Repr = @bitCast(raw);
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

    pub inline fn init(dt: Data) Id {
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
            .Builtin, .Tuple, .Pointer, .Nullable, .Slice => unreachable,
        };
    }

    pub fn file(self: Id, types: *Types) ?File {
        return switch (self.data()) {
            .Builtin, .Pointer, .Slice, .Nullable, .Tuple => null,
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
            .Builtin, .Pointer, .Slice, .Nullable, .Tuple => utils.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| &types.store.get(v).key,
        };
    }

    pub fn getAst(self: Id, types: *Types) Ast.Id {
        return switch (self.data()) {
            .Global, .Builtin, .Pointer, .Slice, .Nullable, .Tuple => utils.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| types.store.get(v).key.loc.ast,
        };
    }

    pub fn items(self: Id, ast: *const Ast, types: *Types) Ast.Slice {
        return switch (self.data()) {
            .Global, .Builtin, .Pointer, .Slice, .Nullable, .Tuple => utils.panic("{s}", .{@tagName(self.data())}),
            .Template, .Func => .{},
            inline else => |v| ast.exprs.get(types.store.get(v).key.loc.ast).Type.fields,
        };
    }

    pub fn captures(self: Id, types: *Types) []const Scope.Capture {
        return switch (self.data()) {
            .Global, .Builtin, .Pointer, .Slice, .Nullable, .Tuple => utils.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| types.store.get(v).key.captures,
        };
    }

    pub fn findCapture(self: Id, id: Ast.Ident, types: *Types) ?*const Scope.Capture {
        return switch (self.data()) {
            .Global, .Builtin, .Pointer, .Slice, .Nullable, .Tuple => utils.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| for (types.store.get(v).key.captures) |*cp| {
                if (cp.id.index == @intFromEnum(id)) break cp;
            } else null,
        };
    }

    pub fn parent(self: Id, types: *Types) Id {
        return switch (self.data()) {
            .Builtin, .Pointer, .Slice, .Nullable, .Tuple => utils.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| types.store.get(v).key.loc.scope,
        };
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
            else => null,
        };
    }

    pub fn len(self: Id, types: *Types) ?usize {
        return switch (self.data()) {
            inline .Struct, .Union, .Enum, .Tuple => |s| s.getFields(types).len,
            .Slice => |s| types.store.get(s).len,
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
            .Slice => |s| if (types.store.get(s).len == null)
                return .{ .offset = tys.Slice.ptr_offset, .kind = .ptr }
            else
                null,
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
            .Pointer => 8,
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
            .Union => |u| {
                var max_size: u64 = 0;
                var alignm: u64 = 1;
                for (u.getFields(types)) |f| {
                    alignm = @max(alignm, f.ty.alignment(types));
                    max_size = @max(max_size, f.ty.size(types));
                }
                max_size = std.mem.alignForward(u64, max_size, alignm);
                return max_size;
            },
            .Struct => |s| s.getSize(types),
            .Slice => |s| if (types.store.get(s).len) |l| l * types.store.get(s).elem.size(types) else 16,
            .Nullable => |n| n.size(types),
            .Global, .Func, .Template => 0,
        };
    }

    pub fn alignment(self: Id, types: *Types) u64 {
        return switch (self.data()) {
            .Builtin, .Enum => @max(1, self.size(types)),
            .Pointer => 8,
            .Nullable => |n| types.store.get(n).inner.alignment(types),
            .Struct => |s| s.getAlignment(types),
            inline .Union, .Tuple => |s| {
                var alignm: u64 = 1;
                for (s.getFields(types)) |f| {
                    alignm = @max(alignm, f.ty.alignment(types));
                }
                return alignm;
            },
            .Slice => |s| if (types.store.get(s).len == null)
                8
            else
                types.store.get(s).elem.alignment(types),
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

        pub fn toString(self: *const Fmt, arena: *utils.Arena) []u8 {
            var tmp = utils.Arena.scrath(arena);
            defer tmp.deinit();
            var arr = std.ArrayListUnmanaged(u8).empty;
            self.fmt(&arr, tmp.arena);
            return arena.dupe(u8, arr.items);
        }

        pub fn fmt(self: *const Fmt, writer: *std.ArrayListUnmanaged(u8), to: *utils.Arena) void {
            errdefer unreachable;

            var tmp = utils.Arena.scrath(to);
            defer tmp.deinit();

            const Task = union(enum) {
                Name: []const u8,
                Type: Id,
                Value: Val,
                PushScope: Id,
                PopScope: usize,

                const Val = struct {
                    ty: Id,
                    offset: u32 = 0,
                    value: u64,

                    pub fn normalize(slf: Val, ts: *Types) Val {
                        return .{ .value = switch (Abi.ableos.categorize(slf.ty, ts)) {
                            .Impossible, .Imaginary, .ByValue => readFromGlobal(ts, @enumFromInt(slf.value), slf.ty, slf.offset),
                            .ByRef, .ByValuePair => slf.value,
                        }, .ty = slf.ty, .offset = slf.offset };
                    }
                };

                pub fn format(s: *const @This(), comptime _: []const u8, _: anytype, wrter: anytype) !void {
                    switch (s.*) {
                        .Name => |n| try wrter.print("name: {s}", .{n}),
                        .Type => |t| try wrter.print("ty: {}", .{t.data()}),
                        .Value => |v| try wrter.print("v: {}", .{v}),
                        .PopScope => try wrter.writeAll("pop scope"),
                    }
                }

                pub fn writeSignedInt(val: i64, wrter: *std.ArrayListUnmanaged(u8), t: *utils.Arena) !void {
                    if (val < 0) {
                        _ = try wrter.write("-");
                        try writeInt(@intCast(-val), wrter, t);
                    } else {
                        try writeInt(@intCast(val), wrter, t);
                    }
                }

                pub fn writeInt(val: u64, wrter: *std.ArrayListUnmanaged(u8), t: *utils.Arena) !void {
                    var chars: [20]u8 = undefined;
                    var value = val;
                    const base = 10;
                    var i: usize = 0;
                    while (value != 0) : (i += 1) {
                        chars[i] = '0' + @as(u8, @truncate(value % base));
                        value /= base;
                    }
                    std.mem.reverse(u8, chars[0..i]);

                    _ = try wrter.appendSlice(t.allocator(), chars[0..i]);
                }
            };

            var work_list = tmp.arena.makeArrayList(Task, 16);
            var seen_captures = std.AutoArrayHashMapUnmanaged(Scope.Capture, void).empty;
            var captures_to_display = std.ArrayListUnmanaged(Scope.Capture).empty;
            var scope_stack = std.ArrayListUnmanaged(Id).empty;
            try seen_captures.ensureTotalCapacity(tmp.arena.allocator(), 32);

            work_list.appendAssumeCapacity(.{ .Type = self.self });

            while (work_list.pop()) |task| switch (task) {
                .PopScope => |v| scope_stack.items.len = v,
                .PushScope => |v| try scope_stack.append(tmp.arena.allocator(), v),
                .Type => |t| switch (t.data()) {
                    .Builtin => |b| try writer.appendSlice(to.allocator(), @tagName(b)),
                    .Pointer => |p| {
                        try writer.appendSlice(to.allocator(), "^");
                        work_list.appendAssumeCapacity(.{ .Type = self.tys.store.get(p).* });
                    },
                    .Slice => |s| {
                        try writer.appendSlice(to.allocator(), "[");
                        if (self.tys.store.get(s).len) |l| {
                            try Task.writeInt(l, writer, to);
                        }
                        try writer.appendSlice(to.allocator(), "]");
                        work_list.appendAssumeCapacity(.{ .Type = self.tys.store.get(s).elem });
                    },
                    .Nullable => |n| {
                        try writer.appendSlice(to.allocator(), "?");
                        work_list.appendAssumeCapacity(.{ .Type = self.tys.store.get(n).inner });
                    },
                    .Tuple => |tupl| {
                        try writer.appendSlice(to.allocator(), "(");
                        var iter = std.mem.reverseIterator(self.tys.store.get(tupl).fields);
                        work_list.ensureUnusedCapacity(
                            tmp.arena.allocator(),
                            iter.index * 2,
                        ) catch unreachable;
                        work_list.appendAssumeCapacity(.{ .Name = ") " });
                        while (iter.next()) |elem| {
                            work_list.appendAssumeCapacity(.{ .Type = elem.ty });
                            work_list.appendAssumeCapacity(.{ .Name = ", " });
                        }
                        _ = work_list.pop();
                    },
                    .Func, .Global, .Template, .Struct, .Union, .Enum => {
                        var cursor = t;
                        var depth: usize = 0;
                        const frame = scope_stack.items.len;
                        work_list.appendAssumeCapacity(.{ .PopScope = frame });
                        while (cursor != .void) : (depth += 1) {
                            if (std.mem.indexOfScalar(Id, scope_stack.items, cursor) != null) {
                                work_list.appendAssumeCapacity(.{ .Name = "." });
                                break;
                            }
                            const key = cursor.getKey(self.tys);
                            cursor = key.loc.scope;

                            captures_to_display.clearRetainingCapacity();
                            try captures_to_display.ensureTotalCapacity(tmp.arena.allocator(), key.captures.len);
                            for (key.captures) |cap| {
                                if (try seen_captures.fetchPut(tmp.arena.allocator(), cap, {}) == null) {
                                    captures_to_display.appendAssumeCapacity(cap);
                                }
                            }

                            try work_list.ensureUnusedCapacity(tmp.arena.allocator(), captures_to_display.items.len * 2 + 4);
                            if (captures_to_display.items.len != 0) {
                                work_list.appendAssumeCapacity(.{ .Name = ")" });
                                var iter = std.mem.reverseIterator(captures_to_display.items);
                                while (iter.next()) |cap| {
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
                            if (key.name.len != 0 and (key.name.len != 1 or key.name[0] != '-')) {
                                if (key.loc.scope == .void) {
                                    const end = std.mem.lastIndexOfScalar(u8, key.name, '.') orelse key.name.len;
                                    work_list.appendAssumeCapacity(.{ .Name = key.name[0..end] });
                                } else {
                                    work_list.appendAssumeCapacity(.{ .Name = key.name });
                                }
                                work_list.appendAssumeCapacity(.{ .Name = "." });
                            }
                        }
                        _ = work_list.pop();
                    },
                },
                .Name => |n| try writer.appendSlice(to.allocator(), n),
                .Value => |v| switch (v.ty.data()) {
                    .Builtin => |b| switch (@as(Builtin, b)) {
                        .never, .any => try writer.appendSlice(to.allocator(), "<invalid>"),
                        .void => try writer.appendSlice(to.allocator(), ".()"),
                        .bool => try writer.appendSlice(to.allocator(), if (v.value != 0) "true" else "false"),
                        .u8, .u16, .u32, .u64, .uint => try Task.writeInt(v.value, writer, to),
                        .i8, .i16, .i32, .i64, .int => try Task.writeInt(@bitCast(v.value), writer, to),
                        .f32 => try writer.writer(to.allocator()).print("{}", .{@as(f32, @bitCast(@as(u32, @truncate(v.value))))}),
                        .f64 => try writer.writer(to.allocator()).print("{}", .{@as(f64, @bitCast(@as(u64, @truncate(v.value))))}),
                        .type => work_list.appendAssumeCapacity(.{ .Type = @enumFromInt(v.value) }),
                    },
                    .Slice => |s| {
                        const slc: tys.Slice = self.tys.store.get(s).*;
                        const ln, const global, const base = if (slc.len) |l| b: {
                            break :b .{ l, v.value, v.offset };
                        } else b: {
                            const ptr = readFromGlobal(self.tys, @enumFromInt(v.value), .uint, v.offset + tys.Slice.ptr_offset);
                            const ln = readFromGlobal(self.tys, @enumFromInt(v.value), .uint, v.offset + tys.Slice.len_offset);

                            const global = self.tys.findSymForPtr(@intCast(ptr), ln * slc.elem.size(self.tys));
                            break :b .{ ln, global catch |err| {
                                try writer.appendSlice(to.allocator(), "<corrupted-slice>(");
                                try writer.appendSlice(to.allocator(), @errorName(err));
                                try writer.appendSlice(to.allocator(), ")");
                                continue;
                            }, 0 };
                        };

                        if (slc.elem == .u8 and slc.len == null) {
                            const glb: utils.EntId(tys.Global) = @enumFromInt(global);
                            try writer.appendSlice(to.allocator(), "\"");
                            try writer.appendSlice(to.allocator(), self.tys.store.get(glb).data[@intCast(base)..][0..@intCast(ln)]);
                            try writer.appendSlice(to.allocator(), "\"");
                            continue;
                        }

                        if (slc.len == null) {
                            try writer.appendSlice(to.allocator(), "&.[");
                        } else {
                            try writer.appendSlice(to.allocator(), ".[");
                        }

                        work_list.ensureUnusedCapacity(tmp.arena.allocator(), @intCast(ln * 2)) catch unreachable;
                        try work_list.append(tmp.arena.allocator(), .{ .Name = "]" });
                        for (0..@intCast(ln)) |i| {
                            const off = i * slc.elem.size(self.tys);
                            work_list.appendAssumeCapacity(.{ .Value = .normalize(.{
                                .ty = slc.elem,
                                .value = global,
                                .offset = @intCast(off),
                            }, self.tys) });
                            work_list.appendAssumeCapacity(.{ .Name = ", " });
                        }
                        _ = work_list.pop();
                    },
                    .Struct => |s| {
                        var offsets = @as(tys.Struct.Id, s).offsetIter(self.tys);
                        try writer.appendSlice(to.allocator(), ".{");
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
                        const global = self.tys.findSymForPtr(@intCast(v.value), ty.size(self.tys)) catch |err| {
                            try writer.appendSlice(to.allocator(), "<corrupted-pointer>(");
                            try writer.appendSlice(to.allocator(), @errorName(err));
                            try writer.appendSlice(to.allocator(), ")");
                            return;
                        };

                        try writer.appendSlice(to.allocator(), "&");
                        work_list.appendAssumeCapacity(.{
                            .Value = .normalize(.{ .ty = ty, .value = global }, self.tys),
                        });
                    },
                    .Tuple => |t| {
                        try writer.appendSlice(to.allocator(), ".(");
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
                        try writer.appendSlice(to.allocator(), ".");
                        try writer.appendSlice(to.allocator(), e.getFields(self.tys)[@intCast(v.value)].name);
                    },
                    .Nullable => |n| {
                        const global = self.tys.store.get(@as(utils.EntId(tys.Global), @enumFromInt(v.value)));
                        if (self.tys.isNullablePresent(n, global, v.offset)) {
                            try writer.appendSlice(to.allocator(), "null");
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
                    .Union => try writer.appendSlice(to.allocator(), "<union: cant display>"),
                    .Template, .Global, .Func => unreachable,
                },
            };
        }

        pub fn format(self: *const Fmt, comptime _: []const u8, _: anytype, writer: anytype) !void {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();
            var arr = std.ArrayListUnmanaged(u8).empty;
            self.fmt(&arr, tmp.arena);
            try writer.writeAll(arr.items);
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

pub fn readFromGlobal(self: *Types, global: utils.EntId(tys.Global), ty: Id, offset: u64) u64 {
    const glob = self.store.get(global);
    var value: u64 = 0;
    @memcpy(
        @as([*]u8, @ptrCast(&value))[0..@intCast(ty.size(self))],
        glob.data[@intCast(offset)..][0..@intCast(ty.size(self))],
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

pub fn retainGlobals(self: *Types, target: Target, backend: anytype, scratch: ?*utils.Arena) bool {
    errdefer unreachable;

    var errored = false;

    const work_list = self.global_work_list.getPtr(target);
    while (work_list.pop()) |global| {
        var scrath = utils.Arena.scrath(scratch);
        defer scrath.deinit();

        const glob: *tys.Global = self.store.get(global);
        if (glob.completion.get(target) == .compiled) continue;
        glob.completion.getPtr(target).* = .compiled;

        var relocs = std.ArrayListUnmanaged(Machine.DataOptions.Reloc){};
        if (target == .runtime) {
            self.findNestedGlobals(&relocs, glob, scrath.arena, glob.ty, 0) catch |err| {
                errored = true;
                self.report(
                    glob.key.loc.file,
                    glob.key.loc.ast,
                    "global is corrupted (of type {}) (global_id: {}): contains a pointer {}",
                    .{ glob.ty, @intFromEnum(global), @errorName(err) },
                );
            };
        }

        backend.emitData(.{
            .id = @intFromEnum(global),
            .name = if (scratch) |s| root.frontend.Types.Id.init(.{ .Global = global })
                .fmt(self).toString(s) else "",
            .value = .{ .init = glob.data },
            .relocs = relocs.items,
            .readonly = glob.readonly,
        });
    }

    return errored;
}

pub fn findNestedGlobals(
    self: *Types,
    relocs: *std.ArrayListUnmanaged(Machine.DataOptions.Reloc),
    global: *tys.Global,
    scratch: *utils.Arena,
    ty: Id,
    offset_f: u64,
) !void {
    const offset: usize = @intCast(offset_f);
    switch (ty.data()) {
        .Union, .Enum, .Builtin => {},
        .Pointer => |p| {
            const base: Id = self.store.get(p).*;

            const ptr_big: u64 = @bitCast(global.data[offset..][0..8].*);
            const ptr: usize = @intCast(ptr_big);

            const cap = base.size(self);
            if (cap == 0) return;

            relocs.append(scratch.allocator(), .{
                .offset = @intCast(offset),
                .target = try self.findSymForPtr(ptr, cap),
            }) catch unreachable;
        },
        .Slice => |s| {
            const slc: *tys.Slice = self.store.get(s);

            if (slc.len) |len| {
                const elem_size = slc.elem.size(self);
                for (0..len) |idx| {
                    try self.findNestedGlobals(
                        relocs,
                        global,
                        scratch,
                        slc.elem,
                        offset + idx * elem_size,
                    );
                }
            } else {
                const ptr_big: u64 = @bitCast(global.data[offset + tys.Slice.ptr_offset ..][0..8].*);
                const ptr: usize = @intCast(ptr_big);
                const len_big: u64 = @bitCast(global.data[offset + tys.Slice.len_offset ..][0..8].*);
                const len: usize = @intCast(len_big);

                const cap = len * slc.elem.size(self);
                if (cap == 0) return;

                relocs.append(scratch.allocator(), .{
                    .offset = @intCast(offset + tys.Slice.ptr_offset),
                    .target = try self.findSymForPtr(ptr, cap),
                }) catch unreachable;
            }
        },
        inline .Struct, .Tuple => |t| {
            var fields_iter = t.offsetIter(self);
            while (fields_iter.next()) |elem| {
                try self.findNestedGlobals(relocs, global, scratch, elem.field.ty, elem.offset);
            }
        },
        .Nullable => |n| {
            if (self.isNullablePresent(n, global, offset)) return;

            const data: *tys.Nullable = self.store.get(n);
            const nieche: ?tys.Nullable.NiecheSpec = data.nieche.offset(self);
            const next_offset = if (nieche != null) data.inner.alignment(self) else 0;
            try self.findNestedGlobals(relocs, global, scratch, data.inner, offset + next_offset);
        },
        .Global, .Func, .Template => unreachable,
    }
}

pub fn isNullablePresent(self: *Types, n: utils.EntId(tys.Nullable), global: *tys.Global, offset: u64) bool {
    const data: *tys.Nullable = self.store.get(n);
    const nieche: ?tys.Nullable.NiecheSpec = data.nieche.offset(self);

    return if (nieche) |niche| b: {
        const abi = niche.kind.abi();
        if (abi == .bot) return false;
        const size = abi.size();

        var value: u64 = 0;
        @memcpy(
            @as(*[8]u8, @ptrCast(&value))[0..@intCast(size)],
            global.data[@intCast(offset + niche.offset)..][0..@intCast(size)],
        );

        break :b value != 0;
    } else global.data[@intCast(offset)] != 0;
}

pub fn findSymForPtr(
    self: *Types,
    ptr: usize,
    cap: u64,
) !u32 {
    const data = &self.ct.gen.out;

    if (ptr < Comptime.stack_size)
        return error.@"to comptime stack";

    if (ptr > data.code.items.len) {
        return error.@"exceeding code section";
    }

    const id: utils.EntId(tys.Global) =
        @enumFromInt(@as(u32, @bitCast(data.code.items[ptr - 4 ..][0..4].*)));

    if (!self.store.isValid(.Global, @intFromEnum(id)))
        return error.@"to something thats not a global";

    self.queue(.runtime, .init(.{ .Global = id }));
    const sym = &data.syms.items[@intFromEnum(data.globals.items[@intFromEnum(id)])];

    if (sym.size != cap)
        return error.@"to a global with different size";

    return @intFromEnum(id);
}

pub fn queue(self: *Types, target: Target, task: Id) void {
    errdefer unreachable;
    switch (task.data()) {
        .Func => |func| {
            if (self.store.get(func).completion.get(target) == .compiled) return;
            try self.func_work_list.getPtr(target).append(self.pool.allocator(), func);
        },
        .Global => |global| {
            if (self.store.get(global).completion.get(target) == .compiled) return;
            try self.global_work_list.getPtr(target).append(self.pool.allocator(), global);
        },
        else => unreachable,
    }
}

pub fn nextTask(self: *Types, target: Target, pop_limit: usize) ?utils.EntId(tys.Func) {
    while (self.func_work_list.get(target).items.len > pop_limit) {
        const func = self.func_work_list.getPtr(target).pop() orelse return null;
        if (self.store.get(func).completion.get(target) == .compiled) continue;
        self.store.get(func).completion.set(target, .compiled);
        return func;
    }
    return null;
}

pub fn init(arena_: Arena, source: []const Ast, diagnostics: std.io.AnyWriter) *Types {
    var arena = arena_;
    const scopes = arena.alloc(Id, source.len);
    @memset(scopes, .void);
    const slot = arena.create(Types);
    slot.* = .{
        .func_work_list = .{ .values = .{ .empty, .empty } },
        .global_work_list = .{ .values = .{ .empty, .empty } },
        .stack_base = @frameAddress(),
        .files = source,
        .file_scopes = scopes,
        .pool = .{
            .arena = arena,
        },
        .ct = .init(&slot.pool),
        .diagnostics = diagnostics,
    };

    slot.ct.gen.emit_global_reloc_offsets = true;

    slot.string = slot.makeSlice(null, .u8);
    slot.source_loc = .init(.{ .Struct = slot.store.add(slot.pool.allocator(), tys.Struct{
        .key = .{
            .loc = .{
                .file = .root,
                .scope = slot.getScope(.root),
                .ast = .zeroSized(.Void),
            },
            .name = "SrcLoc",
            .captures = &.{},
        },
        .index = .empty,
        .alignment = 8,
        .size = 32,
        .fields = slot.pool.arena.dupe(tys.Struct.Field, &.{
            .{ .name = "src", .ty = slot.string },
            .{ .name = "line", .ty = .u32 },
            .{ .name = "col", .ty = .u32 },
        }),
    }) });

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

pub fn checkStack(self: *Types, file: File, pos: anytype) !void {
    const distance = @abs(@as(isize, @bitCast(@frameAddress() -% self.stack_base)));
    if (distance > root.frontend.Parser.stack_limit) {
        self.report(file, pos, "the comptime evaluation recurses too deep", .{});
        //std.debug.dumpCurrentStackTrace(@returnAddress());
        return error.StackOverflow;
    }
}

pub fn deinit(self: *Types) void {
    var arena = self.pool.arena;
    self.ct.in_progress.deinit(self.ct.gen.gpa.allocator());
    self.ct.gen.deinit();
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
    const vl = self.store.add(self.pool.allocator(), payload);
    const id = Id.init(@unionInit(Data, @tagName(tag), vl));
    const slot = self.interner.getOrPutContext(self.pool.allocator(), id, .{ .types = self }) catch unreachable;
    if (slot.found_existing) {
        self.store.pop(vl);
        return slot.key_ptr.*;
    }
    if (@TypeOf(payload) == tys.Tuple) {
        self.store.get(vl).fields = self.pool.arena.dupe(tys.Tuple.Field, payload.fields);
    } else self.store.get(vl).* = payload;
    return slot.key_ptr.*;
}

pub fn makeSlice(self: *Types, len: ?usize, elem: Id) Id {
    return self.internPtr(.Slice, .{ .len = len, .elem = elem });
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

pub fn intern(self: *Types, comptime kind: std.meta.Tag(Data), key: Scope) struct { Map.GetOrPutResult, std.meta.TagPayload(Data, kind) } {
    var mem: std.meta.TagPayload(Data, kind).Data = undefined;
    mem.key = key;
    const ty = self.store.add(self.pool.allocator(), mem);
    const id = Id.init(@unionInit(Data, @tagName(kind), ty));
    const slot = self.interner.getOrPutContext(self.pool.allocator(), id, .{ .types = self }) catch unreachable;
    if (slot.found_existing) {
        std.debug.assert(slot.key_ptr.data() == kind);
        self.store.pop(ty);
        return .{ slot, @field(slot.key_ptr.data(), @tagName(kind)) };
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
        },
        .name = name,
        .captures = captures,
    });
    if (!slot.found_existing) {
        self.store.get(alloc).* = .{
            .key = self.store.get(alloc).key,
            .index = Ast.Index.build(
                self.getFile(file),
                self.getFile(file).exprs.get(ast).Type.fields,
                &self.pool.arena,
            ),
        };
    }
    return slot.key_ptr.*;
}

pub fn dumpAnalErrors(self: *Types, anal_errors: *std.ArrayListUnmanaged(static_anal.Error)) bool {
    for (anal_errors.items) |err| switch (err) {
        .ReturningStack => |loc| {
            self.reportSloc(loc.slot, "stack location escapes the function", .{});
        },
        .StackOob => |loc| {
            self.reportSloc(loc.slot, "this slot has a out of bounds read/write", .{});
            self.reportSloc(loc.access, "...the access is here, stack slot has {} bytes," ++
                " whild access is at {}..{}", .{ loc.size, loc.range.start, loc.range.end });
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

pub fn addUniqueGlobal(self: *Types, scope: Id) utils.EntId(tys.Global) {
    const glob = self.store.add(self.pool.allocator(), tys.Global{
        .key = .{
            .loc = .{
                .file = scope.file(self).?,
                .scope = scope,
                .ast = .zeroSized(.Void),
            },
            .name = "",
            .captures = &.{},
        },
        .data = "",
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
        .name = name,
        .captures = &.{},
    });

    if (!slot.found_existing) {
        self.store.get(alloc).* = .{
            .key = self.store.get(alloc).key,
            .readonly = readonly,
        };
    }
    return .{ slot.key_ptr.*, !slot.found_existing };
}
