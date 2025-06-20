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
const tys = root.frontend.types;

pub const Abi = root.frontend.Abi;

next_struct: u32 = 0,
store: utils.EntStore(root.frontend.types) = .{},
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
handler_signatures: std.EnumArray(std.meta.FieldEnum(Handlers), Handlers.Signature) = undefined,

const Types = @This();
const Map = std.hash_map.HashMapUnmanaged(Id, void, TypeCtx, 70);

pub const Handlers = struct {
    slice_ioob: ?utils.EntId(tys.Func) = null,
    null_unwrap: ?utils.EntId(tys.Func) = null,

    pub const Signature = struct { args: []const Id, ret: Id };
};

pub const Scope = struct {
    file: Types.File,
    scope: Id,
    ast: Ast.Id,
    name: []const u8,
    captures: []const Capture,

    pub const Capture = struct {
        id: Ast.Ident,
        ty: Id,
        value: u64 = 0,
    };

    pub const dummy = Scope{
        .file = .root,
        .scope = .void,
        .ast = .zeroSized(.Void),
        .name = "",
        .captures = &.{},
    };

    pub fn eql(self: Scope, other: Scope) bool {
        return self.file == other.file and self.scope == other.scope and self.ast == other.ast and
            self.captures.len == other.captures.len and
            for (self.captures, other.captures) |a, b| {
                if (!std.meta.eql(a, b)) return false;
            } else true;
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
            inline .Enum, .Union, .Struct, .Func, .Template, .Global => |v, t| self.types.store.get(v).key.eql(self.types.store.get(@field(bd, @tagName(t))).key),
        };
    }

    pub fn hash(self: @This(), adapted_key: Id) u64 {
        var hasher = std.hash.Fnv1a_64.init();
        const adk = adapted_key.data();
        std.hash.autoHash(&hasher, std.meta.activeTag(adk));
        switch (adk) {
            .Builtin => |bl| std.hash.autoHash(&hasher, bl),
            inline .Pointer, .Slice => |s| std.hash.autoHash(&hasher, self.types.store.get(s).*),
            .Nullable => |n| std.hash.autoHash(&hasher, self.types.store.get(n).inner),
            .Tuple => |n| std.hash.autoHashStrat(&hasher, self.types.store.get(n).fields, .Deep),
            inline .Enum, .Union, .Struct, .Func, .Template, .Global => |v| std.hash.autoHashStrat(&hasher, self.types.store.get(v).key, .Deep),
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
            .Template => |t| if (types.store.get(t).temporary) return types.store.get(t).key.scope,
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
            inline .Func, .Template, .Global => |t| types.store.get(t).key.scope.firstType(types),
            .Builtin, .Tuple, .Pointer, .Nullable, .Slice => unreachable,
        };
    }

    pub fn file(self: Id, types: *Types) ?File {
        return switch (self.data()) {
            .Builtin, .Pointer, .Slice, .Nullable, .Tuple => null,
            inline else => |v| types.store.get(v).key.file,
        };
    }

    pub fn index(self: Id, types: *Types) ?Ast.Index {
        return switch (self.data()) {
            inline .Struct, .Union, .Enum => |v| types.store.get(v).index,
            else => null,
        };
    }

    pub fn items(self: Id, ast: *const Ast, types: *Types) Ast.Slice {
        return switch (self.data()) {
            .Global, .Builtin, .Pointer, .Slice, .Nullable, .Tuple => utils.panic("{s}", .{@tagName(self.data())}),
            .Template, .Func => .{},
            inline else => |v, t| ast.exprs.getTyped(@field(std.meta.Tag(Ast.Expr), @tagName(t)), types.store.get(v).key.ast).?.fields,
        };
    }

    pub fn captures(self: Id, types: *Types) []const Scope.Capture {
        return switch (self.data()) {
            .Global, .Builtin, .Pointer, .Slice, .Nullable, .Tuple => utils.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| types.store.get(v).key.captures,
        };
    }

    pub fn findCapture(self: Id, id: Ast.Ident, types: *Types) ?Scope.Capture {
        return switch (self.data()) {
            .Global, .Builtin, .Pointer, .Slice, .Nullable, .Tuple => utils.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| for (types.store.get(v).key.captures) |cp| {
                if (cp.id == id) break cp;
            } else null,
        };
    }

    pub fn parent(self: Id, types: *Types) Id {
        return switch (self.data()) {
            .Global, .Builtin, .Pointer, .Slice, .Nullable, .Tuple => utils.panic("{s}", .{@tagName(self.data())}),
            inline else => |v| types.store.get(v).key.scope,
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
            .Pointer => return .{ .offset = 0, .kind = .ptr },
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
        // TODO: what about uninhabited types?
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
            .Enum => |e| {
                const var_count = e.getFields(types).len;
                if (var_count <= 1) return 0;
                return std.math.ceilPowerOfTwo(u64, std.mem.alignForward(u64, std.math.log2_int(u64, var_count), 8) / 8) catch unreachable;
            },
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
            .Slice => |s| if (types.store.get(s).len == null) 8 else types.store.get(s).elem.alignment(types),
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

        pub fn toString(self: *const Fmt, arena: std.mem.Allocator) ![]u8 {
            return std.fmt.allocPrint(arena, "{}", .{self});
        }

        pub fn format(self: *const Fmt, comptime opts: []const u8, _: anytype, writer: anytype) !void {
            try switch (self.self.data()) {
                .Pointer => |b| writer.print("^{" ++ opts ++ "}", .{self.tys.store.get(b).fmt(self.tys)}),
                .Nullable => |b| writer.print("?{" ++ opts ++ "}", .{self.tys.store.get(b).inner.fmt(self.tys)}),
                .Slice => |b| {
                    try writer.writeAll("[");
                    if (self.tys.store.get(b).len) |l| try writer.print("{d}", .{l});
                    try writer.writeAll("]");
                    try writer.print("{" ++ opts ++ "}", .{self.tys.store.get(b).elem.fmt(self.tys)});
                    return;
                },
                .Tuple => |b| {
                    try writer.writeAll("(");
                    for (self.tys.store.get(b).fields, 0..) |f, i| {
                        if (i != 0) try writer.writeAll(", ");
                        try writer.print("{" ++ opts ++ "}", .{f.ty.fmt(self.tys)});
                    }
                    try writer.writeAll(")");
                    return;
                },
                .Builtin => |b| writer.writeAll(@tagName(b)),
                inline .Func, .Global, .Template, .Struct, .Union, .Enum => |v| {
                    const b = self.tys.store.get(v);
                    if (b.key.scope != .void) {
                        try writer.print("{" ++ opts ++ "}", .{b.key.scope.fmt(self.tys)});
                    }
                    if (b.key.name.len != 0) {
                        const testing = comptime !std.mem.eql(u8, opts, "test") or true;
                        if (b.key.scope != .void and
                            (b.key.scope.data() != .Struct or
                                self.tys.store.get(b.key.scope.data().Struct).key.scope != .void or
                                testing)) try writer.writeAll(".");
                        if (b.key.scope != .void) {
                            try writer.print("{s}", .{b.key.name});
                        } else {
                            if (testing) {
                                var path = std.mem.splitBackwardsAny(u8, b.key.name, "/");
                                try writer.print("{s}", .{path.first()});
                            }
                        }
                    }
                    if (b.key.captures.len != 0) {
                        var written_paren = false;
                        o: for (b.key.captures) |capture| {
                            var cursor = b.key.scope;
                            while (cursor != .void and cursor.data() != .Pointer and cursor.data() != .Builtin) {
                                if (cursor.findCapture(capture.id, self.tys) != null) continue :o;
                                cursor = cursor.parent(self.tys);
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

    pub fn fmt(self: Id, types: *Types) Fmt {
        return .{ .self = self, .tys = types };
    }
};

pub const Target = enum { @"comptime", runtime };

pub fn retainGlobals(self: *Types, target: Target, backend: anytype, scratch: ?std.mem.Allocator) void {
    errdefer unreachable;

    const work_list = self.global_work_list.getPtr(target);
    for (work_list.items) |global| {
        backend.emitData(.{
            .id = @intFromEnum(global),
            .name = if (scratch) |s| try root.frontend.Types.Id.init(.{ .Global = global })
                .fmt(self).toString(s) else "",
            .value = .{ .init = self.store.get(global).data },
            .readonly = self.store.get(global).readonly,
        });
    }
    work_list.items.len = 0;
}

pub fn queue(self: *Types, target: Target, task: Id) void {
    errdefer unreachable;
    switch (task.data()) {
        .Func => |func| {
            if (self.store.get(func).completion.get(target) == .compiled) return;
            self.func_work_list.getPtr(target).appendAssumeCapacity(func);
        },
        .Global => |global| {
            if (self.store.get(global).completion.get(target) == .compiled) return;
            self.global_work_list.getPtr(target).appendAssumeCapacity(global);
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
        .func_work_list = .{ .values = .{
            arena.makeArrayList(utils.EntId(tys.Func), 1024),
            arena.makeArrayList(utils.EntId(tys.Func), 1024),
        } },
        .global_work_list = .{ .values = .{
            arena.makeArrayList(utils.EntId(tys.Global), 1024),
            arena.makeArrayList(utils.EntId(tys.Global), 1024),
        } },
        .stack_base = @frameAddress(),
        .files = source,
        .file_scopes = scopes,
        .pool = .{
            .arena = arena,
        },
        .ct = .init(slot.pool.allocator()),
        .diagnostics = diagnostics,
    };

    slot.string = slot.makeSlice(null, .u8);
    slot.source_loc = .init(.{ .Struct = slot.store.add(slot.pool.allocator(), tys.Struct{
        .key = .{
            .name = "SrcLoc",
            .file = .root,
            .scope = slot.getScope(.root),
            .ast = .zeroSized(.Void),
            .captures = &.{},
        },
        .index = .empty,
        .alignment = 8,
        .size = 32,
        .fields = slot.pool.arena.dupe(tys.Struct.Field, &.{
            .{ .name = "src", .ty = slot.string },
            .{ .name = "line", .ty = .uint },
            .{ .name = "col", .ty = .uint },
        }),
    }) });

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
        },
    };

    return slot;
}

pub fn checkStack(self: *Types, file: File, pos: anytype) !void {
    const distance = @abs(@as(isize, @bitCast(@frameAddress() -% self.stack_base)));
    if (distance > root.frontend.Parser.stack_limit) {
        self.report(file, pos, "the comptime evaluation recurses too deep", .{});
        std.debug.dumpCurrentStackTrace(@returnAddress());
        return error.StackOverflow;
    }
}

pub fn deinit(self: *Types) void {
    var arena = self.pool.arena;
    self.ct.in_progress.deinit(self.ct.gen.gpa);
    self.ct.gen.deinit();
    self.* = undefined;
    arena.deinit();
}

pub fn reportSloc(self: *Types, sloc: graph.Sloc, comptime fmt: []const u8, args: anytype) void {
    std.debug.assert(sloc != graph.Sloc.none);
    self.report(@enumFromInt(sloc.namespace), sloc.index, fmt, args);
}

pub fn report(self: *Types, file_id: File, expr: anytype, comptime fmt: []const u8, args: anytype) void {
    const RemapedArgs = comptime b: {
        var tupl = @typeInfo(@TypeOf(args)).@"struct";
        var fields = tupl.fields[0..tupl.fields.len].*;
        for (&fields) |*f| if (f.type == Types.Id) {
            f.type = Types.Id.Fmt;
            f.alignment = @alignOf(f.type);
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

    const file = self.getFile(file_id);
    Ast.report(file.path, file.source, file.posOf(expr).index, fmt, rargs, self.colors, self.diagnostics);
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
        .scope = scope,
        .file = file,
        .ast = ast,
        .name = name,
        .captures = captures,
    });
    if (!slot.found_existing) {
        self.store.get(alloc).* = .{
            .key = self.store.get(alloc).key,
            .index = Ast.Index.build(
                self.getFile(file),
                @field(self.getFile(file).exprs.get(ast), @tagName(tag)).fields,
                self.pool.arena.allocator(),
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
            self.reportSloc(loc.slot, "this slot has a out of bounds read/write" ++
                " (TODO: show the index location as well)", .{});
        },
        .LoopInvariantBreak => |loc| {
            self.reportSloc(loc.if_node, "the if condition is loop invariant but it" ++
                " decides wheter to break out ouf the loop", .{});
        },
    };
    defer anal_errors.items.len = 0;
    return anal_errors.items.len != 0;
}

pub fn resolveGlobal(
    self: *Types,
    scope: Id,
    name: []const u8,
    ast: Ast.Id,
    readonly: bool,
) struct { Id, bool } {
    const slot, const alloc = self.intern(.Global, .{
        .scope = scope,
        .file = scope.file(self).?,
        .ast = ast,
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
