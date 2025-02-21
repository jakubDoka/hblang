next_struct: u32 = 0,
next_func: u32 = 0,
next_global: u32 = 0,
arena: std.heap.ArenaAllocator,
interner: Map = .{},
file_scopes: []Id,
comptime_code: HbvmGen,
vm: Vm = .{},
diagnostics: std.io.AnyWriter,
files: []const Ast,

const std = @import("std");
const Ast = @import("Ast.zig");
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
            .Ptr => std.meta.eql(ad.Ptr.*, bd.Ptr.*),
            inline else => |v, t| return v.key.eql(@field(bd, @tagName(t)).key),
        };
    }

    pub fn hash(_: @This(), adapted_key: Id) u64 {
        var hasher = std.hash.Fnv1a_64.init();
        const adk = adapted_key.data();
        switch (adk) {
            .Builtin, .Ptr => std.hash.autoHashStrat(&hasher, adk, .Deep),
            inline else => |v| {
                std.hash.autoHashStrat(&hasher, v.key, .Deep);
            },
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
    Struct: *Struct,
    Template: *Template,
    Func: *Func,
    Global: *Global,
};

pub const Key = struct {
    file: File,
    scope: Id,
    ast: Ast.Id,
    capture_idents: Ast.Idents,
    captures: []const Id,

    pub const dummy = Key{
        .file = .root,
        .scope = .void,
        .ast = .zeroSized(.Void),
        .capture_idents = .{},
        .captures = &.{},
    };

    pub fn eql(self: Key, other: Key) bool {
        return self.file == other.file and self.scope == other.scope and self.ast == other.ast and
            std.mem.eql(Id, self.captures, other.captures);
    }
};

pub const Struct = struct {
    key: Key,

    ast_fields: Ast.Slice,
    name: []const u8,
    fields: ?[]const Field = null,

    pub const Field = struct {
        name: []const u8,
        ty: Id,
    };

    pub fn asTy(self: *Struct) Id {
        return Id.init(.{ .Struct = self });
    }

    pub fn getFields(self: *Struct, types: *Types) []const Field {
        if (self.fields) |f| return f;
        const ast = types.getFile(self.key.file);

        var count: usize = 0;
        for (ast.exprs.view(self.ast_fields)) |f| count += @intFromBool(ast.exprs.get(f).BinOp.lhs.tag() == .Tag);

        const fields = types.arena.allocator().alloc(Field, count) catch unreachable;
        var i: usize = 0;
        for (ast.exprs.view(self.ast_fields)) |fast| {
            const field = ast.exprs.get(fast).BinOp;
            if (field.lhs.tag() != .Tag) continue;
            fields[i] = .{
                .name = ast.tokenSrc(ast.exprs.get(field.lhs).Tag.index + 1),
                .ty = Comptime.evalTy(types, .{ .scope = self.asTy() }, field.rhs),
            };
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
    name: []const u8,
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
    name: []const u8,
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
    _,

    const Repr = packed struct(usize) {
        data: std.meta.Int(.unsigned, @bitSizeOf(usize) - @bitSizeOf(std.meta.Tag(Data))),
        flag: std.meta.Tag(std.meta.Tag(Data)),

        inline fn tag(self: Repr) std.meta.Tag(Data) {
            return @enumFromInt(self.flag);
        }
    };

    pub fn fromLexeme(lexeme: Lexer.Lexeme) Id {
        const off = comptime @as(isize, @intFromEnum(Id.void)) - @intFromEnum(Lexer.Lexeme.void);
        return @enumFromInt(@as(isize, @intFromEnum(lexeme)) + off);
    }

    pub inline fn init(dt: Data) Id {
        comptime {
            std.debug.assert(fromLexeme(.i8) == .i8);
        }
        return @enumFromInt(@as(u64, @bitCast(Repr{
            .flag = @intFromEnum(dt),
            .data = @intCast(switch (dt) {
                .Builtin => |b| @intFromEnum(b),
                inline else => |b| @intFromPtr(b),
            }),
        })));
    }

    pub fn file(self: Id) File {
        return switch (self.data()) {
            .Builtin, .Ptr => unreachable,
            inline else => |v| v.key.file,
        };
    }

    pub fn items(self: Id) Ast.Slice {
        return switch (self.data()) {
            .Global, .Builtin, .Ptr => unreachable,
            .Template, .Func => .{},
            inline else => |v| v.ast_fields,
        };
    }

    pub fn captures(self: Id) []const Id {
        return switch (self.data()) {
            .Global, .Builtin, .Ptr => unreachable,
            inline else => |v| v.key.captures,
        };
    }

    pub fn findCapture(self: Id, ast: *const Ast, id: Ast.Ident) ?Id {
        return switch (self.data()) {
            .Global, .Builtin, .Ptr => unreachable,
            inline else => |v| for (ast.exprs.view(v.key.capture_idents), v.key.captures) |cid, c| {
                if (cid == id) break c;
            } else null,
        };
    }

    pub fn parent(self: Id) Id {
        return switch (self.data()) {
            .Global, .Builtin, .Ptr => unreachable,
            inline else => |v| v.key.scope,
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

    pub fn size(self: Id, types: *Types) usize {
        return switch (self.data()) {
            .Builtin => |b| switch (b) {
                .never => unreachable,
                .void => 0,
                .u8, .i8, .bool => 1,
                .u16, .i16 => 2,
                .u32, .i32 => 4,
                .uint, .int, .type => 8,
            },
            .Ptr => 8,
            .Struct => |s| {
                var siz: usize = 0;
                var alignm: usize = 1;
                for (s.getFields(types)) |f| {
                    alignm = @max(alignm, f.ty.alignment(types));
                    siz = std.mem.alignForward(usize, siz, f.ty.alignment(types));
                    siz += f.ty.size(types);
                }
                siz = std.mem.alignForward(usize, siz, alignm);
                return siz;
            },
            else => unreachable,
        };
    }

    pub fn alignment(self: Id, types: *Types) usize {
        return switch (self.data()) {
            .Builtin => self.size(types),
            .Ptr => 8,
            .Struct => |s| {
                var alignm: usize = 1;
                for (s.getFields(types)) |f| {
                    alignm = @max(alignm, f.ty.alignment(types));
                }
                return alignm;
            },
            else => unreachable,
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

    pub fn format(self: *const Id, comptime _: anytype, _: anytype, writer: anytype) !void {
        try switch (self.data()) {
            .Ptr => |b| writer.print("^{}", .{b}),
            .Builtin => |b| writer.writeAll(@tagName(b)),
            .Struct => |b| writer.writeAll(b.name),
            .Template => |b| writer.print("{}", .{b}),
            .Func => |b| writer.print("{}", .{b}),
            .Global => |b| writer.print("{}", .{b}),
        };
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
                .never => unreachable,
                .void => return .Imaginary,
                .u8, .i8, .bool => .i8,
                .u16, .i16 => .i16,
                .u32, .i32 => .i32,
                .uint, .int, .type => .int,
            } },
            .Ptr => .{ .ByValue = .int },
            .Struct => |s| switch (self) {
                .ableos => categorizeAbleosStruct(s, types),
            },
            else => unreachable,
        };
    }

    pub fn categorizeAbleosStruct(stru: *Struct, types: *Types) Spec {
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
    const scopes = gpa.alloc(Id, source.len) catch unreachable;
    @memset(scopes, .void);
    return .{
        .files = source,
        .file_scopes = scopes,
        .arena = .init(gpa),
        .comptime_code = .init(gpa),
        .diagnostics = diagnostics,
    };
}

pub fn deinit(self: *Types) void {
    self.interner.deinit(self.arena.child_allocator);
    self.arena.child_allocator.free(self.file_scopes);
    self.arena.deinit();
    self.comptime_code.out.deinit();
    self.comptime_code.deinit();
    self.* = undefined;
}

pub fn getAst(self: *Types, file: File, expr: Ast.Id) Ast.Expr {
    return self.getFile(file).exprs.get(expr);
}

pub fn getFile(self: *Types, file: File) *const Ast {
    return &self.files[@intFromEnum(file)];
}

pub fn getScope(self: *Types, file: File) Id {
    if (self.file_scopes[@intFromEnum(file)] == .void) {
        self.file_scopes[@intFromEnum(file)] = self.resolveStruct(
            .void,
            file,
            self.getFile(file).path,
            .zeroSized(.Void),
            self.getFile(file).items,
            .{},
            &.{},
        );
    }

    return self.file_scopes[@intFromEnum(file)];
}

pub fn makePtr(self: *Types, v: Id) Id {
    var vl = v;
    const ptr = Id.init(.{ .Ptr = &vl });
    const slot = self.interner.getOrPut(self.arena.child_allocator, ptr) catch unreachable;
    if (slot.found_existing) return slot.key_ptr.*;
    const ptr_slot = self.arena.allocator().create(Id) catch unreachable;
    ptr_slot.* = v;
    slot.key_ptr.* = .init(.{ .Ptr = ptr_slot });
    return slot.key_ptr.*;
}

const Ctx = struct {
    scope: Id,
    name: []const u8 = &.{},

    pub fn init(fl: Id) Ctx {
        return .{ .scope = fl };
    }

    pub fn file(self: Ctx) File {
        return self.scope.file();
    }

    pub fn items(self: Ctx) File {
        return self.scope.items();
    }

    pub fn addName(self: Ctx, name: []const u8) Ctx {
        var v = self;
        v.name = name;
        return v;
    }

    pub fn stripName(self: Ctx) Ctx {
        var v = self;
        v.name = &.{};
        return v;
    }
};

pub fn intern(self: *Types, comptime kind: std.meta.Tag(Data), key: Key) struct { Map.GetOrPutResult, std.meta.TagPayload(Data, kind) } {
    var ty: std.meta.Child(std.meta.TagPayload(Data, kind)) = undefined;
    ty.key = key;
    const id = Id.init(@unionInit(Data, @tagName(kind), &ty));
    const slot = self.interner.getOrPut(self.arena.child_allocator, id) catch unreachable;
    if (slot.found_existing) {
        std.debug.assert(slot.key_ptr.data() == kind);
        return .{ slot, @field(slot.key_ptr.data(), @tagName(kind)) };
    }
    const alloc = self.arena.allocator().create(@TypeOf(ty)) catch unreachable;
    alloc.* = ty;
    slot.key_ptr.* = Id.init(@unionInit(Data, @tagName(kind), alloc));
    return .{ slot, alloc };
}

pub fn resolveStruct(
    self: *Types,
    scope: Id,
    file: File,
    name: []const u8,
    ast: Ast.Id,
    fields: Ast.Slice,
    capture_idents: Ast.Idents,
    captures: []const Id,
) Id {
    const slot, const alloc = self.intern(.Struct, .{
        .scope = scope,
        .file = file,
        .ast = ast,
        .capture_idents = capture_idents,
        .captures = captures,
    });
    if (!slot.found_existing) {
        alloc.* = .{
            .key = alloc.key,
            .ast_fields = fields,
            .name = name,
        };
    }
    return slot.key_ptr.*;
}

pub fn resolveGlobal(self: *Types, scope: Id, name: []const u8, ast: Ast.Id) Id {
    const slot, const alloc = self.intern(.Global, .{
        .scope = scope,
        .file = scope.file(),
        .ast = ast,
        .capture_idents = .{},
        .captures = &.{},
    });
    if (!slot.found_existing) {
        alloc.* = .{
            .key = alloc.key,
            .id = self.next_global,
            .name = name,
        };
        self.next_global += 1;
    }
    return slot.key_ptr.*;
}
