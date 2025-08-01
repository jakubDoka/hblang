const std = @import("std");
const root = @import("hb");
const graph = root.backend.graph;
const utils = root.utils;
const Types = root.frontend.Types;
const Id = Types.Id;
const tys = root.frontend.types;

const Abi = @This();

pub const ableos = Abi{ .cc = .ablecall };
pub const systemv = Abi{ .cc = .systemv };

cc: graph.CallConv,

pub const Builder = union(graph.CallConv) {
    refcall,
    systemv: struct {
        remining_scalar_regs: usize = 6,
        remining_xmm_regs: usize = 8,
    },
    ablecall,
    fastcall,
    @"inline",

    pub const max_elems = 2;

    pub inline fn slice(buf: *[]graph.AbiParam, comptime size: usize) if (size == 1)
        *graph.AbiParam
    else
        *[size]graph.AbiParam {
        defer buf.len = size;
        return if (size == 1) &buf.*[0] else buf.*[0..size];
    }

    pub fn types(self: *Builder, bufr: []graph.AbiParam, is_ret: bool, spec: Spec) []graph.AbiParam {
        var buf_tmp = bufr;
        const buf = &buf_tmp;
        switch (self.*) {
            .ablecall => switch (spec) {
                .Impossible => unreachable,
                .Imaginary => _ = slice(buf, 0),
                .ByValue => |d| slice(buf, 1).* = .{ .Reg = d },
                .ByValuePair => |pair| slice(buf, 2).* =
                    .{ .{ .Reg = pair.types[0] }, .{ .Reg = pair.types[1] } },
                .ByRef => slice(buf, 1).* = .{ .Reg = .i64 },
            },
            .systemv => |*s| switch (spec) {
                .Impossible => unreachable,
                .Imaginary => _ = slice(buf, 0),
                .ByValue => |d| {
                    if (is_ret) {
                        slice(buf, 1).* = .{ .Reg = d };
                    } else if ((d.isInt() and s.remining_scalar_regs == 0) or
                        s.remining_xmm_regs == 0)
                    {
                        slice(buf, 1).* = .{ .Stack = .reg(d) };
                    } else {
                        slice(buf, 1).* = .{ .Reg = d };
                        if (d.isInt()) {
                            s.remining_scalar_regs -= 1;
                        } else {
                            s.remining_xmm_regs -= 1;
                        }
                    }
                },
                .ByValuePair => |pair| {
                    if (is_ret) {
                        slice(buf, 1).* = .{ .Reg = .i64 };
                        s.remining_scalar_regs -= 1;
                    } else if (pair.types[0].isFloat() and pair.types[1].isFloat())
                        if (pair.types[0] == pair.types[1]) {
                            unreachable;
                        } else {
                            slice(buf, 1).* = .{ .Stack = pair.stackSpec() };
                        }
                    else if (pair.types[0].isInt() != pair.types[1].isInt() or
                        (pair.types[0].isInt() and s.remining_scalar_regs < 2) or
                        s.remining_xmm_regs < 2)
                    {
                        slice(buf, 1).* = .{ .Stack = pair.stackSpec() };
                    } else {
                        slice(buf, 2).* = .{ .{ .Reg = pair.types[0] }, .{ .Reg = pair.types[1] } };
                        if (pair.types[0].isInt()) {
                            s.remining_scalar_regs -= 2;
                        } else {
                            s.remining_xmm_regs -= 2;
                        }
                    }
                },
                .ByRef => |size| if (is_ret) {
                    s.remining_scalar_regs -= 1;
                    slice(buf, 1).* = .{ .Reg = .i64 };
                } else {
                    slice(buf, 1).* = .{ .Stack = size };
                },
            },
            else => unreachable,
        }

        return buf_tmp;
    }
};

pub const Pair = struct {
    types: [2]graph.DataType,
    padding: u16,
    alignment: u3,

    pub fn offsets(self: Pair) [2]u64 {
        return .{ 0, self.types[0].size() + self.padding };
    }

    pub fn size(self: Pair) u64 {
        return self.types[0].size() + self.padding + self.types[1].size();
    }

    pub fn stackSpec(self: Pair) graph.AbiParam.StackSpec {
        return .{
            .size = @intCast(self.size()),
            .alignment = self.alignment,
        };
    }
};

pub const TmpSpec = union(enum) {
    ByValue: graph.DataType,
    ByValuePair: Pair,
    ByRef,
    Imaginary,
    Impossible,

    pub fn toPerm(self: TmpSpec, ty: Id, types: *Types) Spec {
        return switch (self) {
            .ByRef => .{ .ByRef = ty.stackSpec(types) },
            inline else => |v, t| @unionInit(Spec, @tagName(t), v),
        };
    }
};

pub const Spec = union(enum) {
    ByValue: graph.DataType,
    ByValuePair: Pair,
    ByRef: graph.AbiParam.StackSpec,
    Imaginary,
    Impossible,

    const max_subtypes = 2;

    pub const Field = struct {
        offset: u64 = 0,
        dt: graph.DataType,
    };

    const Dts = std.BoundedArray(graph.DataType, max_subtypes);
    const Offs = std.BoundedArray(u64, max_subtypes);

    pub fn size(self: Spec) u64 {
        return switch (self) {
            .ByValue => |v| v.size(),
            .ByValuePair => |p| p.size(),
            .ByRef => |r| r.size,
            .Imaginary => 0,
            .Impossible => unreachable,
        };
    }
};

pub fn categorize(self: Abi, ty: Id, types: *Types) TmpSpec {
    return switch (self.cc) {
        .ablecall => switch (ty.data()) {
            .Builtin => |b| categorizeBuiltin(b),
            .Pointer, .FnPtr => .{ .ByValue = .i64 },
            .Enum => |enm| self.categorize(enm.getBackingInt(types), types),
            .Union => |s| categorizeAbleosUnion(s, types),
            .Slice => |s| categorizeAbleosSlice(s, types),
            .Nullable => |n| categorizeAbleosNullable(n, types),
            inline .Struct, .Tuple => |s| categorizeAbleosRecord(s, types),
            .Global, .Func, .Template => unreachable,
        },
        .systemv => switch (ty.data()) {
            inline .Struct, .Union => |s| {
                if (types.store.get(s).abi) |abi| return abi;
                const abi = categorizeSystemv(ty, types);
                types.store.get(s).abi = abi;
                return abi;
            },
            else => categorizeSystemv(ty, types),
        },
        else => unreachable,
    };
}

pub fn categorizeSystemv(ty: Id, types: *Types) TmpSpec {
    const max_vector_size = 512;
    const max_eight_bytes = max_vector_size / 64;

    const Category = enum {
        int,
        sse,
        sseup,

        const Category = @This();

        pub fn max(lhs: Category, rhs: Category) Category {
            return @enumFromInt(@max(@intFromEnum(lhs), @intFromEnum(rhs)));
        }

        const Error = error{ ByRef, Impossible };

        pub fn classify(t: Id, ts: *Types, offset: u64, catas: []?Category) Error!void {
            if (offset & (t.alignment(ts) - 1) != 0) return error.ByRef;

            var class: Category = switch (t.data()) {
                .Builtin => |b| switch (b) {
                    .any => unreachable,
                    .never => return error.Impossible,
                    .void => return,
                    .bool, .i8, .u8, .i16, .u16, .i32 => .int,
                    .u32, .i64, .u64, .int, .uint, .type => .int,
                    .f32, .f64 => .sse,
                },
                .Enum => |e| b: {
                    if (e.getFields(ts).len == 0) return error.Impossible;
                    if (e.getBackingInt(ts) == .void) return;
                    break :b .int;
                },
                .Pointer, .FnPtr => .int,
                .Union => |s| {
                    if (s.getFields(ts).len == 0) return error.Impossible;

                    var impossible = true;

                    for (s.getFields(ts)) |f| {
                        classify(f.ty, ts, offset, catas) catch |err| switch (err) {
                            error.ByRef => return err,
                            error.Impossible => continue,
                        };
                        impossible = false;
                    }
                    if (impossible) return error.Impossible;
                    return;
                },
                .Slice => |s| {
                    const slc = ts.store.get(s);
                    if (slc.len) |len| {
                        for (0..len) |i| {
                            try classify(slc.elem, ts, offset + i * slc.elem.size(ts), catas);
                        }
                    } else {
                        try classify(.uint, ts, offset + tys.Slice.len_offset, catas);
                        try classify(.uint, ts, offset + tys.Slice.ptr_offset, catas);
                    }
                    return;
                },
                .Nullable => |n| {
                    const nl = ts.store.get(n);
                    if (n.isCompact(ts)) {
                        classify(nl.inner, ts, offset, catas) catch |err| switch (err) {
                            error.ByRef => return err,
                            error.Impossible => return,
                        };
                    } else {
                        try classify(.u8, ts, offset, catas);
                        try classify(nl.inner, ts, offset + nl.inner.alignment(ts), catas);
                    }
                    return;
                },
                inline .Struct, .Tuple => |s| {
                    var iter = s.offsetIter(ts);
                    while (iter.next()) |elem| {
                        try classify(elem.field.ty, ts, offset + elem.offset, catas);
                    }
                    return;
                },
                .Global, .Func, .Template => unreachable,
            };

            const first = offset / 8;
            const last = (offset + t.size(ts) + 7) / 8;

            for (catas[@intCast(first)..@intCast(last)]) |*cat| {
                if (cat.*) |old| cat.* = old.max(class) else cat.* = class;

                if (class == .sse) {
                    class = .sseup;
                }
            }
        }

        pub fn regComponent(cls: []const ?Category, i: *usize, size: u64) ?graph.DataType {
            if (i.* >= cls.len) return null;

            switch (cls[i.*] orelse return null) {
                .int => {
                    i.* += 1;
                    return switch (size) {
                        1 => .i8,
                        2 => .i16,
                        3, 4 => .i32,
                        else => .i64,
                    };
                },
                .sse => {
                    var vec_len: usize = 1;
                    while (i.* + vec_len < cls.len and cls[i.* + vec_len] == .sseup) : (vec_len += 1) {}
                    i.* += vec_len;
                    return switch (vec_len) {
                        1 => switch (size) {
                            4 => .f32,
                            else => .f64,
                        },
                        else => graph.DataType.fromRaw(.{
                            .kind = .f64,
                            .one_less_then_lanes = @intCast(((size + 7) / 8) - 1),
                        }),
                    };
                },
                else => unreachable,
            }
        }
    };

    if (ty.size(types) * 8 > max_vector_size) {
        return .ByRef;
    }

    const eight_bytes = (ty.size(types) + 7) / 8;

    var categories_mem: [max_eight_bytes]?Category = @splat(null);
    const categories = categories_mem[0..@intCast(eight_bytes)];

    Category.classify(ty, types, 0, categories) catch |err| switch (err) {
        error.ByRef => return .ByRef,
        error.Impossible => return .Impossible,
    };

    // NOTE: we do this after classify sinc classify catches impossible
    if (eight_bytes == 0) {
        return .Imaginary;
    }

    if (eight_bytes > 2) {
        if (categories[0] != .sse) return .ByRef;
        for (categories[1..]) |cat| if (cat != .sseup) return .ByRef;
    } else {
        var i: usize = 0;
        while (i < categories.len) {
            if (categories[i] == .sseup) {
                categories[i] = .sse;
            } else if (categories[i] == .sse) {
                i += 1;
                while (i < categories.len and categories[i] == .sseup) {
                    i += 1;
                }
            } else {
                i += 1;
            }
        }
    }

    var i: usize = 0;
    const lo = Category.regComponent(categories, &i, ty.size(types)).?;
    if (i * 8 < ty.size(types)) {
        return .{ .ByValuePair = .{
            .types = .{ lo, Category.regComponent(categories, &i, ty.size(types) - i * 8).? },
            .padding = 0,
            .alignment = @intCast(std.math.log2_int(u64, ty.alignment(types))),
        } };
    }

    return .{ .ByValue = lo };
}

pub fn categorizeBuiltin(b: tys.Builtin) TmpSpec {
    return .{ .ByValue = switch (b) {
        .any => unreachable,
        .never => return .Impossible,
        .void => return .Imaginary,
        .u8, .i8, .bool => .i8,
        .u16, .i16 => .i16,
        .u32, .type, .i32 => .i32,
        .uint, .i64, .int, .u64 => .i64,
        .f32 => .f32,
        .f64 => .f64,
    } };
}

pub fn categorizeAbleosNullable(id: utils.EntId(tys.Nullable), types: *Types) TmpSpec {
    const nullable = types.store.get(id);
    const base_abi = Abi.ableos.categorize(nullable.inner, types);
    if (id.isCompact(types)) {
        if (base_abi == .Impossible) return .Imaginary;
        return base_abi;
    }
    return switch (base_abi) {
        .Impossible => .Imaginary,
        .Imaginary => .{ .ByValue = .i8 },
        .ByValue => |v| .{ .ByValuePair = .{
            .types = .{ .i8, v },
            .padding = @intCast(v.size() - 1),
            .alignment = @intCast(std.math.log2_int(u64, v.size())),
        } },
        .ByValuePair, .ByRef => .ByRef,
    };
}

pub fn categorizeAbleosSlice(id: utils.EntId(tys.Slice), types: *Types) TmpSpec {
    const slice = types.store.get(id);
    if (slice.len == null) return .{ .ByValuePair = .{
        .types = .{ .i64, .i64 },
        .padding = 0,
        .alignment = 3,
    } };
    if (slice.len == 0) return .Imaginary;
    const elem_abi = Abi.ableos.categorize(slice.elem, types);
    if (elem_abi == .Impossible) return .Impossible;
    if (elem_abi == .Imaginary) return .Imaginary;
    if (slice.len == 1) return elem_abi;
    if (slice.len == 2 and elem_abi == .ByValue) return .{ .ByValuePair = .{
        .types = .{elem_abi.ByValue} ** 2,
        .padding = 0,
        .alignment = @intCast(std.math.log2_int(u64, elem_abi.ByValue.size())),
    } };
    return .ByRef;
}

pub fn categorizeAbleosUnion(id: utils.EntId(tys.Union), types: *Types) TmpSpec {
    const fields = id.getFields(types);
    if (fields.len == 0) return .Impossible;
    const res = Abi.ableos.categorize(fields[0].ty, types);
    for (fields[1..]) |f| {
        const fspec = Abi.ableos.categorize(f.ty, types);
        if (fspec == .Impossible) continue;
        if (!std.meta.eql(res, fspec)) return .ByRef;
    }
    return res;
}

pub fn categorizeAbleosRecord(stru: anytype, types: *Types) TmpSpec {
    var res: TmpSpec = .Imaginary;
    var prev_offset: u64 = 0;
    var field_offsets = stru.offsetIter(types);
    while (field_offsets.next()) |elem| {
        defer prev_offset = elem.offset + elem.field.ty.size(types);
        const fspec = Abi.ableos.categorize(elem.field.ty, types);
        if (fspec == .Impossible) return .Impossible;
        if (fspec == .Imaginary) continue;
        if (fspec == .ByRef) return fspec;
        if (res == .Imaginary) {
            res = fspec;
            continue;
        }

        if (fspec == .ByValuePair) return .ByRef;
        if (res == .ByValuePair) return .ByRef;
        std.debug.assert(res != .ByRef);

        res = .{ .ByValuePair = .{
            .types = .{ res.ByValue, fspec.ByValue },
            .padding = @intCast(elem.offset - prev_offset),
            .alignment = @intCast(@min(4, std.math.log2_int(
                u64,
                @max(res.ByValue.size(), fspec.ByValue.size()),
            ))),
        } };
    }
    return res;
}

pub fn builder(self: Abi) Builder {
    return switch (self.cc) {
        .systemv => .{ .systemv = .{} },
        inline else => |t| @unionInit(Builder, @tagName(t), {}),
    };
}

pub fn isByRefRet(self: Abi, spec: Spec) bool {
    return switch (self.cc) {
        .ablecall => switch (spec) {
            .ByRef => true,
            else => false,
        },
        .systemv => switch (spec) {
            .ByRef, .ByValuePair => true,
            else => false,
        },
        else => unreachable,
    };
}
