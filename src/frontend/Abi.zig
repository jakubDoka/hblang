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

    pub fn types(self: *Builder, buf: ?[]graph.AbiParam, is_ret: bool, spec: Spec) void {
        switch (self.*) {
            .ablecall => switch (spec) {
                .Impossible => unreachable,
                .Imaginary => {},
                .ByValue => |d| buf.?[0] = .{ .Reg = d },
                .ByValuePair => |pair| buf.?[0..2].* =
                    .{ .{ .Reg = pair.types[0] }, .{ .Reg = pair.types[1] } },
                .ByRef => buf.?[0] = .{ .Reg = .i64 },
            },
            .systemv => |*s| switch (spec) {
                .Impossible => unreachable,
                .Imaginary => {},
                .ByValue => |d| {
                    if (is_ret) {
                        buf.?[0] = .{ .Reg = d };
                    } else if (s.remining_scalar_regs == 0) {
                        buf.?[0] = .{ .Stack = .reg(d) };
                    } else {
                        buf.?[0] = .{ .Reg = d };
                        s.remining_scalar_regs -= 1;
                    }
                },
                .ByValuePair => |pair| {
                    if (is_ret) {
                        buf.?[0] = .{ .Reg = .i64 };
                        s.remining_scalar_regs -= 1;
                    } else if (s.remining_scalar_regs < 2) {
                        buf.?[0] = .{ .Stack = pair.stackSpec() };
                    } else {
                        buf.?[0..2].* = .{ .{ .Reg = pair.types[0] }, .{ .Reg = pair.types[1] } };
                        s.remining_scalar_regs -= 2;
                    }
                },
                .ByRef => |size| if (is_ret) {
                    s.remining_scalar_regs -= 1;
                    buf.?[0] = .{ .Reg = .i64 };
                } else {
                    buf.?[0] = .{ .Stack = size };
                },
            },
            else => unreachable,
        }
    }

    pub fn len(self: Builder, is_ret: bool, spec: Spec) ?usize {
        return switch (self) {
            .ablecall => switch (spec) {
                .Impossible => null,
                .Imaginary => 0,
                .ByValue => 1,
                .ByValuePair => 2,
                .ByRef => if (is_ret) 0 else 1,
            },
            .systemv => |s| switch (spec) {
                .Impossible => null,
                .Imaginary => 0,
                .ByValue => 1,
                .ByValuePair => if (is_ret)
                    0
                else if (s.remining_scalar_regs >= 2)
                    2
                else
                    1,
                .ByRef => if (is_ret) 0 else 1,
            },
            else => unreachable,
        };
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
};

pub fn categorize(self: Abi, ty: Id, types: *Types) TmpSpec {
    return switch (ty.data()) {
        .Builtin => |b| .{ .ByValue = switch (b) {
            .any => unreachable,
            .never => return .Impossible,
            .void => return .Imaginary,
            .u8, .i8, .bool => .i8,
            .u16, .i16 => .i16,
            .u32, .type, .i32 => .i32,
            .uint, .i64, .int, .u64 => .i64,
            .f32 => .f32,
            .f64 => .f64,
        } },
        .Pointer => .{ .ByValue = .i64 },
        .Enum => |enm| .{ .ByValue = switch (@as(u64, enm.getFields(types).len)) {
            0 => return .Impossible,
            1 => return .Imaginary,
            2...255 => .i8,
            256...std.math.maxInt(u16) => .i16,
            std.math.maxInt(u16) + 1...std.math.maxInt(u32) => .i32,
            std.math.maxInt(u32) + 1...std.math.maxInt(u64) => .i64,
        } },
        .Union => |s| switch (self.cc) {
            .ablecall, .systemv => categorizeAbleosUnion(s, types),
            else => unreachable,
        },
        inline .Struct, .Tuple => |s| switch (self.cc) {
            .ablecall, .systemv => categorizeAbleosRecord(s, types),
            else => unreachable,
        },
        .Slice => |s| switch (self.cc) {
            .ablecall, .systemv => categorizeAbleosSlice(s, types),
            else => unreachable,
        },
        .Nullable => |n| switch (self.cc) {
            .ablecall, .systemv => categorizeAbleosNullable(n, types),
            else => unreachable,
        },
        .Global, .Func, .Template => unreachable,
    };
}

pub fn categorizeAbleosNullable(id: utils.EntId(tys.Nullable), types: *Types) TmpSpec {
    const nullable = types.store.get(id);
    const base_abi = Abi.ableos.categorize(nullable.inner, types);
    if (id.isCompact(types)) return base_abi;
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
    if (fields.len == 0) return .Impossible; // TODO: add .Impossible
    const res = Abi.ableos.categorize(fields[0].ty, types);
    for (fields[1..]) |f| {
        const fspec = Abi.ableos.categorize(f.ty, types);
        if (fspec == .Impossible) continue;
        if (!std.meta.eql(res, fspec)) return .ByRef;
    }
    return res;
}

pub fn checkCycles(stru: anytype, types: *Types) bool {
    if (@TypeOf(stru) == tys.Struct.Id or @TypeOf(stru) == tys.Union.Id) {
        const self = types.store.get(stru);
        if (self.recursion_lock) {
            types.report(self.key.file, self.key.ast, "the struct has undecidable alignment (cycle)", .{});
            return true;
        }
        self.recursion_lock = true;
    }
    return false;
}

pub fn categorizeAbleosRecord(stru: anytype, types: *Types) TmpSpec {
    if (checkCycles(stru, types)) return .Imaginary;
    defer if (@TypeOf(stru) == tys.Struct.Id) {
        types.store.get(stru).recursion_lock = false;
    };

    var res: TmpSpec = .Imaginary;
    var offset: u64 = 0;
    for (stru.getFields(types)) |f| {
        const fspec = Abi.ableos.categorize(f.ty, types);
        if (fspec == .Impossible) return .Impossible;
        if (fspec == .Imaginary) continue;
        if (fspec == .ByRef) return fspec;
        if (res == .Imaginary) {
            res = fspec;
            offset += f.ty.size(types);
            continue;
        }

        if (fspec == .ByValuePair) return .ByRef;
        if (res == .ByValuePair) return .ByRef;
        std.debug.assert(res != .ByRef);

        const off = std.mem.alignForward(u64, offset, f.ty.alignment(types));
        res = .{ .ByValuePair = .{
            .types = .{ res.ByValue, fspec.ByValue },
            .padding = @intCast(off - offset),
            .alignment = @intCast(@min(4, std.math.log2_int(
                u64,
                @max(res.ByValue.size(), fspec.ByValue.size()),
            ))),
        } };

        offset = off + f.ty.size(types);
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
