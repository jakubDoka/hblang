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

pub const Pair = struct {
    types: [2]graph.DataType,
    padding: u16,

    pub fn offsets(self: @This()) [2]u64 {
        return .{ 0, self.types[0].size() + self.padding };
    }
};

pub const TmpSpec = union(enum) {
    ByValue: graph.DataType,
    ByValuePair: Pair,
    ByRef,
    Imaginary,

    pub fn toPerm(self: TmpSpec, ty: Id, types: *Types) Spec {
        return switch (self) {
            .ByRef => .{ .ByRef = ty.size(types) },
            inline else => |v, t| @unionInit(Spec, @tagName(t), v),
        };
    }
};

pub const Spec = union(enum) {
    ByValue: graph.DataType,
    ByValuePair: Pair,
    ByRef: u64,
    Imaginary,

    const max_subtypes = 2;

    pub const Field = struct {
        offset: u64 = 0,
        dt: graph.DataType,
    };

    const Dts = std.BoundedArray(graph.DataType, max_subtypes);
    const Offs = std.BoundedArray(u64, max_subtypes);

    pub fn types(self: Spec, buf: []graph.AbiParam, is_ret: bool, abi: Abi) void {
        switch (abi.cc) {
            .ablecall => switch (self) {
                .Imaginary => {},
                .ByValue => |d| buf[0] = .{ .Reg = d },
                .ByValuePair => |pair| buf[0..2].* =
                    .{ .{ .Reg = pair.types[0] }, .{ .Reg = pair.types[1] } },
                .ByRef => buf[0] = .{ .Reg = .i64 },
            },
            .systemv => switch (self) {
                .Imaginary => {},
                .ByValue => |d| buf[0] = .{ .Reg = d },
                .ByValuePair => |pair| if (is_ret and self.isByRefRet(abi)) {
                    buf[0] = .{ .Reg = .i64 };
                } else {
                    buf[0..2].* = .{ .{ .Reg = pair.types[0] }, .{ .Reg = pair.types[1] } };
                },
                .ByRef => |_| buf[0] = .{ .Reg = .i64 },
            },
            else => unreachable,
        }
    }

    pub fn isByRefRet(self: Spec, abi: Abi) bool {
        return switch (abi.cc) {
            .ablecall => switch (self) {
                .ByRef => true,
                else => false,
            },
            .systemv => switch (self) {
                .Imaginary, .ByValue => false,
                else => true,
            },
            else => unreachable,
        };
    }

    pub fn len(self: Spec, is_ret: bool, abi: Abi) usize {
        return switch (abi.cc) {
            .ablecall => switch (self) {
                .Imaginary => 0,
                .ByValue => 1,
                .ByValuePair => 2,
                .ByRef => if (is_ret) 0 else 1,
            },
            .systemv => switch (self) {
                .Imaginary => 0,
                .ByValue => 1,
                .ByValuePair => if (is_ret) 0 else 2,
                .ByRef => if (is_ret) 0 else 1,
            },
            else => unreachable,
        };
    }
};

pub fn categorize(self: Abi, ty: Id, types: *Types) ?TmpSpec {
    return switch (ty.data()) {
        .Builtin => |b| .{ .ByValue = switch (b) {
            .never, .any => return null,
            .void => return .Imaginary,
            .u8, .i8, .bool => .i8,
            .u16, .i16 => .i16,
            .u32, .type, .i32 => .i32,
            .uint, .i64, .int, .u64 => .i64,
            .f32 => .f32,
            .f64 => .f64,
        } },
        .Pointer => .{ .ByValue = .i64 },
        .Enum => .{ .ByValue = switch (ty.size(types)) {
            0 => return .Imaginary,
            1 => .i8,
            2 => .i16,
            4 => .i32,
            8 => .i64,
            else => unreachable,
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

pub fn categorizeAbleosNullable(id: utils.EntId(tys.Nullable), types: *Types) ?TmpSpec {
    const nullable = types.store.get(id);
    const base_abi = Abi.ableos.categorize(nullable.inner, types) orelse return null;
    if (id.isCompact(types)) return base_abi;
    if (base_abi == .Imaginary) return .{ .ByValue = .i8 };
    if (base_abi == .ByValue) return .{ .ByValuePair = .{
        .types = .{ .i8, base_abi.ByValue },
        .padding = @intCast(base_abi.ByValue.size() - 1),
    } };
    return .ByRef;
}

pub fn categorizeAbleosSlice(id: utils.EntId(tys.Slice), types: *Types) ?TmpSpec {
    const slice = types.store.get(id);
    if (slice.len == null) return .{ .ByValuePair = .{ .types = .{ .i64, .i64 }, .padding = 0 } };
    if (slice.len == 0) return .Imaginary;
    const elem_abi = Abi.ableos.categorize(slice.elem, types) orelse return null;
    if (elem_abi == .Imaginary) return .Imaginary;
    if (slice.len == 1) return elem_abi;
    if (slice.len == 2 and elem_abi == .ByValue) return .{ .ByValuePair = .{ .types = .{elem_abi.ByValue} ** 2, .padding = 0 } };
    return .ByRef;
}

pub fn categorizeAbleosUnion(id: utils.EntId(tys.Union), types: *Types) ?TmpSpec {
    const fields = id.getFields(types);
    if (fields.len == 0) return .Imaginary; // TODO: add .Impossible
    const res = Abi.ableos.categorize(fields[0].ty, types) orelse return null;
    for (fields[1..]) |f| {
        const fspec = Abi.ableos.categorize(f.ty, types) orelse continue;
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
        const fspec = Abi.ableos.categorize(f.ty, types) orelse continue;
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
        } };

        offset = off + f.ty.size(types);
    }
    return res;
}
