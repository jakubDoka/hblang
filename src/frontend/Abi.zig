const std = @import("std");
const root = @import("hb");
const graph = root.backend.graph;
const utils = root.utils;
const Types = root.frontend.Types;
const Id = Types.Id;

const Abi = @This();

pub const ableos = Abi{ .cc = .ablecall };
pub const systemv = Abi{ .cc = .systemv };
pub const wasm = Abi{ .cc = .wasmcall };

cc: graph.CallConv,

pub const Spec = ?[]graph.AbiParam;
pub const max_elems = 2;

pub const Buf = struct {
    slots: [max_elems]graph.AbiParam = undefined,
    len: usize = 0,

    pub fn push(self: *Buf, params: graph.AbiParam) void {
        self.slots[self.len] = params;
        self.len += 1;
    }

    pub fn spilled(self: *Buf, spec: graph.AbiParam.StackSpec) void {
        self.slots[0] = .{ .Stack = spec };
        self.len = 1;
    }
};

pub fn isRetByRef(abi: Abi, self: Spec) bool {
    const pr = self orelse return false;
    return switch (abi.cc) {
        .systemv => pr.len > 1 or (pr.len != 0 and pr[0] != .Reg),
        .ablecall, .wasmcall => pr[0] != .Reg,
        .@"inline" => unreachable,
    };
}

pub fn isMultivalue(_: Abi, self: Spec) bool {
    const pr = self orelse return false;
    return pr.len == 2 or (pr.len == 1 and pr[0] == .Stack);
}

pub fn tryCategorizeReg(self: Abi, ty: Id, types: *Types) ?graph.DataType {
    var buf = Buf{};
    const params = categorize(self, ty, types, &buf) orelse unreachable;
    if (params.len != 1) {
        std.debug.assert(params.len == 0);
        return null;
    }
    return params[0].Reg;
}

pub fn categorizeAssumeReg(self: Abi, ty: Id, types: *Types) graph.DataType {
    return tryCategorizeReg(self, ty, types).?;
}

pub fn categorize(self: Abi, ty: Id, types: *Types, buf: *Buf) ?[]graph.AbiParam {
    switch (self.cc) {
        .ablecall, .wasmcall, .systemv => switch (ty.data()) {
            else => {
                // NOTE: well, maybe we can improve some stuff, but eh
                categorizeSystemv(ty, buf, types) catch |err| switch (err) {
                    error.ByRef => buf.spilled(ty.stackSpec(types)),
                    error.Impossible => return null,
                };
            },
        },
        else => unreachable,
    }

    return buf.slots[0..buf.len];
}

pub const Category = union(enum) {
    Impossible,
    Imaginary,
    Scalar: graph.DataType,
    Stack,

    pub fn fromSpec(spec: ?[]graph.AbiParam) Category {
        if (spec) |s| return switch (s.len) {
            0 => .Imaginary,
            1 => if (s[0] == .Reg) .{ .Scalar = s[0].Reg } else .Stack,
            2 => .Stack,
            else => unreachable,
        };

        return .Impossible;
    }
};

pub fn categorizeBuiltinUnwrapped(b: Types.Builtin) graph.DataType {
    return (categorizeBuiltin(b) catch unreachable).?;
}

pub fn categorizeBuiltin(b: Types.Builtin) !?graph.DataType {
    return switch (b) {
        .any => unreachable,
        .never => return error.Impossible,
        .void => return null,
        .u8, .i8, .bool => .i8,
        .u16, .i16 => .i16,
        .u32, .type, .template, .i32 => .i32,
        .uint, .i64, .int, .u64 => .i64,
        .f32 => .f32,
        .f64 => .f64,
    };
}

pub fn categorizeSystemv(ty: Id, bufr: *Buf, types: *Types) !void {
    std.debug.assert(bufr.len == 0);

    const max_vector_size = 512;
    const max_eight_bytes = max_vector_size / 64;

    const Cata = enum {
        int,
        sse,
        sseup,

        const Cata = @This();

        pub fn max(lhs: Cata, rhs: Cata) Cata {
            return @enumFromInt(@max(@intFromEnum(lhs), @intFromEnum(rhs)));
        }

        const Error = error{ ByRef, Impossible };

        pub fn classify(t: Id, ts: *Types, offset: u64, catas: []?Cata) Error!void {
            if (offset & (t.alignment(ts) - 1) != 0) return error.ByRef;

            var class: Cata = switch (t.data()) {
                .Builtin => |b| switch (b) {
                    .any => unreachable,
                    .never => return error.Impossible,
                    .void => return,
                    .bool, .i8, .u8, .i16, .u16, .i32 => .int,
                    .u32, .i64, .u64, .int, .uint, .type, .template => .int,
                    .f32, .f64 => .sse,
                },
                .FuncTy => .int,
                .Pointer => .int,
                .Enum => |e| if (e.get(ts).decls.fields.len == 0)
                    return error.Impossible
                else
                    .int,
                .Option => |o| {
                    classify(o.get(ts).inner, ts, offset, catas) catch |err| switch (err) {
                        error.Impossible => return,
                        else => |e| return e,
                    };
                    const layout = o.get(ts).getLayout(ts);
                    if (!layout.compact) {
                        try classify(
                            layout.inner.storage.ty(),
                            ts,
                            offset + layout.inner.offset,
                            catas,
                        );
                    }

                    return;
                },
                .Slice => {
                    try classify(.uint, ts, offset + 0, catas);
                    try classify(.uint, ts, offset + 8, catas);
                    return;
                },
                .Struct => |s| {
                    for (s.get(ts).getLayout(ts).fields) |f| {
                        try classify(f.ty, ts, offset + f.offset, catas);
                    }
                    return;
                },
                .Union => |u| {
                    if (u.get(ts).decls.fields.len == 0) return error.Impossible;

                    const layout = u.get(ts).getLayout(ts);

                    var impossible = true;

                    for (layout.fields) |f| {
                        classify(f, ts, offset, catas) catch |err| switch (err) {
                            error.ByRef => return err,
                            error.Impossible => continue,
                        };
                        impossible = false;
                    }

                    if (layout.tagLayout()) |tl| {
                        try classify(.nany(tl.id), ts, offset + tl.offset, catas);
                    }

                    if (impossible) return error.Impossible;
                    return;
                },
                .Array => |a| {
                    for (0..@intCast(a.get(ts).len.s)) |i| {
                        try classify(a.get(ts).elem, ts, offset + a.get(ts).elem.size(ts) * i, catas);
                    }
                    return;
                },
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

        pub fn regComp(
            cls: []const ?Cata,
            i: *usize,
            size: u64,
        ) graph.DataType {
            if (i.* >= cls.len) unreachable;

            switch (cls[i.*].?) {
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
                    while (i.* + vec_len < cls.len and
                        cls[i.* + vec_len] == .sseup) : (vec_len += 1)
                    {}
                    i.* += vec_len;
                    return switch (vec_len) {
                        1 => switch (size) {
                            4 => .f32,
                            else => .f64,
                        },
                        2 => .v128,
                        3, 4 => .v254,
                        5, 6, 7, 8 => .v512,
                        else => unreachable,
                    };
                },
                else => unreachable,
            }
        }
    };

    if (ty.size(types) * 8 > max_vector_size) {
        return error.ByRef;
    }

    const eight_bytes = (ty.size(types) + 7) / 8;

    var categories_mem: [max_eight_bytes]?Cata = @splat(null);
    const categories = categories_mem[0..@intCast(eight_bytes)];

    try Cata.classify(ty, types, 0, categories);

    // NOTE: we do this after classify sinc classify catches impossible
    if (eight_bytes == 0) {
        return;
    }

    if (eight_bytes > 2) {
        if (categories[0] != .sse) return error.ByRef;
        for (categories[1..]) |cat| if (cat != .sseup) return error.ByRef;
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
    bufr.push(.{ .Reg = Cata.regComp(categories, &i, ty.size(types)) });
    if (i * 8 < ty.size(types)) {
        bufr.push(.{ .Reg = Cata.regComp(categories, &i, ty.size(types)) });
    }
}
