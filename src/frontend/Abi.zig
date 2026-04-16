const std = @import("std");
const root = @import("hbf");
const graph = root.backend.graph;
const utils = root.utils;
const Types = root.Types;
const Id = Types.Id;

const Abi = @This();

cc: graph.CallConv,
spec: root.backend.Machine.TargetSpec,

pub const Spec = ?[]const graph.AbiParam;
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
        .systemv, .syscall => pr.len > 1 or (pr.len != 0 and pr[0] != .Reg),
        .ablecall, .wasmcall => pr.len == 1 and pr[0] != .Reg,
        .@"inline" => unreachable,
    };
}

pub fn isMultivalue(_: Abi, self: Spec) bool {
    const pr = self orelse return false;
    return pr.len == 2 or (pr.len == 1 and pr[0] == .Stack);
}

pub fn tryCategorizeReg(self: Abi, ty: Id, types: *Types) ?graph.DataType {
    var buf = Buf{};
    const params = categorize(self, ty, types, &buf) orelse return null;
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
        .ablecall, .wasmcall, .systemv, .syscall => switch (ty.data()) {
            else => {
                // NOTE: well, maybe we can improve some stuff, but eh
                categorizeSystemv(ty, buf, types, self.cc) catch |err| switch (err) {
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

pub fn categorizeBuiltin(b: Types.Builtin) !?graph.DataType {
    return .fromTag((try categorizeBuiltinTag(b)) orelse return null);
}

pub fn categorizeBuiltinUnwrappedTag(b: Types.Builtin) graph.DataType.Tag {
    return (categorizeBuiltinTag(b) catch unreachable).?;
}

pub fn categorizeBuiltinUnwrapped(b: Types.Builtin) graph.DataType {
    return .fromTag(categorizeBuiltinUnwrappedTag(b));
}

pub fn categorizeBuiltinTag(b: Types.Builtin) !?graph.DataType.Tag {
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

pub fn categorizeSystemv(ty: Id, bufr: *Buf, types: *Types, cc: graph.CallConv) !void {
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

        const Ctx = struct {
            ts: *Types,
            f32_count: usize = 0,
            last_simd: graph.DataType.Tag = .bot,
            catas: []?Cata,
        };

        pub fn classify(t: Id, offset: u64, ctx: *Ctx) Error!void {
            if (offset & (t.alignment(ctx.ts) - 1) != 0) return error.ByRef;

            if (t == .f32) {
                ctx.f32_count += 1;
            }

            if (t.data() == .Simd) ctx.last_simd = categorizeBuiltinUnwrappedTag(t.data().Simd.lane);

            var class: Cata = switch (t.data()) {
                .Builtin => |b| switch (b) {
                    .any => unreachable,
                    .never => return error.Impossible,
                    .void => return,
                    .bool, .i8, .u8, .i16, .u16, .i32 => .int,
                    .u32, .i64, .u64, .int, .uint, .type, .template => .int,
                    .f32, .f64 => .sse,
                },
                .Simd => |s| if (s.laneCount(ctx.ts) == 1) {
                    try classify(.nany(s.lane), offset, ctx);
                    return;
                } else .sse,
                .FuncTy => .int,
                .Pointer => .int,
                .Enum => |e| if (e.get(ctx.ts).decls.fieldCount() == 0)
                    return error.Impossible
                else
                    .int,
                .Option => |o| {
                    classify(o.get(ctx.ts).inner, offset, ctx) catch |err| switch (err) {
                        error.Impossible => return,
                        else => |e| return e,
                    };
                    const layout = o.get(ctx.ts).getLayout(ctx.ts);
                    if (!layout.compact) {
                        try classify(
                            layout.inner.storage.ty(),

                            offset + layout.inner.offset,
                            ctx,
                        );
                    }

                    return;
                },
                .Slice => {
                    try classify(.uint, offset + 0, ctx);
                    try classify(.uint, offset + 8, ctx);
                    return;
                },
                .Struct => |s| {
                    for (s.get(ctx.ts).getLayout(ctx.ts).fields) |f| {
                        try classify(f.ty, offset + f.offset, ctx);
                    }
                    return;
                },
                .Union => |u| {
                    if (u.get(ctx.ts).decls.fieldCount() == 0) return error.Impossible;

                    const layout = u.get(ctx.ts).getLayout(ctx.ts);

                    var impossible = true;

                    for (layout.fields) |f| {
                        classify(f, offset, ctx) catch |err| switch (err) {
                            error.ByRef => return err,
                            error.Impossible => continue,
                        };
                        impossible = false;
                    }

                    if (layout.tagLayout()) |tl| {
                        try classify(.nany(tl.id), offset + tl.offset, ctx);
                    }

                    if (impossible) return error.Impossible;
                    return;
                },
                .Array => |a| {
                    for (0..@intCast(a.get(ctx.ts).len.s)) |i| {
                        try classify(
                            a.get(ctx.ts).elem,

                            offset + a.get(ctx.ts).elem.size(ctx.ts) * i,
                            ctx,
                        );
                    }
                    return;
                },
            };

            const first = offset / 8;
            const last = (offset + t.size(ctx.ts) + 7) / 8;

            for (ctx.catas[@intCast(first)..@intCast(last)]) |*cat| {
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
            last_simd: graph.DataType.Tag,
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
                        2 => .vec(last_simd, .v128),
                        4 => .vec(last_simd, .v256),
                        8 => .vec(last_simd, .v512),
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

    var ctx = Cata.Ctx{ .ts = types, .catas = categories };
    try Cata.classify(ty, 0, &ctx);

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
    bufr.push(.{ .Reg = Cata.regComp(categories, &i, ty.size(types), ctx.last_simd) });
    if (i * 8 < ty.size(types)) {
        bufr.push(.{ .Reg = Cata.regComp(categories, &i, ty.size(types) - i * 8, ctx.last_simd) });
    }

    if (cc == .wasmcall or cc == .ablecall) {
        if (ctx.f32_count > 2 or (ctx.f32_count != 0 and bufr.len != 1)) return error.ByRef;

        if (ctx.f32_count == 2) {
            std.debug.assert(bufr.len == 1);

            bufr.len = 2;
            @memset(&bufr.slots, .{ .Reg = .f32 });
        }
    }
}
