const std = @import("std");

test {
    _ = @import("zig-out/tests.zig");
    _ = @import("zig-out/vendored_tests.zig");
}

pub fn runTest(name: []const u8, code: []const u8) !void {
    const Parser = @import("parser.zig");
    var ast = try Parser.init(name, code, std.testing.allocator);
    defer ast.deinit(std.testing.allocator);
}

pub fn runVendoredTest(path: []const u8) !void {
    _ = path; // autofix
}

const debug = @import("builtin").mode == .Debug;

const IdRepr = u32;

pub fn EnumId(comptime Tag: type) type {
    return packed struct(IdRepr) {
        taga: std.meta.Tag(Tag),
        index: std.meta.Int(.unsigned, @bitSizeOf(IdRepr) - @bitSizeOf(Tag)),

        pub fn compact(taga: Tag, index: usize) @This() {
            return .{ .taga = @intFromEnum(taga), .index = @intCast(index) };
        }

        pub fn zeroSized(taga: Tag) @This() {
            return .{ .taga = @intFromEnum(taga), .index = 0 };
        }

        pub fn tag(self: @This()) Tag {
            return @enumFromInt(self.taga);
        }
    };
}

pub fn EnumSlice(comptime T: type) type {
    return struct {
        start: u32 = 0,
        end: u32 = 0,

        const Elem = T;

        pub fn isEmpty(self: @This()) bool {
            return self.start == self.end;
        }

        pub fn len(self: @This()) usize {
            return (self.end - self.start) / @sizeOf(Elem);
        }
    };
}

pub fn EnumStore(comptime SelfId: type, comptime T: type) type {
    return struct {
        const Self = @This();
        const payload_align = b: {
            var max_align: u29 = 1;
            for (std.meta.fields(T)) |field| {
                max_align = @max(max_align, @alignOf(field.type));
            }
            break :b max_align;
        };

        store: std.ArrayListAlignedUnmanaged(u8, payload_align) = .{},

        pub fn allocDyn(self: *Self, gpa: std.mem.Allocator, value: T) !SelfId {
            return switch (value) {
                inline else => |v, t| try self.alloc(gpa, t, v),
            };
        }

        pub fn alloc(
            self: *Self,
            gpa: std.mem.Allocator,
            comptime tag: std.meta.Tag(T),
            value: std.meta.TagPayload(T, tag),
        ) !SelfId {
            const Value = @TypeOf(value);
            (try self.allocLow(gpa, Value, 1))[0] = value;
            return SelfId{
                .taga = @intFromEnum(tag),
                .index = @intCast(self.store.items.len - @sizeOf(Value)),
            };
        }

        pub fn allocSlice(
            self: *Self,
            comptime E: type,
            gpa: std.mem.Allocator,
            slice: []const E,
        ) !EnumSlice(E) {
            std.mem.copyForwards(E, try self.allocLow(gpa, E, slice.len), slice);
            return .{
                .start = @intCast(self.store.items.len - @sizeOf(E) * slice.len),
                .end = @intCast(self.store.items.len),
            };
        }

        fn allocLow(self: *Self, gpa: std.mem.Allocator, comptime E: type, count: usize) ![]E {
            const alignment: usize = @alignOf(E);
            const padded_len = alignTo(self.store.items.len, alignment);
            const required_space = padded_len + @sizeOf(E) * count;
            try self.store.resize(gpa, required_space);
            const dest: [*]E = @ptrCast(@alignCast(self.store.items.ptr[padded_len..]));
            return dest[0..count];
        }

        pub fn get(self: *const Self, id: SelfId) T {
            switch (@as(std.meta.Tag(T), @enumFromInt(id.taga))) {
                inline else => |t| {
                    const Value = std.meta.TagPayload(T, t);
                    const loc: *const Value = if (Value != void) @ptrCast(@alignCast(&self.store.items[id.index])) else &{};
                    return @unionInit(T, @tagName(t), loc.*);
                },
            }
        }

        pub fn getTyped(
            self: *const Self,
            comptime tag: std.meta.Tag(T),
            id: SelfId,
        ) ?std.meta.TagPayload(T, tag) {
            if (tag != id.tag()) return null;
            const Value = std.meta.TagPayload(T, tag);
            const loc: *Value = @ptrCast(@alignCast(&self.store.items[id.index]));
            return loc.*;
        }

        pub fn getTypedPtr(
            self: *Self,
            comptime tag: std.meta.Tag(T),
            id: SelfId,
        ) ?*std.meta.TagPayload(T, tag) {
            if (tag != id.tag()) return null;
            const Value = std.meta.TagPayload(T, tag);
            const loc: *Value = @ptrCast(@alignCast(&self.store.items[id.index]));
            return loc;
        }

        pub fn view(self: *const Self, slice: anytype) []@TypeOf(slice).Elem {
            const slc = self.store.items[slice.start..slice.end];
            const len = slc.len / @sizeOf(@TypeOf(slice).Elem);
            const ptr: [*]@TypeOf(slice).Elem = @ptrCast(@alignCast(slc.ptr));
            return ptr[0..len];
        }

        pub fn deinit(self: *Self, gpa: std.mem.Allocator) void {
            self.store.deinit(gpa);
        }
    };
}

pub fn dbg(value: anytype) @TypeOf(value) {
    std.debug.print("{any}\n", .{value});
    return value;
}

pub const StaticTrace = struct {
    index: if (debug) usize else void,
    frames: if (debug) [frame_limit]usize else void,

    const frame_limit = 10;

    pub fn init(return_addr: usize) StaticTrace {
        if (!debug) return undefined;
        var trace: StaticTrace = undefined;
        var stack_trace = std.builtin.StackTrace{
            .index = undefined,
            .instruction_addresses = &trace.frames,
        };
        std.debug.captureStackTrace(return_addr, &stack_trace);
        trace.index = stack_trace.index;
        return trace;
    }

    pub fn dump(self: *StaticTrace) void {
        if (!debug) return;
        std.debug.dumpStackTrace(.{
            .index = self.index,
            .instruction_addresses = &self.frames,
        });
    }
};

pub fn isErr(value: anytype) bool {
    value catch return true;
    return false;
}

pub inline fn alignTo(offset: anytype, alignment: @TypeOf(offset)) @TypeOf(offset) {
    return (offset + alignment - 1) & ~(alignment - 1);
}

pub fn findReadmeSnippet(comptime name: []const u8) ![]const u8 {
    var readme: []const u8 = @embedFile("README.md");
    const headingPat = "#### " ++ name ++ "\n```hb";
    const index = std.mem.indexOf(u8, readme, headingPat) orelse return error.NoStart;
    readme = readme[index + headingPat.len ..];
    const endPat = "```";
    const code = readme[0 .. std.mem.indexOf(u8, readme, endPat) orelse return error.NoEnd];
    readme = readme[code.len + endPat.len ..];
    return code;
}

pub fn TaggedIndex(comptime R: type, comptime T: type) type {
    return packed struct(R) {
        tag_bits: std.meta.Tag(T),
        index: std.meta.Int(.unsigned, @bitSizeOf(R) - @bitSizeOf(T)),

        pub const Tag = T;
        pub const Repr = R;

        pub fn init(tag_bits: T, index: usize) @This() {
            return .{ .tag_bits = @intFromEnum(tag_bits), .index = @intCast(index) };
        }

        pub fn tag(self: @This()) T {
            return @enumFromInt(self.tag_bits);
        }
    };
}

pub fn toTuple(ty: anytype) TupleOf(@TypeOf(ty)) {
    var res: TupleOf(@TypeOf(ty)) = undefined;
    inline for (std.meta.fields(@TypeOf(ty)), 0..) |field, i| res[i] = @field(ty, field.name);
    return res;
}

pub fn TupleOf(comptime T: type) type {
    const fields = std.meta.fields(T);
    var types: [fields.len]std.builtin.Type.StructField = undefined;
    for (fields, &types, 0..) |field, *ty, i| ty.* = .{
        .name = &[1:0]u8{'0' + i},
        .type = field.type,
        .default_value = null,
        .alignment = @alignOf(field.type),
        .is_comptime = false,
    };
    return @Type(.{ .Struct = .{
        .fields = &types,
        .decls = &.{},
        .is_tuple = true,
        .layout = .auto,
    } });
}
