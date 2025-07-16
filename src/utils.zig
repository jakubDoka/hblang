const std = @import("std");

pub const freestanding = @import("builtin").target.os.tag == .freestanding;

pub fn ensureSlot(self: anytype, gpa: std.mem.Allocator, id: usize) !*std.meta.Child(@TypeOf(self.items)) {
    if (self.items.len <= id) {
        const prev_len = self.items.len;
        try self.resize(gpa, id + 1);
        @memset(self.items[prev_len..], .invalid);
    }
    return &self.items[id];
}

pub fn getStdErr() std.io.AnyWriter {
    return if (freestanding) std.io.null_writer.any() else std.io.getStdErr().writer().any();
}

pub fn panic(comptime format: []const u8, args: anytype) noreturn {
    if (debug and !freestanding) std.debug.panic(format, args) else unreachable;
}

pub fn setColor(cfg: std.io.tty.Config, writer: std.io.AnyWriter, color: std.io.tty.Color) !void {
    if (@import("builtin").target.os.tag != .freestanding) try cfg.setColor(writer, color);
}

pub const Pool = struct {
    arena: Arena,
    free: [sclass_count]?*Header = @splat(null),

    const max_alloc_size = 1024 * 1024 * 256;
    const page_size = 1024 * 4;
    const sclass_offset = std.math.log2_int(usize, page_size);
    const sclass_count = std.math.log2_int(usize, max_alloc_size) - sclass_offset;

    const Header = struct {
        next: ?*Header,
    };

    pub fn sclassOf(size: usize) usize {
        std.debug.assert(size <= max_alloc_size);
        return std.math.log2_int_ceil(usize, size) -| sclass_offset;
    }

    pub fn allocator(self: *Pool) std.mem.Allocator {
        const alc_impl = enum {
            fn alloc(ptr: *anyopaque, size: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
                const slf: *Pool = @alignCast(@ptrCast(ptr));
                const alignm = @max(alignment.toByteUnits(), @alignOf(Header));
                std.debug.assert(alignm <= page_size);
                const size_class = sclassOf(size);

                if (slf.free[size_class]) |fr| {
                    slf.free[size_class] = fr.next;
                    return @ptrCast(fr);
                }

                return slf.arena.allocator().rawAlloc(
                    @as(usize, 1) << @intCast(size_class + sclass_offset),
                    std.mem.Alignment.fromByteUnits(alignm),
                    ret_addr,
                );
            }
            fn free(ptr: *anyopaque, mem: []u8, _: std.mem.Alignment, _: usize) void {
                @memset(mem, undefined);
                const slf: *Pool = @alignCast(@ptrCast(ptr));
                const size_class = sclassOf(mem.len);
                const header: *Header = @alignCast(@ptrCast(mem.ptr));
                header.next = slf.free[size_class];
                slf.free[size_class] = header;
            }
            fn remap(_: *anyopaque, mem: []u8, _: std.mem.Alignment, new_len: usize, _: usize) ?[*]u8 {
                return if (sclassOf(mem.len) == sclassOf(new_len)) return mem.ptr else null;
            }
            fn resize(_: *anyopaque, mem: []u8, _: std.mem.Alignment, new_len: usize, _: usize) bool {
                return sclassOf(mem.len) == sclassOf(new_len);
            }
        };

        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alc_impl.alloc,
                .free = alc_impl.free,
                .remap = alc_impl.remap,
                .resize = alc_impl.resize,
            },
        };
    }
};

pub const PooledArena = struct {};

pub const Arena = struct {
    start: [*]align(page_size) u8,
    end: [*]align(page_size) u8,
    pos: [*]u8,

    const page_size = std.heap.pageSize();

    pub const Scratch = struct {
        prev_pos: [*]u8,
        arena: *Arena,

        pub fn deinit(self: *Scratch) void {
            @memset(self.arena.pos[0 .. @intFromPtr(self.arena.pos) - @intFromPtr(self.prev_pos)], undefined);
            self.arena.pos = self.prev_pos;
            self.* = undefined;
        }
    };

    pub threadlocal var scratch: [2]Arena = undefined;

    pub fn initScratch(cap: usize) void {
        for (&scratch) |*slt| slt.* = init(cap);
    }

    pub fn deinitScratch() void {
        for (&scratch) |*slt| slt.deinit();
    }

    pub fn resetScratch() void {
        for (&scratch) |*slt| slt.reset();
    }

    pub fn reset(arena: *Arena) void {
        arena.pos = arena.end;
    }

    pub fn allocated(self: *Arena) usize {
        return @intFromPtr(self.end) - @intFromPtr(self.pos);
    }

    pub fn scrathFromAlloc(except: ?std.mem.Allocator) Scratch {
        for (&scratch) |*slt| if (@as(*anyopaque, slt) != if (except) |e| e.ptr else null) return slt.checkpoint();
        unreachable;
    }

    pub fn scrath(except: ?*Arena) Scratch {
        for (&scratch) |*slt| if (slt != except) return slt.checkpoint();
        unreachable;
    }

    pub fn init(cap: usize) Arena {
        const pages = std.mem.alignForward(usize, cap, page_size);
        const ptr = std.heap.page_allocator.rawAlloc(pages, .fromByteUnits(page_size), @returnAddress()).?;
        return .{
            .end = @alignCast(ptr + pages),
            .start = @alignCast(ptr),
            .pos = @alignCast(ptr),
        };
    }

    pub fn allocator(self: *Arena) std.mem.Allocator {
        const alc_impl = enum {
            fn alloc(ptr: *anyopaque, size: usize, alignment: std.mem.Alignment, _: usize) ?[*]u8 {
                const slf: *Arena = @alignCast(@ptrCast(ptr));
                const alignm = alignment.toByteUnits();
                slf.pos = @ptrFromInt(std.mem.alignForward(usize, @intFromPtr(slf.pos), alignm));
                slf.pos += size;
                std.debug.assert(@intFromPtr(slf.end) > @intFromPtr(slf.pos));
                return slf.pos - size;
            }
            fn free(_: *anyopaque, mem: []u8, _: std.mem.Alignment, _: usize) void {
                @memset(mem, undefined);
            }
            fn remap(ptr: *anyopaque, mem: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
                if (@This().resize(ptr, mem, alignment, new_len, ret_addr)) return mem.ptr;
                return null;
            }
            fn resize(ptr: *anyopaque, mem: []u8, _: std.mem.Alignment, new_len: usize, _: usize) bool {
                const slf: *Arena = @alignCast(@ptrCast(ptr));
                if (mem.ptr + mem.len == slf.pos) {
                    slf.pos += new_len - mem.len;
                    return true;
                }
                return false;
            }
        };

        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alc_impl.alloc,
                .free = alc_impl.free,
                .remap = alc_impl.remap,
                .resize = alc_impl.resize,
            },
        };
    }

    pub fn deinit(self: *Arena) void {
        std.heap.page_allocator.rawFree(self.start[0 .. self.end - self.start], .fromByteUnits(page_size), @returnAddress());
        self.* = undefined;
    }

    pub fn checkpoint(self: *Arena) Scratch {
        return .{ .prev_pos = self.pos, .arena = self };
    }

    pub fn dupe(self: *Arena, comptime Elem: type, values: []const Elem) []Elem {
        const new = self.alloc(Elem, values.len);
        @memcpy(new, values);
        return new;
    }

    pub fn alloc(self: *Arena, comptime T: type, count: usize) []T {
        const size = @sizeOf(T) * count;
        self.pos = @ptrFromInt(std.mem.alignForward(usize, @intFromPtr(self.pos), @alignOf(T)));
        self.pos += size;
        std.debug.assert(@intFromPtr(self.end) > @intFromPtr(self.pos));
        const ptr: [*]T = @alignCast(@ptrCast(self.pos - size));
        const mem = ptr[0..count];
        @memset(mem, undefined);
        return mem;
    }

    pub fn makeArrayList(self: *Arena, comptime T: type, cap: usize) std.ArrayListUnmanaged(T) {
        return .initBuffer(self.alloc(T, cap));
    }

    pub fn create(self: *Arena, comptime T: type) *T {
        return &self.alloc(T, 1).ptr[0];
    }
};

const IdRepr = u32;

pub fn EnumId(comptime T: type) type {
    return enum(IdRepr) {
        _,

        const Tag = std.meta.Tag(T);

        const Repr = packed struct(IdRepr) {
            taga: std.meta.Tag(Tag),
            index: std.meta.Int(.unsigned, @bitSizeOf(IdRepr) - @bitSizeOf(Tag)),
        };

        pub fn compact(taga: Tag, indexa: usize) @This() {
            return @enumFromInt(@as(IdRepr, @bitCast(Repr{ .taga = @intFromEnum(taga), .index = @intCast(indexa) })));
        }

        pub fn zeroSized(taga: Tag) @This() {
            return compact(taga, 0);
        }

        pub fn tag(self: @This()) Tag {
            const repr: Repr = @bitCast(@intFromEnum(self));
            return @enumFromInt(repr.taga);
        }

        pub fn index(self: @This()) u32 {
            const repr: Repr = @bitCast(@intFromEnum(self));
            return repr.index;
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

        pub fn slice(self: @This(), start: usize, end: usize) @This() {
            std.debug.assert(start <= end);
            std.debug.assert(end * @sizeOf(Elem) <= self.end);
            return .{ .start = @intCast(self.start + start * @sizeOf(Elem)), .end = @intCast(self.start + end * @sizeOf(Elem)) };
        }
    };
}

pub fn EnumStore(comptime T: type) type {
    return struct {
        store: std.ArrayListAlignedUnmanaged(u8, payload_align) = .{},

        const Self = @This();
        const payload_align = b: {
            var max_align: u29 = 1;
            for (std.meta.fields(T)) |field| {
                max_align = @max(max_align, @alignOf(field.type));
            }
            break :b max_align;
        };
        const fields = @typeInfo(T).@"union".fields;

        pub const Id = EnumId(T);

        pub fn dupe(self: *const Self, gpa: std.mem.Allocator) !Self {
            return .{ .store = try self.store.clone(gpa) };
        }

        pub fn allocDyn(self: *Self, gpa: std.mem.Allocator, value: T) !Id {
            return switch (value) {
                inline else => |v, t| try self.alloc(gpa, t, v),
            };
        }

        pub fn TagPayload(comptime kind: std.meta.Tag(T)) type {
            return fields[@intFromEnum(kind)].type;
        }

        pub fn alloc(
            self: *Self,
            gpa: std.mem.Allocator,
            comptime tag: std.meta.Tag(T),
            value: TagPayload(tag),
        ) !Id {
            const Value = @TypeOf(value);
            (try self.allocLow(gpa, Value, 1))[0] = value;
            return .compact(tag, self.store.items.len - @sizeOf(Value));
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
            if (count == 0) return &.{};
            std.debug.assert(@alignOf(E) <= payload_align);
            const alignment: usize = @alignOf(E);
            const padded_len = std.mem.alignForward(usize, self.store.items.len, alignment);
            const required_space = padded_len + @sizeOf(E) * count;
            try self.store.resize(gpa, required_space);
            const dest: [*]E = @alignCast(@ptrCast(self.store.items.ptr + padded_len));
            return dest[0..count];
        }

        pub fn get(self: *const Self, id: Id) AsRef(T) {
            const Layout = extern struct { ptr: *align(payload_align) const anyopaque, tag: usize };
            return @bitCast(Layout{ .tag = @intFromEnum(id.tag()), .ptr = @ptrCast(@alignCast(&self.store.items[id.index()])) });
        }

        pub inline fn getTyped(
            self: *const Self,
            comptime tag: std.meta.Tag(T),
            id: Id,
        ) ?*TagPayload(tag) {
            if (tag != id.tag()) return null;
            return @ptrCast(@alignCast(&self.store.items[id.index()]));
        }

        pub fn getTypedPtr(
            self: *Self,
            comptime tag: std.meta.Tag(T),
            id: Id,
        ) ?*TagPayload(tag) {
            if (tag != id.tag()) return null;
            const Value = TagPayload(tag);
            const loc: *Value = @ptrCast(@alignCast(&self.store.items[id.index()]));
            return loc;
        }

        pub fn view(self: *const Self, slice: anytype) []@TypeOf(slice).Elem {
            const slc = self.store.items[slice.start..slice.end];
            if (slc.len == 0) return &.{};
            const len = slc.len / @sizeOf(@TypeOf(slice).Elem);
            const ptr: [*]@TypeOf(slice).Elem = @ptrCast(@alignCast(slc.ptr));
            return ptr[0..len];
        }

        pub fn deinit(self: *Self, gpa: std.mem.Allocator) void {
            self.store.deinit(gpa);
            self.* = undefined;
        }
    };
}

pub fn AsRef(comptime E: type) type {
    const info = @typeInfo(E).@"union";

    var field_arr = info.fields[0..].*;

    for (&field_arr) |*f| {
        if (f.type != void) {
            f.type = *f.type;
            f.alignment = @alignOf(*f.type);
        }
    }

    return @Type(.{ .@"union" = .{
        .layout = .@"extern",
        .tag_type = std.meta.Tag(E),
        .fields = &field_arr,
        .decls = &.{},
    } });
}

pub fn dbg(value: anytype) @TypeOf(value) {
    if (@TypeOf(value) == []const u8) {
        std.debug.print("{s}\n", .{value});
    } else {
        std.debug.print("{any}\n", .{value});
    }
    return value;
}

const debug = @import("builtin").mode == .Debug;

pub fn isErr(value: anytype) bool {
    value catch return true;
    return false;
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

pub fn EntStore(comptime M: type) type {
    return struct {
        const Tag = std.meta.DeclEnum(M);
        pub const Data = b: {
            var fields: [decls.len]std.builtin.Type.UnionField = undefined;

            for (decls, &fields) |d, *f| {
                const Ty = @field(M, d.name);
                const Dt = if (@hasDecl(Ty, "identity")) Ty else EntId(Ty);
                f.* = .{
                    .name = d.name,
                    .type = Dt,
                    .alignment = @alignOf(Dt),
                };
            }

            break :b @Type(.{ .@"union" = .{
                .layout = .auto,
                .tag_type = Tag,
                .fields = &fields,
                .decls = &.{},
            } });
        };

        rpr: Store = .{},

        const decls = std.meta.declarations(M);
        const Store = b: {
            var fields: [decls.len]std.builtin.Type.StructField = undefined;

            for (decls, &fields) |d, *f| {
                const Arr = std.ArrayListUnmanaged(@field(M, d.name));
                f.* = .{
                    .name = d.name,
                    .type = Arr,
                    .alignment = @alignOf(Arr),
                    .is_comptime = false,
                    .default_value_ptr = &Arr.empty,
                };
            }

            break :b @Type(.{ .@"struct" = .{
                .layout = .auto,
                .fields = &fields,
                .decls = &.{},
                .is_tuple = false,
            } });
        };
        const store_fields = std.meta.fields(Store);
        const data_fields = std.meta.fields(Data);
        const Self = @This();

        pub inline fn isValid(self: *Self, comptime kind: Tag, idx: usize) bool {
            return idx < @field(self.rpr, @tagName(kind)).items.len;
        }

        pub inline fn fieldName(comptime Ty: type) std.builtin.Type.StructField {
            return for (decls, store_fields) |d, sf| {
                if (@field(M, d.name) == Ty) return sf;
            } else @compileError(@typeName(Ty));
        }

        pub inline fn add(self: *Self, gpa: std.mem.Allocator, vl: anytype) EntId(@TypeOf(vl)) {
            @field(self.rpr, fieldName(@TypeOf(vl)).name).append(gpa, vl) catch unreachable;
            return @enumFromInt(@field(self.rpr, fieldName(@TypeOf(vl)).name).items.len - 1);
        }

        pub inline fn pop(self: *Self, vl: anytype) void {
            std.debug.assert(@field(self.rpr, fieldName(@TypeOf(vl).Data).name).items.len == @intFromEnum(vl) + 1);
            _ = @field(self.rpr, fieldName(@TypeOf(vl).Data).name).pop().?;
        }

        pub inline fn get(self: *Self, id: anytype) if (@hasDecl(@TypeOf(id), "identity")) @TypeOf(id) else *@TypeOf(id).Data {
            if (@hasDecl(@TypeOf(id), "identity")) return id;
            return &@field(self.rpr, fieldName(@TypeOf(id).Data).name).items[@intFromEnum(id)];
        }

        pub fn TagPayload(comptime kind: Tag) type {
            return data_fields[@intFromEnum(kind)].type;
        }

        pub inline fn unwrap(self: *Self, id: Data, comptime kind: Tag) ?*if (@hasDecl(TagPayload(kind), "identity"))
            TagPayload(kind)
        else
            TagPayload(kind).Data {
            if (id != kind) return null;
            const i = @field(id, @tagName(kind));
            if (@hasDecl(TagPayload(kind), "identity")) return i;
            return &@field(self.rpr, @tagName(kind)).items[@intFromEnum(i)];
        }
    };
}

pub fn EntId(comptime D: type) type {
    if (@hasDecl(D, "Id")) return D.Id;

    return enum(u32) {
        _,
        pub const Data = D;
    };
}
