const std = @import("std");

pub const freestanding = @import("builtin").target.os.tag == .freestanding;

pub fn undistributeComutative(
    a: anytype,
    b: @TypeOf(a),
    c: @TypeOf(a),
    d: @TypeOf(a),
) ?struct { @TypeOf(a), @TypeOf(a), @TypeOf(a) } {
    if (a == b) return .{ a, c, d };
    if (a == c) return .{ a, b, d };
    if (a == d) return .{ a, b, c };

    if (b == c) return .{ b, a, d };
    if (b == d) return .{ b, a, c };

    if (c == d) return .{ c, a, b };

    return null;
}

pub fn undistribute(
    a: anytype,
    b: @TypeOf(a),
    c: @TypeOf(a),
    d: @TypeOf(a),
    is_rhs: bool,
) ?struct { @TypeOf(a), @TypeOf(a), @TypeOf(a) } {
    if (b == d and is_rhs) return .{ a, c, b };
    if (a == c and !is_rhs) return .{ a, b, d };
    return null;
}

pub fn dedupeSorted(comptime T: type, slice: []T) usize {
    if (slice.len == 0) return 0;

    var write_index: usize = 1;
    var last = slice[0];

    for (slice[1..]) |value| {
        if (value != last) {
            slice[write_index] = value;
            last = value;
            write_index += 1;
        }
    }
    return write_index;
}

pub fn ensureSlot(self: anytype, gpa: std.mem.Allocator, id: usize) !*std.meta.Child(@TypeOf(self.items)) {
    if (self.items.len <= id) {
        const prev_len = self.items.len;
        try self.resize(gpa, id + 1);
        @memset(self.items[prev_len..], .invalid);
    }
    return &self.items[id];
}

pub fn panic(comptime format: []const u8, args: anytype) noreturn {
    if (debug and !freestanding) std.debug.panic(format, args) else unreachable;
}

pub fn setColor(cfg: std.io.tty.Config, writer: *std.Io.Writer, color: std.io.tty.Color) !void {
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

    pub fn staleMemory(self: *Pool) usize {
        var total: usize = 0;

        var unit: usize = page_size;
        for (self.free) |header| {
            var cursor = header;
            while (cursor) |hdr| {
                total += unit;
                cursor = hdr.next;
            }
            unit *= 2;
        }

        return total;
    }

    pub fn allocator(self: *Pool) std.mem.Allocator {
        const alc_impl = enum {
            fn alloc(ptr: *anyopaque, size: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
                const slf: *Pool = @ptrCast(@alignCast(ptr));
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
                const slf: *Pool = @ptrCast(@alignCast(ptr));
                const size_class = sclassOf(mem.len);
                const header: *Header = @ptrCast(@alignCast(mem.ptr));
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

pub const Arena = struct {
    start: [*]align(page_size) u8,
    end: [*]align(page_size) u8,
    pos: [*]u8,

    const page_size = std.heap.pageSize();

    threadlocal var inited: bool = false;
    pub threadlocal var scratch: [2]Arena = undefined;

    pub const Scratch = struct {
        prev_pos: [*]u8,
        arena: *Arena,

        pub fn deinit(self: *Scratch) void {
            @memset(self.prev_pos[0 .. @intFromPtr(self.arena.pos) - @intFromPtr(self.prev_pos)], undefined);
            self.arena.pos = self.prev_pos;
            self.* = undefined;
        }
    };

    pub fn initScratch(cap: usize) void {
        if (std.debug.runtime_safety) {
            std.debug.assert(!inited);
            inited = true;
        }
        for (&scratch) |*slt| slt.* = init(cap);
    }

    pub fn deinitScratch() void {
        if (std.debug.runtime_safety) {
            std.debug.assert(inited);
            inited = false;
        }
        for (&scratch) |*slt| slt.deinit();
    }

    pub fn resetScratch() void {
        for (&scratch) |*slt| slt.reset();
    }

    pub fn consumed(arena: *Arena) u64 {
        return @intCast(arena.pos - arena.start);
    }

    pub fn reset(arena: *Arena) void {
        arena.pos = arena.start;
    }

    pub fn allocated(self: *Arena) usize {
        return @intFromPtr(self.end) - @intFromPtr(self.pos);
    }

    pub fn getCapacity(self: *Arena) usize {
        return @intFromPtr(self.end) - @intFromPtr(self.start);
    }

    pub fn subslice(self: *Arena, capacity: usize) Arena {
        const cap = std.mem.alignBackward(usize, capacity, page_size);
        const ptr = self.allocRaw(page_size, cap);
        return .{
            .start = @alignCast(ptr),
            .end = @alignCast(ptr + cap),
            .pos = ptr,
        };
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
                const slf: *Arena = @ptrCast(@alignCast(ptr));
                return slf.allocRaw(alignment.toByteUnits(), size);
            }
            fn free(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize) void {}
            fn remap(ptr: *anyopaque, mem: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
                if (@This().resize(ptr, mem, alignment, new_len, ret_addr)) return mem.ptr;
                return null;
            }
            fn resize(ptr: *anyopaque, mem: []u8, _: std.mem.Alignment, new_len: usize, _: usize) bool {
                const slf: *Arena = @ptrCast(@alignCast(ptr));
                if (mem.ptr + mem.len == slf.pos) {
                    slf.pos += new_len;
                    slf.pos -= mem.len;
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
        const ptr: [*]T = @ptrCast(@alignCast(self.allocRaw(@alignOf(T), @sizeOf(T) * count)));
        const mem = ptr[0..count];
        @memset(mem, undefined);
        return mem;
    }

    pub fn allocRaw(self: *Arena, alignment: usize, size: usize) [*]u8 {
        self.pos = @ptrFromInt(std.mem.alignForward(usize, @intFromPtr(self.pos), alignment));
        self.pos += size;
        std.debug.assert(@intFromPtr(self.end) >= @intFromPtr(self.pos));
        return self.pos - size;
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
        store: std.ArrayListAlignedUnmanaged(u8, .fromByteUnits(payload_align)) = .{},

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
            const dest: [*]E = @ptrCast(@alignCast(self.store.items.ptr + padded_len));
            return dest[0..count];
        }

        pub fn get(self: *const Self, id: Id) AsRef(T) {
            const Layout = extern struct { ptr: *align(payload_align) const anyopaque, tag: usize };
            return @as(*const AsRef(T), @ptrCast(&Layout{ .tag = @intFromEnum(id.tag()), .ptr = @ptrCast(@alignCast(&self.store.items[id.index()])) })).*;
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
        .layout = .auto,
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
                const Arr = SegmentedList(@field(M, d.name));
                f.* = .{
                    .name = d.name,
                    .type = Arr,
                    .alignment = @alignOf(Arr),
                    .is_comptime = false,
                    .default_value_ptr = &Arr{},
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

        pub fn isValid(self: *Self, comptime kind: Tag, idx: usize) bool {
            return idx < @field(self.rpr, @tagName(kind)).meta.len;
        }

        pub fn fieldName(comptime Ty: type) std.builtin.Type.StructField {
            return for (decls, store_fields) |d, sf| {
                if (@field(M, d.name) == Ty) return sf;
            } else @compileError(@typeName(Ty));
        }

        pub fn add(self: *Self, gpa: *Arena, vl: anytype) EntId(@TypeOf(vl)) {
            @field(self.rpr, fieldName(@TypeOf(vl)).name).addOne(gpa).* = vl;
            return @enumFromInt(@field(self.rpr, fieldName(@TypeOf(vl)).name).meta.len - 1);
        }

        pub fn pop(self: *Self, vl: anytype) void {
            std.debug.assert(@field(self.rpr, fieldName(@TypeOf(vl).Data).name).meta.len == @intFromEnum(vl) + 1);
            _ = @field(self.rpr, fieldName(@TypeOf(vl).Data).name).pop().?;
        }

        pub fn get(self: *Self, id: anytype) if (@hasDecl(@TypeOf(id), "identity")) @TypeOf(id) else *@TypeOf(id).Data {
            if (@hasDecl(@TypeOf(id), "identity")) return id;
            return @field(self.rpr, fieldName(@TypeOf(id).Data).name).at(@intFromEnum(id));
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
            return @field(self.rpr, @tagName(kind)).at(@intFromEnum(i));
        }
    };
}

pub fn EntId(comptime D: type) type {
    if (@hasDecl(D, "Id")) return D.Id;

    return enum(u32) {
        _,
        pub const Data = D;

        pub fn get(self: @This(), cont: anytype) *D {
            return cont.store.get(self);
        }
    };
}

pub fn SegmentedList(comptime T: type) type {
    return struct {
        pub const first_segment_size = 1024 * 16;
        pub const first_segment_size_exp = std.math.log2_int(usize, first_segment_size);
        pub const max_segment_size = 1024 * 1024;

        pub const shelf_count = std.math.log2_int(usize, max_segment_size / first_segment_size) + 1;

        shelfs: [shelf_count][*]T = undefined,
        meta: packed struct(usize) {
            active_shelf_count: ShelfIndex = 0,
            len: std.meta.Int(.unsigned, @bitSizeOf(usize) - @bitSizeOf(ShelfIndex)) = 0,
        } = .{},

        const Self = @This();
        const ShelfIndex = std.math.Log2Int(usize);

        pub fn addOne(self: *Self, gpa: *Arena) *T {
            self.ensureCapacity(gpa, self.meta.len + 1);
            const shelf_index = shelfIndex(self.meta.len);
            const box_index = boxIndex(self.meta.len, shelf_index);
            self.meta.len += 1;
            return &self.shelfs[shelf_index][box_index];
        }

        pub fn pop(self: *Self) ?T {
            if (self.meta.len == 0) return null;

            defer self.meta.len -= 1;
            return self.at(self.meta.len - 1).*;
        }

        pub fn at(self: Self, index: usize) *T {
            std.debug.assert(index < self.meta.len);
            const shelf_index = shelfIndex(index);
            const box_index = boxIndex(index, shelf_index);
            return &self.shelfs[shelf_index][box_index];
        }

        pub fn ensureCapacity(self: *Self, arena: *Arena, new_capacity: usize) void {
            const new_cap_shelf_count = shelfCount(new_capacity);
            const old_shelf_count = self.meta.active_shelf_count;
            if (new_cap_shelf_count <= old_shelf_count) {
                @branchHint(.likely);
                return;
            }

            var i: ShelfIndex = old_shelf_count;
            while (i < new_cap_shelf_count) : (i += 1) {
                self.shelfs[i] = arena.alloc(T, shelfSize(i)).ptr;
            }
            self.meta.active_shelf_count = new_cap_shelf_count;
        }

        fn shelfSize(shelf_index: ShelfIndex) usize {
            return @as(usize, 1) << (shelf_index + (first_segment_size_exp + 1));
        }

        fn shelfIndex(list_index: usize) ShelfIndex {
            return std.math.log2_int(usize, list_index + first_segment_size * 2) - first_segment_size_exp - 1;
        }

        fn boxIndex(list_index: usize, shelf_index: ShelfIndex) usize {
            return list_index + first_segment_size * 2 - (@as(usize, 1) << ((first_segment_size_exp + 1) + shelf_index));
        }

        fn shelfCount(box_count: usize) ShelfIndex {
            return @intCast(std.math.log2_int_ceil(usize, box_count + first_segment_size * 2) - first_segment_size_exp - 1);
        }
    };
}

pub const Foo = SegmentedList(usize);

test "segmented list" {
    var arena = Arena.init(1024 * 1024);
    var list = SegmentedList(usize){};

    for (0..1024 * 32) |i| {
        list.addOne(&arena).* = i;
    }

    for (0..1024 * 32) |i| {
        try std.testing.expectEqual(i, list.at(i).*);
    }
}

pub fn SharedQueue(comptime T: type) type {
    return struct {
        shards: []Shard,
        progress: usize = 0,
        cached_counter: usize = 0,
        self_id: usize = std.math.maxInt(usize),
        tasks: []const []T,

        const Self = @This();

        pub const Shard = struct {
            _align: void align(std.atomic.cache_line) = {},
            reserved: std.atomic.Value(usize) = .init(0),
            available: std.atomic.Value(usize) = .init(0),
            waker: std.Thread.ResetEvent = .{},
        };

        pub fn size_of(thread_count: usize, capacity: usize) usize {
            return @sizeOf(T) * capacity * thread_count +
                @sizeOf(Shard) * thread_count +
                @sizeOf([]T) * thread_count;
        }

        pub fn init(arena: *Arena, thread_count: usize, capacity: usize) Self {
            const shards = arena.alloc(Shard, thread_count);
            @memset(shards, .{});

            const tasks = arena.alloc([]T, thread_count);
            for (tasks) |*t| {
                t.* = arena.alloc(T, capacity);
            }

            return .{ .shards = shards, .tasks = tasks };
        }

        pub fn enque(self: *Self, tasks: []const T) void {
            const push_to = (if (!std.meta.hasMethod(T, "hash")) b: {
                comptime std.debug.assert(std.meta.hasUniqueRepresentation(T));
                break :b std.hash.Wyhash.hash(0, @ptrCast(tasks));
            } else T.hash(tasks)) & self.shards.len - 1;

            const target = &self.shards[@intCast(push_to)];

            const idx = target.reserved.fetchAdd(tasks.len, .monotonic);
            @memcpy(self.tasks[@intCast(push_to)][idx..][0..tasks.len], tasks);
            while (target.available.cmpxchgWeak(idx, idx + tasks.len, .release, .monotonic) != null) {}
            target.waker.set();
        }

        pub fn dequeue(self: *Self) ?T {
            const shard = &self.shards[self.self_id];
            if (self.progress == self.cached_counter) {
                self.cached_counter = shard.available.load(.acquire);
                if (self.progress == self.cached_counter) return null;
            }
            self.progress += 1;
            return self.tasks[self.self_id][self.progress - 1];
        }

        pub fn dequeueWait(self: *Self, timeout_ms: usize) ?T {
            const shard = &self.shards[self.self_id];

            while (true) {
                shard.waker.reset();

                // the thread pushed while we were setting the waker
                if (self.dequeue()) |task| return task;

                if (@import("builtin").single_threaded) return null;

                // timeout means no more tasks
                shard.waker.timedWait(timeout_ms * std.time.ns_per_ms) catch {
                    return self.dequeue();
                };

                // if we were woken up, we still might not have tasks, which
                // happens so rarely it doesn't matter, so just try again
                return self.dequeue() orelse continue;
            }
        }
    };
}

pub fn TimeMetrics(comptime StatNames: type) type {
    return struct {
        total: u64 = 0,
        stats: Stats = .{},

        const Self = @This();

        const max_name_len = b: {
            var max: usize = 0;
            for (std.meta.fields(StatNames)) |f| {
                max = @max(max, f.name.len);
            }
            break :b std.fmt.comptimePrint("{d}", .{max});
        };

        const Stats = @Type(b: {
            var fields: [std.meta.fields(StatNames).len]std.builtin.Type.StructField = undefined;
            for (std.meta.fields(StatNames), &fields) |f, *sf| {
                sf.* = .{
                    .name = f.name,
                    .type = u64,
                    .alignment = @alignOf(u64),
                    .is_comptime = false,
                    .default_value_ptr = &@as(u64, 0),
                };
            }
            break :b .{
                .@"struct" = .{
                    .layout = .auto,
                    .fields = &fields,
                    .decls = &.{},
                    .is_tuple = false,
                },
            };
        });

        pub const Scope = if (freestanding) struct {
            pub fn end(_: *@This()) void {}
        } else struct {
            total: *u64,
            stat: *u64,
            timer: std.time.Timer,
            prev_total: u64,

            pub fn end(self: *@This()) void {
                const elapsed = self.timer.lap() - (self.total.* - self.prev_total);
                self.stat.* += elapsed;
                self.total.* += elapsed;
                self.* = undefined;
            }
        };

        pub fn init() Self {
            return .{};
        }

        // THIS handles the nesting
        pub fn begin(self: *Self, comptime name: StatNames) Scope {
            return if (freestanding) .{} else .{
                .stat = &@field(self.stats, @tagName(name)),
                .timer = std.time.Timer.start() catch unreachable,
                .total = &self.total,
                .prev_total = self.total,
            };
        }

        pub fn logStats(self: *Self, out: *std.Io.Writer) void {
            errdefer unreachable;
            try out.print("time metrics:\n", .{});

            var total: u64 = 0;
            inline for (std.meta.fields(Stats)) |f| {
                total += @field(self.stats, f.name);
            }

            const ftotal = @as(f64, @floatFromInt(total));
            try out.print("  total: {d:.9}s\n", .{ftotal / std.time.ns_per_s});

            inline for (std.meta.fields(Stats)) |f| {
                const fvl = @as(f64, @floatFromInt(@field(self.stats, f.name)));
                try out.print("  {s:<" ++ max_name_len ++ "}: ({d:>6.2}%) {d:>10.9}s\n", .{
                    f.name,
                    (fvl / ftotal) * 100,
                    fvl / std.time.ns_per_s,
                });
            }
        }
    };
}

test "queue shard" {
    const tasks_per_thread = 1024 * 1024;

    const thread = struct {
        fn runShardThread(ashard: SharedQueue(u64), waker: *std.Thread.ResetEvent) void {
            waker.wait();

            var shard = ashard;
            for (0..tasks_per_thread) |i| {
                var tasks: u64 = i + shard.self_id * tasks_per_thread;
                shard.enque((&tasks)[0..1]);
                shard.enque((&tasks)[0..1]);
                _ = shard.dequeue() orelse shard.dequeueWait(10);
            }
        }
    };

    const thread_count = 8;

    var arena = Arena.init(SharedQueue(u64).size_of(thread_count, tasks_per_thread * thread_count));
    var shard = SharedQueue(u64).init(&arena, thread_count, tasks_per_thread * thread_count);

    const Thrd = struct {
        thread: std.Thread,
    };

    const tsrgs = std.testing.allocator.alloc(Thrd, thread_count) catch unreachable;
    var waker = std.Thread.ResetEvent{};
    defer std.testing.allocator.free(tsrgs);
    for (tsrgs, 0..) |*thrd, i| {
        shard.self_id = i;
        thrd.* = .{ .thread = try std.Thread.spawn(.{}, thread.runShardThread, .{ shard, &waker }) };
    }

    waker.set();

    for (tsrgs) |thrd| {
        thrd.thread.join();
    }

    var bitset = try std.DynamicBitSetUnmanaged.initEmpty(std.testing.allocator, thread_count * tasks_per_thread);
    defer bitset.deinit(std.testing.allocator);

    for (shard.tasks, shard.shards) |thrd, shrd| {
        for (thrd[0..shrd.available.load(.unordered)]) |task| {
            bitset.set(@bitCast(task));
        }
    }

    std.debug.assert(bitset.count() == thread_count * tasks_per_thread);
}

test "dequeueWait" {
    const thread = struct {
        fn run(queue: SharedQueue(usize)) void {
            var q = queue;
            for (0..10) |i| {
                q.enque(&.{i});
                std.Thread.sleep(10 * std.time.ns_per_ms);
            }
        }
    };

    var arena = Arena.init(1024 * 1024);
    var queue = SharedQueue(usize).init(&arena, 1, 100);
    queue.self_id = 0;

    var tread = std.Thread.spawn(.{}, thread.run, .{queue}) catch unreachable;

    for (0..10) |i| {
        const task = queue.dequeueWait(100).?;
        std.debug.assert(task == i);
    }

    defer tread.join();
}

pub const LineIndex = struct {
    nlines: []const u32,

    pub fn lineCol(self: LineIndex, pos: u32) struct { u32, u32 } {
        var start: usize, var end = .{ 0, self.nlines.len };

        while (start < end) {
            const mid = (start + end) / 2;
            if (pos < self.nlines[mid]) {
                end = mid;
            } else {
                start = mid + 1;
            }
        }

        return .{ @intCast(start), pos - self.nlines[start - 1] };
    }

    pub fn init(file_content: []const u8, arena: *Arena) LineIndex {
        var line_count: usize = 1;
        for (file_content) |c| {
            if (c == '\n') line_count += 1;
        }

        var nlines = arena.alloc(u32, line_count);
        nlines[0] = 0;

        line_count = 1;
        for (file_content, 0..) |c, i| {
            if (c == '\n') {
                nlines[line_count] = @intCast(i + 1);
                line_count += 1;
            }
        }

        return .{ .nlines = nlines };
    }
};

test LineIndex {
    const file_content =
        \\akjdshkdfj
        \\ksjdhks
        \\akjdsk
        \\akjdshkdfj
        \\ksjdhks
        \\akjdsk
    ;

    var arena = Arena.init(4096);
    defer arena.deinit();

    const line_index = LineIndex.init(file_content, &arena);

    var line: u32 = 1;
    var last_nl: usize = 0;
    for (file_content, 0..) |c, i| {
        const lin, const col = line_index.lineCol(@intCast(i));
        try std.testing.expectEqual(line, lin);
        try std.testing.expectEqual(i - last_nl, col);
        if (c == '\n') {
            line += 1;
            last_nl = i + 1;
        }
    }
}
