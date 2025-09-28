const std = @import("std");
const root = @import("hb");
const utils = root.utils;

pub const ExecHeader = extern struct {
    magic_number: [3]u8 = .{ 0x15, 0x91, 0xD2 },
    executable_version: u32 align(1) = 0,

    code_length: u64 align(1) = 0,
    data_length: u64 align(1) = 0,
    debug_length: u64 align(1) = 0,
    symbol_count: u64 align(1) = 0,
    config_length: u64 align(1) = 0,
    metadata_length: u64 align(1) = 0,
};

pub const Symbol = extern struct {
    name: u32,
    kind: enum(u32) { func, data },
    offset: u64,
};

const Reloc = struct {
    slot_rel: i32,
    target_rel: i32,
};

const code_init = root.hbvm.isa.packMany(.{
    .{ .lra, 2, 0, 0 }, // load reloc address
    .{ .li64, 1, 0 },
    .{ .li64, 5, 0 },
});

const code_body = root.hbvm.isa.packMany(.{
    .{ .ld, 3, 2, 0, 4 }, // load offset
    .{ .sxt32, 3, 3 }, // mask of
    .{ .ld, 4, 2, 4, 4 }, // load disp
    .{ .sxt32, 4, 4 }, // mask of
    .{ .add64, 3, 3, 2 }, // compute global offset
    .{ .add64, 4, 4, 3 }, // compute the resuting address
    .{ .st, 4, 3, 0, 8 }, // do the reloc
    .{ .addi64, 1, 1, 1 },
    .{ .addi64, 2, 2, @sizeOf(Reloc) },
    .{ .jltu, 1, 5, 0 },
});

pub fn loadSymMap(arena: std.mem.Allocator, code: []const u8) !std.AutoHashMapUnmanaged(u32, []const u8) {
    const header: ExecHeader = @bitCast(code[0..@sizeOf(ExecHeader)].*);
    const sym_start: usize = @intCast(@sizeOf(ExecHeader) + header.code_length + header.data_length);
    const sym_end: usize = @intCast(header.symbol_count * @sizeOf(Symbol));
    const syms: []align(1) const Symbol =
        @ptrCast(code[sym_start..][0..sym_end]);

    const string_table = code[sym_start..][sym_end..@intCast(header.debug_length)];

    var symbols = std.AutoHashMapUnmanaged(u32, []const u8){};
    for (syms) |sym| {
        const len = std.mem.indexOfScalar(u8, string_table[sym.name..], 0).?;
        try symbols.put(
            arena,
            @intCast(sym.offset - @sizeOf(ExecHeader)),
            string_table[sym.name..][0..len],
        );
    }

    return symbols;
}

pub fn jitLink(self: root.backend.Machine.Data, after: usize) void {
    for (self.relocs.items[after..]) |rel| {
        const target = &self.syms.items[@intFromEnum(rel.target)];
        std.debug.assert(target.kind != .invalid);
        const jump = @as(i64, target.offset) - rel.offset;
        const location: usize = @intCast(rel.offset + @as(u32, @intCast(rel.meta.addend)));

        @memcpy(
            self.code.items[location..][0..rel.meta.slot_size.bytes()],
            @as(*const [8]u8, @ptrCast(&jump))[0..rel.meta.slot_size.bytes()],
        );
    }
}

pub fn flush(self: root.backend.Machine.Data, writer: *std.Io.Writer) anyerror!void {
    var tmp = root.utils.Arena.scrath(null);
    defer tmp.deinit();

    const offset_lookup = tmp.arena.alloc(u32, self.syms.items.len);

    var code_cursor: u32 = @sizeOf(ExecHeader);
    var lengths: struct { func: u32, data: u32, prealloc: u32, tls_prealloc: u32 } = undefined;
    const sets = .{ .func, .data, .prealloc, .tls_prealloc };
    var prev_len: u32 = code_cursor;
    var global_reloc_count: u32 = 0;
    var global_reloc_offset: u32 = undefined;

    const include_relocs = for (self.syms.items) |sym| {
        if (sym.kind == .data and sym.reloc_count != 0) break true;
    } else false;

    inline for (sets) |v| {
        if (v == .func and include_relocs) {
            code_cursor += code_init.len + code_body.len;
        }

        for (offset_lookup, self.syms.items) |*slot, sym| if (sym.kind == v) {
            slot.* = code_cursor;
            code_cursor += sym.size;

            if (v == .data) {
                global_reloc_count += sym.reloc_count;
            }
        };

        if (v == .data and include_relocs) {
            global_reloc_offset = code_cursor;
            code_cursor += global_reloc_count * @sizeOf(Reloc);
        }

        @field(lengths, @tagName(v)) = code_cursor - prev_len;
        prev_len = code_cursor;
    }

    var code_init_buf: []u8 = undefined;
    var code_body_buf: []u8 = undefined;
    if (include_relocs) {
        code_init_buf = tmp.arena.dupe(u8, code_init);
        @memcpy(
            code_init_buf[3..][0..4],
            @as(*const [8]u8, @ptrCast(&(global_reloc_offset - @sizeOf(ExecHeader))))[0..4],
        );
        @memcpy(
            code_init_buf[code_init_buf.len - 8 ..],
            @as(*const [8]u8, @ptrCast(&@as(u64, global_reloc_count))),
        );

        code_body_buf = tmp.arena.dupe(u8, code_body);
        @memcpy(
            code_body_buf[code_body_buf.len - 2 ..],
            @as(*const [8]u8, @ptrCast(&@as(u64, -%code_body_buf.len +
                root.hbvm.isa.instrSize(.jltu))))[0..2],
        );
    }

    var buf = tmp.arena.makeArrayList(Reloc, global_reloc_count);

    for (self.syms.items, offset_lookup) |sym, olp| switch (sym.kind) {
        .func => {
            for (self.relocs.items[sym.reloc_offset..][0..sym.reloc_count]) |*rel| {
                const dest = offset_lookup[@intFromEnum(rel.target)];
                const jump = @as(i64, dest) - (rel.offset + olp);
                const location: usize = @intCast(rel.offset + sym.offset + @as(u32, @intCast(rel.meta.addend)));

                @memcpy(
                    self.code.items[location..][0..rel.meta.slot_size.bytes()],
                    @as(*const [8]u8, @ptrCast(&jump))[0..rel.meta.slot_size.bytes()],
                );
            }
        },
        .data => {
            for (
                self.relocs.items[sym.reloc_offset..][0..sym.reloc_count],
                buf.items.len..,
                buf.addManyAsSliceAssumeCapacity(sym.reloc_count),
            ) |rel, i, *slot| {
                const reloc_offset: i64 = @intCast(global_reloc_offset + i * @sizeOf(Reloc));
                const dest: i64 = offset_lookup[@intFromEnum(rel.target)];

                slot.* = .{
                    .slot_rel = @intCast((rel.offset + olp) - reloc_offset),
                    .target_rel = @intCast(dest - (rel.offset + olp)),
                };
            }
        },
        .invalid => {},
        .prealloc => {
            std.debug.assert(sym.reloc_count == 0);
        },
        .tls_prealloc => {
            std.debug.assert(sym.reloc_count == 0);
        },
    };

    var sym_count: usize = @intFromBool(include_relocs);
    for (self.syms.items) |sym| {
        sym_count += @intFromBool(sym.kind != .invalid);
    }

    try writer.writeStruct(ExecHeader{
        .code_length = lengths.func,
        .data_length = lengths.data + lengths.prealloc + lengths.tls_prealloc,
        .debug_length = sym_count * @sizeOf(Symbol) + self.names.items.len + 1,
        .symbol_count = sym_count,
    }, .little);

    inline for (sets) |v| {
        if (v == .func and include_relocs) {
            try writer.writeAll(code_init_buf);
            try writer.writeAll(code_body_buf);
        }

        for (self.syms.items) |sym| if (sym.kind == v) {
            if (sym.kind == .prealloc) {
                for (0..sym.size) |_| try writer.writeByte(0);
            } else {
                try writer.writeAll(self.code.items[sym.offset..][0..sym.size]);
            }
        };

        if (v == .data and include_relocs) {
            try writer.writeAll(@ptrCast(buf.items));
        }
    }

    for (offset_lookup, self.syms.items) |off, sym| {
        try writer.writeStruct(Symbol{
            .name = sym.name + 1,
            .offset = off,
            .kind = switch (sym.kind) {
                .func => .func,
                .data, .prealloc, .tls_prealloc => .data,
                .invalid => continue,
            },
        }, .little);
    }

    if (include_relocs) {
        try writer.writeStruct(Symbol{
            .name = 0,
            .offset = global_reloc_offset,
            .kind = .data,
        }, .little);
    }

    try writer.writeByte(0);
    try writer.writeAll(self.names.items);

    try writer.flush();
}
