const std = @import("std");
const root = @import("../root.zig");

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
        const dest = self.syms.items[@intFromEnum(rel.target)].offset;
        const jump = @as(i64, dest) - rel.offset;
        const location: usize = @intCast(rel.offset + @as(u32, @intCast(rel.addend)));

        @memcpy(
            self.code.items[location..][0..rel.slot_size],
            @as(*const [8]u8, @ptrCast(&jump))[0..rel.slot_size],
        );
    }
}

pub fn flush(self: root.backend.Machine.Data, writer: std.io.AnyWriter) anyerror!void {
    var tmp = root.utils.Arena.scrath(null);
    defer tmp.deinit();

    const offset_lookup = tmp.arena.alloc(u32, self.syms.items.len);

    var code_cursor: u32 = @sizeOf(ExecHeader);
    var lengths: struct { func: u32, data: u32, prealloc: u32 } = undefined;
    const sets = .{ .func, .data, .prealloc };
    var prev_len: u32 = code_cursor;
    inline for (sets) |v| {
        for (offset_lookup, self.syms.items) |*slot, sym| if (sym.kind == v) {
            slot.* = code_cursor;
            code_cursor += sym.size;
        };
        @field(lengths, @tagName(v)) = code_cursor - prev_len;
        prev_len = code_cursor;
    }

    for (self.syms.items, offset_lookup) |sym, olp| if (sym.kind == .func) {
        for (self.relocs.items[sym.reloc_offset..][0..sym.reloc_count]) |*rel| {
            const dest = offset_lookup[@intFromEnum(rel.target)];
            const jump = @as(i64, dest) - (rel.offset - sym.offset + olp);
            const location: usize = @intCast(rel.offset + @as(u32, @intCast(rel.addend)));

            @memcpy(
                self.code.items[location..][0..rel.slot_size],
                @as(*const [8]u8, @ptrCast(&jump))[0..rel.slot_size],
            );
        }
    };

    var sym_count: usize = 0;
    for (self.syms.items) |sym| {
        sym_count += @intFromBool(sym.kind != .invalid);
    }

    try writer.writeStruct(ExecHeader{
        .code_length = lengths.func,
        .data_length = lengths.data,
        .debug_length = sym_count * @sizeOf(Symbol) + self.names.items.len + 1,
        .symbol_count = sym_count,
    });

    inline for (sets) |v| {
        for (self.syms.items) |sym| if (sym.kind == v) {
            try writer.writeAll(self.code.items[sym.offset..][0..sym.size]);
        };
    }

    for (offset_lookup, self.syms.items) |off, sym| {
        try writer.writeStruct(Symbol{
            .name = sym.name + 1,
            .offset = off,
            .kind = switch (sym.kind) {
                .func => .func,
                .data, .prealloc => .data,
                .invalid => continue,
            },
        });
    }

    try writer.writeByte(0);
    try writer.writeAll(self.names.items);
}
