const std = @import("std");
const root = @import("hb");
const Mach = root.backend.Machine;

const WasmGen = @import("WasmGen.zig");

pub const Header = extern struct {
    magic: [4]u8 = "\x00asm".*,
    version: u32 = 1,
};

pub const SectionId = enum(u8) {
    custom = 0,
    type,
    import,
    function,
    table,
    memory,
    global,
    @"export",
    start,
    element,
    code,
    data,
    data_count,
    tag,

    pub fn raw(self: SectionId) u8 {
        return @intFromEnum(self);
    }
};

pub const Type = enum(u8) {
    fnc = 0x60,
    vec = 0x7b,
    f64 = 0x7c,
    f32 = 0x7d,
    i64 = 0x7f,
    i32 = 0x7e,
};

pub const SigLenTy = u32;
pub fn parseFunction(raw: []const u8) [2][]const u8 {
    const sig_len: SigLenTy = @bitCast(raw[0..@sizeOf(SigLenTy)].*);
    return .{
        raw[@sizeOf(SigLenTy)..][0..sig_len],
        raw[@sizeOf(SigLenTy) + sig_len ..],
    };
}

pub fn flush(self: Mach.Data, out: *std.Io.Writer) !void {
    try out.writeStruct(Header{}, .little);

    var type_section_size: u64 = 0;
    var func_section_size: u64 = 0;
    var func_count: u32 = 0;
    for (self.syms.items) |s| {
        if (s.kind != .func) continue;

        const sig, const body = parseFunction(self.code.items[s.offset..][0..s.size]);
        type_section_size += sig.len;
        func_section_size += body.len;
        func_count += 1;
    }

    try out.writeStruct(SectionId.type, .little);
    try out.writeUleb128(type_section_size);
    {
        try out.writeUleb128(func_count);
        for (self.syms.items) |s| {
            if (s.kind != .func) continue;
            const sig, _ = parseFunction(self.code.items[s.offset..][0..s.size]);
            try out.writeAll(sig);
        }
    }

    try out.writeStruct(SectionId.function, .little);
    try out.writeUleb128(func_section_size);
    {
        try out.writeUleb128(func_count);
        for (self.syms.items) |s| {
            if (s.kind != .func) continue;
            _, const body = parseFunction(self.code.items[s.offset..][0..s.size]);
            try out.writeUleb128(body.len);
            try out.writeAll(body);
        }
    }

    for (self.syms.items) |s| {
        std.debug.assert(s.kind == .func or s.kind == .invalid);
    }

    try out.flush();
}

