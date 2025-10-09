const std = @import("std");
const root = @import("hb");
const Mach = root.backend.Machine;

const WasmGen = @import("WasmGen.zig");
const uleb128Size = root.dwarf.uleb128Size;

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

pub const NameSectionId = enum(u8) {
    module = 0,
    function,
    local,
    type,
    field,
    tag,

    pub fn raw(self: NameSectionId) u8 {
        return @intFromEnum(self);
    }
};

pub const Type = enum(u8) {
    fnc = 0x60,
    vec = 0x7b,
    f64 = 0x7c,
    f32 = 0x7d,
    i64 = 0x7e,
    i32 = 0x7f,

    pub fn raw(self: Type) u8 {
        return @intFromEnum(self);
    }
};

pub const ExternIdx = enum(u8) {
    func = 0,
    table,
    memory,
    global,
    tag,

    pub fn raw(self: ExternIdx) u8 {
        return @intFromEnum(self);
    }
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
    var code_section_size: u64 = 0;
    var name_section_size: u64 = 0;
    var export_section_size: u64 = 0;
    var func_count: u32 = 0;
    var exprted_func_count: u32 = 0;
    for (self.syms.items) |s| {
        if (s.kind != .func) continue;

        const sig, const body = parseFunction(self.code.items[s.offset..][0..s.size]);
        type_section_size += sig.len;
        func_section_size += uleb128Size(func_count);
        code_section_size += uleb128Size(body.len) + body.len;

        const name = self.lookupName(s.name);

        name_section_size += uleb128Size(func_count);
        name_section_size += uleb128Size(name.len) + name.len;

        if (s.linkage == .exported) {
            export_section_size += uleb128Size(name.len) + name.len;
            export_section_size += 1 + uleb128Size(func_count);
            exprted_func_count += 1;
        }

        func_count += 1;
    }

    type_section_size += uleb128Size(func_count);
    func_section_size += uleb128Size(func_count);
    code_section_size += uleb128Size(func_count);

    name_section_size += uleb128Size(func_count); // name map size
    const function_name_subsection_size = name_section_size;
    name_section_size += uleb128Size(function_name_subsection_size); // subsection size
    name_section_size += 1; // subsection id

    export_section_size += uleb128Size(exprted_func_count);

    const name_section_prefix = "name";
    name_section_size += uleb128Size(name_section_prefix.len) + name_section_prefix.len;

    try out.writeByte(SectionId.type.raw());
    try out.writeUleb128(type_section_size);
    {
        try out.writeUleb128(func_count);
        for (self.syms.items) |s| {
            if (s.kind != .func) continue;
            const sig, _ = parseFunction(self.code.items[s.offset..][0..s.size]);
            try out.writeAll(sig);
        }
    }

    try out.writeByte(SectionId.function.raw());
    try out.writeUleb128(func_section_size);
    {
        try out.writeUleb128(func_count);
        var i: u32 = 0;
        for (self.syms.items) |s| {
            if (s.kind != .func) continue;
            try out.writeUleb128(i);
            i += 1;
        }
    }

    try out.writeByte(SectionId.@"export".raw());
    try out.writeUleb128(export_section_size);
    {
        try out.writeUleb128(exprted_func_count);
        var i: u32 = 0;
        for (self.syms.items) |s| {
            if (s.kind != .func) continue;
            defer i += 1;
            if (s.linkage != .exported) continue;
            const name = self.lookupName(s.name);
            try out.writeUleb128(name.len);
            try out.writeAll(name);
            try out.writeByte(ExternIdx.func.raw());
            try out.writeUleb128(i);
        }
    }

    try out.writeByte(SectionId.code.raw());
    try out.writeUleb128(code_section_size);
    {
        try out.writeUleb128(func_count);
        for (self.syms.items) |s| {
            if (s.kind != .func) continue;
            _, const body = parseFunction(self.code.items[s.offset..][0..s.size]);
            try out.writeUleb128(body.len);
            try out.writeAll(body);
        }
    }

    try out.writeByte(SectionId.custom.raw());
    try out.writeUleb128(name_section_size);
    {
        try out.writeUleb128(name_section_prefix.len);
        try out.writeAll(name_section_prefix);

        try out.writeByte(NameSectionId.function.raw());
        try out.writeUleb128(function_name_subsection_size);
        {
            try out.writeUleb128(func_count);
            var i: u32 = 0;
            for (self.syms.items) |s| {
                if (s.kind != .func) continue;
                const name = self.lookupName(s.name);
                try out.writeUleb128(i);
                try out.writeUleb128(name.len);
                try out.writeAll(name);
                i += 1;
            }
        }
    }

    for (self.syms.items) |s| {
        std.debug.assert(s.kind == .func or s.kind == .invalid);
    }

    try out.flush();
}
