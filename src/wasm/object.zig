const std = @import("std");
const root = @import("hb");
const Mach = root.backend.Machine;
const utils = root.utils;

const WasmGen = @import("WasmGen.zig");
const uleb128Size = root.dwarf.uleb128Size;

pub const normal_addend = 0;
pub const fn_ptr_addend = 1;
pub const reloc_int_size = 4;
pub const RelocInt = std.meta.Int(.unsigned, reloc_int_size * 7);

pub const stack_pointer_id = 0;

pub const Header = extern struct {
    magic: [4]u8 = "\x00asm".*,
    version: u32 = 1,
};

pub const SigLenTy = u32;
pub fn parseFunction(raw: []const u8) [2][]const u8 {
    const sig_len: SigLenTy = @bitCast(raw[0..@sizeOf(SigLenTy)].*);
    return .{
        raw[@sizeOf(SigLenTy)..][0..sig_len],
        raw[@sizeOf(SigLenTy) + sig_len ..],
    };
}

pub fn flush(
    self: Mach.Data,
    out: *std.Io.Writer,
    stack_size: u64,
    extra_function_types: []const u8,
    extra_function_type_count: u64,
) !void {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var type_section_size: u64 = extra_function_types.len;
    var import_section_size: u64 = 0;
    var import_count: u32 = 0;
    var func_section_size: u64 = 0;
    var func_count: u32 = 0;
    var table_section_size: u64 = 0;
    var memory_section_size: u64 = 0;
    var memory_count: u64 = 0;
    var global_section_size: u64 = 0;
    var global_count: u64 = 0;
    var export_section_size: u64 = 0;
    var exprted_count: u32 = 0;
    var element_section_size: u64 = 0;
    var code_section_size: u64 = 0;
    var name_section_size: u64 = 0;
    var data_section_size: u64 = 0;
    var global_offsets = tmp.arena.alloc(u32, self.syms.items.len);
    var reloc_ids = tmp.arena.alloc(RelocInt, self.syms.items.len);
    var referenced_funcs = std.AutoArrayHashMapUnmanaged(Mach.Data.SymIdx, void).empty;

    const import_module_name = "env";

    // imports preced the declarations
    for (self.syms.items, 0..) |s, i| {
        if (s.kind != .func or s.linkage != .imported) continue;

        const name = self.lookupName(s.name);

        import_section_size += uleb128Size(import_module_name.len) + import_module_name.len;
        import_section_size += uleb128Size(name.len) + name.len;
        import_section_size += 1 + uleb128Size(extra_function_type_count + import_count);

        type_section_size += s.size;

        reloc_ids[i] = @intCast(import_count);

        import_count += 1;
    }

    for (self.syms.items, 0..) |s, i| {
        if (s.kind != .invalid) {
            for (self.relocs.items[s.reloc_offset..][0..s.reloc_count]) |rel| {
                if (rel.meta.addend != fn_ptr_addend) continue;
                referenced_funcs.put(tmp.arena.allocator(), rel.target, {}) catch unreachable;
            }
        }

        switch (s.kind) {
            .func => {
                if (s.linkage == .imported) continue;

                const sig, const body = parseFunction(self.code.items[s.offset..][0..s.size]);
                const name = self.lookupName(s.name);

                type_section_size += sig.len;

                func_section_size += uleb128Size(extra_function_type_count + import_count + func_count);

                if (s.linkage == .exported) {
                    export_section_size += uleb128Size(name.len) + name.len;
                    export_section_size += 1 + uleb128Size(import_count + func_count);
                    exprted_count += 1;
                }

                code_section_size += uleb128Size(body.len) + body.len;

                name_section_size += uleb128Size(import_count + func_count);
                name_section_size += uleb128Size(name.len) + name.len;

                reloc_ids[i] = @intCast(import_count + func_count);
                func_count += 1;
            },
            .data => {
                global_section_size += 1; // global pointer type
                global_section_size += 1; // immutable
                global_section_size += 1 +
                    uleb128Size(stack_size + data_section_size) + 1; // offset

                global_offsets[i] = @intCast(data_section_size);

                data_section_size += s.size;

                reloc_ids[i] = @intCast(global_count + 1);
                global_count += 1;
            },
            .prealloc, .tls_prealloc => {
                global_count += 1;
            },
            .invalid => {},
        }
    }

    global_count = 0;

    var total_prealloc_size = data_section_size;
    for (self.syms.items, 0..) |s, i| {
        if (s.kind == .prealloc or s.kind == .tls_prealloc) {
            global_section_size += 1; // global pointer type
            global_section_size += 1; // immutable
            global_section_size += 1 +
                uleb128Size(stack_size + total_prealloc_size) + 1; // offset

            global_offsets[i] = @intCast(total_prealloc_size);

            total_prealloc_size += s.size;

            reloc_ids[i] = @intCast(global_count + 1);
            global_count += 1;
        } else if (s.kind == .data) {
            global_count += 1;
        }
    }

    type_section_size += uleb128Size(extra_function_type_count + import_count + func_count);

    import_section_size += uleb128Size(import_count);

    func_section_size += uleb128Size(func_count);

    table_section_size += uleb128Size(1); // always one table

    table_section_size += 1; // funcref
    table_section_size += 1 + uleb128Size(referenced_funcs.entries.len); // no limmit

    memory_count += 1; // global memory, prefixed with stack and global variables
    memory_section_size += uleb128Size(memory_count);
    memory_section_size += 1 +
        uleb128Size(stack_size / std.math.maxInt(u16)); // memory type

    global_count += 1; // stack pointer
    global_section_size += uleb128Size(global_count);
    global_section_size += 1; // stack pointer type
    global_section_size += 1; // stack pointer mutability
    global_section_size += 1 + uleb128Size(stack_size) + 1; // stack pointer initializer

    const stack_pointer_export_name = "__stack_pointer";
    exprted_count += 1;
    export_section_size +=
        uleb128Size(stack_pointer_export_name.len) +
        stack_pointer_export_name.len +
        1 + uleb128Size(0);

    const memory_export_name = "memory";
    exprted_count += 1;
    export_section_size +=
        uleb128Size(memory_export_name.len) +
        memory_export_name.len +
        1 + uleb128Size(0);

    export_section_size += uleb128Size(exprted_count);

    element_section_size += 1; // elem count

    element_section_size += uleb128Size(0); // kind
    element_section_size += 1 + uleb128Size(0) + 1; // offset

    element_section_size += uleb128Size(referenced_funcs.entries.len);
    for (referenced_funcs.entries.items(.key)) |idx| {
        element_section_size += uleb128Size(reloc_ids[@intFromEnum(idx)]);
    }

    code_section_size += uleb128Size(func_count);

    name_section_size += uleb128Size(func_count); // name map size
    const function_name_subsection_size = name_section_size;
    name_section_size += uleb128Size(function_name_subsection_size); // subsection size
    name_section_size += 1; // subsection id
    const name_section_prefix = "name";
    name_section_size += uleb128Size(name_section_prefix.len) +
        name_section_prefix.len;

    const init_data_size = data_section_size;
    data_section_size += uleb128Size(1); // data count
    data_section_size += 1; // tag
    data_section_size += 1 + uleb128Size(stack_size) + 1; // offset
    data_section_size += uleb128Size(init_data_size); // data

    try out.writeStruct(Header{}, .little);

    try out.writeByte(SectionId.type.raw());
    try out.writeUleb128(type_section_size);
    {
        try out.writeUleb128(extra_function_type_count + import_count + func_count);

        try out.writeAll(extra_function_types);

        for (self.syms.items) |s| {
            if (s.kind != .func or s.linkage != .imported) continue;
            try out.writeAll(self.code.items[s.offset..][0..s.size]);
        }

        for (self.syms.items) |s| {
            if (s.kind != .func or s.linkage == .imported) continue;
            const sig, _ = parseFunction(self.code.items[s.offset..][0..s.size]);
            try out.writeAll(sig);
        }
    }

    try out.writeByte(SectionId.import.raw());
    try out.writeUleb128(import_section_size);
    {
        try out.writeUleb128(import_count);

        var i: u32 = 0;
        for (self.syms.items) |s| {
            if (s.kind != .func or s.linkage != .imported) continue;

            try out.writeUleb128(import_module_name.len);
            try out.writeAll(import_module_name);

            const name = self.lookupName(s.name);
            try out.writeUleb128(name.len);
            try out.writeAll(name);

            try out.writeByte(ExternIdx.func.raw());
            try out.writeUleb128(extra_function_type_count + i);
            i += 1;
        }
    }

    try out.writeByte(SectionId.function.raw());
    try out.writeUleb128(func_section_size);
    {
        try out.writeUleb128(func_count);
        var i: u32 = 0;
        for (self.syms.items) |s| {
            if (s.kind != .func or s.linkage == .imported) continue;
            try out.writeUleb128(extra_function_type_count + import_count + i);
            i += 1;
        }
    }

    try out.writeByte(SectionId.table.raw());
    try out.writeUleb128(table_section_size);
    {
        try out.writeUleb128(1);

        try out.writeByte(0x70); // funcref
        try out.writeByte(0); // no limmit
        try out.writeUleb128(referenced_funcs.entries.len);
    }

    try out.writeByte(SectionId.memory.raw());
    try out.writeUleb128(memory_section_size);
    {
        try out.writeUleb128(memory_count);
        try out.writeByte(0); // no limmit
        try out.writeUleb128(std.mem.alignForward(
            u64,
            stack_size + total_prealloc_size,
            std.math.maxInt(u16) + 1,
        ) / std.math.maxInt(u16) + 1);
    }

    try out.writeByte(SectionId.global.raw());
    try out.writeUleb128(global_section_size);
    {
        try out.writeUleb128(global_count);

        try out.writeByte(Type.i64.raw());
        try out.writeByte(1);

        try out.writeByte(opb(.i64_const));
        try out.writeUleb128(stack_size);

        try out.writeByte(opb(.end));

        for (self.syms.items, global_offsets) |s, off| {
            if (s.kind != .data and s.kind != .prealloc and s.kind != .tls_prealloc) continue;

            try out.writeByte(Type.i64.raw());
            try out.writeByte(0);

            try out.writeByte(opb(.i64_const));
            try out.writeUleb128(stack_size + off);
            try out.writeByte(opb(.end));
        }
    }

    try out.writeByte(SectionId.@"export".raw());
    try out.writeUleb128(export_section_size);
    {
        try out.writeUleb128(exprted_count);

        try out.writeUleb128(stack_pointer_export_name.len);
        try out.writeAll(stack_pointer_export_name);
        try out.writeByte(ExternIdx.global.raw());
        try out.writeUleb128(0);

        try out.writeUleb128(memory_export_name.len);
        try out.writeAll(memory_export_name);
        try out.writeByte(ExternIdx.memory.raw());
        try out.writeUleb128(0);

        var i: u32 = import_count;
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

    try out.writeByte(SectionId.element.raw());
    try out.writeUleb128(element_section_size);
    {
        try out.writeUleb128(1);

        try out.writeUleb128(0);
        try out.writeByte(opb(.i32_const));
        try out.writeSleb128(0);
        try out.writeByte(opb(.end));

        try out.writeUleb128(referenced_funcs.entries.len);
        for (referenced_funcs.entries.items(.key)) |idx| {
            try out.writeUleb128(reloc_ids[@intFromEnum(idx)]);
        }
    }

    try out.writeByte(SectionId.code.raw());
    try out.writeUleb128(code_section_size);
    {
        try out.writeUleb128(func_count);
        for (self.syms.items) |s| {
            if (s.kind != .func or s.linkage == .imported) continue;
            const mem = self.code.items[s.offset..][0..s.size];

            for (self.relocs.items[s.reloc_offset..][0..s.reloc_count]) |rel| {
                if (rel.meta.addend == fn_ptr_addend) {
                    const target = referenced_funcs.getIndex(rel.target).?;
                    std.leb.writeSignedFixed(
                        reloc_int_size,
                        mem[rel.offset..][0..reloc_int_size],
                        @intCast(target),
                    );
                } else {
                    std.debug.assert(rel.meta.addend == normal_addend);
                    const target = reloc_ids[@intFromEnum(rel.target)];
                    std.leb.writeUnsignedFixed(
                        reloc_int_size,
                        mem[rel.offset..][0..reloc_int_size],
                        target,
                    );
                }
            }

            _, const body = parseFunction(mem);
            try out.writeUleb128(body.len);
            try out.writeAll(body);
        }
    }

    try out.writeByte(SectionId.data.raw());
    try out.writeUleb128(data_section_size);
    {
        try out.writeUleb128(1); // data count
        try out.writeUleb128(0); // active memory

        // offset
        try out.writeByte(opb(.i32_const));
        try out.writeSleb128(stack_size);
        try out.writeByte(opb(.end));

        // data
        try out.writeUleb128(init_data_size);
        for (self.syms.items) |s| {
            if (s.kind != .data) continue;

            const mem = self.code.items[s.offset..][0..s.size];

            for (self.relocs.items[s.reloc_offset..][0..s.reloc_count]) |rel| {
                if (rel.meta.addend == fn_ptr_addend) {
                    const target: u64 = referenced_funcs.getIndex(rel.target).?;
                    @memcpy(mem[rel.offset..][0..8], std.mem.asBytes(&target));
                } else {
                    const target = global_offsets[@intFromEnum(rel.target)] + stack_size;
                    @memcpy(mem[rel.offset..][0..8], std.mem.asBytes(&target));
                }
            }

            try out.writeAll(mem);
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
            var i: u32 = import_count;
            for (self.syms.items) |s| {
                if (s.kind != .func or s.linkage == .imported) continue;
                try out.writeUleb128(i);
                const name = self.lookupName(s.name);
                try out.writeUleb128(name.len);
                try out.writeAll(name);
                i += 1;
            }
        }
    }

    try out.flush();
}

pub inline fn opb(comptime op: Op) u8 {
    return @intFromEnum(op);
}

pub const Op = enum(u8) {
    @"unreachable" = 0x00,
    nop = 0x01,
    block = 0x02,
    loop = 0x03,
    @"if" = 0x04,
    @"else" = 0x05,

    end = 0x0b,
    br = 0x0c,
    br_if = 0x0d,
    br_table = 0x0e,
    @"return" = 0x0f,
    call = 0x10,
    call_indirect = 0x11,

    drop = 0x1a,
    select = 0x1b,
    select_t = 0x1c,

    local_get = 0x20,
    local_set = 0x21,
    local_tee = 0x22,
    global_get = 0x23,
    global_set = 0x24,

    i32_load = 0x28,
    i64_load = 0x29,
    f32_load = 0x2a,
    f64_load = 0x2b,
    i32_load8_s = 0x2c,
    i32_load8_u = 0x2d,
    i32_load16_s = 0x2e,
    i32_load16_u = 0x2f,
    i64_load8_s = 0x30,
    i64_load8_u = 0x31,
    i64_load16_s = 0x32,
    i64_load16_u = 0x33,
    i64_load32_s = 0x34,
    i64_load32_u = 0x35,
    i32_store = 0x36,
    i64_store = 0x37,
    f32_store = 0x38,
    f64_store = 0x39,
    i32_store8 = 0x3a,
    i32_store16 = 0x3b,
    i64_store8 = 0x3c,
    i64_store16 = 0x3d,
    i64_store32 = 0x3e,
    memory_size = 0x3f,
    memory_grow = 0x40,

    i32_const = 0x41,
    i64_const = 0x42,
    f32_const = 0x43,
    f64_const = 0x44,

    i32_eqz = 0x45,
    i32_eq = 0x46,
    i32_ne = 0x47,
    i32_lt_s = 0x48,
    i32_lt_u = 0x49,
    i32_gt_s = 0x4a,
    i32_gt_u = 0x4b,
    i32_le_s = 0x4c,
    i32_le_u = 0x4d,
    i32_ge_s = 0x4e,
    i32_ge_u = 0x4f,

    i64_eqz = 0x50,
    i64_eq = 0x51,
    i64_ne = 0x52,
    i64_lt_s = 0x53,
    i64_lt_u = 0x54,
    i64_gt_s = 0x55,
    i64_gt_u = 0x56,
    i64_le_s = 0x57,
    i64_le_u = 0x58,
    i64_ge_s = 0x59,
    i64_ge_u = 0x5a,

    f32_eq = 0x5b,
    f32_ne = 0x5c,
    f32_lt = 0x5d,
    f32_gt = 0x5e,
    f32_le = 0x5f,
    f32_ge = 0x60,

    f64_eq = 0x61,
    f64_ne = 0x62,
    f64_lt = 0x63,
    f64_gt = 0x64,
    f64_le = 0x65,
    f64_ge = 0x66,

    i32_clz = 0x67,
    i32_ctz = 0x68,
    i32_popcnt = 0x69,
    i32_add = 0x6a,
    i32_sub = 0x6b,
    i32_mul = 0x6c,
    i32_div_s = 0x6d,
    i32_div_u = 0x6e,
    i32_rem_s = 0x6f,
    i32_rem_u = 0x70,
    i32_and = 0x71,
    i32_or = 0x72,
    i32_xor = 0x73,
    i32_shl = 0x74,
    i32_shr_s = 0x75,
    i32_shr_u = 0x76,
    i32_rotl = 0x77,
    i32_rotr = 0x78,

    i64_clz = 0x79,
    i64_ctz = 0x7a,
    i64_popcnt = 0x7b,
    i64_add = 0x7c,
    i64_sub = 0x7d,
    i64_mul = 0x7e,
    i64_div_s = 0x7f,
    i64_div_u = 0x80,
    i64_rem_s = 0x81,
    i64_rem_u = 0x82,
    i64_and = 0x83,
    i64_or = 0x84,
    i64_xor = 0x85,
    i64_shl = 0x86,
    i64_shr_s = 0x87,
    i64_shr_u = 0x88,
    i64_rotl = 0x89,
    i64_rotr = 0x8a,

    f32_abs = 0x8b,
    f32_neg = 0x8c,
    f32_ceil = 0x8d,
    f32_floor = 0x8e,
    f32_trunc = 0x8f,
    f32_nearest = 0x90,
    f32_sqrt = 0x91,
    f32_add = 0x92,
    f32_sub = 0x93,
    f32_mul = 0x94,
    f32_div = 0x95,
    f32_min = 0x96,
    f32_max = 0x97,
    f32_copysign = 0x98,
    f64_abs = 0x99,
    f64_neg = 0x9a,
    f64_ceil = 0x9b,
    f64_floor = 0x9c,
    f64_trunc = 0x9d,
    f64_nearest = 0x9e,
    f64_sqrt = 0x9f,
    f64_add = 0xa0,
    f64_sub = 0xa1,
    f64_mul = 0xa2,
    f64_div = 0xa3,
    f64_min = 0xa4,
    f64_max = 0xa5,
    f64_copysign = 0xa6,

    i32_wrap_i64 = 0xa7,
    i32_trunc_f32_s = 0xa8,
    i32_trunc_f32_u = 0xa9,
    i32_trunc_f64_s = 0xaa,
    i32_trunc_f64_u = 0xab,
    i64_extend_i32_s = 0xac,
    i64_extend_i32_u = 0xad,
    i64_trunc_f32_s = 0xae,
    i64_trunc_f32_u = 0xaf,
    i64_trunc_f64_s = 0xb0,
    i64_trunc_f64_u = 0xb1,
    f32_convert_i32_s = 0xb2,
    f32_convert_i32_u = 0xb3,
    f32_convert_i64_s = 0xb4,
    f32_convert_i64_u = 0xb5,
    f32_demote_f64 = 0xb6,
    f64_convert_i32_s = 0xb7,
    f64_convert_i32_u = 0xb8,
    f64_convert_i64_s = 0xb9,
    f64_convert_i64_u = 0xba,
    f32_promote_f64 = 0xbb,
    i32_reinterpret_f32 = 0xbc,
    i64_reinterpret_f64 = 0xbd,
    f32_reinterpret_i32 = 0xbe,
    f64_reinterpret_i64 = 0xbf,

    i32_extend8_s = 0xc0,
    i32_extend16_s = 0xc1,
    i64_extend8_s = 0xc2,
    i64_extend16_s = 0xc3,
    i64_extend32_s = 0xc4,

    prefix_fb = 0xfb,
    prefix_fc = 0xfc,
    prefix_fd = 0xfd,
    prefix_fe = 0xfe,

    invalid = 0xff,
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
