const std = @import("std");

pub const UnitHeader = extern struct {
    unit_length: u32,
    version: u16 = 5,
    unit_type: UnitType = .compile,
    address_size: u8 = 8,
    debug_abbrev_offset: u32 = 0,

    comptime {
        std.debug.assert(std.meta.hasUniqueRepresentation(@This()));
    }
};

pub const UnitType = enum(u8) {
    compile = 0x01,
};

pub fn writeIleb128(buf: *[10]u8, arg: i64) []u8 {
    const Int = @TypeOf(arg);
    const Signed = if (@typeInfo(Int).int.bits < 8) i8 else Int;
    const Unsigned = std.meta.Int(.unsigned, @typeInfo(Signed).int.bits);
    var value: Signed = arg;

    var i: usize = 0;
    while (true) : (i += 1) {
        const unsigned: Unsigned = @bitCast(value);
        const byte: u8 = @truncate(unsigned);
        value >>= 6;
        if (value == -1 or value == 0) {
            buf[i] = byte & 0x7F;
            i += 1;
            break;
        } else {
            value >>= 1;
            buf[i] = byte | 0x80;
        }
    }

    std.debug.assert(i > 0);

    return buf[0..i];
}

pub fn writeUleb128(buf: *[10]u8, arg: u64) []u8 {
    const Int = @TypeOf(arg);
    const Value = if (@typeInfo(Int).int.bits < 8) u8 else Int;
    var value: Value = arg;

    var i: usize = 0;
    while (true) : (i += 1) {
        const byte: u8 = @truncate(value & 0x7f);
        value >>= 7;
        if (value == 0) {
            buf[i] = byte;
            i += 1;
            break;
        } else {
            buf[i] = byte | 0x80;
        }
    }

    std.debug.assert(i > 0);

    return buf[0..i];
}

const compile_unit_abbrev = 1;
const subprogram_abbrev = 2;

pub const CompileUnitRelocs = struct {
    text_base_offset: usize,
};

pub fn writeCompileUnit(writer: *std.Io.Writer, root_file: []const u8, code_size: u32) CompileUnitRelocs {
    errdefer unreachable;

    var buf: [10]u8 = undefined;
    try writer.writeAll(writeUleb128(&buf, compile_unit_abbrev));

    const producer = "fbc\x00";

    try writer.writeAll(producer);
    try writer.writeByte(0x29);

    try writer.writeAll(root_file);
    try writer.writeByte(0);

    try writer.writeInt(u64, 0, .little);
    try writer.writeInt(u32, code_size, .little);

    return CompileUnitRelocs{
        .text_base_offset = writeUleb128(&buf, compile_unit_abbrev).len +
            producer.len +
            1 +
            root_file.len + 1,
    };
}

pub const SubprogramRelocs = struct {
    text_base_offset: usize,
};

pub fn writeSubprogram(writer: *std.Io.Writer, name: []const u8, size: u32, stack_size: u32) SubprogramRelocs {
    errdefer unreachable;

    var buf: [10]u8 = undefined;
    try writer.writeAll(writeUleb128(&buf, subprogram_abbrev));

    try writer.writeAll(name);
    try writer.writeByte(0);

    try writer.writeInt(u64, 0, .little);
    try writer.writeInt(u32, size, .little);

    writeUnwindInfo(writer, stack_size);

    return SubprogramRelocs{
        .text_base_offset = writeUleb128(&buf, subprogram_abbrev).len +
            name.len + 1,
    };
}

pub fn endSiblings(writer: *std.Io.Writer) void {
    errdefer unreachable;
    var buf: [10]u8 = undefined;
    try writer.writeAll(writeUleb128(&buf, 0));
}

pub fn writeAbbrev(writer: *std.Io.Writer) void {
    errdefer unreachable;

    writeAbbrevEntry(writer, compile_unit_abbrev, .compile_unit, true, &.{
        .{ .producer, .string },
        .{ .language, .data1 },
        .{ .name, .string },
        .{ .low_pc, .addr },
        .{ .high_pc, .data4 },
    });

    // generic subprogram
    writeAbbrevEntry(writer, subprogram_abbrev, .subprogram, false, &.{
        .{ .name, .string },
        .{ .low_pc, .addr },
        .{ .high_pc, .data4 },
        .{ .frame_base, .exprloc },
        .{ .call_all_tail_calls, .flag_present },
    });

    var buf: [10]u8 = undefined;
    try writer.writeAll(writeUleb128(&buf, 0));
}

pub fn writeUnwindInfo(writer: *std.Io.Writer, stack_size: u32) void {
    _ = stack_size; // autofix
    errdefer unreachable;

    var buf: [10]u8 = undefined;
    const expr_size = 1;
    try writer.writeAll(writeUleb128(&buf, expr_size));
    try writer.writeByte(@intFromEnum(Op.call_frame_cfa));
}

pub fn writeFrameEntry(writer: *std.Io.Writer, stack_size: u32) void {
    _ = writer; // autofix
    _ = stack_size; // autofix
}

pub fn writeAbbrevEntry(
    writer: *std.Io.Writer,
    code: u64,
    tag: Tag,
    has_children: bool,
    fields: []const struct { Attribute, Form },
) void {
    errdefer unreachable;

    var tbuf: [10]u8 = undefined;

    try writer.writeAll(writeUleb128(&tbuf, code));
    try writer.writeAll(writeUleb128(&tbuf, @intFromEnum(tag)));
    try writer.writeByte(@intFromBool(has_children));

    for (fields) |field| {
        try writer.writeAll(writeUleb128(&tbuf, @intFromEnum(field[0])));
        try writer.writeAll(writeUleb128(&tbuf, @intFromEnum(field[1])));
    }

    try writer.writeAll(&.{ 0, 0 });
}

pub const Op = enum(u8) {
    addr = 0x03, // 1 constant address (size is target specific)
    deref = 0x06, // 0
    const1u = 0x08, // 1 1-byte constant
    const1s = 0x09, // 1 1-byte constant
    const2u = 0x0a, // 1 2-byte constant
    const2s = 0x0b, // 1 2-byte constant
    const4u = 0x0c, // 1 4-byte constant
    const4s = 0x0d, // 1 4-byte constant
    const8u = 0x0e, // 1 8-byte constant
    const8s = 0x0f, // 1 8-byte constant
    constu = 0x10, // 1 ULEB128 constant
    consts = 0x11, // 1 SLEB128 constant
    dup = 0x12, // 0
    drop = 0x13, // 0
    over = 0x14, // 0
    pick = 0x15, // 1 1-byte stack index
    swap = 0x16, // 0
    rot = 0x17, // 0
    xderef = 0x18, // 0
    abs = 0x19, // 0
    @"and" = 0x1a, // 0
    div = 0x1b, // 0
    minus = 0x1c, // 0
    mod = 0x1d, // 0
    mul = 0x1e, // 0
    neg = 0x1f, // 0
    not = 0x20, // 0
    @"or" = 0x21, // 0
    plus = 0x22, // 0
    plus_uconst = 0x23, // 1 ULEB128 addend
    shl = 0x24, // 0
    shr = 0x25, // 0
    shra = 0x26, // 0
    xor = 0x27, // 0
    bra = 0x28, // 1 signed 2-byte constant
    eq = 0x29, // 0
    ge = 0x2a, // 0
    gt = 0x2b, // 0
    le = 0x2c, // 0
    lt = 0x2d, // 0
    ne = 0x2e, // 0
    skip = 0x2f, // 1 signed 2-byte constant
    lit0 = 0x30, // 0
    lit1 = 0x31, // 0 literals 0 .. 31 = . . . (DW_OP_lit0 + literal)
    lit31 = 0x4f, // 0
    reg0 = 0x50, // 0
    reg1 = 0x51, // 0 reg 0 .. 31 = . . . (DW_OP_reg0 + regnum)
    reg31 = 0x6f, // 0
    breg0 = 0x70, // 1 SLEB128 offset
    breg1 = 0x71, // 1 base register 0 .. 31 = ... (DW_OP_breg0 + regnum)
    breg31 = 0x8f, // 1
    regx = 0x90, // 1 ULEB128 register
    fbreg = 0x91, // 1 SLEB128 offset
    bregx = 0x92, // 2 ULEB128 register, SLEB128 offset
    piece = 0x93, // 1 ULEB128 size of piece
    deref_size = 0x94, // 1 1-byte size of data retrieved
    xderef_size = 0x95, // 1 1-byte size of data retrieved
    nop = 0x96, // 0
    push_object_address = 0x97, // 0
    call2 = 0x98, // 1 2-byte offset of DIE
    call4 = 0x99, // 1 4-byte offset of DIE
    call_ref = 0x9a, // 1 4- or 8-byte offset of DIE
    form_tls_address = 0x9b, // 0
    call_frame_cfa = 0x9c, // 0
    bit_piece = 0x9d, // 2 ULEB128 size, ULEB128 offset
    implicit_value = 0x9e, // 2 ULEB128 size, block of that size
    stack_value = 0x9f, // 0
    implicit_pointer = 0xa0, // 2 4- or 8-byte offset of DIE, SLEB128 constant offset
    addrx = 0xa1, // 1 ULEB128 indirect address
    constx = 0xa2, // 1 ULEB128 indirect constant
    entry_value = 0xa3, // 2 ULEB128 size, block of that size
    const_type = 0xa4, // 3 ULEB128 type entry offset, 1-byte size, constant value
    regval_type = 0xa5, // 2 ULEB128 register number, ULEB128 constant offset
    deref_type = 0xa6, // 2 1-byte size, ULEB128 type entry offset
    xderef_type = 0xa7, // 2 1-byte size, ULEB128 type entry offset
    convert = 0xa8, // 1 ULEB128 type entry offset
    reinterpret = 0xa9, // 1 ULEB128 type entry offset
    const lo_user = 0xe0; //
    const hi_user = 0xf; //f
};

pub const Tag = enum(u8) {
    array_type = 0x01,
    class_type = 0x02,
    entry_point = 0x03,
    enumeration_type = 0x04,
    formal_parameter = 0x05,
    imported_declaration = 0x08,
    label = 0x0a,
    lexical_block = 0x0b,
    member = 0x0d,
    pointer_type = 0x0f,
    reference_type = 0x10,
    compile_unit = 0x11,
    string_type = 0x12,
    structure_type = 0x13,
    subroutine_type = 0x15,
    typedef = 0x16,
    union_type = 0x17,
    unspecified_parameters = 0x18,
    variant = 0x19,
    common_block = 0x1a,
    common_inclusion = 0x1b,
    inheritance = 0x1c,
    inlined_subroutine = 0x1d,
    module = 0x1e,
    ptr_to_member_type = 0x1f,
    set_type = 0x20,
    subrange_type = 0x21,
    with_stmt = 0x22,
    access_declaration = 0x23,
    base_type = 0x24,
    catch_block = 0x25,
    const_type = 0x26,
    constant = 0x27,
    enumerator = 0x28,
    file_type = 0x29,
    friend = 0x2a,
    namelist = 0x2b,
    namelist_item = 0x2c,
    packed_type = 0x2d,
    subprogram = 0x2e,
    template_type_parameter = 0x2f,
    template_value_parameter = 0x30,
    thrown_type = 0x31,
    try_block = 0x32,
    variant_part = 0x33,
    variable = 0x34,
    volatile_type = 0x35,
    dwarf_procedure = 0x36,
    restrict_type = 0x37,
    interface_type = 0x38,
    namespace = 0x39,
    imported_module = 0x3a,
    unspecified_type = 0x3b,
    partial_unit = 0x3c,
    imported_unit = 0x3d,
    condition = 0x3f,
    shared_type = 0x40,
    type_unit = 0x41,
    rvalue_reference_type = 0x42,
    template_alias = 0x43,
    coarray_type = 0x44,
    generic_subrange = 0x45,
    dynamic_type = 0x46,
    atomic_type = 0x47,
    call_site = 0x48,
    call_site_parameter = 0x49,
    skeleton_unit = 0x4a,
    immutable_type = 0x4b,
    const lo_user = 0x4080;
    const hi_user = 0xf;
};

pub const Attribute = enum(u8) {
    sibling = 0x01, // reference
    location = 0x02, // exprloc, loclist
    name = 0x03, // string
    ordering = 0x09, // constant
    byte_size = 0x0b, // constant, exprloc, reference
    bit_size = 0x0d, // constant, exprloc, reference
    stmt_list = 0x10, // lineptr
    low_pc = 0x11, // address
    high_pc = 0x12, // address, constant
    language = 0x13, // constant
    discr = 0x15, // reference
    discr_value = 0x16, // constant
    visibility = 0x17, // constant
    import = 0x18, // reference
    string_length = 0x19, // exprloc, loclist, reference
    common_reference = 0x1a, // reference
    comp_dir = 0x1b, // string
    const_value = 0x1c, // block, constant, string
    containing_type = 0x1d, // reference
    default_value = 0x1e, // constant, reference, flag
    @"inline" = 0x20, // constant
    is_optional = 0x21, // flag
    lower_bound = 0x22, // constant, exprloc, reference
    producer = 0x25, // string
    prototyped = 0x27, // flag
    return_addr = 0x2a, // exprloc, loclist
    start_scope = 0x2c, // constant, rnglist
    bit_stride = 0x2e, // constant, exprloc, reference
    upper_bound = 0x2f, // constant, exprloc, reference
    abstract_origin = 0x31, // reference
    accessibility = 0x32, // constant
    address_class = 0x33, // constant
    artificial = 0x34, // flag
    base_types = 0x35, // reference
    calling_convention = 0x36, // constant
    count = 0x37, // constant, exprloc, reference
    data_member_location = 0x38, // constant, exprloc, loclist
    decl_column = 0x39, // constant
    decl_file = 0x3a, // constant
    decl_line = 0x3b, // constant
    declaration = 0x3c, // flag
    discr_list = 0x3d, // block
    encoding = 0x3e, // constant
    external = 0x3f, // flag
    frame_base = 0x40, // exprloc, loclist
    friend = 0x41, // reference
    identifier_case = 0x42, // constant
    namelist_item = 0x44, // reference
    priority = 0x45, // reference
    segment = 0x46, // exprloc, loclist
    specification = 0x47, // reference
    static_link = 0x48, // exprloc, loclist
    type = 0x49, // reference
    use_location = 0x4a, // exprloc, loclist
    variable_parameter = 0x4b, // flag
    virtuality = 0x4c, // constant
    vtable_elem_location = 0x4d, // exprloc, loclist
    allocated = 0x4e, // constant, exprloc, reference
    associated = 0x4f, // constant, exprloc, reference
    data_location = 0x50, // exprloc
    byte_stride = 0x51, // constant, exprloc, reference
    entry_pc = 0x52, // address, constant
    use_UTF8 = 0x53, // flag
    extension = 0x54, // reference
    ranges = 0x55, // rnglist
    trampoline = 0x56, // address, flag, reference, string
    call_column = 0x57, // constant
    call_file = 0x58, // constant
    call_line = 0x59, // constant
    description = 0x5a, // string
    binary_scale = 0x5b, // constant
    decimal_scale = 0x5c, // constant
    small = 0x5d, // reference
    decimal_sign = 0x5e, // constant
    digit_count = 0x5f, // constant
    picture_string = 0x60, // string
    mutable = 0x61, // flag
    threads_scaled = 0x62, // flag
    explicit = 0x63, // flag
    object_pointer = 0x64, // reference
    endianity = 0x65, // constant
    elemental = 0x66, // flag
    pure = 0x67, // flag
    recursive = 0x68, // flag
    signature = 0x69, // reference
    main_subprogram = 0x6a, // flag
    data_bit_offset = 0x6b, // constant
    const_expr = 0x6c, // flag
    enum_class = 0x6d, // flag
    linkage_name = 0x6e, // string
    string_length_bit_size = 0x6f, // constant
    string_length_byte_size = 0x70, // constant
    rank = 0x71, // constant, exprloc
    str_offsets_base = 0x72, // stroffsetsptr
    addr_base = 0x73, // addrptr
    rnglists_base = 0x74, // rnglistsptr
    dwo_name = 0x76, // string
    reference = 0x77, // flag
    rvalue_reference = 0x78, // flag
    macros = 0x79, // macptr
    call_all_calls = 0x7a, // flag
    call_all_source_calls = 0x7b, // flag
    call_all_tail_calls = 0x7c, // flag
    call_return_pc = 0x7d, // address
    call_value = 0x7e, // exprloc
    call_origin = 0x7f, // exprloc
    call_parameter = 0x80, // reference
    call_pc = 0x81, // address
    call_tail_call = 0x82, // flag
    call_target = 0x83, // exprloc
    call_target_clobbered = 0x84, // exprloc
    call_data_location = 0x85, // exprloc
    call_data_value = 0x86, // exprloc
    noreturn = 0x87, // flag
    alignment = 0x88, // constant
    export_symbols = 0x89, // flag
    deleted = 0x8a, // flag
    defaulted = 0x8b, // constant
    loclists_base = 0x8c, // loclistsptr

    const lo_user = 0x2000;
    const hi_user = 0x3f;
};

pub const Form = enum(u8) {
    addr = 0x01, // address
    block2 = 0x03, // block
    block4 = 0x04, // block
    data2 = 0x05, // constant
    data4 = 0x06, // constant
    data8 = 0x07, // constant
    string = 0x08, // string
    block = 0x09, // block
    block1 = 0x0a, // block
    data1 = 0x0b, // constant
    flag = 0x0c, // flag
    sdata = 0x0d, // constant
    strp = 0x0e, // string
    udata = 0x0f, // constant
    ref_addr = 0x10, // reference
    ref1 = 0x11, // reference
    ref2 = 0x12, // reference
    ref4 = 0x13, // reference
    ref8 = 0x14, // reference
    ref_udata = 0x15, // reference
    indirect = 0x16, // (see Section 7.5.3 on page 203)
    sec_offset = 0x17, // addrptr, lineptr, loclist, loclistsptr, macptr, rnglist, rnglistsptr, stroffsetsptr
    exprloc = 0x18, // exprloc
    flag_present = 0x19, // flag
    strx = 0x1a, // string
    addrx = 0x1b, // address
    ref_sup4 = 0x1c, // reference
    strp_sup = 0x1d, // string
    data16 = 0x1e, // constant
    line_strp = 0x1f, // string
    ref_sig8 = 0x20, // reference
    implicit_const = 0x21, // constant
    loclistx = 0x22, // loclist
    rnglistx = 0x23, // rnglist
    ref_sup8 = 0x24, // reference
    strx1 = 0x25, // string
    strx2 = 0x26, // string
    strx3 = 0x27, // string
    strx4 = 0x28, // string
    addrx1 = 0x29, // address
    addrx2 = 0x2a, // address
    addrx3 = 0x2b, // address
    addrx4 = 0x2c, // address
};
