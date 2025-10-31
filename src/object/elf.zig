const std = @import("std");

const Object = @This();
const root = @import("hb");
const dwarf = root.dwarf;
const utils = root.utils;
const Arch = root.object.Arch;

const Addr = u64;
const Half = u16;
const Off = u64;
const Sword = i32;
const Word = u32;
const XWord = u64;
const SXWord = i64;
const unsigned_char = u8;

pub const Machine = enum(Half) {
    ET_NONE = 0,
    EM_M32 = 1,
    EM_SPARC = 2,
    EM_386 = 3,
    EM_68K = 4,
    EM_88K = 5,
    EM_860 = 7,
    EM_MIPS = 8,
    EM_MIPS_RS4_BE = 10,
    EM_x86_64 = 0x3e,
    _,
};

pub const Type = enum(Half) {
    none = 0,
    rel = 1,
    exec = 2,
    dyn = 3,
    core = 4,
    loproc = 0xff00,
    hiproc = 0xffff,
};

pub const Sections = enum(Word) {
    @".shstrtab" = 1,
    @".strtab",
    @".symtab",
    @".text",
    @".rela.text",
    @".data",
    @".rela.data",
    @".debug_info",
    @".rela.debug_info",
    @".debug_abbrev",
    @".eh_frame",
    @".rela.eh_frame",
    @".debug_line",
    @".rela.debug_line",
    @".bss",
    @".tbss",

    const fnames = &[_][]const u8{""} ++ std.meta.fieldNames(Sections);

    const section_specs = b: {
        var positions: [fnames.len]Word = undefined;
        var fs: []const u8 = "";
        for (fnames, &positions) |s, *ps| {
            ps.* = fs.len;
            fs = fs ++ s ++ "\x00";
        }
        break :b .{ .fs = fs, .positions = positions };
    };

    pub fn pos(self: Sections) Word {
        return section_specs.positions[@intFromEnum(self)];
    }
};

pub const FileHeader = extern struct {
    ident: extern struct {
        magic: [4]unsigned_char = "\x7fELF".*,
        class: enum(unsigned_char) { none, @"32", @"64" } = .@"64",
        data2: enum(unsigned_char) { none, lsb, msb } = .lsb,
        version: unsigned_char = 1,
        pad: [9]unsigned_char = [_]unsigned_char{0} ** 9,
    } = .{},
    type: Type = .rel,
    machine: Machine,
    version: Word = 1,
    entry: Addr = 0,
    phoff: Off = 0,
    shoff: Off = @sizeOf(FileHeader),
    flags: Word = 0,
    ehsize: Half = @sizeOf(FileHeader),
    phentsize: Half = 0,
    phnum: Half = 0,
    shentsize: Half = @sizeOf(SectionHeader),
    shnum: Half = std.meta.fields(Sections).len + 1,
    shstrndx: SectionIndex = @enumFromInt(@intFromEnum(Sections.@".shstrtab")),
};

pub const Rela = extern struct {
    offset: Addr,
    info: packed struct {
        type: enum(u32) {
            R_X86_64_64 = 1,
            R_X86_64_PC32 = 2,
            R_X86_64_PLT32 = 4,
        } = .R_X86_64_PC32,
        sym: u32,
    },
    addend: SXWord,
};

pub const SectionIndex = enum(Half) {
    undef = 0,
    LOPROC = 0xff00,
    HIPROC = 0xff1f,
    ABS = 0xfff1,
    COMMON = 0xfff2,
    _,
};

pub const SectionType = enum(Word) {
    null = 0,
    progbits = 1,
    symtab = 2,
    strtab = 3,
    rela = 4,
    hash = 5,
    dynamic = 6,
    note = 7,
    nobits = 8,
    rel = 9,
    shlib = 10,
    dynsym = 11,
    loproc = 0x70000000,
    hiproc = 0x7fffffff,
    louser = 0x80000000,
    hiuser = 0xffffffff,
    _,
};

pub const SectionHeader = extern struct {
    sh_name: Word,
    sh_type: SectionType,
    sh_flags: SectionFlags = .{},
    sh_addr: Addr = 0,
    sh_offset: Off,
    sh_size: XWord,
    sh_link: Word = 0,
    sh_info: Word = 0,
    sh_addralign: XWord = 0,
    sh_entsize: XWord = 0,

    pub const first = std.mem.zeroes(SectionHeader);
};

pub const SectionFlags = packed struct(Word) {
    write: bool = false,
    alloc: bool = false,
    execinstr: bool = false,
    merge: bool = false,
    strings: bool = false,
    info_link: bool = false,
    link_order: bool = false,
    os_nonconforming: bool = false,
    group: bool = false,
    tls: bool = false,
    compressed: bool = false,
    pad: u21 = 0,
};

pub const SymbolName = enum(Word) {
    empty,
    _,
};

pub const Symbol = extern struct {
    name: SymbolName,
    info: packed struct(unsigned_char) {
        type: enum(u4) {
            notype = 0,
            object = 1,
            func = 2,
            section = 3,
            file = 4,
            loproc = 13,
            hiproc = 15,
        },
        bind: enum(u4) {
            local = 0,
            global = 1,
            weak = 2,
            loproc = 13,
            hiproc = 15,
        },
    },
    other: unsigned_char = 0,
    shndx: SectionIndex = @enumFromInt(4),
    value: Addr,
    size: XWord,

    pub const first = std.mem.zeroes(Symbol);
};

fn find_section_header(sctions: []align(1) const SectionHeader, shstr_table: []const u8, name: []const u8) ?*align(1) const SectionHeader {
    return for (sctions) |*s| {
        if (std.mem.startsWith(u8, shstr_table[s.sh_name..], name)) break s;
    } else unreachable;
}

pub fn read(bytes: []const u8, gpa: std.mem.Allocator) anyerror!root.backend.Machine.Data {
    const header: FileHeader = @bitCast(bytes[0..@sizeOf(FileHeader)].*);
    const sctions: []align(1) const SectionHeader = @ptrCast(bytes[header.shoff..][0 .. header.shnum * header.shentsize]);
    const shstr_table: []const u8 = bytes[sctions[@intFromEnum(header.shstrndx)].sh_offset..][0..sctions[@intFromEnum(header.shstrndx)].sh_size];

    const sym_tab = find_section_header(sctions, shstr_table, ".symtab").?;
    const symbols: []align(1) const Symbol = @ptrCast(bytes[sym_tab.sh_offset..][0..sym_tab.sh_size]);

    const str_tab = find_section_header(sctions, shstr_table, ".strtab").?;
    const str_table: []const u8 = bytes[str_tab.sh_offset..][0..str_tab.sh_size];

    const bss = find_section_header(sctions, shstr_table, ".bss").?;
    const tbss = find_section_header(sctions, shstr_table, ".tbss").?;

    const text_rela: []align(1) const Rela = if (find_section_header(sctions, shstr_table, ".rela.text")) |relocs|
        @ptrCast(bytes[relocs.sh_offset..][0..relocs.sh_size])
    else
        &.{};

    var data = root.backend.Machine.Data{};

    try data.relocs.ensureTotalCapacity(gpa, text_rela.len);

    for (symbols[1..]) |s| {
        var slot: @TypeOf(data).SymIdx = .invalid;

        var name = str_table[@intFromEnum(s.name)..];
        name = name[0..std.mem.indexOfScalar(u8, name, 0).?];

        _ = try data.startDefineSym(
            gpa,
            &slot,
            name,
            switch (s.info.type) {
                .func => .func,
                .object => .data,
                else => unreachable,
            },
            switch (s.info.bind) {
                .local => if (s.shndx == .undef) .imported else .local,
                .global => .exported,
                else => unreachable,
            },
            true,
            false,
            @splat(0),
        );

        if (s.shndx != .undef) append: {
            const sction = &sctions[@intFromEnum(s.shndx)];
            if (sction == bss or sction == tbss) break :append;
            const section = bytes[sction.sh_offset..][0..sction.sh_size];
            try data.code.appendSlice(gpa, section[s.value..][0..s.size]);
        }

        if (s.info.type == .func) {
            for (text_rela) |r| {
                if (r.offset > s.value and r.offset - s.value <= s.size) {
                    data.relocs.appendAssumeCapacity(.{
                        .target = @enumFromInt(r.info.sym - 1),
                        .offset = @intCast((r.offset - s.value) + data.syms.items[@intFromEnum(slot)].offset),
                        .meta = .{
                            .addend = @intCast(r.addend),
                            .slot_size = switch (r.info.type) {
                                .R_X86_64_PC32, .R_X86_64_PLT32 => .@"4",
                                .R_X86_64_64 => .@"8",
                            },
                        },
                    });
                }
            }
        }
        data.endDefineSym(slot);
    }

    return data;
}

pub fn flush(self: root.backend.Machine.Data, arch: Arch, writer: *std.Io.Writer) anyerror!void {
    var tmp = root.utils.Arena.scrath(null);
    defer tmp.deinit();

    var section_alloc_cursor: usize = 0;

    const header = FileHeader{
        .machine = switch (arch) {
            .x86_64 => .EM_x86_64,
        },
    };

    try writer.writeStruct(header, .little);
    section_alloc_cursor += @sizeOf(FileHeader);
    section_alloc_cursor += @sizeOf(SectionHeader) * Sections.fnames.len;

    // TODO: handle alignment properly

    try writer.writeStruct(SectionHeader.first, .little);

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".shstrtab".pos(),
        .sh_type = .strtab,
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(Sections.section_specs.fs.len),
    }, .little);
    section_alloc_cursor += Sections.section_specs.fs.len;

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".strtab".pos(),
        .sh_type = .strtab,
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(self.names.items.len + 1),
    }, .little);
    section_alloc_cursor += self.names.items.len + 1;

    const projection = tmp.arena.alloc(u32, self.syms.items.len);
    for (0..self.syms.items.len) |i| projection[i] = @intCast(i);
    std.sort.pdq(u32, projection, self.syms.items, struct {
        fn lessThen(syms: []root.backend.Machine.Data.Sym, lhs: u32, rhs: u32) bool {
            return syms[lhs].kind != .invalid and (syms[rhs].kind == .invalid or
                @intFromEnum(syms[lhs].linkage) < @intFromEnum(syms[rhs].linkage));
        }
    }.lessThen);

    var local_sim_count: Word = 0;
    if (projection.len > 0) {
        while (self.syms.items[projection[local_sim_count]].linkage == .local)
            local_sim_count += 1;
    }

    var sym_count: Word = 1;
    for (self.syms.items) |s| sym_count += @intFromBool(s.kind != .invalid);

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".symtab".pos(),
        .sh_type = .symtab,
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(sym_count * @sizeOf(Symbol)),
        .sh_entsize = @sizeOf(Symbol),
        .sh_link = 2,
        .sh_info = local_sim_count + 1,
    }, .little);
    section_alloc_cursor += sym_count * @sizeOf(Symbol);

    var text_size: usize = 0;
    var data_size: usize = 0;
    var prealloc_size: usize = 0;
    var tls_prealloc_size: usize = 0;
    var text_rel_count: usize = 0;
    var data_rel_count: usize = 0;
    for (self.syms.items) |sm| switch (sm.kind) {
        .func => {
            text_size += sm.size;
            text_rel_count += sm.reloc_count;
        },
        .data => {
            data_size += sm.size;
            data_rel_count += sm.reloc_count;
        },
        .prealloc => {
            prealloc_size += sm.size;
        },
        .tls_prealloc => {
            tls_prealloc_size += sm.size;
        },
        .invalid => {},
    };

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".text".pos(),
        .sh_type = .progbits,
        .sh_flags = .{ .alloc = true, .execinstr = true },
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(text_size),
    }, .little);
    section_alloc_cursor += text_size;

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".rela.text".pos(),
        .sh_type = .rela,
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(text_rel_count * @sizeOf(Rela)),
        .sh_entsize = @sizeOf(Rela),
        .sh_info = @intFromEnum(Sections.@".text"),
        .sh_link = @intFromEnum(Sections.@".symtab"),
    }, .little);
    section_alloc_cursor += text_rel_count * @sizeOf(Rela);

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".data".pos(),
        .sh_type = .progbits,
        .sh_flags = .{ .alloc = true, .write = true },
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(data_size),
    }, .little);
    section_alloc_cursor += data_size;

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".rela.data".pos(),
        .sh_type = .rela,
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(data_rel_count * @sizeOf(Rela)),
        .sh_entsize = @sizeOf(Rela),
        .sh_info = @intFromEnum(Sections.@".data"),
        .sh_link = @intFromEnum(Sections.@".symtab"),
    }, .little);
    section_alloc_cursor += data_rel_count * @sizeOf(Rela);

    // compute size of debug info
    // and collect the relocations
    var debug_info_rela = std.ArrayList(Rela){};

    const root_file = "main.hb";

    var debug_size = std.Io.Writer.Discarding.init(&.{});

    try debug_size.writer.writeStruct(dwarf.UnitHeader{ .unit_length = 0 }, .little);
    {
        const prev_len = debug_size.count;
        const base_reloc = dwarf.writeCompileUnit(&debug_size.writer, root_file, @intCast(text_size));
        try debug_info_rela.append(tmp.arena.allocator(), .{
            .offset = prev_len + base_reloc.text_base_offset,
            .info = .{
                // grab the func at offset 0
                // TODO: rather then doing this, maybe emit a symbol
                .sym = for (self.syms.items, 0..) |s, i| {
                    if (s.kind == .func and s.linkage == .local) break @intCast(i);
                } else for (self.syms.items, 0..) |s, i| {
                    if (s.kind == .func) break @intCast(i);
                } else unreachable,
                .type = .R_X86_64_64,
            },
            .addend = 0,
        });
    }

    for (self.syms.items, 0..) |s, i| {
        if (s.kind != .func) continue;
        const prev_len = debug_size.count;
        const reloc = dwarf.writeSubprogram(&debug_size.writer, self.lookupName(s.name), s.size);
        try debug_info_rela.append(tmp.arena.allocator(), .{
            .offset = prev_len + reloc.text_base_offset,
            .info = .{
                // this well get projected later
                .sym = @intCast(i),
                .type = .R_X86_64_64,
            },
            .addend = 0,
        });
    }

    dwarf.endSiblings(&debug_size.writer);

    const debug_info_size = debug_size.count;
    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".debug_info".pos(),
        .sh_type = .progbits,
        .sh_flags = .{ .alloc = true },
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(debug_info_size),
        .sh_link = @intFromEnum(Sections.@".symtab"),
    }, .little);
    section_alloc_cursor += debug_info_size;

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".rela.debug_info".pos(),
        .sh_type = .rela,
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(debug_info_rela.items.len * @sizeOf(Rela)),
        .sh_entsize = @sizeOf(Rela),
        .sh_info = @intFromEnum(Sections.@".debug_info"),
        .sh_link = @intFromEnum(Sections.@".symtab"),
    }, .little);
    section_alloc_cursor += debug_info_rela.items.len * @sizeOf(Rela);

    debug_size.count = 0;
    dwarf.writeAbbrev(&debug_size.writer);
    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".debug_abbrev".pos(),
        .sh_type = .progbits,
        .sh_flags = .{ .alloc = true },
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(debug_size.count),
    }, .little);
    section_alloc_cursor += debug_size.count;

    debug_size.count = 0;

    const eh_align = 8;
    var eh_frame_rela = std.ArrayList(Rela){};

    debug_size.count = 0;
    dwarf.writeCie(&debug_size.writer);
    std.debug.assert(debug_size.count % eh_align == 0);

    for (self.syms.items, 0..) |s, i| {
        if (s.kind != .func) continue;
        const prev_len = debug_size.count;
        const reloc = dwarf.writeFde(&debug_size.writer, @intCast(prev_len), s.size, s.stack_size);
        try eh_frame_rela.append(tmp.arena.allocator(), .{
            .offset = prev_len + reloc.function_address,
            .info = .{
                // this well get projected later
                .sym = @intCast(i),
                .type = .R_X86_64_64,
            },
            .addend = 0,
        });

        std.debug.assert(debug_size.count % eh_align == 0);
    }

    dwarf.endEhFrame(&debug_size.writer);

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".eh_frame".pos(),
        .sh_type = .progbits,
        .sh_flags = .{ .alloc = true },
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(debug_size.count),
    }, .little);
    section_alloc_cursor += debug_size.count;

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".rela.eh_frame".pos(),
        .sh_type = .rela,
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(eh_frame_rela.items.len * @sizeOf(Rela)),
        .sh_entsize = @sizeOf(Rela),
        .sh_info = @intFromEnum(Sections.@".eh_frame"),
        .sh_link = @intFromEnum(Sections.@".symtab"),
    }, .little);
    section_alloc_cursor += eh_frame_rela.items.len * @sizeOf(Rela);

    var line_info_header = dwarf.LineInfoHeader{
        .file_names = @ptrCast(self.files),
    };
    line_info_header.computeHeaderLength();

    debug_size.count = 0;
    line_info_header.write(&debug_size.writer);
    const header_size = debug_size.count;
    try debug_size.writer.writeAll(self.line_info.items);

    line_info_header.unit_length = @intCast(debug_size.count - 4);

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".debug_line".pos(),
        .sh_type = .progbits,
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(debug_size.count),
    }, .little);
    section_alloc_cursor += debug_size.count;

    var retain_idx: usize = 0;
    var line_info_relocs = self.line_info_relocs.items;
    for (line_info_relocs) |rl| {
        if (self.syms.items[@intFromEnum(rl.target)].kind != .func) continue;
        self.line_info_relocs.items[retain_idx] = rl;
        retain_idx += 1;
    }
    line_info_relocs.len = retain_idx;

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".rela.debug_line".pos(),
        .sh_type = .rela,
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(line_info_relocs.len * @sizeOf(Rela)),
        .sh_entsize = @sizeOf(Rela),
        .sh_link = @intFromEnum(Sections.@".symtab"),
        .sh_info = @intFromEnum(Sections.@".debug_line"),
    }, .little);
    section_alloc_cursor += line_info_relocs.len * @sizeOf(Rela);

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".bss".pos(),
        .sh_type = .nobits,
        .sh_flags = .{ .alloc = true, .write = true },
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(prealloc_size),
        .sh_link = @intFromEnum(Sections.@".symtab"),
    }, .little);
    section_alloc_cursor += prealloc_size;

    try writer.writeStruct(SectionHeader{
        .sh_name = Sections.@".tbss".pos(),
        .sh_type = .nobits,
        .sh_flags = .{ .alloc = true, .write = true },
        .sh_offset = @intCast(section_alloc_cursor),
        .sh_size = @intCast(tls_prealloc_size),
        .sh_link = @intFromEnum(Sections.@".symtab"),
    }, .little);
    section_alloc_cursor += tls_prealloc_size;

    try writer.writeAll(Sections.section_specs.fs);
    try writer.writeByte(0);
    try writer.writeAll(self.names.items);
    try writer.writeStruct(Symbol.first, .little);

    const projected_offsets = tmp.arena.alloc(u32, projection.len);
    const reloc_proj = tmp.arena.alloc(u32, projection.len);

    var text_offset_cursor: u32 = 0;
    var data_offset_cursor: u32 = 0;
    var prealloc_offset_cursor: u32 = 0;
    var tls_prealloc_offset_cursor: u32 = 0;
    for (projection[0 .. sym_count - 1], projected_offsets[0 .. sym_count - 1], 0..) |symid, *poff, i| {
        reloc_proj[symid] = @intCast(i);

        const sym = &self.syms.items[symid];
        std.debug.assert(sym.kind != .invalid);
        poff.* = switch (sym.kind) {
            .func => text_offset_cursor,
            .data => data_offset_cursor,
            .prealloc => prealloc_offset_cursor,
            .tls_prealloc => tls_prealloc_offset_cursor,
            .invalid => unreachable,
        };
        try writer.writeStruct(Symbol{
            .name = @enumFromInt(sym.name + 1),
            .size = sym.size,
            .value = poff.*,
            .info = .{
                .type = switch (sym.kind) {
                    .func => .func,
                    .data, .prealloc, .tls_prealloc => .object,
                    .invalid => unreachable,
                },
                .bind = switch (sym.linkage) {
                    .imported, .exported => .global,
                    .local => .local,
                },
            },
            .shndx = switch (sym.linkage) {
                .local, .exported => switch (sym.kind) {
                    .func => @enumFromInt(@intFromEnum(Sections.@".text")),
                    .data => @enumFromInt(@intFromEnum(Sections.@".data")),
                    .prealloc => @enumFromInt(@intFromEnum(Sections.@".bss")),
                    .tls_prealloc => @enumFromInt(@intFromEnum(Sections.@".tbss")),
                    .invalid => unreachable,
                },
                .imported => @enumFromInt(0),
            },
        }, .little);

        switch (sym.kind) {
            .func => text_offset_cursor += sym.size,
            .data => data_offset_cursor += sym.size,
            .prealloc => prealloc_offset_cursor += sym.size,
            .tls_prealloc => tls_prealloc_offset_cursor += sym.size,
            .invalid => unreachable,
        }
    }

    inline for (.{ .func, .data }) |k| {
        for (projection) |symid| {
            const sym = &self.syms.items[symid];
            if (sym.kind != k) continue;
            try writer.writeAll(self.code.items[sym.offset..][0..sym.size]);
        }

        for (projection, projected_offsets) |symid, poff| {
            const sym = &self.syms.items[symid];
            if (sym.kind != k) continue;
            for (self.relocs.items[sym.reloc_offset..][0..sym.reloc_count]) |rl| {
                if (reloc_proj[@intFromEnum(rl.target)] > sym_count) {
                    root.utils.panic("{} {} {} {s}\n", .{ rl.target, self.syms.items[@intFromEnum(rl.target)].kind, sym, self.lookupName(sym.name) });
                }
                try writer.writeStruct(Rela{
                    .offset = rl.offset + poff,
                    .info = .{
                        .type = switch (rl.meta.slot_size) {
                            .@"4" => if (self.syms.items[@intFromEnum(rl.target)].linkage == .imported)
                                .R_X86_64_PLT32
                            else
                                .R_X86_64_PC32,
                            .@"8" => b: {
                                std.debug.assert(k == .data);
                                break :b .R_X86_64_64;
                            },
                        },
                        .sym = reloc_proj[@intFromEnum(rl.target)] + 1,
                    },
                    .addend = rl.meta.addend,
                }, .little);
            }
        }
    }

    try writer.writeStruct(
        dwarf.UnitHeader{ .unit_length = @intCast(debug_info_size - 4) },
        .little,
    );

    _ = dwarf.writeCompileUnit(writer, root_file, @intCast(text_size));
    for (self.syms.items) |s| {
        if (s.kind != .func) continue;
        _ = dwarf.writeSubprogram(writer, self.lookupName(s.name), s.size);
    }
    dwarf.endSiblings(writer);

    for (debug_info_rela.items) |*rl| {
        rl.info.sym = reloc_proj[rl.info.sym] + 1;
    }
    try writer.writeAll(@ptrCast(debug_info_rela.items));

    dwarf.writeAbbrev(writer);

    debug_size.count = 0;
    dwarf.writeCie(writer);
    dwarf.writeCie(&debug_size.writer);
    std.debug.assert(debug_size.count % eh_align == 0);

    for (self.syms.items) |s| {
        if (s.kind != .func) continue;
        const prev_len = debug_size.count;
        _ = dwarf.writeFde(writer, @intCast(prev_len), s.size, s.stack_size);
        _ = dwarf.writeFde(&debug_size.writer, @intCast(prev_len), s.size, s.stack_size);
        std.debug.assert(debug_size.count % eh_align == 0);
    }
    dwarf.endEhFrame(writer);
    dwarf.endEhFrame(&debug_size.writer);

    for (eh_frame_rela.items) |*rl| {
        rl.info.sym = reloc_proj[rl.info.sym] + 1;
    }
    try writer.writeAll(@ptrCast(eh_frame_rela.items));

    line_info_header.write(writer);
    try writer.writeAll(self.line_info.items);

    for (line_info_relocs) |rl| {
        try writer.writeStruct(Rela{
            .offset = @intCast(rl.offset + header_size),
            .info = .{
                .type = switch (rl.meta.slot_size) {
                    .@"4" => .R_X86_64_PC32,
                    .@"8" => .R_X86_64_64,
                },
                .sym = reloc_proj[@intFromEnum(rl.target)] + 1,
            },
            .addend = rl.meta.addend,
        }, .little);
    }

    try writer.flush();
}
