const std = @import("std");

const Object = @This();
const root = @import("hb");
const dwarf = root.dwarf;

pub const Arch = enum {
    x86_64,
};

pub const Flush = fn (root.backend.Machine.Data, Arch, std.io.AnyWriter) anyerror!void;

pub const elf = enum {
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
        @".bss",

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
        sh_flags: SectionFlags,
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
        write: bool,
        alloc: bool,
        execinstr: bool,
        pad: u29 = 0,

        pub const empty = SectionFlags{ .write = false, .alloc = false, .execinstr = false };
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
            );

            if (s.shndx != .undef) append: {
                const sction = &sctions[@intFromEnum(s.shndx)];
                if (sction == bss) break :append;
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

    pub fn flush(self: root.backend.Machine.Data, arch: Arch, writer_: std.io.AnyWriter) anyerror!void {
        var tmp = root.utils.Arena.scrath(null);
        defer tmp.deinit();

        var writer_impl = std.io.bufferedWriter(writer_);
        const writer = writer_impl.writer();

        var section_alloc_cursor: usize = 0;

        const header = FileHeader{
            .machine = switch (arch) {
                .x86_64 => .EM_x86_64,
            },
        };

        try writer.writeStruct(header);
        section_alloc_cursor += @sizeOf(FileHeader);
        section_alloc_cursor += @sizeOf(SectionHeader) * Sections.fnames.len;

        try writer.writeStruct(SectionHeader.first);

        try writer.writeStruct(SectionHeader{
            .sh_name = Sections.@".shstrtab".pos(),
            .sh_type = .strtab,
            .sh_flags = .empty,
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(Sections.section_specs.fs.len),
        });
        section_alloc_cursor += Sections.section_specs.fs.len;

        try writer.writeStruct(SectionHeader{
            .sh_name = Sections.@".strtab".pos(),
            .sh_type = .strtab,
            .sh_flags = .empty,
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(self.names.items.len + 1),
        });
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
            .sh_flags = .empty,
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(sym_count * @sizeOf(Symbol)),
            .sh_entsize = @sizeOf(Symbol),
            .sh_link = 2,
            .sh_info = local_sim_count + 1,
        });
        section_alloc_cursor += sym_count * @sizeOf(Symbol);

        var text_size: usize = 0;
        var data_size: usize = 0;
        var prealloc_size: usize = 0;
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
            .invalid => {},
        };

        try writer.writeStruct(SectionHeader{
            .sh_name = Sections.@".text".pos(),
            .sh_type = .progbits,
            .sh_flags = .{ .alloc = true, .execinstr = true, .write = false },
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(text_size),
        });
        section_alloc_cursor += text_size;

        try writer.writeStruct(SectionHeader{
            .sh_name = Sections.@".rela.text".pos(),
            .sh_type = .rela,
            .sh_flags = .empty,
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(text_rel_count * @sizeOf(Rela)),
            .sh_entsize = @sizeOf(Rela),
            .sh_info = @intFromEnum(Sections.@".text"),
            .sh_link = @intFromEnum(Sections.@".symtab"),
        });
        section_alloc_cursor += text_rel_count * @sizeOf(Rela);

        try writer.writeStruct(SectionHeader{
            .sh_name = Sections.@".data".pos(),
            .sh_type = .progbits,
            .sh_flags = .{ .alloc = true, .write = true, .execinstr = false },
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(data_size),
        });
        section_alloc_cursor += data_size;

        try writer.writeStruct(SectionHeader{
            .sh_name = Sections.@".rela.data".pos(),
            .sh_type = .rela,
            .sh_flags = .empty,
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(data_rel_count * @sizeOf(Rela)),
            .sh_entsize = @sizeOf(Rela),
            .sh_info = @intFromEnum(Sections.@".data"),
            .sh_link = @intFromEnum(Sections.@".symtab"),
        });
        section_alloc_cursor += data_rel_count * @sizeOf(Rela);

        // compute size of debug info
        // and collect the relocations
        var debug_info_rela = std.ArrayListUnmanaged(Rela){};

        const root_file = "main.hb";

        var debug_size = std.io.countingWriter(std.io.null_writer);

        try debug_size.writer().writeStruct(dwarf.UnitHeader{ .unit_length = 0 });
        {
            const prev_len = debug_size.bytes_written;
            const base_reloc = dwarf.writeCompileUnit(debug_size.writer().any(), root_file, @intCast(text_size));
            try debug_info_rela.append(tmp.arena.allocator(), .{
                .offset = prev_len + base_reloc.text_base_offset,
                .info = .{
                    // grab the func at offset 0
                    // TODO: rather then doing this, maybe emit a symbol
                    .sym = for (self.syms.items, 0..) |s, i| {
                        if (s.kind == .func) break @intCast(i);
                    } else unreachable,
                    .type = .R_X86_64_64,
                },
                .addend = 0,
            });
        }

        for (self.syms.items, 0..) |s, i| {
            if (s.kind != .func) continue;
            const prev_len = debug_size.bytes_written;
            const reloc = dwarf.writeSubprogram(debug_size.writer().any(), self.lookupName(s.name), s.size, s.stack_size);
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

        dwarf.endSiblings(debug_size.writer().any());

        const debug_info_size = debug_size.bytes_written;
        try writer.writeStruct(SectionHeader{
            .sh_name = Sections.@".debug_info".pos(),
            .sh_type = .progbits,
            .sh_flags = .{ .alloc = true, .write = false, .execinstr = false },
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(debug_info_size),
            .sh_link = @intFromEnum(Sections.@".symtab"),
        });
        section_alloc_cursor += debug_info_size;

        try writer.writeStruct(SectionHeader{
            .sh_name = Sections.@".rela.debug_info".pos(),
            .sh_type = .rela,
            .sh_flags = .empty,
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(debug_info_rela.items.len * @sizeOf(Rela)),
            .sh_entsize = @sizeOf(Rela),
            .sh_info = @intFromEnum(Sections.@".debug_info"),
            .sh_link = @intFromEnum(Sections.@".symtab"),
        });
        section_alloc_cursor += debug_info_rela.items.len * @sizeOf(Rela);

        debug_size.bytes_written = 0;
        dwarf.writeAbbrev(debug_size.writer().any());
        try writer.writeStruct(SectionHeader{
            .sh_name = Sections.@".debug_abbrev".pos(),
            .sh_type = .progbits,
            .sh_flags = .{ .alloc = true, .write = false, .execinstr = false },
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(debug_size.bytes_written),
        });
        section_alloc_cursor += debug_size.bytes_written;

        try writer.writeStruct(SectionHeader{
            .sh_name = Sections.@".bss".pos(),
            .sh_type = .nobits,
            .sh_flags = .{ .alloc = true, .write = true, .execinstr = false },
            .sh_offset = @intCast(section_alloc_cursor),
            .sh_size = @intCast(prealloc_size),
            .sh_link = @intFromEnum(Sections.@".symtab"),
        });
        section_alloc_cursor += prealloc_size;

        try writer.writeAll(Sections.section_specs.fs);
        try writer.writeByte(0);
        try writer.writeAll(self.names.items);
        try writer.writeStruct(Symbol.first);

        const projected_offsets = tmp.arena.alloc(u32, projection.len);
        const reloc_proj = tmp.arena.alloc(u32, projection.len);

        var text_offset_cursor: u32 = 0;
        var data_offset_cursor: u32 = 0;
        var prealloc_offset_cursor: u32 = 0;
        for (projection[0 .. sym_count - 1], projected_offsets[0 .. sym_count - 1], 0..) |symid, *poff, i| {
            reloc_proj[symid] = @intCast(i);

            const sym = &self.syms.items[symid];
            poff.* = switch (sym.kind) {
                .func => text_offset_cursor,
                .data => data_offset_cursor,
                .prealloc => prealloc_offset_cursor,
                .invalid => unreachable,
            };
            try writer.writeStruct(elf.Symbol{
                .name = @enumFromInt(sym.name + 1),
                .size = sym.size,
                .value = poff.*,
                .info = .{
                    .type = switch (sym.kind) {
                        .func => .func,
                        .data, .prealloc => .object,
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
                        .invalid => unreachable,
                    },
                    .imported => @enumFromInt(0),
                },
            });

            switch (sym.kind) {
                .func => text_offset_cursor += sym.size,
                .data => data_offset_cursor += sym.size,
                .prealloc => prealloc_offset_cursor += sym.size,
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
                    });
                }
            }
        }

        try writer.writeStruct(dwarf.UnitHeader{ .unit_length = @intCast(debug_info_size - 4) });

        _ = dwarf.writeCompileUnit(writer.any(), root_file, @intCast(text_size));

        for (self.syms.items) |s| {
            if (s.kind != .func) continue;
            _ = dwarf.writeSubprogram(writer.any(), self.lookupName(s.name), s.size, s.stack_size);
        }

        dwarf.endSiblings(writer.any());

        for (debug_info_rela.items) |*rl| {
            rl.info.sym = reloc_proj[rl.info.sym] + 1;
        }

        try writer.writeAll(@ptrCast(debug_info_rela.items));

        dwarf.writeAbbrev(writer.any());

        try writer_impl.flush();
    }
};

pub const coff = struct {
    pub const FileHeader = extern struct {
        Machine: Machine,
        NumberOfSections: u16,
        TimeDateStamp: u32,
        PointerToSymbolTable: u32,
        NumberOfSymbols: u32,
        SizeOfOptionalHeader: u16 = 0,
        Characteristics: Characteristics = .{},

        comptime {
            std.debug.assert(@sizeOf(@This()) == 20);
        }
    };

    pub const Machine = enum(u16) {
        UNKNOWN = 0x0,
        I386 = 0x14c, // 32-bit
        AMD64 = 0x8664, // x86_64
    };

    pub const Characteristics = extern struct {
        _reserved: u16 = 0, // ignored in .obj
    };

    // 📦 Section Header
    pub const SectionHeader = extern struct {
        Name: [8]u8,
        VirtualSize: u32 = 0, // ignored
        VirtualAddress: u32 = 0, // ignored
        SizeOfRawData: u32,
        PointerToRawData: u32,
        PointerToRelocations: u32,
        PointerToLinenumbers: u32 = 0, // deprecated
        NumberOfRelocations: u16,
        NumberOfLinenumbers: u16,
        Characteristics: SectionFlags,

        comptime {
            std.debug.assert(@sizeOf(@This()) == 40);
        }
    };

    pub const SectionFlags = packed struct(u32) {
        p1: u5 = 0,
        cnt_code: bool = false,
        cnt_initializet_data: bool = false,
        cnt_uninitialized_data: bool = false,
        p2: u1 = 0,
        lnk_info_data: bool = false,
        p3: u1 = 0,
        lnk_remove: bool = false,
        lnk_comdat: bool = false,
        p4: u2 = 0,
        gprel: bool = false,
        mem_purgeable: bool = false,
        mem_16bit: bool = false,
        mem_locked: bool = false,
        mem_preload: bool = false,
        align_bytes: u4 = 0,
        lnk_nreloc_ovfl: bool = false,
        mem_discardable: bool = false,
        mem_not_cached: bool = false,
        mem_not_paged: bool = false,
        mem_shared: bool = false,
        mem_execute: bool = false,
        mem_read: bool = false,
        mem_write: bool = false,
    };

    // 🔣 Symbol Table Entry
    pub const Symbol = extern struct {
        Name: SymbolName,
        Value: u32,
        SectionNumber: SectionNumber,
        Type: SymbolType,
        StorageClass: StorageClass,
        NumberOfAuxSymbols: u8,
    };

    pub const SymbolName = extern union {
        ShortName: [8]u8,
        LongName: packed struct {
            Zeroes: u32 = 0,
            Offset: u32,
        },

        comptime {
            std.debug.assert(@sizeOf(@This()) == 8);
        }
    };

    pub const SectionNumber = enum(i16) {
        UNDEFINED = 0,
        // Actual sections start at 1
        ABSOLUTE = -1,
        DEBUG = -2,
        custom = std.math.maxInt(i16),
        _,
    };

    pub const SymbolType = enum(u16) {
        NULL = 0x0000,
        FUNCTION = 0x0020,
    };

    pub const StorageClass = enum(u8) {
        NULL = 0,
        EXTERNAL = 2,
        STATIC = 3,
        FUNCTION = 101,
        END_OF_FUNCTION = 255,
    };

    pub const Builder = struct {
        // +--------------------+
        // | COFF Header        |
        // +--------------------+
        // | Section Headers    |
        // +--------------------+
        // | Raw Section Data   |
        // +--------------------+
        // | Symbol Table       |
        // +--------------------+
        // | String Table       |
        // +--------------------+

        text: std.ArrayListUnmanaged(u8) = .{},

        symbol_table: std.ArrayListUnmanaged(Symbol) = .{},

        string_table: std.ArrayListUnmanaged(u8) = .{},

        pub fn flush(self: *Builder, arch: Arch, writer: std.io.AnyWriter) !void {
            const section_data_start = @sizeOf(FileHeader) + @sizeOf(SectionHeader);
            const header = FileHeader{
                .Machine = switch (arch) {
                    .x86_64 => .AMD64,
                },
                .TimeDateStamp = 0,
                .NumberOfSections = 1,
                .NumberOfSymbols = @intCast(self.symbol_table.items.len),
                .PointerToSymbolTable = @intCast(section_data_start +
                    self.text.items.len),
            };

            try writer.writeStruct(header);

            const text = SectionHeader{
                .Name = splatName(".text").?,
                .SizeOfRawData = @intCast(self.text.items.len),
                .PointerToRawData = @intCast(section_data_start),
                .PointerToRelocations = 0,
                .NumberOfRelocations = 0,
                .NumberOfLinenumbers = 0,
                .Characteristics = .{ .cnt_code = true, .mem_execute = true, .mem_read = true },
            };
            try writer.writeStruct(text);

            try writer.writeAll(self.text.items);

            comptime std.debug.assert(@import("builtin").target.cpu.arch.endian() == .little);

            for (self.symbol_table.items) |sym| {
                try writer.writeAll(std.mem.asBytes(&sym.Name));
                inline for (std.meta.fields(@TypeOf(sym))[1..]) |f| {
                    if (@typeInfo(f.type) == .@"enum") {
                        try writer.writeInt(@typeInfo(f.type).@"enum".tag_type, @intFromEnum(@field(sym, f.name)), .little);
                    } else {
                        try writer.writeInt(f.type, @field(sym, f.name), .little);
                    }
                }
            }

            try writer.writeInt(u32, @intCast(4 + self.string_table.items.len), .little);
            try writer.writeAll(self.string_table.items);

            self.symbol_table.items.len = 0;
            self.string_table.items.len = 0;
            self.text.items.len = 0;
        }

        pub fn addName(self: *Builder, gpa: std.mem.Allocator, name: []const u8) !SymbolName {
            if (splatName(name)) |nm| return .{ .ShortName = nm };

            const pos = self.string_table.items.len;
            try self.string_table.appendSlice(gpa, name);
            try self.string_table.append(gpa, 0);

            return .{ .LongName = .{ .Offset = @intCast(pos) } };
        }

        pub fn deinit(self: *Builder, gpa: std.mem.Allocator) void {
            self.text.deinit(gpa);
            self.symbol_table.deinit(gpa);
            self.string_table.deinit(gpa);
        }
    };

    pub fn splatName(name: []const u8) ?[8]u8 {
        if (name.len > 8) return null;
        var buf: [8]u8 = [_]u8{0} ** 8;
        @memcpy(buf[0..name.len], name);
        return buf;
    }
};

//pub fn main() !void {
//    const stdout = std.io.getStdOut().writer();
//    const file = try std.fs.cwd().createFile("obj.obj", .{});
//    defer file.close();
//    const writer = file.writer();
//
//    var arena_impl = std.heap.ArenaAllocator.init(std.heap.page_allocator);
//    const arena = arena_impl.allocator();
//
//    var builder = Object.init(if (true) .linux else .windows, .x86_64);
//
//    const main_fn = try builder.declareFunc(arena, "main", .global);
//
//    // Machine code: xor eax, eax; ret
//    const code = [_]u8{ 0xB8, 0x40, 0x00, 0x00, 0x00, 0xC3 };
//    try builder.defineFunc(arena, main_fn, &code);
//
//    try builder.flush(writer.any());
//
//    try stdout.print("ELF object written to obj.obj\n", .{});
//}
