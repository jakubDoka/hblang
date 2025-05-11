const std = @import("std");

const Object = @This();

arch: Arch,
builder: union(enum) {
    Elf: Elf.Builder,
    Coff: Coff.Builder,
},

pub fn init(os: Os, arch: Arch) Object {
    return .{
        .builder = switch (os) {
            .linux => .{ .Elf = .{} },
            .windows => .{ .Coff = .{} },
        },
        .arch = arch,
    };
}

pub fn declareFunc(self: *Object, gpa: std.mem.Allocator, name: []const u8, linkage: Linkage) !Func {
    switch (self.builder) {
        .Elf => |*e| {
            try e.symbol_table.append(gpa, .{
                .name = try e.addName(gpa, name),
                .info = .{
                    .bind = switch (linkage) {
                        .local => .local,
                        .global => .global,
                        .import => .global,
                    },
                    .type = .func,
                },
                .value = if (linkage == .import) 0 else undefined,
                .size = if (linkage == .import) 0 else undefined,
                .shndx = if (linkage == .import) .undef else @enumFromInt(4),
            });

            return @enumFromInt(e.symbol_table.items.len - 1);
        },
        .Coff => |*e| {
            try e.symbol_table.append(gpa, .{
                .Name = try e.addName(gpa, name),
                .Value = if (linkage == .import) 0 else undefined,
                .SectionNumber = if (linkage == .import) unreachable else @enumFromInt(1),
                .Type = .FUNCTION,
                .StorageClass = switch (linkage) {
                    .global, .import => .EXTERNAL,
                    .local => .STATIC,
                },
                .NumberOfAuxSymbols = 0,
            });

            return @enumFromInt(e.symbol_table.items.len - 1);
        },
    }
}

pub fn defineFunc(self: *Object, gpa: std.mem.Allocator, id: Func, body: []const u8) !void {
    switch (self.builder) {
        .Elf => |*e| {
            const sym = &e.symbol_table.items[@intFromEnum(id)];
            sym.size = body.len;
            sym.value = e.text.items.len;
            try e.text.appendSlice(gpa, body);
        },
        .Coff => |*e| {
            const sym = &e.symbol_table.items[@intFromEnum(id)];
            sym.Value = @intCast(e.text.items.len);
        },
    }
}

pub fn flush(self: *Object, writer: std.io.AnyWriter) !void {
    switch (self.builder) {
        inline else => |*v| try v.flush(self.arch, writer),
    }
}

pub fn deinit(self: *Object, gpa: std.mem.Allocator) void {
    switch (self.builder) {
        inline else => |*v| v.deinit(gpa),
    }
}

pub const Func = enum(u32) { invalid = std.math.maxInt(u32), _ };

pub const Linkage = enum {
    local,
    global,
    import,
};

pub const Os = enum {
    linux,
    windows,
};

pub const Arch = enum {
    x86_64,
};

pub const Elf = struct {
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

    const sections: []const []const u8 = &.{
        "",
        ".shstrtab",
        ".strtab",
        ".symtab",
        ".text",
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
        shnum: Half = sections.len,
        shstrndx: SectionIndex = @enumFromInt(1),
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

    pub const Builder = struct {
        text: std.ArrayListUnmanaged(u8) = .{},
        symbol_table: std.ArrayListUnmanaged(Symbol) = .{},
        string_table: std.ArrayListUnmanaged(u8) = .{},

        pub fn flush(self: *Builder, arch: Arch, writer: std.io.AnyWriter) !void {
            comptime var positions: [sections.len]Word = undefined;
            const section_name_table = comptime b: {
                var fs: []const u8 = "";
                for (sections, &positions) |s, *ps| {
                    ps.* = fs.len;
                    fs = fs ++ s ++ "\x00";
                }
                break :b fs;
            };

            var section_alloc_cursor: usize = 0;

            const header = FileHeader{
                .machine = switch (arch) {
                    .x86_64 => .EM_x86_64,
                },
            };

            try writer.writeStruct(header);
            section_alloc_cursor += @sizeOf(FileHeader);
            section_alloc_cursor += @sizeOf(SectionHeader) * sections.len;

            try writer.writeStruct(SectionHeader.first);

            try writer.writeStruct(SectionHeader{
                .sh_name = positions[1],
                .sh_type = .strtab,
                .sh_flags = .empty,
                .sh_offset = @intCast(section_alloc_cursor),
                .sh_size = @intCast(section_name_table.len),
            });
            section_alloc_cursor += section_name_table.len;

            try writer.writeStruct(SectionHeader{
                .sh_name = positions[2],
                .sh_type = .strtab,
                .sh_flags = .empty,
                .sh_offset = @intCast(section_alloc_cursor),
                .sh_size = @intCast(self.string_table.items.len),
            });
            section_alloc_cursor += self.string_table.items.len;

            std.sort.pdq(Symbol, self.symbol_table.items, {}, struct {
                fn lessThen(_: void, lhs: Symbol, rhs: Symbol) bool {
                    return @intFromEnum(lhs.info.bind) < @intFromEnum(rhs.info.bind);
                }
            }.lessThen);

            var local_sim_count: Word = 0;
            while (self.symbol_table.items[local_sim_count].info.bind == .local)
                local_sim_count += 1;

            try writer.writeStruct(SectionHeader{
                .sh_name = positions[3],
                .sh_type = .symtab,
                .sh_flags = .empty,
                .sh_offset = @intCast(section_alloc_cursor),
                .sh_size = @intCast((self.symbol_table.items.len + 1) * @sizeOf(Symbol)),
                .sh_entsize = @sizeOf(Symbol),
                .sh_link = 2,
                .sh_info = local_sim_count + 1,
            });
            section_alloc_cursor += (self.symbol_table.items.len + 1) * @sizeOf(Symbol);

            try writer.writeStruct(SectionHeader{
                .sh_name = positions[4],
                .sh_type = .progbits,
                .sh_flags = .{ .alloc = true, .execinstr = true, .write = false },
                .sh_offset = @intCast(section_alloc_cursor),
                .sh_size = @intCast(self.text.items.len),
            });
            section_alloc_cursor += self.text.items.len;

            try writer.writeAll(section_name_table);
            try writer.writeAll(self.string_table.items);
            try writer.writeStruct(Symbol.first);
            for (self.symbol_table.items) |s| try writer.writeStruct(s);
            try writer.writeAll(self.text.items);

            self.symbol_table.items.len = 0;
            self.string_table.items.len = 0;
            self.text.items.len = 0;
        }

        pub fn addName(self: *Builder, gpa: std.mem.Allocator, name: []const u8) !SymbolName {
            if (self.string_table.items.len == 0) {
                @branchHint(.cold);
                try self.string_table.append(gpa, 0);
            }

            const pos = self.string_table.items.len;
            try self.string_table.appendSlice(gpa, name);
            try self.string_table.append(gpa, 0);
            return @enumFromInt(pos);
        }

        pub fn deinit(self: *Builder, gpa: std.mem.Allocator) void {
            self.text.deinit(gpa);
            self.symbol_table.deinit(gpa);
            self.string_table.deinit(gpa);
        }
    };
};

pub const Coff = struct {
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

pub fn main() !void {
    const stdout = std.io.getStdOut().writer();
    const file = try std.fs.cwd().createFile("obj.obj", .{});
    defer file.close();
    const writer = file.writer();

    var arena_impl = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const arena = arena_impl.allocator();

    var builder = Object.init(if (true) .linux else .windows, .x86_64);

    const main_fn = try builder.declareFunc(arena, "main", .global);

    // Machine code: xor eax, eax; ret
    const code = [_]u8{ 0xB8, 0x40, 0x00, 0x00, 0x00, 0xC3 };
    try builder.defineFunc(arena, main_fn, &code);

    try builder.flush(writer.any());

    try stdout.print("ELF object written to obj.obj\n", .{});
}
