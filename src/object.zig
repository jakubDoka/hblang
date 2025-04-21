const std = @import("std");

pub const Coff = struct {
    pub const FileHeader = extern struct {
        Machine: Machine,
        NumberOfSections: u16 = undefined,
        TimeDateStamp: u32,
        PointerToSymbolTable: u32 = undefined,
        NumberOfSymbols: u32 = undefined,
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

        pub fn flush(self: Builder, header: *FileHeader, writer: std.io.AnyWriter) !void {
            header.NumberOfSections = 1;
            header.NumberOfSymbols = @intCast(self.symbol_table.items.len);
            const section_data_start = @sizeOf(FileHeader) + @sizeOf(SectionHeader);
            header.PointerToSymbolTable = @intCast(section_data_start +
                self.text.items.len);

            try writer.writeStruct(header.*);

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

    var builder = Coff.Builder{};

    const main_fn = Coff.Symbol{
        .Name = try builder.addName(arena, "main"),
        .Value = @intCast(builder.text.items.len),
        .SectionNumber = @enumFromInt(1),
        .Type = .FUNCTION,
        .StorageClass = .EXTERNAL,
        .NumberOfAuxSymbols = 0,
    };
    try builder.symbol_table.append(arena, main_fn);

    // Machine code: xor eax, eax; ret
    const code = [_]u8{ 0xB8, 0x45, 0x00, 0x00, 0x00, 0xC3 };
    try builder.text.appendSlice(arena, &code);

    var header = Coff.FileHeader{ .Machine = .AMD64, .TimeDateStamp = @intCast(std.time.timestamp()) };

    try builder.flush(&header, writer.any());

    try stdout.print("PE/COFF object written to obj.obj\n", .{});
}
