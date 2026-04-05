pub const Builder = @import("backend/Builder.zig");
pub const Machine = @import("backend/Machine.zig");
pub const Regalloc = @import("backend/Regalloc.zig");
pub const mem2reg = @import("backend/mem2reg.zig");
pub const gcm = @import("backend/gcm.zig");
pub const static_anal = @import("backend/static_anal.zig");
pub const inliner = @import("backend/inliner.zig");
pub const graph = @import("backend/graph.zig");

pub const hbvm = opaque {
    pub const Vm = @import("hbvm/Vm.zig");
    pub const isa = @import("hbvm/isa.zig");
    pub const HbvmGen = @import("hbvm/HbvmGen.zig");
    pub const object = @import("hbvm/object.zig");
};

pub const x86_64 = opaque {
    pub const X86_64Gen = @import("x86_64/X86_64Gen.zig");
};

pub const wasm = opaque {
    pub const WasmGen = @import("wasm/WasmGen.zig");
    pub const object = @import("wasm/object.zig");
};

pub const object = opaque {
    pub const elf = @import("object/elf.zig");
    pub const coff = @import("object/coff.zig");

    pub const Arch = enum {
        x86_64,
    };
};

pub const dwarf = @import("dwarf.zig");

pub const utils = @import("utils-lib");

const std = @import("std");

pub const LineIndex = struct {
    nlines: []const u32,

    pub fn lineCol(self: LineIndex, pos: u32) struct { u32, u32 } {
        var start: usize, var end = .{ 0, self.nlines.len };

        while (start < end) {
            const mid = (start + end) / 2;
            if (pos < self.nlines[mid]) {
                end = mid;
            } else {
                start = mid + 1;
            }
        }

        return .{ @intCast(start), pos - self.nlines[start - 1] };
    }

    pub fn init(file_content: []const u8, arena: *utils.Arena) LineIndex {
        var line_count: usize = 1;
        for (file_content) |c| {
            if (c == '\n') line_count += 1;
        }

        var nlines = arena.alloc(u32, line_count);
        nlines[0] = 0;

        line_count = 1;
        for (file_content, 0..) |c, i| {
            if (c == '\n') {
                nlines[line_count] = @intCast(i + 1);
                line_count += 1;
            }
        }

        return .{ .nlines = nlines };
    }
};

test LineIndex {
    const file_content =
        \\akjdshkdfj
        \\ksjdhks
        \\akjdsk
        \\akjdshkdfj
        \\ksjdhks
        \\akjdsk
    ;

    var arena = utils.Arena.init(4096);
    defer arena.deinit();

    const line_index = LineIndex.init(file_content, &arena);

    var line: u32 = 1;
    var last_nl: usize = 0;
    for (file_content, 0..) |c, i| {
        const lin, const col = line_index.lineCol(@intCast(i));
        try std.testing.expectEqual(line, lin);
        try std.testing.expectEqual(i - last_nl, col);
        if (c == '\n') {
            line += 1;
            last_nl = i + 1;
        }
    }
}
