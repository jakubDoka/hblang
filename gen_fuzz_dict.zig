const std = @import("std");
const Lexer = @import("src/Lexer.zig");

pub fn main() !void {
    var arena_state = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const arena = arena_state.allocator();

    const args = try std.process.argsAlloc(arena);
    const out, const case_path, const test_out = args[1..4].*;

    generate_dict: {
        var file = try std.fs.createFileAbsolute(out, .{});
        defer file.close();
        const writer = file.writer();

        inline for (@typeInfo(Lexer.Lexeme).@"enum".fields) |f| {
            if (comptime std.ascii.isUpper(f.name[0])) continue;
            if (f.name[0] == '"') {
                try writer.print("\"\\\"\"\n", .{});
            } else {
                try writer.print("\"{s}\"\n", .{f.name});
            }
        }

        break :generate_dict;
    }

    generate_cases: {
        const readme = try std.fs.cwd().readFileAlloc(arena, case_path, 1024 * 1024);

        const out_dir = try std.fs.openDirAbsolute(test_out, .{});

        var iter = std.mem.splitSequence(u8, readme, "#### ");
        while (iter.next()) |segment| {
            const pos = std.mem.indexOf(u8, segment, "\n```hb") orelse continue;
            const name = segment[0..pos];
            const end = std.mem.indexOf(u8, segment[pos + 6 ..], "```\n") orelse continue;
            const body = std.mem.trim(u8, segment[pos + 6 ..][0..end], "\n \t");

            try out_dir.writeFile(.{ .sub_path = name, .data = body });
        }

        break :generate_cases;
    }
}
