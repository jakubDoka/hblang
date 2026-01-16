const std = @import("std");

pub fn main() !void {
    var arena_state = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const arena = arena_state.allocator();

    const args = try std.process.argsAlloc(arena);
    const case_path, const out = args[1..3].*;

    const case = try std.fs.cwd().readFileAlloc(arena, case_path, 1024 * 1024);

    const out_file = try std.fs.cwd().createFile(out, .{});
    defer out_file.close();
    var buffer: [1024 * 4]u8 = undefined;
    var writer = out_file.writer(&buffer);

    try writer.interface.print(
        \\const utils = @import("utils");
        \\
        \\
    , .{});

    var iter = std.mem.splitSequence(u8, case, "#### ");
    var i: usize = 0;
    while (iter.next()) |segment| {
        const pos = std.mem.indexOf(u8, segment, "\n```hb") orelse continue;
        const name = std.mem.trim(u8, segment[0..pos], "\n\r\t ");
        const end = std.mem.indexOf(u8, segment[pos + 6 ..], "```") orelse continue;
        var body = std.mem.trim(u8, segment[pos + 6 ..][0..end], "\n\r\t ");

        body = try std.mem.replaceOwned(u8, arena, body, "\\", "\\\\");
        body = try std.mem.replaceOwned(u8, arena, body, "    ", "\\t");
        body = try std.mem.replaceOwned(u8, arena, body, "\n", "\\n");
        body = try std.mem.replaceOwned(u8, arena, body, "\r", "\\r");
        body = try std.mem.replaceOwned(u8, arena, body, "\"", "\\\"");

        try writer.interface.print(
            \\test "{s} {x}" {{
            \\    try utils.runTest(
            \\        "{s}",
            \\        "{s}",
            \\        std.testing.allocator,
            \\
        ,
            .{ name, i, name, body },
        );

        try writer.interface.writeAll(
            \\    );
            \\}
            \\
            \\
        );

        i += 1;
    }

    try writer.interface.flush();
}
