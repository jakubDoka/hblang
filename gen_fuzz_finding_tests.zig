const std = @import("std");

pub fn main() !void {
    var arena_state = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const arena = arena_state.allocator();

    const args = try std.process.argsAlloc(arena);
    const root, const case_dir, const switch_arg, const out = args[1..5].*;

    const out_file = try std.fs.cwd().createFile(out, .{});
    defer out_file.close();
    const writer = out_file.writer();

    try writer.print(
        \\const root = @import("../{s}");
        \\
        \\
    , .{root});

    if (std.mem.eql(u8, switch_arg, "disabled")) return;

    var crash_dir = try std.fs.openDirAbsolute(case_dir, .{});
    crash_dir = try crash_dir.openDir("default/crashes", .{ .iterate = true });

    var escaped = std.ArrayList(u8).init(arena);
    var iter = crash_dir.iterate();
    while (try iter.next()) |file| {
        if (!std.mem.startsWith(u8, file.name, "id:")) continue;
        const segment = try crash_dir.readFileAlloc(arena, file.name, 1024 * 1024);

        const name = file.name;
        var body = segment;
        body = try std.mem.replaceOwned(u8, arena, body, "\\", "\\\\");

        escaped.items.len = 0;
        for (body) |c| {
            if (std.ascii.isPrint(c)) {
                try escaped.append(c);
            } else {
                try escaped.writer().print("\\x{x:02}", .{c});
            }
        }
        body = escaped.items;
        body = try std.mem.replaceOwned(u8, arena, body, "\"", "\\\"");

        try writer.print(
            \\test "{s}" {{
            \\    try root.runFuzzFindingTest(
            \\        "{s}",
            \\        "{s}",
            \\
        ,
            .{ name, name, body },
        );

        try writer.writeAll(
            \\    );
            \\}
            \\
            \\
        );
    }
}
