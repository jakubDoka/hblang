const std = @import("std");

pub fn main() !void {
    var arena_state = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const arena = arena_state.allocator();

    const args = try std.process.argsAlloc(arena);
    const vendored_tests, const root, const example_dir, const out = args[1..5].*;

    const out_file = try std.fs.cwd().createFile(out, .{});
    defer out_file.close();
    const writer = out_file.writer();

    try writer.print(
        \\const root = @import("../{s}");
        \\
        \\
    , .{root});

    var stack = std.ArrayList([]const u8).init(arena);
    var vendored = try std.fs.cwd().openDir(vendored_tests, .{ .iterate = true });
    var walker = vendored.iterate();
    while (try walker.next()) |node| {
        if (node.kind != .directory) std.debug.panic("vendored dir can only contain directories {s}", .{node.name});

        try stack.append(try std.fs.path.join(arena, &.{ node.name, example_dir }));
        while (stack.pop()) |path| {
            var edir = try vendored.openDir(path, .{ .iterate = true });
            var ewalker = edir.iterate();
            while (try ewalker.next()) |example| {
                if (example.kind == .directory) {
                    try stack.append(try std.fs.path.join(arena, &.{ path, example.name }));
                }
                if (example.kind != .file) continue;
                if (!std.mem.endsWith(u8, example.name, ".hb")) continue;

                const name = try std.fs.path.join(arena, &.{ vendored_tests, path, example.name });
                try writer.print(
                    \\test "{s}" {{
                    \\    try root.runVendoredTest("{s}");
                    \\}}
                    \\
                    \\
                , .{ name, name });
            }
        }
    }
}
