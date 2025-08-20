const std = @import("std");

pub fn main() !void {
    var arena_state = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const arena = arena_state.allocator();

    const args = try std.process.argsAlloc(arena);
    const vendored_tests, const example_dir, const out = args[1..4].*;

    const out_file = try std.fs.cwd().createFile(out, .{});
    defer out_file.close();
    var buffer: [1024 * 4]u8 = undefined;
    var writer = out_file.writer(&buffer);

    try writer.interface.print(
        \\const utils = @import("utils");
        \\
        \\
    , .{});

    const cwd = try std.fs.cwd().realpathAlloc(arena, "vendored-tests");

    const path_projections = std.StaticStringMap([]const [2][]const u8).initComptime(.{
        .{ "hblsp", &.{.{ "lily", "vendored-tests/hblsp/lily/src/lib.hb" }} },
    });

    var vendored = try std.fs.cwd().openDir(vendored_tests, .{ .iterate = true });
    var walker = vendored.iterate();
    while (try walker.next()) |node| {
        if (node.kind != .directory) std.debug.panic("vendored dir can only contain directories {s}", .{node.name});

        var test_args = std.ArrayList(u8).empty;
        const pwriter = test_args.writer(arena);
        {
            const projs = path_projections.get(node.name) orelse &.{};
            try pwriter.writeAll("&.{");
            for (projs) |proj| {
                try pwriter.print(".{{\"{s}\", \"{s}\"}},", .{ proj[0], proj[1] });
            }
            try pwriter.writeAll("}");
        }

        const example_dir_name = try std.fs.path.join(arena, &.{ node.name, example_dir });
        var dir = vendored.openDir(example_dir_name, .{ .iterate = true }) catch continue;
        var example_walker = try dir.walk(arena);
        while (try example_walker.next()) |example| {
            if (example.kind != .file) continue;
            if (!std.mem.endsWith(u8, example.basename, ".hb")) continue;

            const path = try std.fs.path.join(arena, &.{ vendored_tests, node.name, example_dir, example.path });
            const name = try std.mem.replaceOwned(u8, arena, path, "\\", "\\\\");
            try writer.interface.print(
                \\test "{s}" {{
                \\    try utils.runVendoredTest("{s}", {s});
                \\}}
                \\
                \\
            , .{
                try std.mem.replaceOwned(u8, arena, name[cwd.len..], example_dir_name, ""),
                name,
                test_args.items,
            });
        }
    }

    try writer.interface.flush();
}
