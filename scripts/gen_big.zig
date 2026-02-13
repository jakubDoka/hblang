const std = @import("std");

var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
const gpa = arena.allocator();

pub fn main() !void {
    const file_count = 1000;
    const funcs_per_file = 100;
    const dir = "big-source";

    var sbuf: [1024 * 4]u8 = undefined;
    var output = std.fs.File.stdout().writer(&sbuf);

    for (0..file_count) |i| {
        const name = try std.fmt.allocPrint(gpa, "func{}.hb", .{i});
        const path = try std.fs.path.join(gpa, &.{ dir, name });

        try output.interface.print("mod{} := @use(\"{s}\")\n", .{ i, path });

        const file = try std.fs.cwd().createFile(path, .{ .truncate = true });
        defer file.close();

        var fbuf: [1024 * 4]u8 = undefined;
        var fwriter = file.writer(&fbuf);

        for (0..funcs_per_file) |j| {
            try fwriter.interface.print(
                \\func{} := fn(): void {{
                \\    i := 0
                \\    while i < 10 {{
                \\        j := 0
                \\        while j < 10 {{
                \\            k := 0
                \\            while k < 10 {{
                \\                func{}()
                \\                k += 1
                \\            }}
                \\            j += 1
                \\        }}
                \\        i += 1
                \\    }}
                \\}}
                \\
            , .{ j + 1, j });
        }

        try fwriter.interface.print(
            \\func0 := fn(): void {{
            \\}}
            \\main := fn(): void {{
            \\    func{}()
            \\}}
            \\
        , .{funcs_per_file});

        try fwriter.interface.flush();
    }

    try output.interface.writeAll("main := fn(): void {\n");
    for (0..file_count) |i| {
        try output.interface.print("    mod{}.main()\n", .{i});
    }
    try output.interface.writeAll("}\n");

    try output.interface.flush();
}
