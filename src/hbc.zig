const std = @import("std");

const hb = @import("hb");

var cli_buff: [1024 * 8]u8 = undefined;

pub fn main() !void {
    var opts = hb.CompileOptions{
        .diagnostics = std.io.getStdErr().writer().any(),
        .error_colors = std.io.tty.detectConfig(std.io.getStdErr()),
        .colors = std.io.tty.detectConfig(std.io.getStdOut()),
        .output = std.io.getStdOut().writer().any(),
    };

    var cli_scratch = std.heap.FixedBufferAllocator.init(&cli_buff);

    try opts.loadCli(cli_scratch.allocator());

    hb.utils.Arena.initScratch(opts.scratch_memory);

    for (0..opts.benchmark_rounds) |_| {
        hb.compile(opts) catch |err| switch (err) {
            error.Failed => std.process.exit(1),
            else => return err,
        };
    }
}
