const std = @import("std");

const hb = @import("hb");

var cli_buff: [1024 * 8]u8 = undefined;
var err_buffer: [1024 * 4]u8 = undefined;
var out_buffer: [1024 * 4]u8 = undefined;

pub fn main() !void {
    var diag_writer = std.fs.File.stderr().writer(&err_buffer);
    var out_writer = std.fs.File.stdout().writer(&out_buffer);

    var opts = hb.CompileOptions{
        .diagnostics = &diag_writer.interface,
        .error_colors = std.io.tty.detectConfig(std.fs.File.stderr()),
        .colors = std.io.tty.detectConfig(std.fs.File.stdout()),
        .output = &out_writer.interface,
    };

    var cli_scratch = std.heap.FixedBufferAllocator.init(&cli_buff);

    try opts.loadCli(cli_scratch.allocator());

    hb.utils.Arena.initScratch(opts.scratch_memory);

    for (0..opts.benchmark_rounds) |_| {
        hb.compile(opts) catch |err| switch (err) {
            error.Failed => {
                diag_writer.interface.flush() catch {};
                std.process.exit(1);
            },
            else => return err,
        };
    }
}
