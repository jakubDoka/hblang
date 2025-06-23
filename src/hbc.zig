const std = @import("std");

const hb = @import("hb");
const static_anal = hb.backend.static_anal;
const Arena = hb.utils.Arena;

var gpa_impl = std.heap.DebugAllocator(.{}){};
const gpa = if (std.debug.runtime_safety) gpa_impl.allocator() else std.heap.smp_allocator;
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

    var arena = (hb.compile(opts) catch |err| switch (err) {
        error.Failed => std.process.exit(1),
        else => return err,
    }).arena;
    if (std.debug.runtime_safety) arena.deinit();
}
