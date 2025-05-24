const std = @import("std");

const hb = @import("hb");
const static_anal = hb.backend.static_anal;
const Arena = hb.utils.Arena;

pub fn main() !void {
    Arena.initScratch(1024 * 1024 * 10);
    defer Arena.deinitScratch();

    var gpa_impl = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_impl.deinit();

    var opts = hb.CompileOptions{
        .gpa = gpa_impl.allocator(),
        .diagnostics = std.io.getStdErr().writer().any(),
        .colors = std.io.tty.detectConfig(std.io.getStdOut()),
        .output = std.io.getStdOut().writer().any(),
    };
    defer opts.deinit();

    var cli_buff: [1024 * 8]u8 = undefined;
    var cli_scratch = std.heap.FixedBufferAllocator.init(&cli_buff);

    try opts.loadCli(cli_scratch.allocator());

    var arena = (try hb.compile(opts)).arena;
    arena.deinit();
}
