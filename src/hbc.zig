const std = @import("std");

const hb = @import("hb");

pub fn main() !void {
    const extra_threads = parseCliArgs(null, null).extra_threads + 1;

    const thread_count = @min(extra_threads, std.Thread.getCpuCount() catch 1);
    hb.utils.lane.boot(thread_count, {}, entry);
}

threadlocal var cli_buff: [1024 * 8]u8 = undefined;
fn parseCliArgs(diagnostics: ?*std.Io.Writer, output: ?*std.Io.Writer) hb.CompileOptions {
    var opts = hb.CompileOptions{
        .diagnostics = diagnostics,
        .error_colors = std.io.tty.detectConfig(std.fs.File.stderr()),
        .colors = std.io.tty.detectConfig(std.fs.File.stdout()),
        .output = output,
    };

    var cli_scratch = std.heap.FixedBufferAllocator.init(&cli_buff);

    opts.loadCli(cli_scratch.allocator()) catch {
        opts.logDiag(
            "failed to load cli arguments (OOM)\n",
            .{},
        );
        if (diagnostics) |d| d.flush() catch unreachable;
    };

    return opts;
}

threadlocal var err_buffer: [1024 * 4]u8 = undefined;
threadlocal var out_buffer: [1024 * 4]u8 = undefined;
fn entry(_: void) void {
    var diag_writer = std.fs.File.stderr().writer(&err_buffer);
    var out_writer = std.fs.File.stdout().writer(&out_buffer);

    const opts = parseCliArgs(&diag_writer.interface, &out_writer.interface);

    hb.utils.Arena.initScratch(opts.scratch_memory);

    for (0..opts.benchmark_rounds) |_| {
        hb.compile(opts) catch |err| switch (err) {
            error.Failed => {
                diag_writer.interface.flush() catch {};
                if (hb.utils.lane.isRoot()) std.process.exit(1);
            },
            else => unreachable,
        };
    }
}
