const std = @import("std");

pub fn captureStdOut(run: *std.Build.Step.Run, basename: []const u8) std.Build.LazyPath {
    std.debug.assert(run.stdio != .inherit);

    if (run.captured_stdout) |output| return .{ .generated = .{ .file = &output.generated_file } };

    const output = run.step.owner.allocator.create(std.Build.Step.Run.Output) catch @panic("OOM");
    output.* = .{
        .prefix = "",
        .basename = basename,
        .generated_file = .{ .step = &run.step },
    };
    run.captured_stdout = output;
    return .{ .generated = .{ .file = &output.generated_file } };
}

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const hblang = b.dependency("hblang", .{
        .target = target,
        .optimize = optimize,
    });
    const hbc = hblang.artifact("hbc");
    const run_hbc = b.addRunArtifact(hbc);
    run_hbc.addFileArg(b.path("main.hb"));
    run_hbc.addArg("--target");
    run_hbc.addArg("x86_64-linux");
    run_hbc.addArg("--optimizations");
    run_hbc.addArg("release");
    run_hbc.addArg("--mangle-terminal");
    const main_obj = captureStdOut(run_hbc, "main.o");

    const raylib_dep = b.dependency("raylib", .{
        .target = target,
        .optimize = optimize,
    });
    const raylib = raylib_dep.artifact("raylib");

    const exe = b.addExecutable(.{
        .name = "example",
        .target = target,
        .optimize = optimize,
    });

    exe.addObjectFile(main_obj);
    exe.linkLibrary(raylib);

    const run = b.step("run", "run the example");
    const run_exe = b.addRunArtifact(exe);
    run.dependOn(&run_exe.step);
}
