const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe = b.addExecutable(.{
        .name = "hblang",
        .root_source_file = b.path("main.zig"),
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(exe);

    const unit_tests = b.addTest(.{
        .root_source_file = b.path("main.zig"),
        .target = target,
        .optimize = optimize,
    });

    unit_tests.step.dependOn(example_tests: {
        const gen = b.addExecutable(.{
            .name = "gen_tests.zig",
            .root_source_file = b.path("gen_tests.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
        });

        const run_gen = b.addRunArtifact(gen);
        run_gen.addFileArg(b.path("README.md"));
        run_gen.addArg("main.zig");
        const out = run_gen.addOutputFileArg("tests.zig");
        break :example_tests &b.addInstallFile(out, "tests.zig").step;
    });

    unit_tests.step.dependOn(vendored_tests: {
        const grn = b.addExecutable(.{
            .name = "gen_tests.zig",
            .root_source_file = b.path("gen_vendored_tests.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
        });

        const run_gen = b.addRunArtifact(grn);
        run_gen.has_side_effects = true;
        run_gen.addDirectoryArg(b.path("vendored-tests"));
        run_gen.addArg("main.zig");
        run_gen.addArg("hbc-tests");
        const out = run_gen.addOutputFileArg("vendored_tests.zig");
        break :vendored_tests &b.addInstallFile(out, "vendored_tests.zig").step;
    });

    const run_lib_unit_tests = b.addRunArtifact(unit_tests);

    const run_step = b.step("run", "Run the app");
    run_step.dependOn(&run_lib_unit_tests.step);
}
