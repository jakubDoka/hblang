const std = @import("std");

pub fn build(b: *std.Build) !void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const lib = b.addStaticLibrary(.{
        .name = "hblang",
        .root_source_file = b.path("lib.zig"),
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(lib);

    const exe = b.addExecutable(.{
        .name = "hblang",
        .root_source_file = b.path("main.zig"),
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(exe);

    const vendored_tests = vendored_tests: {
        const grn = b.addExecutable(.{
            .name = "gen_tests.zig",
            .root_source_file = b.path("gen_vendored_tests.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
        });

        const run_gen = b.addRunArtifact(grn);
        run_gen.has_side_effects = true;
        run_gen.addDirectoryArg(b.path("vendored-tests"));
        run_gen.addArg("tests.zig");
        run_gen.addArg("hbc-tests");
        const out = run_gen.addOutputFileArg("vendored_tests.zig");
        break :vendored_tests &b.addInstallFile(out, "vendored_tests.zig").step;
    };

    const tests = example_tests: {
        const gen = b.addExecutable(.{
            .name = "gen_tests.zig",
            .root_source_file = b.path("gen_tests.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
        });

        const run_gen = b.addRunArtifact(gen);
        run_gen.has_side_effects = true;
        run_gen.addFileArg(b.path("README.md"));
        run_gen.addArg("tests.zig");
        const out = run_gen.addOutputFileArg("tests.zig");
        const installed = b.addInstallFile(out, "tests.zig");

        {
            const rdm_stat = try std.fs.cwd().statFile("README.md");
            const stat = if (std.fs.cwd().statFile("zig-out/tests.zig")) |s| s.mtime else |_| 0;
            run_gen.has_side_effects = rdm_stat.mtime > stat;
        }

        break :example_tests &installed.step;
    };

    const fuzz = b.addExecutable(.{
        .name = "fuzz",
        .root_source_file = b.path("fuzz.zig"),
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(fuzz);

    const fuzz_step = b.step("fuzz", "guzz");

    fuzz_step.dependOn(&b.addInstallArtifact(fuzz, .{}).step);
    fuzz_step.dependOn(&b.addRunArtifact(fuzz).step);

    const check_unit_tests = b.addTest(.{
        .root_source_file = b.path("tests.zig"),
        .target = b.graph.host,
        .optimize = optimize,
    });
    check_unit_tests.step.dependOn(vendored_tests);
    check_unit_tests.step.dependOn(tests);

    const check_step = b.step("check", "Run the app");
    check_step.dependOn(&check_unit_tests.step);

    const test_filter = b.option([]const u8, "tf", "passed as a filter to tests");

    const unit_tests = b.addTest(.{
        .root_source_file = b.path("tests.zig"),
        .target = b.graph.host,
        .optimize = optimize,
        .filter = test_filter,
    });
    unit_tests.step.dependOn(vendored_tests);
    unit_tests.step.dependOn(tests);

    const test_step = b.step("test", "Run the app");
    test_step.dependOn(&b.addRunArtifact(unit_tests).step);
}
