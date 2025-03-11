const std = @import("std");

pub fn build(b: *std.Build) !void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe = b.addExecutable(.{
        .name = "hbc",
        .root_source_file = b.path("src/hbc.zig"),
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
            .use_llvm = false,
            .use_lld = false,
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
            .use_llvm = false,
            .use_lld = false,
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

    const check_step = b.step("check", "type check");
    const test_step = b.step("test", "run tests");
    const run_step = b.step("run", "Run the app");

    check_step.dependOn(&exe.step);
    run_step.dependOn(&b.addRunArtifact(exe).step);

    const fuzz_finding_tests = fuzzing: {
        const dict_gen = b.addExecutable(.{
            .name = "gen_fuzz_dict.zig",
            .root_source_file = b.path("gen_fuzz_dict.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
            .use_llvm = false,
            .use_lld = false,
        });

        const run_gen = b.addRunArtifact(dict_gen);
        const dict_out = run_gen.addOutputFileArg("hblang.dict");
        run_gen.addFileArg(b.path("README.md"));
        const cases = run_gen.addOutputDirectoryArg("fuzz-cases");

        const fuzz = b.addStaticLibrary(.{
            .name = "fuzz",
            .root_source_file = b.path("fuzz.zig"),
            .single_threaded = true,
            .target = b.graph.host,
            .optimize = optimize,
            .strip = false,
        });
        fuzz.pie = true;
        fuzz.want_lto = true;
        fuzz.bundle_compiler_rt = true;

        const afl_lto = b.addSystemCommand(&.{ "afl-clang-lto", "-o" });
        const afl_lto_out = afl_lto.addOutputFileArg("fuzz");
        afl_lto.addArtifactArg(fuzz);

        const fuzz_duration = b.option([]const u8, "fuzz-duration", "n seconds to fuzz for") orelse "1";
        const fuzz_tests = b.option(bool, "fuzz-tests", "also run the fuzz findings") orelse false;
        const refuzz = b.option(bool, "refuzz", "rerun fuzzing") orelse b: {
            _ = std.fs.cwd().statFile("zig-out/fuzz_finding_tests.zig") catch break :b true;
            break :b false;
        };

        if (!refuzz) {
            break :fuzzing null;
        }

        const run_afl = b.addSystemCommand(&.{"afl-fuzz"});
        run_afl.addArg("-i");
        run_afl.addDirectoryArg(cases);
        run_afl.addArg("-o");
        const out_dir = run_afl.addOutputDirectoryArg("findings");
        run_afl.addArg("-x");
        run_afl.addFileArg(dict_out);
        run_afl.addArgs(&.{ "-V", fuzz_duration });
        run_afl.addArg("--");
        run_afl.addFileArg(afl_lto_out);

        const gen_finding_tests = b.addExecutable(.{
            .name = "gen_fuzz_finding_tests.zig",
            .root_source_file = b.path("gen_fuzz_finding_tests.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
            .use_llvm = false,
            .use_lld = false,
        });

        const run_gen_finding_tests = b.addRunArtifact(gen_finding_tests);
        run_gen_finding_tests.addArg("tests.zig");
        if (fuzz_tests) {
            run_gen_finding_tests.addDirectoryArg(out_dir);
            run_gen_finding_tests.addArg("enabled");
        } else {
            run_gen_finding_tests.addArg("");
            run_gen_finding_tests.addArg("disabled");
        }
        const out_src = run_gen_finding_tests.addOutputFileArg("fuzz_finding_tests.zig");

        break :fuzzing &b.addInstallFile(out_src, "fuzz_finding_tests.zig").step;
    };

    {
        const unit_tests = b.addTest(.{
            .root_source_file = b.path("tests.zig"),
            .target = b.graph.host,
            .optimize = optimize,
            .use_llvm = false,
            .use_lld = false,
        });
        check_step.dependOn(&unit_tests.step);
    }

    testing: {
        const test_filter = b.option([]const u8, "tf", "passed as a filter to tests");

        const unit_tests = b.addTest(.{
            .root_source_file = b.path("tests.zig"),
            .target = b.graph.host,
            .optimize = optimize,
            .filter = test_filter,
            .use_llvm = false,
            .use_lld = false,
        });
        unit_tests.step.dependOn(vendored_tests);
        unit_tests.step.dependOn(tests);
        if (fuzz_finding_tests) |fft| unit_tests.step.dependOn(fft);

        test_step.dependOn(&b.addRunArtifact(unit_tests).step);
        break :testing;
    }
}
