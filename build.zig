const std = @import("std");

fn wasmAsset(b: *std.Build, optimize: std.builtin.OptimizeMode, comptime name: []const u8, expeors: []const []const u8) std.Build.LazyPath {
    const exe = b.addExecutable(.{
        .name = name,
        .root_source_file = b.path("src/depell/" ++ name ++ ".zig"),
        .target = b.resolveTargetQuery(.{ .cpu_arch = .wasm32, .os_tag = .freestanding }),
        .optimize = optimize,
    });

    exe.entry = .disabled;
    exe.root_module.export_symbol_names = expeors;

    return exe.getEmittedBin();
}

pub fn build(b: *std.Build) !void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    hbc: {
        const exe = b.addExecutable(.{
            .name = "hbc",
            .root_source_file = b.path("src/hbc.zig"),
            .target = target,
            .optimize = optimize,
        });
        b.installArtifact(exe);

        break :hbc;
    }

    const test_step = b.step("test", "run tests");
    const test_filter = b.option([]const u8, "tf", "passed as a filter to tests");

    vendored_tests: {
        const grn = b.addExecutable(.{
            .name = "gen_vendored_tests",
            .root_source_file = b.path("scripts/gen_vendored_tests.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
            .use_llvm = false,
            .use_lld = false,
        });

        const run_gen = b.addRunArtifact(grn);
        run_gen.has_side_effects = true;
        run_gen.addDirectoryArg(b.path("vendored-tests"));
        run_gen.addArg("hbc-tests");
        const out = run_gen.addOutputFileArg("vendored_tests.zig");

        const test_run = b.addTest(.{
            .name = "vendored_tests",
            .root_source_file = out,
            .target = b.graph.host,
            .optimize = optimize,
            .filter = test_filter,
            .use_llvm = false,
            .use_lld = false,
        });

        test_run.root_module.addAnonymousImport("utils", .{ .root_source_file = b.path("src/tests.zig") });
        test_step.dependOn(&b.addRunArtifact(test_run).step);

        break :vendored_tests;
    }

    example_tests: {
        const gen = b.addExecutable(.{
            .name = "gen_tests.zig",
            .root_source_file = b.path("scripts/gen_tests.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
            .use_llvm = false,
            .use_lld = false,
        });

        const run_gen = b.addRunArtifact(gen);
        run_gen.addFileArg(b.path("README.md"));
        const out = run_gen.addOutputFileArg("tests.zig");

        const test_run = b.addTest(.{
            .name = "vendored_tests",
            .root_source_file = out,
            .target = b.graph.host,
            .optimize = optimize,
            .filter = test_filter,
            .use_llvm = false,
            .use_lld = false,
        });

        test_run.root_module.addAnonymousImport("utils", .{ .root_source_file = b.path("src/tests.zig") });
        test_step.dependOn(&b.addRunArtifact(test_run).step);

        break :example_tests;
    }

    const test_module = test_module: {
        const module = b.addModule("test", .{
            .root_source_file = b.path("src/tests.zig"),
            .target = b.graph.host,
            .optimize = optimize,
        });

        break :test_module module;
    };

    check: {
        const check_step = b.step("check", "type check");
        check_step.dependOn(&b.addTest(.{ .root_module = test_module }).step);
        break :check;
    }

    const fuzz_finding_tests = fuzzing: {
        const dict_gen = b.addExecutable(.{
            .name = "gen_fuzz_dict.zig",
            .root_source_file = b.path("scripts/gen_fuzz_dict.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
            .use_llvm = false,
            .use_lld = false,
        });

        dict_gen.root_module.addAnonymousImport("Lexer", .{ .root_source_file = b.path("src/frontend/Lexer.zig") });

        const run_gen = b.addRunArtifact(dict_gen);
        const dict_out = run_gen.addOutputFileArg("hblang.dict");
        run_gen.addFileArg(b.path("README.md"));
        const cases = run_gen.addOutputDirectoryArg("fuzz-cases");

        const fuzz = b.addStaticLibrary(.{
            .name = "fuzz",
            .root_source_file = b.path("src/fuzz.zig"),
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

        if (!refuzz) break :fuzzing null;

        const fuzzes = b.option(usize, "jobs", "amount of cores to fuzz on") orelse try std.Thread.getCpuCount();

        // this is pure crap
        const run_whatev = b.addSystemCommand(&.{"echo"});
        const out_dir = run_whatev.addOutputDirectoryArg("findings");

        const gen_finding_tests = b.addExecutable(.{
            .name = "gen_fuzz_finding_tests.zig",
            .root_source_file = b.path("scripts/gen_fuzz_finding_tests.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
            .use_llvm = false,
            .use_lld = false,
        });

        for (0..fuzzes) |i| {
            const run_afl = b.addSystemCommand(&.{"afl-fuzz"});

            run_afl.addArg("-i");
            run_afl.addDirectoryArg(cases);
            run_afl.addArg("-o");
            run_afl.addDirectoryArg(out_dir);
            run_afl.addArg(if (i == 0) "-M" else "-S");
            run_afl.addArg(try std.fmt.allocPrint(b.allocator, "worker{}", .{i}));
            run_afl.addArg("-x");
            run_afl.addFileArg(dict_out);
            run_afl.addArgs(&.{ "-V", fuzz_duration });
            run_afl.addArg("--");
            run_afl.addFileArg(afl_lto_out);
            run_afl.stdio = .{ .check = .{} };
            run_afl.has_side_effects = true;

            gen_finding_tests.step.dependOn(&run_afl.step);
        }

        const run_gen_finding_tests = b.addRunArtifact(gen_finding_tests);
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

    testing: {
        const unit_tests = b.addTest(.{
            .root_module = test_module,
            .filter = test_filter,
            .use_llvm = false,
            .use_lld = false,
        });
        if (fuzz_finding_tests) |fft| unit_tests.step.dependOn(fft);
        test_step.dependOn(&b.addRunArtifact(unit_tests).step);

        break :testing;
    }
}
