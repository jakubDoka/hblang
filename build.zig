const std = @import("std");

pub fn build(b: *std.Build) !void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const use_llvm = b.option(bool, "use-llvm", "use llvm, last resort option") orelse (b.graph.host.result.os.tag == .windows);
    const use_lld = b.option(bool, "use-lld", "use lld, last resort option") orelse (b.graph.host.result.os.tag == .windows);

    hb: {
        _ = b.addModule("hb", .{
            .root_source_file = b.path("src/root.zig"),
            .target = target,
            .optimize = optimize,
        });

        break :hb;
    }

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
            .use_llvm = use_llvm,
            .use_lld = use_lld,
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
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        test_run.root_module.addAnonymousImport("utils", .{ .root_source_file = b.path("src/tests.zig") });
        const tr = b.addRunArtifact(test_run);
        tr.has_side_effects = true;
        test_step.dependOn(&tr.step);

        break :vendored_tests;
    }

    example_tests: {
        const gen = b.addExecutable(.{
            .name = "gen_tests.zig",
            .root_source_file = b.path("scripts/gen_tests.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        const run_gen = b.addRunArtifact(gen);
        run_gen.addFileArg(b.path("README.md"));
        const out = run_gen.addOutputFileArg("tests.zig");

        const test_run = b.addTest(.{
            .name = "example_tests",
            .root_source_file = out,
            .target = b.graph.host,
            .optimize = optimize,
            .filter = test_filter,
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        test_run.root_module.addAnonymousImport("utils", .{ .root_source_file = b.path("src/tests.zig") });
        const run = b.addRunArtifact(test_run);
        run.has_side_effects = true;
        test_step.dependOn(&run.step);

        break :example_tests;
    }

    example_tests: {
        const test_run = b.addTest(.{
            .name = "fuzz_finding_tests",
            .root_source_file = b.path("src/fuzz_finding_tests.zig"),
            .target = b.graph.host,
            .optimize = optimize,
            .filter = test_filter,
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        test_run.root_module.addAnonymousImport("utils", .{ .root_source_file = b.path("src/tests.zig") });
        const run = b.addRunArtifact(test_run);
        run.has_side_effects = true;
        test_step.dependOn(&run.step);

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

    fuzzing: {
        const dict_gen = b.addExecutable(.{
            .name = "gen_fuzz_dict.zig",
            .root_source_file = b.path("scripts/gen_fuzz_dict.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
            .use_llvm = use_llvm,
            .use_lld = use_lld,
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

        const fuzzes = b.option(usize, "jobs", "amount of cores to fuzz on") orelse try std.Thread.getCpuCount();

        // this is pure crap
        const run_whatev = b.addSystemCommand(&.{"echo"});
        run_whatev.has_side_effects = true;
        const out_dir = run_whatev.addOutputDirectoryArg("findings");

        const gen_finding_tests = b.addExecutable(.{
            .name = "gen_fuzz_finding_tests.zig",
            .root_source_file = b.path("scripts/gen_fuzz_finding_tests.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        const run_gen_finding_tests = b.addRunArtifact(gen_finding_tests);
        run_gen_finding_tests.has_side_effects = true;
        run_gen_finding_tests.addDirectoryArg(out_dir);
        run_gen_finding_tests.addArg("enabled");
        const fuzz_out = run_gen_finding_tests.addOutputFileArg("fuzz_finding_tests.zig");

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
            run_afl.has_side_effects = true;

            run_gen_finding_tests.step.dependOn(&run_afl.step);
        }

        const fuzz_step = b.step("fuzz", "run the fuzzer");
        fuzz_step.dependOn(&b.addInstallFile(fuzz_out, "fuzz_finding_tests.zig").step);

        break :fuzzing;
    }
}
