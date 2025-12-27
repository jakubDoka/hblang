const std = @import("std");

pub fn build(b: *std.Build) !void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const dont_simulate = b.option(bool, "dont-simulate", "dont run the code, just compile during tests") orelse false;
    const use_llvm = b.option(bool, "use-llvm", "use llvm, last resort option") orelse
        (b.graph.host.result.os.tag == .windows) or optimize != .Debug;
    const use_lld = b.option(bool, "use-lld", "use lld, last resort option") orelse
        (b.graph.host.result.os.tag == .windows) or optimize != .Debug;
    const stack_size = b.option(usize, "stack-size", "the amount of stack for the build") orelse 1024 * 1024 * 4;

    const check_step = b.step("check", "type check");

    const options = b.addOptions();
    options.addOption(usize, "stack_size", stack_size);
    options.addOption(bool, "dont_simulate", dont_simulate);

    const zydis = zydis: {
        const zydis = b.dependency("zydis", .{});
        const zycore = b.dependency("zycore", .{});

        const m = b.addModule("zidis", .{
            .root_source_file = b.path("src/zydis.zig"),
            .target = target,
            .optimize = .ReleaseFast,
        });

        m.addIncludePath(zydis.path("include/"));
        m.addIncludePath(zydis.path("src/"));
        m.addIncludePath(zycore.path("include/"));

        for ([_]*std.Build.Dependency{ zydis, zycore }) |dep| {
            const path = dep.path("src/");
            var dir = try std.fs.openDirAbsolute(path.getPath(b), .{ .iterate = true });
            var iter = try dir.walk(b.allocator);

            var files = std.ArrayList([]const u8).empty;

            while (try iter.next()) |fl| {
                if (std.mem.endsWith(u8, fl.path, ".c")) {
                    try files.append(b.allocator, try b.allocator.dupe(u8, fl.path));
                }
            }

            m.addCSourceFiles(.{
                .root = path,
                .files = files.items,
                .flags = &.{"-DZYAN_NO_LIBC"},
            });
        }

        break :zydis m;
    };

    const hb = hb: {
        const hb = b.addModule("hb", .{
            .root_source_file = b.path("src/root.zig"),
            .target = target,
            .optimize = optimize,
        });

        hb.addOptions("options", options);
        hb.addImport("zydis", zydis);
        hb.addImport("hb", hb);

        break :hb hb;
    };

    hbc: {
        const exe = b.addExecutable(.{
            .name = "hbc",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/hbc.zig"),
                .target = target,
                .optimize = optimize,
                .single_threaded = true,
            }),
            .use_llvm = use_llvm,
            .use_lld = use_lld,
            //.strip = false,
        });
        exe.stack_size = stack_size;
        b.installArtifact(exe);

        exe.root_module.addImport("zydis", zydis);
        exe.root_module.addImport("hb", hb);

        break :hbc;
    }

    const test_step = b.step("test", "run tests");
    const test_filter = if (b.option([]const u8, "tf", "passed as a filter to tests")) |f| &.{f} else &.{};

    hb_test: {
        test_step.dependOn(&b.addRunArtifact(b.addTest(.{
            .root_module = hb,
            .filters = test_filter,
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        })).step);

        break :hb_test;
    }

    const test_module = test_module: {
        const module = b.addModule("test", .{
            .root_source_file = b.path("src/tests.zig"),
            .target = b.graph.host,
            .optimize = optimize,
        });

        module.addImport("hb", hb);
        module.addImport("zydis", zydis);

        break :test_module module;
    };

    vendored_tests: {
        const grn = b.addExecutable(.{
            .name = "gen_vendored_tests",
            .root_module = b.createModule(.{
                .root_source_file = b.path("scripts/gen_vendored_tests.zig"),
                .target = b.graph.host,
                .optimize = .Debug,
            }),
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        check_step.dependOn(&grn.step);

        const run_gen = b.addRunArtifact(grn);
        run_gen.has_side_effects = true;
        run_gen.addDirectoryArg(b.path("vendored-tests"));
        run_gen.addArg("hbc-tests");
        const out = run_gen.addOutputFileArg("vendored_tests.zig");

        const test_run = b.addTest(.{
            .name = "vendored_tests",
            .root_module = b.createModule(.{
                .root_source_file = out,
                .target = b.graph.host,
                .optimize = optimize,
                .single_threaded = true,
            }),
            .filters = test_filter,
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        test_run.root_module.addImport("utils", test_module);
        const tr = b.addRunArtifact(test_run);
        tr.has_side_effects = true;
        test_step.dependOn(&tr.step);

        break :vendored_tests;
    }

    example_tests: {
        const gen = b.addExecutable(.{
            .name = "gen_tests.zig",
            .root_module = b.createModule(.{
                .root_source_file = b.path("scripts/gen_tests.zig"),
                .target = b.graph.host,
                .optimize = .Debug,
                .single_threaded = true,
            }),
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        check_step.dependOn(&gen.step);

        inline for (
            .{ "example_tests", "bugfix_tests" },
            .{ "README.md", "BUGFIX.md" },
        ) |name, source| {
            const run_gen = b.addRunArtifact(gen);
            run_gen.addFileArg(b.path(source));
            const out = run_gen.addOutputFileArg("tests.zig");

            const test_run = b.addTest(.{
                .name = name,
                .root_module = b.createModule(.{
                    .root_source_file = out,
                    .target = b.graph.host,
                    .optimize = optimize,
                    .single_threaded = true,
                }),
                .filters = test_filter,
                .use_llvm = use_llvm,
                .use_lld = use_lld,
            });

            test_run.root_module.addImport("utils", test_module);
            const run = b.addRunArtifact(test_run);
            run.has_side_effects = true;
            test_step.dependOn(&run.step);
        }

        break :example_tests;
    }

    fuzz_fidning_tests: {
        const test_run = b.addTest(.{
            .name = "fuzz_finding_tests",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/fuzz_finding_tests.zig"),
                .target = b.graph.host,
                .optimize = optimize,
                .single_threaded = true,
            }),
            .filters = test_filter,
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        test_run.root_module.addImport("utils", test_module);
        const run = b.addRunArtifact(test_run);
        run.has_side_effects = true;
        test_step.dependOn(&run.step);

        break :fuzz_fidning_tests;
    }

    rewrite_dsl_gen: {
        const gen = b.addExecutable(.{
            .name = "rewrite-dsl",
            .root_module = b.createModule(.{
                .root_source_file = b.path("scripts/rewrite_dsl.zig"),
                .target = b.graph.host,
                .optimize = .Debug,
            }),
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        check_step.dependOn(&gen.step);

        const files = [_][]const u8{
            "src/x86_64/mach_peeps.clj",
            "src/hbvm/mach_peeps.clj",
            "src/wasm/mach_peeps.clj",
            "src/backend/ideal_peeps.clj",
        };

        const backends = [_][]const u8{
            "x86_64.X86_64Gen",
            "hbvm.HbvmGen",
            "wasm.WasmGen",
            "graph.IdealGen",
        };

        for (files, backends) |file, backend| {
            const run_gen = b.addRunArtifact(gen);
            run_gen.addFileArg(b.path(file));
            const zig_file = try std.mem.replaceOwned(u8, b.allocator, file, ".clj", ".zig");
            const out = run_gen.addOutputFileArg(zig_file);
            hb.addAnonymousImport(backend, .{
                .root_source_file = out,
                .imports = &.{.{ .name = "hb", .module = hb }},
            });
        }

        break :rewrite_dsl_gen;
    }

    check: {
        const t = b.addTest(.{ .root_module = test_module });
        check_step.dependOn(&t.step);

        break :check;
    }

    // NOTE: this does not work, dont know why
    if (false) fuzzing: {
        const dict_gen = b.addExecutable(.{
            .name = "gen_fuzz_dict.zig",
            .root_module = b.createModule(.{
                .root_source_file = b.path("scripts/gen_fuzz_dict.zig"),
                .target = b.graph.host,
                .optimize = .Debug,
            }),
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        check_step.dependOn(&dict_gen.step);

        dict_gen.root_module.addAnonymousImport("Lexer", .{ .root_source_file = b.path("src/frontend/Lexer.zig") });

        const run_gen = b.addRunArtifact(dict_gen);
        const dict_out = run_gen.addOutputFileArg("hblang.dict");
        run_gen.addFileArg(b.path("README.md"));
        run_gen.addFileArg(b.path("BUGFIX.md"));
        const cases = run_gen.addOutputDirectoryArg("fuzz-cases");

        const afl_kit = {}; //@import("afl_kit");

        const fuzz = b.addObject(.{
            .name = "fuzz",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/fuzz.zig"),
                .target = b.graph.host,
                .optimize = optimize,
                .single_threaded = true,
                .stack_check = false,
                .link_libc = true,
                .strip = false,
            }),
            .use_llvm = true,
            .use_lld = true,
        });

        fuzz.root_module.addImport("hb", hb);

        check_step.dependOn(&fuzz.step);

        const instrumented = afl_kit.addInstrumentedExe(
            b,
            target,
            optimize,
            null,
            true,
            fuzz,
            &.{},
        ).?;

        const fuzz_duration = b.option([]const u8, "fuzz-duration", "n seconds to fuzz for") orelse "1";

        const fuzzes = b.option(usize, "jobs", "amount of cores to fuzz on") orelse try std.Thread.getCpuCount();

        // this is pure crap
        const run_whatev = b.addSystemCommand(&.{"echo"});
        run_whatev.has_side_effects = true;
        const out_dir = run_whatev.addOutputDirectoryArg("findings");

        const gen_finding_tests = b.addExecutable(.{
            .name = "gen_fuzz_finding_tests.zig",
            .root_module = b.createModule(.{
                .root_source_file = b.path("scripts/gen_fuzz_finding_tests.zig"),
                .target = b.graph.host,
                .optimize = .Debug,
            }),
            .use_llvm = use_llvm,
            .use_lld = use_lld,
        });

        check_step.dependOn(&gen_finding_tests.step);

        const run_gen_finding_tests = b.addRunArtifact(gen_finding_tests);
        run_gen_finding_tests.has_side_effects = true;
        run_gen_finding_tests.addDirectoryArg(out_dir);
        run_gen_finding_tests.addArg("enabled");
        const fuzz_out = run_gen_finding_tests.addOutputFileArg("fuzz_finding_tests.zig");

        for (0..fuzzes) |i| {
            const run_afl = b.addSystemCommand(&.{"afl-fuzz"});

            run_afl.setEnvironmentVariable("AFL_BENCH_UNTIL_CRASH", "1");

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
            run_afl.addFileArg(instrumented);
            run_afl.has_side_effects = true;

            run_gen_finding_tests.step.dependOn(&run_afl.step);
        }

        const fuzz_step = b.step("fuzz", "run the fuzzer");
        fuzz_step.dependOn(&b.addInstallFile(fuzz_out, "fuzz_finding_tests.zig").step);

        break :fuzzing;
    }
}
