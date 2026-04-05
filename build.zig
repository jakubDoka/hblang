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
    const dont_clean_up_x86_64 = b.option(bool, "dont-clean-up-x86-64", "keep the onject file from the test execution") orelse false;
    const report_trace_size = b.option(usize, "report-trace-size", "amout of frames on each report logged") orelse 0;
    const log_ct_exec = b.option(bool, "log-ct-exec", "log the instructions executed during comptime") orelse false;

    const check_step = b.step("check", "type check");

    const boptions = b.addOptions();
    boptions.addOption(bool, "cleanup_x86_64", !dont_clean_up_x86_64);

    const foptions = b.addOptions();
    foptions.addOption(usize, "stack_size", stack_size);
    foptions.addOption(bool, "dont_simulate", dont_simulate);
    foptions.addOption(usize, "report_trace_size", report_trace_size);
    foptions.addOption(bool, "log_ct_exec", log_ct_exec);

    const utils = b.dependency("utils", .{
        .target = target,
        .optimize = optimize,
    });

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

    const hbb = hbs: {
        const hbb = b.addModule("hb", .{
            .root_source_file = b.path("src/backend.zig"),
            .target = target,
            .optimize = optimize,
        });

        hbb.addOptions("options", boptions);
        hbb.addImport("zydis", zydis);
        hbb.addImport("hbb", hbb);
        hbb.addImport("utils-lib", utils.module("utils"));

        break :hbs hbb;
    };

    const hbf = hb: {
        const hbf = b.addModule("hb", .{
            .root_source_file = b.path("src/root.zig"),
            .target = target,
            .optimize = optimize,
        });

        hbf.addOptions("options", foptions);
        hbf.addImport("zydis", zydis);
        hbf.addImport("hbf", hbf);
        hbf.addImport("hbb", hbb);
        hbf.addImport("utils-lib", utils.module("utils"));

        break :hb hbf;
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
        exe.root_module.addImport("hb", hbf);

        break :hbc;
    }

    gen_big: {
        const gen_big_step = b.step("gen-big", "yea");

        const exe = b.addExecutable(.{
            .name = "hbc",
            .root_module = b.createModule(.{
                .root_source_file = b.path("scripts/gen_big.zig"),
                .target = b.graph.host,
                .optimize = .Debug,
            }),
        });
        check_step.dependOn(&exe.step);
        gen_big_step.dependOn(&b.addRunArtifact(exe).step);

        break :gen_big;
    }

    const test_step = b.step("test", "run tests");
    const test_filter = if (b.option(
        []const u8,
        "tf",
        "passed as a filter to tests",
    )) |f| &.{f} else &.{};

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
            hbb.addAnonymousImport(backend, .{
                .root_source_file = out,
                .imports = &.{.{ .name = "hbb", .module = hbb }},
            });
        }

        break :rewrite_dsl_gen;
    }

    check: {
        const amalgamation = b.addTest(.{
            .name = "check",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/amalgamation.zig"),
                .target = target,
                .optimize = optimize,
            }),
        });

        amalgamation.root_module.addImport("hbb", hbb);
        amalgamation.root_module.addImport("hbf", hbf);

        check_step.dependOn(&amalgamation.step);

        break :check;
    }

    if (true) example_tests: {
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

            test_run.root_module.addImport("utils", hbf);
            const run = b.addRunArtifact(test_run);
            run.has_side_effects = true;
            test_step.dependOn(&run.step);
        }

        break :example_tests;
    }

    if (true) vendored_tests: {
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

        test_run.root_module.addImport("utils", hbf);
        const tr = b.addRunArtifact(test_run);
        tr.has_side_effects = true;
        test_step.dependOn(&tr.step);

        break :vendored_tests;
    }
}
