const std = @import("std");

const root = @import("hb");
const isa = root.hbvm.isa;
const Types = root.frontend.Types;
const Builder = root.backend.Builder;
const Node = Builder.BuildNode;
const Func = root.backend.graph.Func(Builder);
const graph = root.backend.graph;
const utils = root.utils;
const static_anal = root.backend.static_anal;
const Ast = root.frontend.Ast;
const Arena = utils.Arena;
const Codegen = root.frontend.Codegen;
const Comptime = root.frontend.Comptime;
const Lexer = root.frontend.Lexer;
const Machine = root.backend.Machine;
const HbvmGen = root.hbvm.HbvmGen;
const Vm = root.hbvm.Vm;
const tys = root.frontend.types;
const OptOptions = root.backend.Machine.OptOptions;
pub const eca = HbvmGen.eca;

pub const comptime_uuid = Machine.Data.uuidConst("comptime");

pub const comptime_opts = Machine.OptOptions{
    .mode = .debug,
};

vm: Vm = .{},
gen: HbvmGen,
in_progress: std.ArrayList(Loc) = .{},
type_instances: std.HashMapUnmanaged(
    Types.Id,
    void,
    TypeInstanceCtx,
    std.hash_map.default_max_load_percentage,
) = .{},

pub const TypeInstanceCtx = struct {
    types: *Types,

    pub fn eql(self: @This(), a: Types.Id, b: Types.Id) bool {
        const ad, const bd = .{ a.data(), b.data() };
        if (std.meta.activeTag(ad) != std.meta.activeTag(bd)) return false;

        return switch (ad) {
            inline .Struct, .Union, .Enum => |s, t| s.deepEqual(self.types, @field(bd, @tagName(t))),
            else => utils.panic("{s}", .{@tagName(ad)}),
        };
    }

    pub fn hash(self: @This(), key: Types.Id) u64 {
        var hasher = std.hash.Fnv1a_64.init();
        const adk = key.data();
        std.hash.autoHash(&hasher, std.meta.activeTag(adk));
        switch (adk) {
            inline .Struct, .Union, .Enum => |s| s.deepHash(self.types, &hasher),
            else => utils.panic("{s}", .{@tagName(adk)}),
        }
        return hasher.final();
    }
};

pub fn optimizeComptime(self: OptOptions, comptime Backend: type, ctx: anytype, func: *graph.Func(Backend)) []const u16 {
    OptOptions.idealizeDead(Backend, ctx, func);
    OptOptions.doMem2Reg(Backend, func);
    OptOptions.idealizeGeneric(Backend, ctx, func, false);
    OptOptions.idealizeMach(Backend, ctx, func);
    OptOptions.doGcm(Backend, func);
    if (self.error_buf != null) {
        self.doStaticAnal(Backend, func);
    }
    return root.backend.Regalloc.rallocIgnoreStats(Backend, func);
}

pub const stack_size = 1024 * 128;

pub const Loc = packed struct(u64) {
    ast: Ast.Id,
    scope: Types.Id,
};

pub const InteruptCode = enum(u64) {
    Struct,
    Union,
    Enum,
    Type,
    indirect_call,
    name_of,
    make_array,
    ChildOf,
    kind_of,
    len_of,
    decl_count_of,
    size_of,
    align_of,
    type_info,
    alloc_global,
};

pub fn init(gpa: std.mem.Allocator) Comptime {
    var self = Comptime{ .gen = .{ .gpa = gpa } };
    self.gen.mach.out.code.resize(gpa, stack_size) catch unreachable;
    self.gen.mach.out.code.items[self.gen.mach.out.code.items.len - 1] = @intFromEnum(isa.Op.tx);
    self.gen.mach.out.code.items[self.gen.mach.out.code.items.len - 2] = @intFromEnum(isa.Op.eca);
    self.vm.regs.set(.stack_addr, stack_size - 8);
    return self;
}

pub fn deinit(self: *Comptime) void {
    self.in_progress.deinit(self.getGpa());
    self.type_instances.deinit(self.getGpa());
    self.gen.deinit();
}

pub fn getTypes(self: *Comptime) *Types {
    return @alignCast(@fieldParentPtr("ct", self));
}

pub inline fn getGpa(self: *Comptime) std.mem.Allocator {
    return self.gen.gpa;
}

pub inline fn ecaArg(self: *Comptime, idx: usize) u64 {
    return self.vm.regs.get(.arg(idx));
}

pub inline fn ecaArgAst(self: *Comptime, idx: usize) Ast.Id {
    return @enumFromInt(@as(u32, @truncate(self.ecaArg(idx))));
}

pub inline fn ecaArgSloc(self: *Comptime, idx: usize) graph.Sloc {
    return @bitCast(self.ecaArg(idx));
}

pub inline fn ecaArgTy(self: *Comptime, idx: usize) Types.Id {
    return @enumFromInt(@as(u32, @truncate(self.vm.regs.get(.arg(idx)))));
}

pub const PartialEvalResult = union(enum) {
    DependsOnRuntimeControlFlow: *Node,
    Unsupported: struct { *Node, []const u8 },
    InvalidCaptureAccess: graph.Sloc,
    OutOfBounds: struct { graph.Sloc, u64, i65 },
};

const PartialEvalCtx = struct {
    target: Types.Target,
    file: Types.File,
    scope: Types.Id,
    pos: u32,
    error_slot: *PartialEvalResult,
    runtime_abi: Types.Abi,

    pub inline fn err(self: PartialEvalCtx, res: PartialEvalResult) error{Never} {
        self.error_slot.* = res;
        return error.Never;
    }
};

pub fn partialEval(self: *Comptime, ctx: PartialEvalCtx, bl: *Builder, expr: *Node) error{Never}!*Node {
    const types = self.getTypes();

    const revisited = expr.schedule == 0;
    if (revisited) return expr;
    expr.schedule = 0;
    errdefer {
        expr.schedule = std.math.maxInt(u16);
    }

    switch (expr.extra2()) {
        .GlobalAddr => |extra| {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            _ = try self.partialEvalGlobal(ctx, expr, extra.id);
            const interestingOps = try self.collectMemOps(ctx, expr, tmp.arena);
            try self.executeMemOps(ctx, bl, interestingOps, @enumFromInt(extra.id), expr);

            expr.schedule = std.math.maxInt(u16);
            return expr;
        },
        .CInt => {
            expr.schedule = std.math.maxInt(u16);
            if (expr.data_type == .top) {
                return ctx.err(.{ .InvalidCaptureAccess = expr.sloc });
            }
            return expr;
        },
        .UnOp => |extra| {
            const opr = expr.inputs()[1].?;
            const oper = try self.partialEval(ctx, bl, opr);

            const res = extra.op.eval(expr.data_type, opr.data_type, oper.extra(.CInt).value);
            const node_res = bl.addIntImm(.none, expr.data_type, res);
            bl.func.subsume(node_res, expr);
            return node_res;
        },
        .BinOp => |extra| {
            const lhs = expr.inputs()[1].?;
            const lhs_val = try self.partialEval(ctx, bl, lhs);
            const rhs = expr.inputs()[2].?;
            const rhs_val = try self.partialEval(ctx, bl, rhs);

            if (lhs_val.kind != .CInt) {
                if (rhs_val.kind != .CInt) {
                    return ctx.err(.{ .Unsupported = .{ rhs_val, "rhs of binop" } });
                }

                return expr;
            }

            const res = extra.op.eval(expr.data_type, lhs_val.extra(.CInt).value, rhs_val.extra(.CInt).value);
            const node_res = bl.addIntImm(.none, expr.data_type, res);
            bl.func.subsume(node_res, expr);
            return node_res;
        },
        .Local => {
            const global = types.addUniqueGlobal(ctx.scope);
            const mem = types.pool.arena.alloc(
                u8,
                @intCast(expr.inputs()[1].?.extra(.LocalAlloc).size),
            );
            types.store.get(global).data = .{ .mut = mem };
            types.store.get(global).ty = @enumFromInt(expr.inputs()[1].?.extra(.LocalAlloc).debug_ty);
            expr.inputs()[1].?.extra(.LocalAlloc).meta = @intFromEnum(global);

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const interestingOps = try self.collectMemOps(ctx, expr, tmp.arena);

            const res = bl.addGlobalAddr(.none, @intFromEnum(global));
            bl.func.subsume(res, expr);

            res.schedule = 0;
            defer res.schedule = std.math.maxInt(u16);

            try self.executeMemOps(ctx, bl, interestingOps, global, res);

            return res;
        },
        .Load => {
            const base, const offset = (try self.partialEval(ctx, bl, expr.base())).knownOffset();

            const res = switch (base.extra2()) {
                .GlobalAddr => |extra| b: {
                    _ = try self.partialEvalGlobal(ctx, base, extra.id);

                    const gid: utils.EntId(tys.Global) = @enumFromInt(extra.id);
                    const global: *tys.Global = types.store.get(gid);
                    const mem = global.data.slice(self);

                    for (global.relocs) |rel| {
                        if (rel.offset == offset) {
                            var ptr: u64 = 0;
                            @memcpy(std.mem.asBytes(&ptr), mem[rel.offset..][0..8]);
                            const target = types.findSymForPtr(ptr) catch unreachable;
                            break :b bl.addGlobalAddr(.none, target);
                        }
                    }

                    const abs_off = std.math.cast(u64, offset) orelse {
                        return ctx.err(.{
                            .OutOfBounds = .{ expr.sloc, mem.len, offset },
                        });
                    };

                    const up_to = abs_off + expr.data_type.size();

                    if (mem.len < up_to) {
                        return ctx.err(.{
                            .OutOfBounds = .{ expr.sloc, mem.len, up_to },
                        });
                    }

                    var value: i64 = 0;
                    @memcpy(
                        std.mem.asBytes(&value)[0..@intCast(expr.data_type.size())],
                        mem[@intCast(abs_off)..][0..@intCast(expr.data_type.size())],
                    );

                    break :b bl.addIntImm(.none, expr.data_type, value);
                },
                else => return ctx.err(.{ .Unsupported = .{ base, "load base" } }),
            };

            bl.func.subsume(res, expr);
            return res;
        },
        .Ret => return (try self.partialEvalCall(ctx, bl, expr.inputs()[0].?, expr)).?,
        else => return ctx.err(.{ .Unsupported = .{ expr, "TODO: generic op" } }),
    }
}

pub fn collectMemOps(self: *Comptime, ctx: PartialEvalCtx, expr: *Node, scratch: *Arena) ![]Node.Out {
    _ = self;
    var interestingOps = std.ArrayList(Node.Out){};
    for (expr.outputs()) |o| {
        errdefer unreachable;
        if (o.get().kind == .BinOp) {
            for (o.get().outputs()) |oo| try interestingOps.append(scratch.allocator(), oo);
        } else {
            try interestingOps.append(scratch.allocator(), o);
        }
    }

    // lca saves us some time, maybe
    var lca: ?*Func.CfgNode = null;
    for (interestingOps.items) |o| {
        const op = o.get();
        if (op.isStore()) {
            lca = (lca orelse op.cfg0()).findLca(op.cfg0());
        }
    }

    // vlaidate we dont depend on runtim control flow
    for (interestingOps.items) |o| {
        const op = o.get();
        if (!op.isStore()) continue;
        if (op.cfg0() == lca) continue;

        var seen_if_branch: ?*Node = null;

        var cursor = op.cfg0();
        while (cursor != lca) : (cursor = cursor.idom()) {
            if (cursor.base.kind == .Else or cursor.base.kind == .Then) {
                seen_if_branch = cursor.base.inputs()[0].?
                    .outputs()[@intFromBool(cursor.base.kind == .Then)].get();
            }
            if (cursor.base.kind == .Loop) {
                const to_find = seen_if_branch orelse
                    return ctx.err(.{ .DependsOnRuntimeControlFlow = op });
                var back_cursor = cursor.base.inputs()[1].?.asCfg().?;
                while (back_cursor != cursor) : (back_cursor = back_cursor.idom()) {
                    if (&back_cursor.base == to_find) {
                        seen_if_branch = null;
                        break;
                    }
                }
            }
        }

        if (seen_if_branch != null) {
            return ctx.err(.{ .DependsOnRuntimeControlFlow = op });
        }
    }

    return interestingOps.items;
}

pub fn executeMemOps(
    self: *Comptime,
    ctx: PartialEvalCtx,
    bl: *Builder,
    interestingOps: []Node.Out,
    glob: utils.EntId(tys.Global),
    res: *Node,
) !void {
    // TODO: this is not actualy handling the order of operations properly

    const types = self.getTypes();

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const mem = self.getTypes().store.get(@as(
        utils.EntId(tys.Global),
        @enumFromInt(res.extra(.GlobalAddr).id),
    )).data.mutSlice(self).?;

    var red_from = false;
    var snapshots = std.ArrayList(struct { utils.EntId(tys.Global), usize }){};
    for (interestingOps, 0..) |o, i| {
        const op = o.get();

        if (op.kind == .Scope or op.kind == .Pin) continue;

        const is_comptime_ref =
            (op.isStore() and op.base() == op.inputs()[o.pos()].?) or
            op.kind == .Call or op.kind == .Load;

        if (is_comptime_ref and red_from) {
            const snapshot = types.addUniqueGlobal(ctx.scope);
            snapshot.get(types).data = .{ .imm = types.pool.arena.dupe(u8, glob.get(types).data.slice(self)) };
            snapshot.get(types).ty = glob.get(types).ty;
            snapshots.append(tmp.arena.allocator(), .{ snapshot, i }) catch unreachable;
            types.queue(ctx.target, .init(.{ .Global = snapshot }));

            red_from = false;
        } else {
            if (!is_comptime_ref) red_from = true;
        }

        switch (op.kind) {
            .Store => {
                const base, const offset = op.base().knownOffset();
                if (base != res) {
                    continue;
                }

                const val = try self.partialEval(ctx, bl, op.value().?);

                switch (val.extra2()) {
                    .CInt => |extra| {
                        @memcpy(
                            mem[@intCast(offset)..][0..@intCast(op.data_type.size())],
                            std.mem.asBytes(&extra.value)[0..@intCast(op.data_type.size())],
                        );
                    },
                    .GlobalAddr => |extra| {
                        const addr = try self.partialEvalGlobal(ctx, val, extra.id);
                        std.debug.assert(op.data_type.size() == 8);
                        @memcpy(mem[@intCast(offset)..][0..8], std.mem.asBytes(&addr));
                    },
                    else => return ctx.err(.{ .Unsupported = .{ val, "stack store value" } }),
                }

                bl.func.subsume(op.mem(), op);
            },
            .Call => if (op.outputs().len != 0) {
                _ = try self.partialEvalCall(ctx, bl, op.outputs()[0].get(), null);
            },
            .Load => {
                if (op.schedule == 0) {
                    continue;
                }

                _ = try self.partialEval(ctx, bl, op);
            },
            .Scope => {},
            .MemCpy => {
                const other, const dst_offset = op.base().knownOffset();
                if (other != res) continue;

                const src, const src_offset = (try self.partialEval(ctx, bl, op.inputs()[3].?))
                    .knownOffset();
                if (src.kind != .GlobalAddr) return ctx.err(.{ .Unsupported = .{ op, "TODO: memcpy src" } });

                _ = try self.partialEvalGlobal(ctx, src, src.extra(.GlobalAddr).id);

                const len = try self.partialEval(ctx, bl, op.inputs()[4].?);
                if (len.kind != .CInt) return ctx.err(.{ .Unsupported = .{ op, "TODO: memcpy len" } });

                const other_mem = self.getTypes().store.get(@as(
                    utils.EntId(tys.Global),
                    @enumFromInt(src.extra(.GlobalAddr).id),
                )).data.mutSlice(self).?;

                @memcpy(
                    mem[@intCast(dst_offset)..][0..@intCast(len.extra(.CInt).value)],
                    other_mem[@intCast(src_offset)..][0..@intCast(len.extra(.CInt).value)],
                );

                bl.func.subsume(op.mem(), op);
            },
            else => return ctx.err(.{ .Unsupported = .{ op, "TODO: stack mut op" } }),
        }
    }

    var prev_up_to: usize = 0;
    for (snapshots.items) |snap| {
        const snap_glob, const up_to = snap;
        const node = bl.addGlobalAddr(.none, @intFromEnum(snap_glob));

        for (interestingOps[prev_up_to..up_to]) |op| {
            if (op.get().isDead()) continue;

            const base = op.get().inputs()[op.pos()].?;

            const replacement = if (base == res) node else if (base.kind == .BinOp) b: {
                const edit_pos = for (base.inputs(), 0..) |inp, i| {
                    if (inp.? == res) break i;
                } else unreachable;

                const deps = tmp.arena.dupe(?*Node, base.inputs());
                deps[edit_pos] = node;

                break :b bl.func.addNode(.BinOp, base.sloc, base.data_type, deps, base.extra(.BinOp).*);
            } else unreachable;

            _ = bl.func.setInput(op.get(), op.pos(), replacement);
        }

        prev_up_to = up_to;
    }
}

pub fn partialEvalCall(self: *Comptime, ctx: PartialEvalCtx, bl: *Builder, curr: *Node, from_ret: ?*Node) !?*Node {
    const types = self.getTypes();

    if (curr.schedule == 0) return null;
    curr.schedule = 0;

    const call: *Node = curr.inputs()[0].?;
    std.debug.assert(call.kind == .Call);

    if (call.extra(.Call).id != Types.comptime_only_fn) {
        const func_id: utils.EntId(tys.Func) = @enumFromInt(call.extra(.Call).id);
        const func = types.store.get(func_id);

        if (func.recursion_lock) {
            types.report(func.key.loc.file, func.key.loc.ast, "the functions types most likely depend on it being evaluated", .{});
            return ctx.err(.{ .Unsupported = .{ curr, "recursive call" } });
        }

        if (func.completion.get(.@"comptime") == .queued) {
            self.jitFunc(func_id, ctx.runtime_abi) catch return ctx.err(.{ .Unsupported = .{ curr, "jit func" } });
        }
        if (types.store.get(func_id).errored) return ctx.err(.{ .Unsupported = .{ curr, "errored" } });
        std.debug.assert(types.store.get(func_id).completion.get(.@"comptime") == .compiled);
        std.debug.assert(self.gen.mach.out.funcs.items.len > call.extra(.Call).id);
    }

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var globals = tmp.arena.makeArrayList(*Node, call.inputs().len - 2);
    // we need this because another call could clogger us
    var args = tmp.arena.alloc(u64, call.inputs().len - 2);
    for (call.inputs()[2..], 0..) |arg, arg_idx| {
        const argv = try self.partialEval(ctx, bl, arg.?);
        args[arg_idx] = switch (argv.extra2()) {
            .CInt => |extra| @bitCast(extra.value),
            .GlobalAddr => |extra| b: {
                globals.appendAssumeCapacity(argv);
                break :b try self.partialEvalGlobal(ctx, argv, extra.id);
            },
            else => return ctx.err(.{ .Unsupported = .{ argv, "function argument" } }),
        };
    }

    for (args, 0..) |a, i| {
        types.ct.vm.regs.set(.arg(i), a);
    }

    types.ct.runVm(ctx.file, ctx.pos, call.extra(.Call).id, &.{}) catch {
        return ctx.err(.{ .Unsupported = .{ curr, "vm error" } });
    };

    for (globals.items) |g| {
        _ = try self.partialEvalGlobal(ctx, g, g.extra(.GlobalAddr).id);
    }

    var rret: ?*Node = null;
    for (tmp.arena.dupe(Node.Out, curr.outputs())) |n| {
        const o = n.get();
        if (o.kind == .Ret) {
            const idx = o.extra(.Ret).index;
            const ret = types.ct.vm.regs.get(.ret(idx));
            const ret_vl = bl.addIntImm(.none, o.data_type, @bitCast(ret));
            if (o == from_ret) rret = ret_vl;
            bl.func.subsume(ret_vl, o);
        }
        if (o.kind == .Mem) {
            bl.func.subsume(call.inputs()[1].?, o);
        }
    }
    // NOTE: the backend expects this
    call.data_type = .bot;
    bl.func.subsume(call.inputs()[0].?, curr);

    return rret;
}

pub fn partialEvalGlobal(self: *Comptime, ctx: PartialEvalCtx, curr: *Node, global: u32) !u64 {
    const types = self.getTypes();
    const gid: utils.EntId(tys.Global) = @enumFromInt(global);
    // TODO: clean this up

    gid.get(types).completion.set(.@"comptime", .queued);
    types.queue(.@"comptime", .init(.{ .Global = gid }));
    if (types.retainGlobals(.@"comptime", &self.gen.mach, false)) {
        return ctx.err(.{ .Unsupported = .{ curr, "retained globals" } });
    }

    return self.gen.mach.out.syms.items[@intFromEnum(self.gen.mach.out.globals.items[global])].offset;
}

pub fn runVm(
    self: *Comptime,
    file: Types.File,
    pos: u32,
    entry_id: u32,
    return_loc: []u8,
) !void {
    const types = self.getTypes();

    const stack_end = self.vm.regs.get(.stack_addr);

    self.vm.ip = if (entry_id == Types.comptime_only_fn)
        stack_size - 2
    else
        self.gen.mach.out.syms.items[@intFromEnum(self.gen.mach.out.funcs.items[entry_id])].offset;
    std.debug.assert(self.vm.ip < self.gen.mach.out.code.items.len);

    @memcpy(self.gen.mach.out.code.items[@intCast(stack_end - return_loc.len)..@intCast(stack_end)], return_loc);

    self.vm.fuel = 1024 * 16;
    self.vm.regs.set(.ret_addr, stack_size - 1); // return to hardcoded tx
    if (return_loc.len != 0) {
        if (stack_end < return_loc.len) {
            types.report(file, pos, "the global variable overflowed the" ++
                " comptime stack, consider using `x: <type> = @embed(\"<filename>\")`" ++
                " or `x: <type> = idk`", .{});
            return error.Never;
        }
        self.vm.regs.set(.arg(0), stack_end - return_loc.len);
    }
    self.vm.regs.set(.stack_addr, stack_end - return_loc.len);

    const log = false;
    var stderr = if (log) std.fs.File.stderr().writer(&.{});
    var vm_ctx = Vm.SafeContext{
        .writer = if (log) &stderr.interface else null,
        .color_cfg = .escape_codes,
        .memory = self.gen.mach.out.code.items,
        .code_start = 0,
        .code_end = 0,
    };

    while (true) switch (b: {
        var hbvm_met = types.metrics.begin(.hbvm);
        defer hbvm_met.end();
        break :b self.vm.run(&vm_ctx) catch |err| {
            types.report(file, pos, "comptime execution failed: {}", .{@errorName(err)});
            // std.debug.dumpCurrentStackTrace(@returnAddress());
            return error.Never;
        };
    }) {
        .tx => break,
        .eca => self.doInterrupt(&vm_ctx),
        else => unreachable,
    };

    @memcpy(return_loc, self.gen.mach.out.code.items[@intCast(stack_end - return_loc.len)..@intCast(stack_end)]);
    self.vm.regs.set(.stack_addr, stack_end);
}

pub fn doInterrupt(self: *Comptime, vm_ctx: *Vm.SafeContext) void {
    const types = self.getTypes();

    const InterruptFrame = extern struct {
        ip: usize,
        fuel: usize,
    };

    begin_interrup: {
        const stack_ptr = self.vm.regs.get(.stack_addr) - @sizeOf(InterruptFrame);
        vm_ctx.memory[@intCast(stack_ptr)..][0..@sizeOf(InterruptFrame)].* =
            @bitCast(InterruptFrame{ .ip = self.vm.ip, .fuel = self.vm.fuel });
        self.vm.regs.set(.stack_addr, stack_ptr);
        break :begin_interrup;
    }

    defer end_interrupt: {
        const stack_ptr = self.vm.regs.get(.stack_addr);
        const frame: InterruptFrame = @bitCast(vm_ctx.memory[@intCast(stack_ptr)..][0..@sizeOf(InterruptFrame)].*);
        self.vm.ip = frame.ip;
        self.vm.fuel = frame.fuel;
        self.vm.regs.set(.stack_addr, stack_ptr + @sizeOf(InterruptFrame));
        break :end_interrupt;
    }

    switch (@as(InteruptCode, @enumFromInt(self.ecaArg(0)))) {
        .Type => self.doTypeInterrupt(vm_ctx),
        .Struct, .Union, .Enum => |t| {
            const scope = self.ecaArgTy(1);
            const ast = types.getFile(scope.file(types).?);
            const struct_ast_id = self.ecaArgAst(2);
            const struct_ast = ast.exprs.get(struct_ast_id).Type;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();
            const captures = tmp.arena.alloc(Types.Scope.Capture, struct_ast.captures.len());

            const prefix = 5;
            for (captures, ast.exprs.view(struct_ast.captures), 0..) |*slot, cp, i| {
                slot.* = .{
                    .id = .fromCapture(cp),
                    .ty = @enumFromInt(self.ecaArg(prefix + i * 2)),
                    .value = @bitCast(self.ecaArg(prefix + i * 2 + 1)),
                };
                slot.id.has_value = true;
                if (slot.ty.size(types) < 8) slot.value &=
                    (@as(i64, 1) << @intCast(slot.ty.size(types) * 8)) - 1;
            }

            const res = switch (t) {
                inline .Struct, .Union, .Enum => |tg| types.resolveFielded(
                    @field(std.meta.Tag(Types.Data), @tagName(tg)),
                    scope,
                    scope.file(types).?,
                    @as(
                        [*]const u8,
                        @ptrFromInt(@as(usize, @intCast(self.vm.regs.get(.arg(3))))),
                    )[0..@intCast(self.vm.regs.get(.arg(4)))],
                    struct_ast_id,
                    captures,
                    null,
                ),
                else => unreachable,
            };

            self.vm.regs.set(.ret(0), @intFromEnum(res));
        },
        .indirect_call => {
            unreachable;
        },
        .name_of => {
            const ty = self.ecaArgTy(1);
            const value = self.ecaArg(2);

            const enm: tys.Enum.Id = ty.data().Enum;
            const fields = enm.getFields(types);

            if (value > fields.len) {
                //   types.report(lfile, expr, "the enum value is out of bounds, it has no name", .{});
                unreachable; // TODO: the enum value is corrupted
            }

            const ret_addr = self.gen.mach.out.code.items.len;

            self.gen.mach.out.code.appendSlice(self.getGpa(), fields[@intCast(value)].name) catch unreachable;
            vm_ctx.memory = self.gen.mach.out.code.items;

            self.vm.regs.set(.ret(0), ret_addr);
            self.vm.regs.set(.ret(1), fields[@intCast(value)].name.len);
        },
        .make_array => {
            const len = self.ecaArg(1);
            const ty = self.ecaArgTy(2);
            const slice = types.makeArray(@intCast(len), ty);
            self.vm.regs.set(.ret(0), @intFromEnum(slice));
        },
        .ChildOf => {
            const ty = self.ecaArgTy(2);

            self.vm.regs.set(.ret(0), @intFromEnum(ty.child(types) orelse b: {
                types.reportSloc(self.ecaArgSloc(1), "directive only work on pointer" ++
                    " types and slices, {} is not", .{ty});
                break :b .never;
            }));
        },
        .kind_of => {
            const ty = self.ecaArgTy(2);
            self.vm.regs.set(.ret(0), @intFromEnum(ty.data()));
        },
        .decl_count_of => {
            const ty = self.ecaArgTy(2);
            self.vm.regs.set(.ret(0), if (ty.index(types)) |i| i.map.entries.len else 0);
        },
        .len_of => {
            const ty = self.ecaArgTy(2);
            self.vm.regs.set(.ret(0), ty.len(types) orelse b: {
                types.reportSloc(self.ecaArgSloc(1), "directive only works on structs" ++
                    " and arrays, {} is not", .{ty});
                break :b 0;
            });
        },
        .size_of => {
            const ty = self.ecaArgTy(2);
            self.vm.regs.set(.ret(0), ty.size(types));
        },
        .align_of => {
            const ty = self.ecaArgTy(2);
            self.vm.regs.set(.ret(0), ty.alignment(types));
        },
        .type_info => self.doTypeInfoInterrupt(vm_ctx),
        .alloc_global => {
            const elem_ty = self.ecaArgTy(1);
            const ptr = self.ecaArg(2);
            const len: usize = @intCast(self.ecaArg(3));

            const mem = vm_ctx.memory[@intCast(ptr)..][0..@intCast(len * elem_ty.size(types))];

            const slice = types.addInternedGlobal(types.makeArray(len, elem_ty), mem);

            types.queue(.@"comptime", .init(.{ .Global = slice }));
            if (types.retainGlobals(.@"comptime", &self.gen.mach, true)) {
                self.vm.regs.set(.ret(0), elem_ty.alignment(types));
                self.vm.regs.set(.ret(1), 0);
            } else {
                const off = self.gen.mach.out.syms.items[@intFromEnum(self.gen.mach.out.globals.items[@intFromEnum(slice)])].offset;
                self.vm.regs.set(.ret(0), off);
                self.vm.regs.set(.ret(1), len);
            }
        },
    }
}

pub fn doTypeInterrupt(self: *Comptime, vm_ctx: *Vm.SafeContext) void {
    const types = self.getTypes();

    const sloc = self.ecaArgSloc(1);
    const scope = self.ecaArgTy(2);
    const ast = self.ecaArgAst(3);
    const data: Types.TypeInfo = @bitCast(vm_ctx.memory[@intCast(self.ecaArg(4))..][0..@sizeOf(Types.TypeInfo)].*);

    const key = Types.Scope{ .loc = .{
        .scope = scope,
        .file = @enumFromInt(sloc.namespace),
        .ast = ast,
    } };

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const res = switch (data.kind) {
        .@"@struct" => str: {
            const struct_data = data.data.@"@struct";

            const raw_fields = struct_data.fields.slice(self);
            const fields = tmp.arena.alloc(tys.Struct.Field, raw_fields.len);

            for (raw_fields, fields) |rf, *f| {
                f.* = .{
                    .name = rf.name.slice(self),
                    .ty = rf.ty,
                    .defalut_value = undefined,
                };
            }

            const stru = tys.Struct{
                .key = key,
                .index = .empty,
                .alignment = if (struct_data.alignment != 0) struct_data.alignment else b: {
                    var max: u64 = 0;
                    for (fields) |f| max = @max(max, f.ty.alignment(types));
                    break :b max;
                },
                .fields = fields,
            };

            const id: tys.Struct.Id = types.store.add(&types.pool.arena, stru);
            const entry = self.type_instances.getOrPutContext(
                self.getGpa(),
                .init(.{ .Struct = id }),
                .{ .types = types },
            ) catch unreachable;

            if (!entry.found_existing) {
                const stru_data: *tys.Struct = types.store.get(id);
                const perm_fields = types.pool.arena.dupe(tys.Struct.Field, stru_data.fields.?);
                for (perm_fields) |*f| {
                    f.name = types.pool.arena.dupe(u8, f.name);
                }
                stru_data.fields = perm_fields;
            } else {
                types.store.pop(id);
            }

            break :str entry.key_ptr.*;
        },
        .@"@union" => uni: {
            const union_data = data.data.@"@union";

            const raw_fields = union_data.fields.slice(self);
            const fields = tmp.arena.alloc(tys.Union.Field, raw_fields.len);

            for (raw_fields, fields) |rf, *f| {
                f.* = .{
                    .name = rf.name.slice(self),
                    .ty = rf.ty,
                };
            }

            const stru = tys.Union{
                .key = key,
                .index = .empty,
                .tag = union_data.tag,
                .fields = fields,
            };

            const id: tys.Union.Id = types.store.add(&types.pool.arena, stru);
            const entry = self.type_instances.getOrPutContext(
                self.getGpa(),
                .init(.{ .Union = id }),
                .{ .types = types },
            ) catch unreachable;

            if (!entry.found_existing) {
                const stru_data: *tys.Union = types.store.get(id);
                const perm_fields = types.pool.arena.dupe(tys.Union.Field, stru_data.fields.?);
                for (perm_fields) |*f| {
                    f.name = types.pool.arena.dupe(u8, f.name);
                }
                stru_data.fields = perm_fields;
            } else {
                types.store.pop(id);
            }

            break :uni entry.key_ptr.*;
        },
        .@"@enum" => enu: {
            const enum_data = data.data.@"@enum";

            const raw_fields = enum_data.fields.slice(self);
            const fields = tmp.arena.alloc(tys.Enum.Field, raw_fields.len);

            for (raw_fields, fields) |rf, *f| {
                f.* = .{
                    .name = rf.name.slice(self),
                    .value = rf.value,
                };
            }

            const stru = tys.Enum{
                .key = key,
                .index = .empty,
                .backing_int = enum_data.backing_int,
                .fields = fields,
            };

            const id: tys.Enum.Id = types.store.add(&types.pool.arena, stru);
            const entry = self.type_instances.getOrPutContext(
                self.getGpa(),
                .init(.{ .Enum = id }),
                .{ .types = types },
            ) catch unreachable;

            if (!entry.found_existing) {
                const stru_data: *tys.Enum = types.store.get(id);
                const perm_fields = types.pool.arena.dupe(tys.Enum.Field, stru_data.fields.?);
                for (perm_fields) |*f| {
                    f.name = types.pool.arena.dupe(u8, f.name);
                }
                stru_data.fields = perm_fields;
            } else {
                types.store.pop(id);
            }

            break :enu entry.key_ptr.*;
        },
        .pointer => types.makePtr(data.data.pointer),
        .slice => types.makeSlice(data.data.slice),
        .nullable => types.makeNullable(data.data.nullable),
        .tuple => types.makeTuple(@ptrCast(types.pool.arena.dupe(
            Types.Id,
            data.data.tuple.slice(self),
        ))),
        .fnty => types.internPtr(.FnTy, .{
            .args = @ptrCast(types.pool.arena.dupe(
                Types.Id,
                data.data.fnty.args.slice(self),
            )),
            .ret = data.data.fnty.ret,
        }),
        .array => types.makeArray(data.data.array.len, data.data.array.elem),
        .simd => types.makeSimd(data.data.simd.elem, data.data.simd.len),
        .builtin, .template, .global, .@"@fn" => return types.reportSloc(sloc, "can not be constructed (yet?)", .{}),
    };

    self.vm.regs.set(.ret(0), @intFromEnum(res));
}

pub fn doTypeInfoInterrupt(self: *Comptime, vm_ctx: *Vm.SafeContext) void {
    const types = self.getTypes();

    const ret_addr = self.ecaArg(1);
    const ty = self.ecaArgTy(3);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const tp: Types.TypeInfo = switch (ty.data()) {
        .Builtin => .{ .kind = .builtin, .data = .{ .builtin = {} } },
        .Pointer => |ptr_ty| .{
            .kind = .pointer,
            .data = .{ .pointer = types.store.get(ptr_ty).* },
        },
        .Slice => |slice_ty| .{
            .kind = .slice,
            .data = .{ .slice = types.store.get(slice_ty).elem },
        },
        .Nullable => |nullable_ty| .{
            .kind = .nullable,
            .data = .{ .nullable = types.store.get(nullable_ty).inner },
        },
        .Array => |array_ty| .{
            .kind = .array,
            .data = .{ .array = types.store.get(array_ty).* },
        },
        .Struct => |sty| b: {
            const struct_ty: tys.Struct.Id = sty;

            const fields = struct_ty.getFields(types);

            const Field = @TypeOf(@as(Types.TypeInfo, undefined)
                .data.@"@struct".fields).elem;

            const field_mem = tmp.arena.alloc(Field, fields.len);

            for (fields, 0..) |f, i| {
                field_mem[i] = .{
                    .name = .alloc(self, f.name),
                    .ty = f.ty,
                    .defalut_value = undefined,
                };
            }

            break :b .{ .kind = .@"@struct", .data = .{ .@"@struct" = .{
                .alignment = struct_ty.getAlignment(types),
                .fields = .alloc(self, field_mem),
                .decls = self.allocDecls(ty),
            } } };
        },
        .Enum => |enum_ty| b: {
            const fields = enum_ty.getFields(types);

            const Field = @TypeOf(@as(Types.TypeInfo, undefined)
                .data.@"@enum".fields).elem;

            const field_mem = tmp.arena.alloc(Field, fields.len);

            for (fields, 0..) |f, i| {
                field_mem[i] = .{ .name = .alloc(self, f.name), .value = f.value };
            }

            break :b .{ .kind = .@"@enum", .data = .{ .@"@enum" = .{
                .backing_int = enum_ty.getBackingInt(types),
                .fields = .alloc(self, field_mem),
                .decls = self.allocDecls(ty),
            } } };
        },
        .Union => |union_ty| b: {
            const fields = union_ty.getFields(types);

            const Field = @TypeOf(@as(Types.TypeInfo, undefined)
                .data.@"@union".fields).elem;

            const field_mem = tmp.arena.alloc(Field, fields.len);

            for (fields, 0..) |f, i| {
                field_mem[i] = .{ .name = .alloc(self, f.name), .ty = f.ty };
            }

            break :b .{ .kind = .@"@union", .data = .{ .@"@union" = .{
                .tag = union_ty.getTag(types),
                .fields = .alloc(self, field_mem),
                .decls = self.allocDecls(ty),
            } } };
        },
        .FnTy => |fnptr_ty| b: {
            const sig: *tys.FnTy = types.store.get(fnptr_ty);

            break :b .{ .kind = .fnty, .data = .{ .fnty = .{
                .args = .alloc(self, sig.args),
                .ret = sig.ret,
            } } };
        },
        .Func => |fn_ty| b: {
            const sig: *tys.Func = types.store.get(fn_ty);

            break :b .{ .kind = .@"@fn", .data = .{ .@"@fn" = .{
                .args = .alloc(self, sig.args),
                .ret = sig.ret,
            } } };
        },
        .Tuple => |tuple_ty| b: {
            const fields = tuple_ty.getFields(types);

            break :b .{
                .kind = .tuple,
                .data = .{ .tuple = .alloc(self, @ptrCast(fields)) },
            };
        },
        .Template => |template_ty| b: {
            const template: *tys.Template = types.store.get(template_ty);
            break :b .{
                .kind = .template,
                .data = .{ .template = .{ .is_inline = template.is_inline } },
            };
        },
        .Global => |global_ty| b: {
            const global: *tys.Global = types.store.get(global_ty);
            break :b .{ .kind = .global, .data = .{ .global = .{
                .ty = global.ty,
                .readonly = global.readonly,
            } } };
        },
        .Simd => |simd_ty| b: {
            const simd: *tys.Simd = types.store.get(simd_ty);
            break :b .{ .kind = .simd, .data = .{ .simd = .{
                .elem = simd.elem,
                .len = simd.len,
            } } };
        },
    };

    vm_ctx.memory = self.gen.mach.out.code.items;
    const ptr = vm_ctx.memory[@intCast(ret_addr)..].ptr;
    @as(*align(1) Types.TypeInfo, @ptrCast(ptr)).* = tp;
}

pub fn allocDecls(self: *Comptime, ty: Types.Id) Types.Slice(Types.TypeInfo.Decl) {
    const index = ty.index(self.getTypes()).?;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const decls = tmp.arena.alloc(Types.TypeInfo.Decl, index.map.entries.len);
    for (index.map.entries.items(.value), decls) |key, *d| {
        d.* = .{
            .name = .alloc(self, key.name),
        };
    }
    return .alloc(self, decls);
}

pub fn jitFunc(self: *Comptime, fnc: utils.EntId(tys.Func), root_abi: Types.Abi) !void {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const gen = Codegen.init(tmp.arena, self.getTypes(), .@"comptime", .ableos);
    defer gen.deinit();

    self.getTypes().queue(gen.target, .init(.{ .Func = fnc }));
    try compileDependencies(
        gen,
        self.getTypes().func_work_list.get(gen.target).items.len - 1,
        self.getTypes().ct.gen.mach.out.relocs.items.len,
        root_abi,
    );
}

pub fn jitExpr(
    self: *Comptime,
    name: []const u8,
    scope: Codegen.Scope,
    ctx: Codegen.Ctx,
    value: Ast.Id,
) !struct { JitResult, Types.Id } {
    return self.jitExprLow(name, scope, ctx, false, value) catch |err| switch (err) {
        error.Never => {
            if (scope == .Tmp) scope.Tmp.errored = true;
            return error.Never;
        },
    };
}

pub fn inferType(self: *Comptime, name: []const u8, scope: Codegen.Scope, ctx: Codegen.Ctx, value: Ast.Id) !Types.Id {
    return (self.jitExprLow(name, scope, ctx, true, value) catch |err| switch (err) {
        error.Never => {
            if (scope == .Tmp) scope.Tmp.errored = true;
            return err;
        },
    })[1];
}

pub fn addInProgress(self: *Comptime, expr: Ast.Id, scope: Types.Id) !void {
    const types = self.getTypes();

    if (std.mem.indexOfScalar(Loc, self.in_progress.items, .{
        .ast = expr,
        .scope = scope,
    })) |idx| {
        for (self.in_progress.items[idx..]) |lc| {
            types.report(lc.scope.file(self.getTypes()).?, lc.ast, "cycle goes trough here", .{});
        }
        return error.Never;
    }

    self.in_progress.append(self.getGpa(), .{ .ast = expr, .scope = scope }) catch unreachable;
}

pub const JitResult = union(enum) {
    func: utils.EntId(tys.Func),
    constant: i64,
};

pub fn jitExprLow(
    self: *Comptime,
    name: []const u8,
    scope: Codegen.Scope,
    ctx: Codegen.Ctx,
    only_inference: bool,
    value: Ast.Id,
) error{Never}!struct { JitResult, Types.Id } {
    const types = self.getTypes();
    const ast = types.getFile(scope.file(types));

    if (value.tag() == .Buty) {
        types.stats.skipped_buty_jit_exprs += 1;
        return .{ .{ .constant = @intFromEnum(Types.Id.fromLexeme(ast.exprs.get(value).Buty.*.bt)) }, .type };
    }

    var jit_met = types.metrics.begin(.jit);
    defer jit_met.end();

    const id = types.allocTempType(tys.Func);
    defer types.freeTempType(tys.Func, id);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const gen = Codegen.init(tmp.arena, types, .@"comptime", .ableos);
    defer gen.deinit();

    gen.only_inference = only_inference;

    const pop_until = types.func_work_list.get(.@"comptime").items.len;
    const new_syms_pop_until = self.getTypes().ct.gen.mach.out.relocs.items.len;

    var ret: Codegen.Value = undefined;
    {
        var scratch = tmp.arena.checkpoint();
        defer scratch.deinit();
        defer gen.bl.func.reset();

        const token = gen.beginBuilder(tmp.arena, .never, &.{.{ .Reg = .i64 }}, &.{}, 0, 0);
        gen.source = .init(scope, types);
        gen.name = name;
        gen.struct_ret_ptr = null;

        const ptr = gen.bl.addParam(.none, 0, @intFromEnum(Types.Id.never));

        ret = gen.emit(ctx.addLoc(ptr), value) catch |err| switch (err) {
            error.Never => return error.Never,
            error.Unreachable => .{ .ty = .never },
        };
        if (ctx.ty) |ty| {
            try gen.typeCheck(value, &ret, ty);
        }

        if (ret.id == .Value and ret.id.Value.kind == .CInt) {
            types.func_work_list.getPtr(.@"comptime").items.len = pop_until;
            types.stats.skipped_constant_jit_exprs += 1;
            return .{ .{ .constant = ret.id.Value.extra(.CInt).value }, ret.ty };
        }

        if (types.retainGlobals(.@"comptime", &self.gen.mach, true)) return error.Never;

        if (ret.id == .Pointer and gen.abiCata(ret.ty) == .ByValue and
            ret.id.Pointer.kind == .GlobalAddr)
        {
            types.func_work_list.getPtr(.@"comptime").items.len = pop_until;
            const cnst = self.gen.mach.out.readFromSym(
                ret.id.Pointer.extra(.GlobalAddr).id,
                0,
                @intCast(ret.ty.size(self.getTypes())),
                true,
            ).?.value;
            types.stats.skipped_global_jit_exprs += 1;
            return .{ .{ .constant = cnst }, ret.ty };
        }

        types.stats.full_jit_exprs += 1;

        gen.emitGenericStore(.none, ptr, &ret);

        gen.bl.end(token);

        if (!only_inference) {
            gen.errored = self.getTypes().retainGlobals(.@"comptime", &self.gen.mach, true) or
                gen.errored;

            const reg_alloc_results = optimizeComptime(comptime_opts, HbvmGen, &self.gen, @ptrCast(&gen.bl.func));

            var emit_func_met = types.metrics.begin(.jit_emit_func);
            defer emit_func_met.end();
            self.gen.emitFunc(
                @ptrCast(&gen.bl.func),
                .{
                    .id = @intFromEnum(id),
                    .linkage = .exported,
                    .is_inline = false,
                    .optimizations = .{ .allocs = reg_alloc_results },
                    .builtins = .{},
                    .uuid = comptime_uuid,
                },
            );
        }
    }

    if (gen.errored) {
        return error.Never;
    }

    if (!only_inference) {
        compileDependencies(gen, pop_until, new_syms_pop_until, gen.abi) catch return error.Never;
    } else {
        types.func_work_list.getPtr(.@"comptime").items.len = pop_until;
    }

    return .{ .{ .func = id }, ret.ty };
}

pub fn compileDependencies(self: *Codegen, pop_until: usize, new_syms_pop_until: usize, root_abi: Types.Abi) !void {
    while (self.types.nextTask(self.target, pop_until)) |func| {
        if (!self.types.canPop(self.target, pop_until)) {
            self.abi = root_abi;
        }

        defer self.bl.func.reset();

        try self.build(func);

        self.errored = self.types.retainGlobals(self.target, &self.types.ct.gen.mach, true) or
            self.errored;

        const reg_alloc_results = optimizeComptime(comptime_opts, HbvmGen, &self.types.ct.gen, @ptrCast(&self.bl.func));

        var emit_func_met = self.types.metrics.begin(.jit_emit_func);
        self.types.ct.gen.emitFunc(
            @ptrCast(&self.bl.func),
            .{
                .id = @intFromEnum(func),
                .linkage = .local,
                .is_inline = false,
                .optimizations = .{ .allocs = reg_alloc_results },
                .builtins = .{},
                .uuid = comptime_uuid,
            },
        );
        emit_func_met.end();
    }

    root.hbvm.object.jitLink(self.types.ct.gen.mach.out, new_syms_pop_until);
}

pub fn evalTy(self: *Comptime, name: []const u8, scope: Codegen.Scope, ty_expr: Ast.Id) !Types.Id {
    const res, _ = try self.eval(name, scope, ty_expr, .type);

    const types = self.getTypes();
    return Types.Id.fromRaw(res, types) orelse {
        types.report(scope.file(types), ty_expr, "resulting type has a corrupted value", .{});
        return error.Never;
    };
}

pub fn eval(self: *Comptime, name: []const u8, scope: Codegen.Scope, int_conts: Ast.Id, ty: ?Types.Id) !struct { i64, Types.Id } {
    const res, const t = try self.jitExpr(name, scope, .{ .ty = ty }, int_conts);
    const types = self.getTypes();
    const file = scope.file(types);
    switch (res) {
        .func => |id| {
            var data: [8]u8 = @splat(0);
            try self.runVm(file, types.posOf(file, int_conts).index, @intFromEnum(id), &data);
            return .{ @bitCast(data), t };
        },
        .constant => |c| return .{ c, t },
    }
}

pub fn evalIntConst(self: *Comptime, scope: Codegen.Scope, int_conts: Ast.Id) !i64 {
    const res, _ = try self.eval("", scope, int_conts, null);
    return res;
}

pub fn evalGlobal(self: *Comptime, name: []const u8, global: utils.EntId(tys.Global), ty: ?Types.Id, value: Ast.Id) error{Never}!void {
    const types = self.getTypes();
    const glbal = global.get(types);
    const file = glbal.key.loc.file;
    const ast = types.getFile(file);

    if (value.tag() == .Idk) {
        const exp_ty = ty orelse {
            return types.report(file, value, "the uninitialized variable needs a type", .{});
        };

        glbal.ty = exp_ty;
        glbal.uninit = true;
        glbal.data = .{ .imm = &.{} };
        glbal.data.imm.len = @intCast(exp_ty.size(types));
        return;
    }

    if (value.tag() == .Directive and ast.exprs.get(value).Directive.kind == .thread_local_storage) {
        const expr = ast.exprs.get(value).Directive;
        if (expr.args.len() != 0) {
            return types.report(file, expr, "the @thread_local_storage directive only takes 0 arguments, TODO: support initializer", .{});
        }

        const exp_ty = ty orelse {
            return types.report(file, value, "the uninitialized variable needs a type", .{});
        };

        glbal.ty = exp_ty;
        glbal.uninit = true;
        glbal.thread_local = true;
        glbal.data = .{ .imm = &.{} };
        glbal.data.imm.len = @intCast(exp_ty.size(types));
        return;
    }

    const res, const fty = try self.jitExpr(name, .{ .Perm = self.getTypes().store.get(global).key.loc.scope }, .{ .ty = ty }, value);
    const data = types.pool.arena.alloc(u8, @intCast(fty.size(types)));
    switch (res) {
        .func => |id| {
            try self.runVm(file, types.posOf(file, value).index, @intFromEnum(id), data);
        },
        .constant => |c| {
            @memcpy(data, @as(*const [@sizeOf(@TypeOf(c))]u8, @ptrCast(&c))[0..data.len]);
        },
    }

    glbal.data = .{ .imm = data };
    glbal.ty = fty;
    if (fty == .type) {
        const typ: Types.Id = @enumFromInt(@as(u32, @bitCast(data[0..4].*)));
        if (typ.data() == .Template) {
            const item = typ.data().Template.get(types);
            if (std.mem.eql(u8, name, item.key.name(types))) item.is_inline = glbal.readonly;
        }
    }

    if (fty.data() == .FnTy) {
        const id: utils.EntId(tys.Func) = @enumFromInt(@as(u32, @bitCast(data[0..4].*)));
        const func = types.store.get(id);
        if (std.mem.eql(u8, name, func.key.name(types))) func.is_inline = glbal.readonly;
    }
}
