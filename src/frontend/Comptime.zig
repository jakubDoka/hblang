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

vm: Vm = .{},
gen: HbvmGen,
in_progress: std.ArrayListUnmanaged(Loc) = .{},

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
    name_of,
    make_array,
    ChildOf,
    kind_of,
    len_of,
    size_of,
    align_of,
    type_info,
};

pub fn init(gpa: *utils.Pool) Comptime {
    var self = Comptime{ .gen = .{ .gpa = gpa } };
    self.gen.out.code.resize(gpa.allocator(), stack_size) catch unreachable;
    self.gen.out.code.items[self.gen.out.code.items.len - 1] = @intFromEnum(isa.Op.tx);
    self.gen.out.code.items[self.gen.out.code.items.len - 2] = @intFromEnum(isa.Op.eca);
    self.vm.regs.set(.stack_addr, stack_size - 2);
    return self;
}

pub fn getTypes(self: *Comptime) *Types {
    return @alignCast(@fieldParentPtr("ct", self));
}

inline fn getGpa(self: *Comptime) std.mem.Allocator {
    return self.gen.gpa.allocator();
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

pub const PartialEvalResult = union(enum) {
    Resolved: u64,
    Arbitrary: utils.EntId(tys.Global),
    DependsOnRuntimeControlFlow: *Node,
    Unsupported: struct { *Node, []const u8 },
};

pub const PartialEvalResult2 = union(enum) {
    Arbitrary: utils.EntId(tys.Global),
    DependsOnRuntimeControlFlow: *Node,
    Unsupported: struct { *Node, []const u8 },
};

const PartialEvalCtx = struct {
    file: Types.File,
    scope: Types.Id,
    pos: u32,
    error_slot: *PartialEvalResult2,

    pub inline fn err(self: PartialEvalCtx, res: PartialEvalResult2) error{Never} {
        self.error_slot.* = res;
        return error.Never;
    }
};

pub fn partialEval2(self: *Comptime, ctx: PartialEvalCtx, bl: *Builder, expr: *Node) error{Never}!*Node {
    const types = self.getTypes();

    switch (expr.extra2()) {
        .CInt => return expr,
        .UnOp => |extra| {
            const opr = expr.inputs()[1].?;
            const oper = try self.partialEval2(ctx, bl, opr);

            const res = extra.op.eval(expr.data_type, opr.data_type, oper.extra(.CInt).value);
            const node_res = bl.addIntImm(.none, expr.data_type, res);
            bl.func.subsume(node_res, expr);
            return node_res;
        },
        .BinOp => |extra| {
            const lhs = expr.inputs()[1].?;
            const rhs = expr.inputs()[2].?;
            const lhs_val = try self.partialEval2(ctx, bl, lhs);
            const rhs_val = try self.partialEval2(ctx, bl, rhs);

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

            var lca: ?*Func.CfgNode = null;
            var interestingOps = std.ArrayList(*Node){};
            for (expr.outputs()) |o| {
                if (o.get().kind != .BinOp) {
                    if (!o.get().isMemOp() or
                        o.get().base() != o.get() or
                        o.get().isSub(graph.MemCpy))
                    {
                        return ctx.err(.{ .Unsupported = .{ o.get(), "stack mem op" } });
                    }
                }

                const use = o.get().tryCfg0() orelse switch (o.get().extra2()) {
                    .BinOp => |extra| {
                        if (extra.op != .iadd and extra.op != .isub) {
                            return ctx.err(.{ .Unsupported = .{ o.get(), "stack binop" } });
                        }

                        for (o.get().outputs()) |oo| {
                            if (!oo.get().isMemOp() or
                                oo.get().base() != o.get() or
                                oo.get().isSub(graph.MemCpy))
                            {
                                return ctx.err(.{ .Unsupported = .{ oo.get(), "stack mem op" } });
                            }

                            const use = oo.get().tryCfg0() orelse continue;
                            lca = (lca orelse use).findLca(use);
                            interestingOps.append(tmp.arena.allocator(), oo.get()) catch unreachable;
                        }

                        continue;
                    },
                    else => return ctx.err(.{ .Unsupported = .{ o.get(), "floating stack op" } }),
                };
                lca = (lca orelse use).findLca(use);
                interestingOps.append(tmp.arena.allocator(), o.get()) catch unreachable;
            }

            for (interestingOps.items) |op| {
                if (op.cfg0() == lca) continue;

                for (interestingOps.items) |oop| {
                    if (oop.cfg0() == lca or oop == op or
                        oop.cfg0().idepth() < op.cfg0().idepth()) continue;

                    var cursor = oop.cfg0();
                    while (cursor != lca) {
                        if (op.cfg0() == cursor) break;
                        cursor = cursor.idom();
                    } else {
                        return ctx.err(.{ .DependsOnRuntimeControlFlow = oop });
                    }
                }
            }

            for (interestingOps.items) |op| {
                switch (op.kind) {
                    .Store => {
                        const base, const offset = op.base().knownOffset();
                        std.debug.assert(base == expr);

                        const val = try self.partialEval2(ctx, bl, op.value().?);

                        switch (val.extra2()) {
                            .CInt => |extra| {
                                @memcpy(
                                    mem[@intCast(offset)..][0..op.data_type.size()],
                                    std.mem.asBytes(&extra.value)[0..op.data_type.size()],
                                );
                            },
                            else => return ctx.err(.{ .Unsupported = .{ val, "stack store value" } }),
                        }
                    },
                    else => return ctx.err(.{ .Unsupported = .{ op, "TODO: stack mut op" } }),
                }
            }

            types.queue(.@"comptime", .init(.{ .Global = global }));

            return bl.addGlobalAddr(.none, @intFromEnum(global));
        },
        .Load => {
            const base, const offset = (try self.partialEval2(ctx, bl, expr.base())).knownOffset();

            switch (base.extra2()) {
                .GlobalAddr => |extra| {
                    const gid: utils.EntId(tys.Global) = @enumFromInt(extra.id);
                    const global: *tys.Global = types.store.get(gid);

                    if (types.store.get(gid).completion.get(.@"comptime") != .compiled) {
                        types.queue(.@"comptime", .init(.{ .Global = gid }));
                        if (types.retainGlobals(.@"comptime", &self.gen)) {
                            return ctx.err(.{ .Unsupported = .{ base, "retained globals" } });
                        }
                    }

                    for (global.relocs) |rel| {
                        if (rel.offset == offset) {
                            return bl.addGlobalAddr(.none, rel.target);
                        }
                    }

                    const mem = global.data.mut;
                    var value: i64 = 0;
                    @memcpy(
                        std.mem.asBytes(&value)[0..expr.data_type.size()],
                        mem[@intCast(offset)..][0..expr.data_type.size()],
                    );

                    return bl.addIntImm(.none, expr.data_type, value);
                },
                else => return ctx.err(.{ .Unsupported = .{ base, "load base" } }),
            }
        },
        else => return ctx.err(.{ .Unsupported = .{ expr, "TODO: generic op" } }),
    }
}

pub fn partialEval(self: *Comptime, file: Types.File, scope: Types.Id, pos: u32, bl: *Builder, expr: *Node) PartialEvalResult {
    errdefer unreachable;

    const types = self.getTypes();

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    // TODO: maybe use the vm stack instead
    var work_list = std.ArrayListUnmanaged(*Node).initBuffer(tmp.arena.alloc(*Node, 1024));

    work_list.appendAssumeCapacity(expr);

    for (0..100000) |_| {
        const curr: *Node = work_list.pop().?;
        if (curr.isDead()) continue;
        std.debug.print("{f}\n", .{curr});
        const res = switch (curr.kind) {
            .Local => b: {
                {
                    const global = curr.inputs()[1].?.extra(.LocalAlloc).meta;

                    if (global != std.math.maxInt(u32)) {
                        types.store.get(@as(utils.EntId(tys.Global), @enumFromInt(global))).data.freeze();

                        if (work_list.items.len == 0) {
                            return .{ .Arbitrary = @enumFromInt(global) };
                        } else {
                            break :b bl.addGlobalAddr(curr.sloc, global);
                        }
                    }
                }

                work_list.appendAssumeCapacity(curr);

                var iter = std.mem.reverseIterator(curr.outputs());
                while (iter.next()) |o| {
                    const use: *Node = o.get();
                    if (use.knownMemOp()) |op| {
                        const base, _ = op[0].base().knownOffset();
                        if (op[0].isStore() and base == curr) {
                            work_list.appendAssumeCapacity(op[0]);
                            continue;
                        } else if (op[0].isStore() or op[0].isLoad()) {
                            continue;
                        }
                    }
                    if (use.kind == .Call) {
                        std.debug.print("foob\n", .{});
                        work_list.appendAssumeCapacity(use.outputs()[0].get());
                        continue;
                    }
                    if (use.kind == .Scope) continue;
                    if (use.outputs().len == 0) continue;
                    return .{ .Unsupported = .{ use, "local" } };
                }

                const global = types.addUniqueGlobal(scope);
                types.store.get(global).data = .{ .mut = types.pool.arena.alloc(
                    u8,
                    @intCast(curr.inputs()[1].?.extra(.LocalAlloc).size),
                ) };
                types.store.get(global).ty = @enumFromInt(curr.inputs()[1].?.extra(.LocalAlloc).debug_ty);
                curr.inputs()[1].?.extra(.LocalAlloc).meta = @intFromEnum(global);

                continue;
            },
            .Store => {
                const base, const offset = curr.base().knownOffset();
                if (base.kind != .Local) {
                    return .{ .Unsupported = .{ curr, "non local store" } };
                }
                const global: utils.EntId(tys.Global) = @enumFromInt(base.inputs()[1].?.extra(.LocalAlloc).meta);
                const data = types.store.get(global).data;

                if (curr.value().?.kind != .CInt) {
                    work_list.appendAssumeCapacity(curr);
                    work_list.appendAssumeCapacity(curr.value().?);
                    continue;
                }

                const value = curr.value().?.extra(.CInt).value;
                @memcpy(
                    data.mut[@intCast(offset)..][0..@intCast(curr.data_type.size())],
                    @as([*]const u8, @ptrCast(&value))[0..@intCast(curr.data_type.size())],
                );

                bl.func.subsume(curr.mem(), curr);

                continue;
            },
            .GlobalAddr => b: {
                const global = curr.extra(.GlobalAddr).id;
                const below = work_list.getLastOrNull() orelse {
                    return .{ .Arbitrary = @enumFromInt(global) };
                };
                _ = below; // autofix

                const gid: utils.EntId(tys.Global) = @enumFromInt(global);
                if (types.store.get(gid).completion.get(.@"comptime") != .compiled) {
                    types.queue(.@"comptime", .init(.{ .Global = gid }));
                    if (types.retainGlobals(.@"comptime", &self.gen)) {
                        return .{ .Unsupported = .{ curr, "retained globals" } };
                    }
                }

                const addr = self.gen.out.syms.items[@intFromEnum(self.gen.out.globals.items[global])].offset;
                break :b bl.addIntImm(curr.sloc, .i64, addr);
            },
            .CInt => {
                if (work_list.items.len == 0) {
                    return .{ .Resolved = @as(u64, @bitCast(curr.extra(.CInt).*)) };
                }

                continue;
            },
            .Phi => b: {
                if (curr.inputs()[0].?.kind == .Loop and curr.inputs()[2] == null) {
                    break :b curr.inputs()[1].?;
                } else {
                    return .{ .Unsupported = .{ curr, "phi" } };
                }
            },
            .BinOp, .UnOp => |t| b: {
                var requeued = false;

                for (curr.inputs()[1..]) |arg| {
                    if (arg.?.kind != .CInt) {
                        if (!requeued) work_list.appendAssumeCapacity(curr);
                        work_list.appendAssumeCapacity(arg.?);
                        requeued = true;
                    }
                }
                if (requeued) continue;

                switch (t) {
                    .BinOp => {
                        const lhs, const rhs = .{ curr.inputs()[1].?.extra(.CInt).value, curr.inputs()[2].?.extra(.CInt).value };
                        break :b bl.addIntImm(.none, curr.data_type, curr.extra(.BinOp).op.eval(curr.data_type, lhs, rhs));
                    },
                    .UnOp => {
                        const oper = curr.inputs()[1].?.extra(.CInt).value;
                        break :b bl.addIntImm(.none, curr.data_type, curr.extra(.UnOp).op
                            .eval(curr.inputs()[1].?.data_type, curr.data_type, oper));
                    },
                    else => unreachable,
                }
            },
            .Ret => {
                work_list.appendAssumeCapacity(curr.inputs()[0].?);
                continue;
            },
            .CallEnd => {
                const call: *Node = curr.inputs()[0].?;
                std.debug.assert(call.kind == .Call);

                if (call.extra(.Call).id != eca) {
                    const func_id: utils.EntId(tys.Func) = @enumFromInt(call.extra(.Call).id);
                    const func = types.store.get(func_id);

                    if (func.recursion_lock) {
                        types.report(func.key.loc.file, func.key.loc.ast, "the functions types most likely depend on it being evaluated", .{});
                        return .{ .Unsupported = .{ curr, "recursive call" } };
                    }

                    if (func.completion.get(.@"comptime") == .queued) {
                        self.jitFunc(func_id) catch return .{ .Unsupported = .{ curr, "jit func" } };
                    }
                    if (types.store.get(func_id).errored) return .{ .Unsupported = .{ curr, "errored" } };
                    std.debug.assert(types.store.get(func_id).completion.get(.@"comptime") == .compiled);
                    std.debug.assert(self.gen.out.funcs.items.len > call.extra(.Call).id);
                }

                var requeued = false;
                for (call.inputs()[2..], 0..) |arg, arg_idx| {
                    if (arg.?.kind != .CInt) {
                        if (!requeued) work_list.appendAssumeCapacity(curr);
                        work_list.appendAssumeCapacity(arg.?);
                        requeued = true;
                    } else {
                        types.ct.vm.regs.set(.arg(arg_idx), @bitCast(arg.?.extra(.CInt).*));
                    }
                }

                if (requeued) continue;

                types.ct.runVm(file, pos, call.extra(.Call).id, &.{}) catch {
                    return .{ .Unsupported = .{ curr, "vm error" } };
                };

                for (tmp.arena.dupe(Node.Out, curr.outputs())) |n| {
                    const o = n.get();
                    if (o.kind == .Ret) {
                        const idx = o.extra(.Ret).index;
                        const ret = types.ct.vm.regs.get(.ret(idx));
                        const ret_vl = bl.addIntImm(.none, o.data_type, @bitCast(ret));
                        bl.func.subsume(ret_vl, o);
                        work_list.appendAssumeCapacity(ret_vl);
                    }
                    if (o.kind == .Mem) {
                        bl.func.subsume(call.inputs()[1].?, o);
                    }
                }
                // NOTE: the backend expects this
                call.data_type = .bot;
                bl.func.subsume(call.inputs()[0].?, curr);
                continue;
            },
            .Load => b: {
                const base, const offset = curr.base().knownOffset();

                if (base.kind == .GlobalAddr) {
                    const glob_id: utils.EntId(tys.Global) = @enumFromInt(base.extra(.GlobalAddr).id);
                    const glob: *tys.Global = types.store.get(glob_id);

                    std.debug.assert(curr.data_type.isInt());

                    var mem: u64 = 0;
                    @memcpy(
                        @as([*]u8, @ptrCast(&mem))[0..@intCast(curr.data_type.size())],
                        glob.data.slice()[@intCast(offset)..][0..@intCast(curr.data_type.size())],
                    );

                    break :b bl.addIntImm(.none, curr.data_type, @bitCast(mem));
                } else if (base.kind == .CInt) {
                    var mem: u64 = 0;

                    @memcpy(
                        @as([*]u8, @ptrCast(&mem))[0..@intCast(curr.data_type.size())],
                        self.gen.out.code.items[@intCast(base.extra(.CInt).value + offset)..][0..@intCast(curr.data_type.size())],
                    );

                    break :b bl.addIntImm(.none, curr.data_type, @bitCast(mem));
                } else if (base.kind == .Local) fold_initializer: {
                    var call: ?*Node = null;
                    var has_stores = false;
                    for (base.outputs()) |o| {
                        if (o.get().kind == .Call and o.pos() >= 2) {
                            if (call) |_| {
                                return .{ .Unsupported = .{ curr, "multiple calls" } };
                            }
                            call = o.get();
                        }

                        has_stores = has_stores or o.get().isStore();
                    }

                    const initializer = call orelse {
                        break :fold_initializer;
                    };

                    if (has_stores) return .{ .Unsupported = .{ curr, "initializer has stores" } };

                    work_list.appendAssumeCapacity(curr);
                    work_list.appendAssumeCapacity(initializer.outputs()[0].get());
                    continue;
                } else if (curr.base().kind == .BinOp and curr.base().inputs()[2].?.kind != .CInt) {
                    work_list.appendAssumeCapacity(curr);
                    work_list.appendAssumeCapacity(curr.base().inputs()[2].?);
                    continue;
                } else if (curr.base().kind == .BinOp and
                    curr.base().extra(.BinOp).op.neutralElememnt(.i64) ==
                        curr.base().inputs()[2].?.extra(.CInt).value)
                {
                    bl.func.subsume(curr.base().inputs()[1].?, curr.base());
                } else {
                    work_list.appendAssumeCapacity(curr);
                    work_list.appendAssumeCapacity(curr.base());
                    continue;
                }

                const loop_bit = 1 << 0;
                const if_bit = 1 << 1;

                const util = enum {
                    pub fn setBit(v: u16, bit: u16) u16 {
                        return v | bit;
                    }

                    pub fn clearBit(v: u16, bit: u16) u16 {
                        return v & ~bit;
                    }

                    pub fn hasBit(v: u16, bit: u16) bool {
                        return v & bit != 0;
                    }
                };

                var cursor = curr.mem();
                const bs = work_list.items.len;
                var seen = std.ArrayList(*Node).empty;
                var no_errors = false;
                defer if (!no_errors) for (seen.items) |v| {
                    v.schedule = std.math.maxInt(u16);
                };

                var loop_depth: usize = 0;
                for (0..10000) |_| {
                    if (work_list.items.len != bs) {
                        var data_dep_cont: usize = 0;
                        for (cursor.outputs()) |o| {
                            if (o.get().isLoad()) continue;
                            if (o.get().kind == .Call and o.pos() != 1) {
                                continue;
                            }
                            if (o.get().kind == .Scope) continue;

                            data_dep_cont += 1;
                        }
                        if (data_dep_cont > 1) {
                            if (data_dep_cont > 3) {
                                for (cursor.outputs()) |o| {
                                    std.debug.print("{f}\n\n", .{o});

                                    for (o.get().inputs()) |oo| {
                                        std.debug.print("<-{f}\n", .{oo.?});
                                    }
                                    std.debug.print("\n", .{});
                                    for (o.get().outputs()) |oo| {
                                        std.debug.print("->{f}\n", .{oo.get()});
                                    }
                                    std.debug.print("\n", .{});
                                }

                                std.debug.print("{f}\n", .{types.getFile(file).codePointer(pos)});
                                unreachable;
                            }
                            if (util.hasBit(cursor.schedule, if_bit)) {
                                cursor.schedule = util.clearBit(cursor.schedule, if_bit);
                                std.mem.swap(*Node, &work_list.items[work_list.items.len - 1], &cursor);
                                try seen.append(tmp.arena.allocator(), cursor);
                                continue;
                            } else {
                                cursor.schedule = util.setBit(cursor.schedule, if_bit);
                                _ = work_list.pop().?;
                            }
                        }
                    }

                    if (cursor.isStore()) {
                        if (cursor.base() != curr.base()) {
                            cursor = cursor.mem();
                        } else if (work_list.items.len == bs and loop_depth == 0) {
                            no_errors = true;
                            break :b cursor.value().?;
                        } else {
                            return .{ .DependsOnRuntimeControlFlow = curr };
                        }
                    } else if (cursor.kind == .Mem) {
                        if (cursor.inputs()[0].?.kind == .Start) {
                            return .{ .Unsupported = .{ cursor, "uninit comptime mem" } };
                        }
                        cursor = cursor.inputs()[0].?.inputs()[0].?.inputs()[1].?;
                    } else if (cursor.kind == .Phi) {
                        if (cursor.cfg0().base.kind == .Loop) {
                            if (cursor.inputs()[2] == null) {
                                cursor = cursor.inputs()[1].?;
                                continue;
                            }

                            if (util.hasBit(cursor.schedule, loop_bit)) {
                                try seen.append(tmp.arena.allocator(), cursor);
                                cursor.schedule = util.clearBit(cursor.schedule, loop_bit);
                                cursor = cursor.inputs()[2].?;
                                loop_depth += 1;
                            } else {
                                cursor.schedule = util.setBit(cursor.schedule, loop_bit);
                                cursor = cursor.inputs()[1].?;
                                loop_depth -= 1;
                            }
                        } else {
                            work_list.appendAssumeCapacity(cursor.inputs()[1].?);
                            cursor = cursor.inputs()[2].?;
                        }
                    } else {
                        return .{ .Unsupported = .{ cursor, "undandled load" } };
                    }
                } else unreachable;
            },
            else => return .{ .Unsupported = .{ curr, "undandled node" } },
        };

        bl.func.subsume(res, curr);
        work_list.appendAssumeCapacity(res);
    } else unreachable;
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

    self.vm.ip = if (entry_id == eca)
        stack_size - 2
    else
        self.gen.out.syms.items[@intFromEnum(self.gen.out.funcs.items[entry_id])].offset;
    std.debug.assert(self.vm.ip < self.gen.out.code.items.len);

    self.vm.fuel = 1024 * 128;
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

    var vm_ctx = Vm.SafeContext{
        .writer = if (false) std.fs.File.stderr().writer().any() else null,
        .color_cfg = .escape_codes,
        .memory = self.gen.out.code.items,
        .code_start = 0,
        .code_end = 0,
    };

    while (true) switch (b: {
        var hbvm_met = types.metrics.begin(.hbvm);
        defer hbvm_met.end();
        break :b self.vm.run(&vm_ctx) catch |err| {
            types.report(file, pos, "comptime execution failed: {}", .{@errorName(err)});
            return error.Never;
        };
    }) {
        .tx => break,
        .eca => {
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
                .Struct, .Union, .Enum => |t| {
                    const scope: Types.Id = @enumFromInt(self.ecaArg(1));
                    const ast = types.getFile(scope.file(types).?);
                    const struct_ast_id = self.ecaArgAst(2);
                    const struct_ast = ast.exprs.get(struct_ast_id).Type;

                    var tmp = utils.Arena.scrath(null);
                    defer tmp.deinit();
                    const captures = tmp.arena.alloc(Types.Scope.Capture, struct_ast.captures.len());

                    const prefix = 5;
                    for (captures, ast.exprs.view(struct_ast.captures), 0..) |*slot, cp, i| {
                        slot.* = .{
                            .id = .fromIdent(cp.id),
                            .ty = @enumFromInt(self.ecaArg(prefix + i * 2)),
                            .value = self.ecaArg(prefix + i * 2 + 1),
                        };
                        if (slot.ty.size(types) < 8) slot.value &=
                            (@as(u64, 1) << @intCast(slot.ty.size(types) * 8)) - 1;
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
                        ),
                        else => unreachable,
                    };

                    self.vm.regs.set(.ret(0), @intFromEnum(res));
                },
                .name_of => {
                    const ty: Types.Id = @enumFromInt(self.ecaArg(1));
                    const value = self.ecaArg(2);

                    const enm: tys.Enum.Id = ty.data().Enum;
                    const fields = enm.getFields(types);

                    if (value > fields.len) {
                        //   types.report(lfile, expr, "the enum value is out of bounds, it has no name", .{});
                        unreachable; // TODO: the enum value is corrupted
                    }

                    const ret_addr = self.gen.out.code.items.len;

                    self.gen.out.code.appendSlice(self.getGpa(), fields[@intCast(value)].name) catch unreachable;
                    vm_ctx.memory = self.gen.out.code.items;

                    self.vm.regs.set(.ret(0), ret_addr);
                    self.vm.regs.set(.ret(1), fields[@intCast(value)].name.len);
                },
                .make_array => {
                    const len = self.ecaArg(1);
                    const ty: Types.Id = @enumFromInt(self.ecaArg(2));
                    const slice = types.makeArray(@intCast(len), ty);
                    self.vm.regs.set(.ret(0), @intFromEnum(slice));
                },
                .ChildOf => {
                    const ty: Types.Id = @enumFromInt(self.ecaArg(2));

                    self.vm.regs.set(.ret(0), @intFromEnum(ty.child(types) orelse b: {
                        types.reportSloc(self.ecaArgSloc(1), "directive only work on pointer" ++
                            " types and slices, {} is not", .{ty});
                        break :b .never;
                    }));
                },
                .kind_of => {
                    const ty: Types.Id = @enumFromInt(self.ecaArg(2));
                    self.vm.regs.set(.ret(0), @intFromEnum(ty.data()));
                },
                .len_of => {
                    const ty: Types.Id = @enumFromInt(self.ecaArg(2));
                    self.vm.regs.set(.ret(0), ty.len(types) orelse b: {
                        types.reportSloc(self.ecaArgSloc(1), "directive only works on structs" ++
                            " and arrays, {} is not", .{ty});
                        break :b 0;
                    });
                },
                .size_of => {
                    const ty: Types.Id = @enumFromInt(self.ecaArg(2));
                    self.vm.regs.set(.ret(0), ty.size(types));
                },
                .align_of => {
                    const ty: Types.Id = @enumFromInt(self.ecaArg(2));
                    self.vm.regs.set(.ret(0), ty.alignment(types));
                },
                .type_info => {
                    const ret_addr = self.ecaArg(1);
                    const ty: Types.Id = @enumFromInt(self.ecaArg(3));

                    vm_ctx.memory[@intCast(ret_addr)..][0] = @intFromEnum(std.meta.activeTag(ty.data()));

                    var tmp = utils.Arena.scrath(null);
                    defer tmp.deinit();

                    const tp: Types.TypeInfo = switch (ty.data()) {
                        .Builtin => .{ .kind = .builtin, .data = .{ .builtin = {} } },
                        .Pointer => |ptr_ty| .{ .kind = .pointer, .data = .{ .pointer = types.store.get(ptr_ty).* } },
                        .Slice => |slice_ty| .{ .kind = .slice, .data = .{ .slice = types.store.get(slice_ty).* } },
                        .Nullable => |nullable_ty| .{ .kind = .nullable, .data = .{ .nullable = types.store.get(nullable_ty).inner } },
                        .Array => |array_ty| .{ .kind = .array, .data = .{ .array = types.store.get(array_ty).* } },
                        .Struct => |sty| b: {
                            const struct_ty: tys.Struct.Id = sty;

                            const fields = struct_ty.getFields(types);

                            const Field = @TypeOf(@as(Types.TypeInfo, undefined).data.@"@struct".fields).elem;

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
                            } } };
                        },
                        .Enum => |enum_ty| b: {
                            const fields = enum_ty.getFields(types);

                            const Field = @TypeOf(@as(Types.TypeInfo, undefined).data.@"@enum".fields).elem;

                            const field_mem = tmp.arena.alloc(Field, fields.len);

                            for (fields, 0..) |f, i| {
                                field_mem[i] = .{ .name = .alloc(self, f.name), .value = f.value };
                            }

                            break :b .{ .kind = .@"@enum", .data = .{ .@"@enum" = .{
                                .backing_int = enum_ty.getBackingInt(types),
                                .fields = .alloc(self, field_mem),
                            } } };
                        },
                        .Union => |union_ty| b: {
                            const fields = union_ty.getFields(types);

                            const Field = @TypeOf(@as(Types.TypeInfo, undefined).data.@"@union".fields).elem;

                            const field_mem = tmp.arena.alloc(Field, fields.len);

                            for (fields, 0..) |f, i| {
                                field_mem[i] = .{ .name = .alloc(self, f.name), .ty = f.ty };
                            }

                            break :b .{ .kind = .@"@union", .data = .{ .@"@union" = .{
                                .fields = .alloc(self, field_mem),
                            } } };
                        },
                        .FnPtr => |fnptr_ty| b: {
                            const sig: *tys.FnPtr = types.store.get(fnptr_ty);

                            break :b .{ .kind = .fnptr, .data = .{ .fnptr = .{
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

                            break :b .{ .kind = .tuple, .data = .{ .tuple = .alloc(self, @ptrCast(fields)) } };
                        },
                        .Template => |template_ty| b: {
                            const template: *tys.Template = types.store.get(template_ty);
                            break :b .{ .kind = .template, .data = .{ .template = .{ .is_inline = template.is_inline } } };
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

                    @as(*align(1) Types.TypeInfo, @ptrCast(vm_ctx.memory[@intCast(ret_addr)..].ptr)).* = tp;
                },
            }
        },
        else => unreachable,
    };

    @memcpy(return_loc, self.gen.out.code.items[@intCast(stack_end - return_loc.len)..@intCast(stack_end)]);
    self.vm.regs.set(.stack_addr, stack_end);
}

pub fn jitFunc(self: *Comptime, fnc: utils.EntId(tys.Func)) !void {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const gen = Codegen.init(tmp.arena, self.getTypes(), .@"comptime", .ableos);
    defer gen.deinit();

    self.getTypes().queue(gen.target, .init(.{ .Func = fnc }));
    try compileDependencies(
        gen,
        self.getTypes().func_work_list.get(gen.target).items.len - 1,
        self.getTypes().ct.gen.out.relocs.items.len,
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
    const new_syms_pop_until = self.getTypes().ct.gen.out.relocs.items.len;

    var ret: Codegen.Value = undefined;
    {
        var scratch = tmp.arena.checkpoint();
        defer scratch.deinit();
        defer gen.bl.func.reset();

        const token = gen.beginBuilder(tmp.arena, .never, &.{.{ .Reg = .i64 }}, &.{}, .{});
        gen.ast = ast;
        gen.parent_scope = scope;
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

        if (types.retainGlobals(.@"comptime", &self.gen)) return error.Never;

        if (ret.id == .Pointer and gen.abiCata(ret.ty) == .ByValue and
            ret.id.Pointer.kind == .GlobalAddr)
        {
            types.func_work_list.getPtr(.@"comptime").items.len = pop_until;
            const cnst = self.gen.out.readFromSym(
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
            gen.errored = self.getTypes().retainGlobals(.@"comptime", &self.gen) or
                gen.errored;

            const reg_alloc_results = optimizeComptime(.debug, HbvmGen, &self.gen, @ptrCast(&gen.bl.func));

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
                },
            );
        }
    }

    if (gen.errored) {
        return error.Never;
    }

    if (!only_inference) {
        compileDependencies(gen, pop_until, new_syms_pop_until) catch return error.Never;
    } else {
        types.func_work_list.getPtr(.@"comptime").items.len = pop_until;
    }

    return .{ .{ .func = id }, ret.ty };
}

pub fn compileDependencies(self: *Codegen, pop_until: usize, new_syms_pop_until: usize) !void {
    while (self.types.nextTask(self.target, pop_until, null)) |func| {
        defer self.bl.func.reset();

        try self.build(func);

        self.errored = self.types.retainGlobals(self.target, &self.types.ct.gen) or
            self.errored;

        const reg_alloc_results = optimizeComptime(.debug, HbvmGen, &self.types.ct.gen, @ptrCast(&self.bl.func));

        var emit_func_met = self.types.metrics.begin(.jit_emit_func);
        self.types.ct.gen.emitFunc(
            @ptrCast(&self.bl.func),
            .{
                .id = @intFromEnum(func),
                .linkage = .local,
                .is_inline = false,
                .optimizations = .{ .allocs = reg_alloc_results },
                .builtins = .{},
            },
        );
        emit_func_met.end();
    }

    root.hbvm.object.jitLink(self.types.ct.gen.out, new_syms_pop_until);
}

pub fn evalTy(self: *Comptime, name: []const u8, scope: Codegen.Scope, ty_expr: Ast.Id) !Types.Id {
    const types = self.getTypes();
    const res, _ = try self.jitExpr(name, scope, .{ .ty = .type }, ty_expr);
    const file = scope.file(types);

    switch (res) {
        .func => |id| {
            var data: [8]u8 = undefined;
            try self.runVm(scope.file(types), types.getFile(file).posOf(ty_expr).index, @intFromEnum(id), &data);
            return Types.Id.fromRaw(@bitCast(data[0..4].*), types) orelse {
                types.report(scope.file(types), ty_expr, "resulting type has a corrupted value", .{});
                return error.Never;
            };
        },
        .constant => |vl| {
            return Types.Id.fromRaw(@truncate(@as(u64, @bitCast(vl))), types) orelse {
                types.report(scope.file(types), ty_expr, "resulting type has a corrupted value", .{});
                return error.Never;
            };
        },
    }
}

pub fn evalIntConst(self: *Comptime, scope: Codegen.Scope, int_conts: Ast.Id) !i64 {
    const res, _ = try self.jitExpr("", scope, .{ .ty = .uint }, int_conts);
    const types = self.getTypes();
    const file = scope.file(types);
    switch (res) {
        .func => |id| {
            var data: [8]u8 = undefined;
            try self.runVm(file, types.posOf(file, int_conts).index, @intFromEnum(id), &data);
            return @bitCast(data);
        },
        .constant => |c| return c,
    }
}

pub fn evalGlobal(self: *Comptime, name: []const u8, global: utils.EntId(tys.Global), ty: ?Types.Id, value: Ast.Id) error{Never}!void {
    const types = self.getTypes();
    const glbal = types.store.get(global);
    const file = glbal.key.loc.file;

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

    const res, const fty = try self.jitExpr(name, .{ .Perm = self.getTypes().store.get(global).key.loc.scope }, .{ .ty = ty }, value);
    const data = types.pool.arena.allocator().alloc(u8, @intCast(fty.size(types))) catch unreachable;
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
        inline for (.{ .Func, .Template }) |tag| {
            if (typ.data() == tag) {
                const item = types.store.get(@field(typ.data(), @tagName(tag)));
                if (std.mem.eql(u8, name, item.key.name(types))) item.is_inline = glbal.readonly;
            }
        }
    }
}
