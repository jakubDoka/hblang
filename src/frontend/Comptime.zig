const std = @import("std");

const root = @import("hb");
const isa = root.hbvm.isa;
const Types = root.frontend.Types;
const Builder = root.backend.Builder;
const Node = Builder.BuildNode;
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
pub const eca = HbvmGen.eca;

vm: Vm = .{},
gen: HbvmGen,
in_progress: std.ArrayListUnmanaged(Loc) = .{},

pub const opts = root.backend.Machine.OptOptions{
    .do_dead_code_elimination = true,
    .do_inlining = false,
    .do_generic_peeps = true,
    .do_machine_peeps = true,
    .mem2reg = true,
    .do_gcm = true,
    .do_uninit_analisys = true,
};

pub const stack_size = 1024 * 100;

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
};

pub fn init(gpa: *utils.Pool) Comptime {
    var self = Comptime{ .gen = .{ .gpa = gpa } };
    self.gen.out.code.resize(gpa.allocator(), stack_size) catch unreachable;
    self.gen.out.code.items[self.gen.out.code.items.len - 1] = @intFromEnum(isa.Op.tx);
    self.gen.out.code.items[self.gen.out.code.items.len - 2] = @intFromEnum(isa.Op.eca);
    self.vm.regs.set(.stack_addr, stack_size - 2);
    return self;
}

inline fn getTypes(self: *Comptime) *Types {
    return @fieldParentPtr("ct", self);
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
    Unsupported: *Node,
};

pub fn partialEval(self: *Comptime, file: Types.File, scope: Types.Id, pos: u32, bl: *Builder, expr: *Node, ty: Types.Id) PartialEvalResult {
    const abi: Types.Abi = .ableos;
    const types = self.getTypes();

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    // TODO: maybe use the vm stack instead
    var work_list = std.ArrayListUnmanaged(*Node).initBuffer(tmp.arena.alloc(*Node, 1024));

    work_list.appendAssumeCapacity(expr);

    while (true) {
        const curr: *Node = work_list.pop().?;
        if (curr.id == std.math.maxInt(u16)) continue;
        const res = switch (curr.kind) {
            .Local => {
                {
                    const global = curr.inputs()[1].?.extra(.LocalAlloc).meta;

                    if (global != std.math.maxInt(u32)) {
                        if (work_list.items.len == 0) {
                            return .{ .Arbitrary = @enumFromInt(global) };
                        }
                    }
                }

                work_list.appendAssumeCapacity(curr);

                const global = types.addUniqueGlobal(scope);
                types.store.get(global).data = types.pool.arena.alloc(
                    u8,
                    @intCast(curr.inputs()[1].?.extra(.LocalAlloc).size),
                );
                types.store.get(global).ty = ty;
                curr.inputs()[1].?.extra(.LocalAlloc).meta = @intFromEnum(global);

                var tmpa = tmp.arena.checkpoint();
                defer tmpa.deinit();

                var iter = std.mem.reverseIterator(curr.outputs());
                while (iter.next()) |o| {
                    const use: *Node = o.get();
                    if (use.knownMemOp()) |op| {
                        if (op[0].isStore()) {
                            work_list.appendAssumeCapacity(op[0]);
                            continue;
                        }
                    }
                    return .{ .Unsupported = curr };
                }

                continue;
            },
            .Store => {
                const base, const offset = curr.base().knownOffset();
                if (base.kind != .Local) {
                    return .{ .Unsupported = curr };
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
                    data[@intCast(offset)..][0..@intCast(curr.data_type.size())],
                    @as([*]const u8, @ptrCast(&value))[0..@intCast(curr.data_type.size())],
                );

                bl.func.subsume(curr.mem(), curr);

                continue;
            },
            .GlobalAddr => {
                const global = curr.extra(.GlobalAddr).id;
                const below = work_list.getLastOrNull() orelse {
                    return .{ .Arbitrary = @enumFromInt(global) };
                };
                const gid: utils.EntId(tys.Global) = @enumFromInt(global);
                if (types.store.get(gid).completion.get(.@"comptime") != .compiled) {
                    types.queue(.@"comptime", .init(.{ .Global = gid }));
                    if (types.retainGlobals(.@"comptime", &self.gen, null)) {
                        return .{ .Unsupported = curr };
                    }
                }

                const addr = self.gen.out.syms.items[@intFromEnum(self.gen.out.globals.items[global])].offset;
                bl.func.setInputNoIntern(below, 3, bl.addIntImm(curr.sloc, .i64, addr));
                continue;
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
                    return .{ .Unsupported = curr };
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

                if (call.extra(.Call).signature.returns().?.len != 1) {
                    types.report(file, pos, "the function returns something we cant handle", .{});
                    return .{ .Unsupported = curr };
                }

                var ret_ty: graph.DataType = .i64;
                if (call.extra(.Call).id != eca) {
                    const func_id: utils.EntId(tys.Func) = @enumFromInt(call.extra(.Call).id);
                    const func = types.store.get(func_id);

                    if (func.recursion_lock) {
                        types.report(func.key.loc.file, func.key.loc.ast, "the functions types most likely depend on it being evaluated", .{});
                        return .{ .Unsupported = curr };
                    }

                    ret_ty = abi.categorize(func.ret, types).ByValue;
                    if (func.completion.get(.@"comptime") == .queued) {
                        self.jitFunc(func_id) catch return .{ .Unsupported = curr };
                    }
                    if (types.store.get(func_id).errored) return .{ .Unsupported = curr };
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
                    return .{ .Unsupported = curr };
                };

                const ret = types.ct.vm.regs.get(.ret(0));
                const ret_vl = bl.addIntImm(.none, ret_ty, @bitCast(ret));
                for (tmp.arena.dupe(Node.Out, curr.outputs())) |n| {
                    const o = n.get();
                    if (o.kind == .Ret) {
                        bl.func.subsume(ret_vl, o);
                    }
                    if (o.kind == .Mem) {
                        bl.func.subsume(call.inputs()[1].?, o);
                    }
                }
                bl.func.subsume(call.inputs()[0].?, curr);
                work_list.appendAssumeCapacity(ret_vl);
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
                        glob.data[@intCast(offset)..][0..@intCast(curr.data_type.size())],
                    );

                    break :b bl.addIntImm(.none, curr.data_type, @bitCast(mem));
                }

                if (curr.base().kind == .BinOp and curr.base().inputs()[2].?.kind != .CInt) {
                    work_list.appendAssumeCapacity(curr);
                    work_list.appendAssumeCapacity(curr.base().inputs()[2].?);
                    continue;
                }

                if (curr.base().kind == .BinOp and
                    curr.base().extra(.BinOp).op.neutralElememnt() ==
                        curr.base().inputs()[2].?.extra(.CInt).value)
                {
                    bl.func.subsume(curr.base().inputs()[1].?, curr.base());
                }

                var cursor = curr.mem();
                const bs = work_list.items.len;
                while (true) {
                    const is_spilt = work_list.items.len != bs;
                    if (is_spilt) {
                        var data_dep_cont: usize = 0;
                        if (for (cursor.outputs()) |o| {
                            if (o.get().isLoad()) continue;
                            if (o.get().schedule == 0) continue;
                            data_dep_cont += 1;
                        } else data_dep_cont > 1) {
                            cursor.schedule = 0;
                            cursor = work_list.pop().?;
                        }
                    }

                    if (cursor.isStore()) {
                        if (cursor.base() != curr.base()) {
                            cursor = cursor.mem();
                        } else if (!is_spilt) {
                            break :b cursor.value().?;
                        } else {
                            return .{ .DependsOnRuntimeControlFlow = curr };
                        }
                    } else if (cursor.kind == .Mem) {
                        if (cursor.inputs()[0].?.kind == .Start) {
                            return .{ .Unsupported = cursor };
                        }
                        cursor = cursor.inputs()[0].?.inputs()[0].?.inputs()[1].?;
                    } else if (cursor.kind == .Phi) {
                        if (cursor.cfg0().base.kind == .Loop) {
                            cursor = cursor.inputs()[1].?;
                            continue;
                        }

                        // NOTE: there are two main events occuring, etiher we
                        // encounter a phi, in which case we both branches or,
                        // we encounter a store that has two dependants, in
                        // wich case we swap with the top of the stack and
                        // traverse that instesd until we arrive to the same
                        // joining point that has a dependence on the top of
                        // the stack
                        //
                        work_list.appendAssumeCapacity(cursor.inputs()[1].?);
                        cursor = cursor.inputs()[2].?;
                    } else {
                        return .{ .Unsupported = cursor };
                    }
                }
            },
            else => return .{ .Unsupported = curr },
        };

        bl.func.subsume(res, curr);
        work_list.appendAssumeCapacity(res);
    }
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
    if (return_loc.len != 0) self.vm.regs.set(.arg(0), stack_end - return_loc.len);
    self.vm.regs.set(.stack_addr, stack_end - return_loc.len);

    var vm_ctx = Vm.SafeContext{
        .writer = if (false) types.diagnostics else std.io.null_writer.any(),
        .color_cfg = .escape_codes,
        .memory = self.gen.out.code.items,
        .code_start = 0,
        .code_end = 0,
    };

    while (true) switch (self.vm.run(&vm_ctx) catch |err| {
        types.report(file, pos, "comptime execution failed: {}", .{@errorName(err)});
        return error.Never;
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

            switch (@as(InteruptCode, @enumFromInt(self.vm.regs.get(.arg(0))))) {
                .Struct, .Union, .Enum => |t| {
                    const scope: Types.Id = @enumFromInt(self.ecaArg(1));
                    const ast = types.getFile(scope.file(types).?);
                    const struct_ast_id = self.ecaArgAst(2);
                    const struct_ast = ast.exprs.get(struct_ast_id).Type;

                    const captures = types.pool.arena.alloc(Types.Scope.Capture, struct_ast.captures.len());

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
                    const slice = types.makeSlice(@intCast(len), ty);
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
    return self.jitExprLow(name, scope, ctx, false, value) catch {
        if (scope == .Tmp) scope.Tmp.errored = true;
        return error.Never;
    };
}

pub fn inferType(self: *Comptime, name: []const u8, scope: Codegen.Scope, ctx: Codegen.Ctx, value: Ast.Id) !Types.Id {
    return (self.jitExprLow(name, scope, ctx, true, value) catch {
        if (scope == .Tmp) scope.Tmp.errored = true;
        return error.Never;
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
) !struct { JitResult, Types.Id } {
    const types = self.getTypes();
    const id = types.store.add(types.pool.allocator(), @as(tys.Func, undefined));

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
        gen.ast = types.getFile(scope.file(types));
        gen.parent_scope = scope;
        gen.name = name;
        gen.struct_ret_ptr = null;

        const ptr = gen.bl.addParam(.none, 0);

        ret = gen.emit(ctx.addLoc(ptr), value) catch |err| switch (err) {
            error.Never => return err,
            error.Unreachable => .{ .ty = .never },
        };
        if (ctx.ty) |ty| {
            try gen.typeCheck(value, &ret, ty);
        }

        if (ret.id == .Value and ret.id.Value.kind == .CInt) {
            types.func_work_list.getPtr(.@"comptime").items.len = pop_until;
            return .{ .{ .constant = ret.id.Value.extra(.CInt).value }, ret.ty };
        }

        gen.emitGenericStore(.none, ptr, &ret);

        gen.bl.end(token);

        if (!only_inference) {
            gen.errored = self.getTypes().retainGlobals(.@"comptime", &self.gen, null) or
                gen.errored;

            self.gen.emitFunc(
                @ptrCast(&gen.bl.func),
                .{
                    .id = @intFromEnum(id),
                    .linkage = .exported,
                    .is_inline = false,
                    .optimizations = opts,
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
    while (self.types.nextTask(self.target, pop_until)) |func| {
        defer self.bl.func.reset();

        try self.build(func);

        self.errored = self.types.retainGlobals(self.target, &self.types.ct.gen, null) or
            self.errored;

        self.types.ct.gen.emitFunc(
            @ptrCast(&self.bl.func),
            .{
                .id = @intFromEnum(func),
                .linkage = .local,
                .is_inline = false,
                .optimizations = opts,
                .builtins = .{},
            },
        );
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

pub fn evalGlobal(self: *Comptime, name: []const u8, global: utils.EntId(tys.Global), ty: ?Types.Id, value: Ast.Id) !void {
    const types = self.getTypes();
    const res, const fty = try self.jitExpr(name, .{ .Perm = self.getTypes().store.get(global).key.loc.scope }, .{ .ty = ty }, value);
    const file = types.store.get(global).key.loc.file;
    const data = types.pool.arena.allocator().alloc(u8, @intCast(fty.size(types))) catch unreachable;
    switch (res) {
        .func => |id| {
            try self.runVm(file, types.posOf(file, value).index, @intFromEnum(id), data);
        },
        .constant => |c| {
            @memcpy(data, @as(*const [@sizeOf(@TypeOf(c))]u8, @ptrCast(&c))[0..data.len]);
        },
    }

    const glbal = types.store.get(global);
    glbal.data = data;
    glbal.ty = fty;
    if (fty == .type) {
        const typ: Types.Id = @enumFromInt(@as(u32, @bitCast(data[0..4].*)));
        inline for (.{ .Func, .Template }) |tag| {
            if (typ.data() == tag) {
                const item = types.store.get(@field(typ.data(), @tagName(tag)));
                if (std.mem.eql(u8, name, item.key.name)) item.is_inline = glbal.readonly;
            }
        }
    }
}
