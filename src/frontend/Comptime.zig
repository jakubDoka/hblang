const std = @import("std");

const root = @import("../root.zig");
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
const HbvmGen = root.hbvm.HbvmGen;
const Vm = root.hbvm.Vm;
pub const eca = HbvmGen.eca;

vm: Vm = .{},
comptime_code: HbvmGen,
in_progress: std.ArrayListUnmanaged(Loc) = .{},

pub const stack_size = 1024 * 100;

pub const Loc = struct {
    ast: Ast.Id,
    file: Types.File,
};

pub const InteruptCode = enum(u64) {
    Struct,
    Union,
    Enum,
};

pub fn init(gpa: std.mem.Allocator) Comptime {
    var self = Comptime{ .comptime_code = .{ .gpa = gpa } };
    self.comptime_code.out.resize(gpa, stack_size) catch unreachable;
    self.comptime_code.out.items[self.comptime_code.out.items.len - 1] = @intFromEnum(isa.Op.tx);
    self.comptime_code.out.items[self.comptime_code.out.items.len - 2] = @intFromEnum(isa.Op.eca);
    self.vm.regs.set(.stack_addr, stack_size - 2);
    return self;
}

inline fn getTypes(self: *Comptime) *Types {
    return @fieldParentPtr("ct", self);
}

inline fn getGpa(self: *Comptime) std.mem.Allocator {
    return self.comptime_code.gpa;
}

pub inline fn ecaArg(self: *Comptime, idx: usize) u64 {
    return self.vm.regs.get(.arg(idx));
}

pub const PartialEvalResult = union(enum) {
    Resolved: u64,
    Unsupported: *Node,
};

pub fn partialEval(self: *Comptime, bl: *Builder, expr: *Node) PartialEvalResult {
    const abi: Types.Abi = .ableos;
    const types = self.getTypes();

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var work_list = std.ArrayListUnmanaged(*Node).initBuffer(tmp.arena.alloc(*Node, 32));

    work_list.appendAssumeCapacity(expr);

    while (true) {
        const curr = work_list.pop().?;
        const res = switch (curr.kind) {
            .CInt => {
                if (work_list.items.len == 0) {
                    return .{ .Resolved = @as(u64, @bitCast(curr.extra(.CInt).*)) };
                }

                continue;
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
                        const lhs, const rhs = .{ curr.inputs()[1].?.extra(.CInt).*, curr.inputs()[2].?.extra(.CInt).* };
                        break :b bl.addIntImm(curr.data_type, curr.extra(.BinOp).eval(lhs, rhs));
                    },
                    .UnOp => {
                        const oper = curr.inputs()[1].?.extra(.CInt).*;
                        break :b bl.addIntImm(curr.data_type, curr.extra(.UnOp).eval(curr.data_type, oper));
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
                std.debug.assert(call.extra(.Call).ret_count == 1);

                var ret_ty: graph.DataType = .int;
                if (call.extra(.Call).id != eca) {
                    const func = types.funcs.items[call.extra(.Call).id];
                    ret_ty = (abi.categorize(func.ret, types) orelse return .{ .Unsupported = curr }).ByValue;
                    if (func.completion.get(.@"comptime") == .queued) {
                        self.jitFunc(func) catch return .{ .Unsupported = curr };
                        std.debug.assert(func.completion.get(.@"comptime") == .compiled);
                    }
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

                types.ct.runVm("", call.extra(.Call).id, &.{});

                const ret = types.ct.vm.regs.get(.ret(0));
                const ret_vl = bl.addIntImm(ret_ty, @bitCast(ret));
                for (tmp.arena.dupe(*Node, curr.outputs())) |o| {
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
                if (curr.base().kind == .GlobalAddr) {
                    const glob = types.globals.items[curr.base().extra(.GlobalAddr).id];

                    std.debug.assert(curr.data_type.isInt());

                    var mem: u64 = 0;
                    @memcpy(@as([*]u8, @ptrCast(&mem))[0..curr.data_type.size()], glob.data[0..curr.data_type.size()]);

                    break :b bl.addIntImm(curr.data_type, @bitCast(mem));
                }

                var cursor = curr.mem();
                while (true) {
                    if (cursor.isStore()) {
                        if (cursor.base() != curr.base()) {
                            cursor = cursor.mem();
                        } else break :b cursor.value();
                    } else if (cursor.kind == .Mem) {
                        if (cursor.inputs()[0].?.kind == .Start) {
                            return .{ .Unsupported = cursor };
                        }
                        cursor = cursor.inputs()[0].?.inputs()[0].?.inputs()[1].?;
                    } else return .{ .Unsupported = cursor };
                }
            },
            else => return .{ .Unsupported = curr },
        };

        bl.func.subsume(res, curr);
        work_list.appendAssumeCapacity(res);
    }
}

pub fn runVm(self: *Comptime, name: []const u8, entry_id: u32, return_loc: []u8) void {
    const types = self.getTypes();

    const stack_end = self.vm.regs.get(.stack_addr);

    self.vm.ip = if (entry_id == eca) stack_size - 2 else self.comptime_code.funcs.items[entry_id].offset;
    self.vm.fuel = 1024;
    self.vm.regs.set(.ret_addr, stack_size - 1); // return to hardcoded tx
    if (return_loc.len != 0) self.vm.regs.set(.arg(0), stack_end - return_loc.len);
    self.vm.regs.set(.stack_addr, stack_end - return_loc.len);

    var vm_ctx = Vm.SafeContext{
        .writer = if (false) std.io.getStdErr().writer().any() else std.io.null_writer.any(),
        .color_cfg = .escape_codes,
        .memory = self.comptime_code.out.items,
        .code_start = 0,
        .code_end = 0,
    };

    while (true) switch (self.vm.run(&vm_ctx) catch @panic("no")) {
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
                inline .Struct, .Union, .Enum => |t| {
                    const scope: Types.Id = @enumFromInt(self.ecaArg(1));
                    const ast = types.getFile(scope.file().?);
                    const struct_ast_id: Ast.Id = @enumFromInt(@as(u32, @truncate(self.ecaArg(2))));
                    const struct_ast = ast.exprs.getTyped(@field(std.meta.Tag(Ast.Expr), @tagName(t)), struct_ast_id).?;

                    const captures = types.arena.alloc(Types.Key.Capture, struct_ast.captures.len());

                    for (captures, ast.exprs.view(struct_ast.captures), 0..) |*slot, id, i| {
                        slot.* = .{ .id = id, .ty = @enumFromInt(self.ecaArg(3 + i * 2)), .value = self.ecaArg(3 + i * 2 + 1) };
                    }

                    const res = types.resolveFielded(
                        @field(std.meta.Tag(Types.Data), @tagName(t)),
                        scope,
                        scope.file().?,
                        name,
                        struct_ast_id,
                        captures,
                    );

                    self.vm.regs.set(.ret(0), @intFromEnum(res));
                },
            }
        },
        else => unreachable,
    };

    @memcpy(return_loc, self.comptime_code.out.items[@intCast(stack_end - return_loc.len)..@intCast(stack_end)]);
    self.vm.regs.set(.stack_addr, stack_end);
}

pub fn jitFunc(self: *Comptime, fnc: *Types.Func) !void {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();
    var gen = Codegen.init(self.getGpa(), tmp.arena, self.getTypes(), .@"comptime");
    defer gen.deinit();

    gen.queue(.{ .Func = fnc });
    try compileDependencies(&gen, self.comptime_code.global_relocs.items.len);
}

pub fn jitExpr(self: *Comptime, name: []const u8, scope: Codegen.Scope, ctx: Codegen.Ctx, value: Ast.Id) !struct { u32, Types.Id } {
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

pub fn jitExprLow(
    self: *Comptime,
    name: []const u8,
    scope: Codegen.Scope,
    ctx: Codegen.Ctx,
    only_inference: bool,
    value: Ast.Id,
) !struct { u32, Types.Id } {
    const types = self.getTypes();
    const id: u32 = @intCast(types.funcs.items.len);
    types.funcs.append(types.arena.allocator(), undefined) catch unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var gen = Codegen.init(self.getGpa(), tmp.arena, types, .@"comptime");
    defer gen.deinit();

    for (self.in_progress.items, 0..) |p, i| {
        if (std.meta.eql(p, .{ .ast = value, .file = scope.file() })) {
            for (self.in_progress.items[i..]) |lc| {
                types.report(lc.file, lc.ast, "cycle goes trough here", .{});
            }
            return error.Never;
        }
    }
    self.in_progress.append(self.comptime_code.gpa, .{ .ast = value, .file = scope.file() }) catch unreachable;
    defer _ = self.in_progress.pop().?;

    gen.only_inference = only_inference;

    const reloc_frame = self.comptime_code.global_relocs.items.len;

    var ret: Codegen.Value = undefined;
    {
        var scratch = tmp.arena.checkpoint();
        defer {
            scratch.deinit();
            gen.bl.func.reset();
        }

        const token, const params, _ = gen.beginBuilder(tmp.arena, .never, 1, 0);
        gen.ast = types.getFile(scope.file());
        gen.parent_scope = scope;
        gen.name = name;
        gen.struct_ret_ptr = null;

        params[0] = .int;
        const ptr = gen.bl.addParam(0);

        ret = try gen.emit(ctx.addLoc(ptr), value);
        if (ctx.ty) |ty| {
            try gen.typeCheck(value, &ret, ty);
        }
        gen.emitGenericStore(ptr, &ret);

        gen.bl.end(token);

        if (!only_inference) {
            self.comptime_code.emitFunc(
                @ptrCast(&gen.bl.func),
                .{ .id = id, .entry = true },
            );
        }
    }

    if (gen.errored) {
        return error.Never;
    }

    if (!only_inference)
        compileDependencies(&gen, reloc_frame) catch return error.Never;

    return .{ id, ret.ty };
}

pub fn compileDependencies(self: *Codegen, reloc_util: usize) !void {
    while (self.nextTask()) |task| switch (task) {
        .Func => |func| {
            defer {
                self.bl.func.reset();
            }

            try self.build(func);

            self.types.ct.comptime_code.emitFunc(
                @ptrCast(&self.bl.func),
                .{ .id = func.id },
            );
        },
        .Global => |glob| {
            self.types.ct.comptime_code.emitData(.{
                .id = glob.id,
                .value = .{ .init = glob.data },
            });
        },
    };

    _ = self.types.ct.comptime_code.link(reloc_util, true);
}

pub fn evalTy(self: *Comptime, name: []const u8, scope: Codegen.Scope, ty_expr: Ast.Id) !Types.Id {
    const id, _ = try self.jitExpr(name, scope, .{ .ty = .type }, ty_expr);

    var data: [8]u8 = undefined;
    self.runVm(name, id, &data);
    return @enumFromInt(@as(u64, @bitCast(data)));
}

pub fn evalIntConst(self: *Comptime, scope: Codegen.Scope, int_conts: Ast.Id) !i64 {
    const id, _ = try self.jitExpr("", scope, .{ .ty = .uint }, int_conts);
    var data: [8]u8 = undefined;
    self.runVm("", id, &data);
    return @bitCast(data);
}

pub fn evalGlobal(self: *Comptime, name: []const u8, global: *Types.Global, ty: ?Types.Id, value: Ast.Id) !void {
    const id, const fty = try self.jitExpr(name, .{ .Perm = global.key.scope }, .{ .ty = ty }, value);
    const data = self.getTypes().arena.allocator().alloc(u8, @intCast(fty.size(self.getTypes()))) catch unreachable;
    self.runVm(name, id, data);
    global.data = data;
    global.ty = fty;
}
