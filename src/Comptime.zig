vm: Vm = .{},
comptime_code: HbvmGen,

const std = @import("std");
const isa = @import("isa.zig");
const graph = @import("graph.zig");
const root = @import("utils.zig");
const Codegen = @import("Codegen.zig");
const Types = @import("Types.zig");
const Ast = @import("Ast.zig");
const Vm = @import("Vm.zig");
const HbvmGen = @import("HbvmGen.zig");
const Comptime = @import("Comptime.zig");
const Builder = @import("Builder.zig");
const Node = Builder.BuildNode;

pub const eca = @import("HbvmGen.zig").eca;
pub const stack_size = 1024 * 100;

pub const InteruptCode = enum(u64) {
    Struct,
    Union,
};

pub fn init(gpa: std.mem.Allocator) Comptime {
    var self = Comptime{ .comptime_code = .init(gpa) };
    self.comptime_code.out.resize(stack_size) catch unreachable;
    self.comptime_code.out.items[self.comptime_code.out.items.len - 1] = @intFromEnum(isa.Op.tx);
    self.comptime_code.out.items[self.comptime_code.out.items.len - 2] = @intFromEnum(isa.Op.eca);
    self.vm.regs.set(.stack_addr, stack_size - 2);
    return self;
}

inline fn getTypes(self: *Comptime) *Types {
    return @fieldParentPtr("ct", self);
}

inline fn getGpa(self: *Comptime) std.mem.Allocator {
    return self.comptime_code.out.allocator;
}

pub inline fn ecaArg(self: *Comptime, idx: usize) u64 {
    return self.vm.regs.get(.arg(1, idx));
}

pub fn partialEval(self: *Comptime, bl: *Builder, expr: *Node) u64 {
    const abi: Types.Abi = .ableos;
    const types = self.getTypes();

    var tmp = root.Arena.scrath(null);
    defer tmp.deinit();

    var work_list = std.ArrayListUnmanaged(*Node).initBuffer(tmp.arena.alloc(*Node, 32));

    work_list.appendAssumeCapacity(expr);

    while (true) {
        const curr = work_list.pop().?;
        const res = switch (curr.kind) {
            .CInt => {
                if (work_list.items.len == 0) {
                    return @as(u64, @bitCast(curr.extra(.CInt).*));
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
                    ret_ty = abi.categorize(func.ret, types).ByValue;
                    if (func.completion.get(.@"comptime") == .queued) {
                        self.jitFunc(func);
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
                        types.ct.vm.regs.set(.arg(call.extra(.Call).ret_count, arg_idx), @bitCast(arg.?.extra(.CInt).*));
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
                var cursor = curr.mem();
                while (true) {
                    if (cursor.isStore()) {
                        if (cursor.base() != curr.base()) {
                            cursor = cursor.mem();
                        } else break :b cursor.value();
                    } else if (cursor.kind == .Mem) {
                        if (cursor.inputs()[0].?.kind == .Start) {
                            unreachable;
                        }
                        cursor = cursor.inputs()[0].?.inputs()[0].?.inputs()[1].?;
                    } else std.debug.panic("{}\n", .{cursor});
                }
            },
            else => std.debug.panic("{}", .{curr}),
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
    self.vm.regs.set(.arg(0, 0), stack_end - return_loc.len);
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
                ip: u64,
                fuel: u64,
            };

            begin_interrup: {
                const stack_ptr = self.vm.regs.get(.stack_addr) - @sizeOf(InterruptFrame);
                vm_ctx.memory[stack_ptr..][0..@sizeOf(InterruptFrame)].* =
                    @bitCast(InterruptFrame{ .ip = self.vm.ip, .fuel = self.vm.fuel });
                self.vm.regs.set(.stack_addr, stack_ptr);
                break :begin_interrup;
            }

            defer end_interrupt: {
                const stack_ptr = self.vm.regs.get(.stack_addr);
                const frame: InterruptFrame = @bitCast(vm_ctx.memory[stack_ptr..][0..@sizeOf(InterruptFrame)].*);
                self.vm.ip = frame.ip;
                self.vm.fuel = frame.fuel;
                self.vm.regs.set(.stack_addr, stack_ptr + @sizeOf(InterruptFrame));
                break :end_interrupt;
            }

            switch (@as(InteruptCode, @enumFromInt(self.vm.regs.get(.arg(1, 0))))) {
                .Struct => {
                    const scope: Types.Id = @enumFromInt(self.ecaArg(1));
                    const ast = types.getFile(scope.file());
                    const struct_ast_id: Ast.Id = @bitCast(@as(u32, @truncate(self.ecaArg(2))));
                    const struct_ast = ast.exprs.getTyped(.Struct, struct_ast_id).?;

                    const captures = types.arena.alloc(Types.Key.Capture, struct_ast.captures.len());

                    for (captures, ast.exprs.view(struct_ast.captures), 0..) |*slot, id, i| {
                        slot.* = .{ .id = id, .ty = @enumFromInt(self.ecaArg(3 + i * 2)), .value = self.ecaArg(3 + i * 2 + 1) };
                    }

                    const res = types.resolveStruct(
                        scope,
                        scope.file(),
                        name,
                        struct_ast_id,
                        struct_ast.fields,
                        captures,
                    );

                    self.vm.regs.set(.ret(0), @intFromEnum(res));
                },
                .Union => {
                    const scope: Types.Id = @enumFromInt(self.ecaArg(1));
                    const ast = types.getFile(scope.file());
                    const union_ast_id: Ast.Id = @bitCast(@as(u32, @truncate(self.ecaArg(2))));
                    const union_ast = ast.exprs.getTyped(.Union, union_ast_id).?;

                    const captures = types.arena.alloc(Types.Key.Capture, union_ast.captures.len());

                    for (captures, ast.exprs.view(union_ast.captures), 0..) |*slot, id, i| {
                        slot.* = .{ .id = id, .ty = @enumFromInt(self.ecaArg(3 + i * 2)), .value = self.ecaArg(3 + i * 2 + 1) };
                    }

                    const res = types.resolveUnion(
                        scope,
                        scope.file(),
                        name,
                        union_ast_id,
                        union_ast.fields,
                        captures,
                    );

                    self.vm.regs.set(.ret(0), @intFromEnum(res));
                },
            }
        },
        else => unreachable,
    };

    @memcpy(return_loc, self.comptime_code.out.items[stack_end - return_loc.len .. stack_end]);
    self.vm.regs.set(.stack_addr, stack_end);
}

pub fn jitFunc(self: *Comptime, fnc: *Types.Func) void {
    var tmp = root.Arena.scrath(null);
    defer tmp.deinit();
    var gen = Codegen.init(self.getGpa(), tmp.arena, self.getTypes(), .@"comptime");
    defer gen.deinit();

    gen.queue(.{ .Func = fnc });
    compileDependencies(&gen, self.comptime_code.global_relocs.items.len);
}

pub fn jitExpr(self: *Comptime, name: []const u8, scope: Codegen.Scope, ctx: Codegen.Ctx, value: Ast.Id) ?struct { u32, Types.Id } {
    const types = self.getTypes();
    const id: u32 = @intCast(types.funcs.items.len);
    types.funcs.append(types.arena.allocator(), undefined) catch unreachable;

    var tmp = root.Arena.scrath(null);
    defer tmp.deinit();

    var gen = Codegen.init(self.getGpa(), tmp.arena, types, .@"comptime");
    defer gen.deinit();

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

        ret = gen.emit(ctx.addLoc(ptr), value);
        if (ctx.ty) |ty| {
            if (gen.typeCheck(value, &ret, ty)) return null;
        }
        gen.emitGenericStore(ptr, &ret);

        gen.bl.end(token);

        self.comptime_code.emitFunc(
            @ptrCast(&gen.bl.func),
            .{ .id = id, .entry = true },
        );
    }

    compileDependencies(&gen, reloc_frame);

    return .{ id, ret.ty };
}

pub fn compileDependencies(self: *Codegen, reloc_util: usize) void {
    while (self.nextTask()) |task| switch (task) {
        .Func => |func| {
            defer {
                self.bl.func.reset();
            }

            self.build(func) catch {
                unreachable;
            };

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

pub fn evalTy(self: *Comptime, name: []const u8, scope: Codegen.Scope, ty_expr: Ast.Id) Types.Id {
    const id, _ = self.jitExpr(name, scope, .{ .ty = .type }, ty_expr) orelse return .never;

    var data: [8]u8 = undefined;
    self.runVm(name, id, &data);
    return @enumFromInt(@as(u64, @bitCast(data)));
}

pub fn evalIntConst(self: *Comptime, scope: Codegen.Scope, int_conts: Ast.Id) i64 {
    const id, _ = self.jitExpr("", scope, .{ .ty = .uint }, int_conts) orelse return 0;
    var data: [8]u8 = undefined;
    self.runVm("", id, &data);
    return @bitCast(data);
}

pub fn evalGlobal(self: *Comptime, name: []const u8, global: *Types.Global, ty: ?Types.Id, value: Ast.Id) void {
    const id, const fty = self.jitExpr(name, .{ .Perm = global.key.scope }, .{ .ty = ty }, value) orelse {
        global.ty = .never;
        return;
    };
    const data = self.getTypes().arena.allocator().alloc(u8, fty.size(self.getTypes())) catch unreachable;
    self.runVm(name, id, data);
    global.data = data;
    global.ty = fty;
}
