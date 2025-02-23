vm: Vm = .{},
comptime_code: HbvmGen,

const std = @import("std");
const isa = @import("isa.zig");
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
};

pub fn init(gpa: std.mem.Allocator) Comptime {
    var self = Comptime{ .comptime_code = .init(gpa) };
    self.comptime_code.out.resize(stack_size) catch unreachable;
    self.comptime_code.out.items[self.comptime_code.out.items.len - 1] = @intFromEnum(isa.Op.tx);
    self.vm.regs.set(.stack_addr, stack_size - 1);
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

    var eval_stack = std.ArrayListUnmanaged(*Node).initBuffer(tmp.arena.alloc(*Node, 32));

    eval_stack.appendAssumeCapacity(expr);

    while (true) {
        const curr = eval_stack.pop().?;
        switch (curr.kind) {
            .CInt => {
                if (eval_stack.items.len == 0) {
                    return @as(u64, @bitCast(curr.extra(.CInt).*));
                }
            },
            .Ret => {
                eval_stack.appendAssumeCapacity(curr.inputs()[0].?);
            },
            .CallEnd => {
                const call: *Node = curr.inputs()[0].?;
                std.debug.assert(call.kind == .Call);
                std.debug.assert(call.extra(.Call).ret_count == 1);

                const func = types.funcs.items[call.extra(.Call).id];
                if (func.completion.get(.@"comptime") == .queued) {
                    self.jitFunc(func);
                    std.debug.assert(func.completion.get(.@"comptime") == .compiled);
                }

                var requeued = false;
                for (call.inputs()[2..], 0..) |arg, arg_idx| {
                    if (arg.?.kind != .CInt) {
                        if (!requeued) eval_stack.appendAssumeCapacity(curr);
                        eval_stack.appendAssumeCapacity(arg.?);
                        requeued = true;
                    } else {
                        types.ct.vm.regs.set(.arg(call.extra(.Call).ret_count, arg_idx), @bitCast(arg.?.extra(.CInt).*));
                    }
                }

                if (requeued) continue;

                types.ct.runVm(func.id, &.{});

                const ret = types.ct.vm.regs.get(.ret(0));
                const ret_ty = abi.categorize(func.ret, types).ByValue;
                eval_stack.appendAssumeCapacity(bl.addIntImm(ret_ty, @bitCast(ret)));
            },
            .Load => {
                var cursor = curr.mem();
                while (true) {
                    if (cursor.isStore()) {
                        if (cursor.base() != curr.base()) {
                            cursor = cursor.mem();
                        } else break;
                    } else if (cursor.kind == .Mem) {
                        cursor = cursor.inputs()[0].?.inputs()[0].?.inputs()[1].?;
                    } else std.debug.panic("{}\n", .{cursor});
                }
                eval_stack.appendAssumeCapacity(cursor.value());
            },
            else => std.debug.panic("{}", .{curr}),
        }
    }
}

pub fn runVm(self: *Comptime, entry_id: u32, return_loc: []u8) void {
    const types = self.getTypes();

    const stack_end = self.vm.regs.get(.stack_addr);

    self.vm.ip = self.comptime_code.funcs.items[entry_id].offset;
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

    while (true) switch (self.vm.run(&vm_ctx) catch unreachable) {
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

                    const captures = types.arena.alloc(Types.Id, struct_ast.captures.len());
                    for (captures, 3..) |*slot, i| {
                        slot.* = @enumFromInt(self.ecaArg(i));
                    }

                    const res = types.resolveStruct(
                        scope,
                        scope.file(),
                        "",
                        struct_ast_id,
                        struct_ast.fields,
                        struct_ast.captures,
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
    compileDependencies(&gen);
}

pub fn jitExpr(self: *Comptime, name: []const u8, scope: Codegen.Scope, ctx: Codegen.Ctx, value: Ast.Id) struct { u32, Types.Id } {
    const types = self.getTypes();
    const id: u32 = @intCast(types.funcs.items.len);
    types.funcs.append(types.arena.allocator(), undefined) catch unreachable;

    var tmp = root.Arena.scrath(null);
    defer tmp.deinit();

    var gen = Codegen.init(self.getGpa(), tmp.arena, types, .@"comptime");
    defer gen.deinit();

    var ret: Codegen.Value = undefined;
    {
        var scratch = tmp.arena.checkpoint();
        defer {
            scratch.deinit();
            gen.bl.func.reset();
        }

        const token, const params, _ = gen.beginBuilder(tmp.arena, .never, 1, 0);
        gen.parent_scope = scope;
        gen.name = name;
        gen.struct_ret_ptr = null;

        params[0] = .int;
        const ptr = gen.bl.addParam(0);

        ret = gen.emit(ctx.addLoc(ptr), value);
        gen.emitGenericStore(ptr, &ret);

        gen.bl.end(token);

        self.comptime_code.emitFunc(
            @ptrCast(&gen.bl.func),
            .{ .id = id, .entry = true },
        );
    }

    compileDependencies(&gen);

    return .{ id, ret.ty };
}

pub fn compileDependencies(self: *Codegen) void {
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
                .name = glob.name,
                .id = glob.id,
                .value = .{ .init = glob.data },
            });
        },
    };

    _ = self.types.ct.comptime_code.link(true);
}

pub fn evalTy(self: *Comptime, name: []const u8, scope: Codegen.Scope, ty_expr: Ast.Id) Types.Id {
    const id, _ = self.jitExpr(name, scope, .{ .ty = .type }, ty_expr);
    var data: [8]u8 = undefined;
    self.runVm(id, &data);
    return @enumFromInt(@as(u64, @bitCast(data)));
}

pub fn evalGlobal(self: *Comptime, name: []const u8, global: *Types.Global, ty: ?Types.Id, value: Ast.Id) void {
    const id, const fty = self.jitExpr(name, .{ .Perm = global.key.scope }, .{ .ty = ty }, value);
    const data = self.getTypes().arena.allocator().alloc(u8, fty.size(self.getTypes())) catch unreachable;
    self.runVm(id, data);
    global.data = data;
    global.ty = fty;
}
