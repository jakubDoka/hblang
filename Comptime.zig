const std = @import("std");
const Codegen = @import("Codegen.zig");
const Types = @import("Types.zig");
const Ast = @import("Ast.zig");
const Vm = @import("Vm.zig");

pub const eca = @import("HbvmGen.zig").eca;

pub fn runVm(self: *Types, entry_id: u32, return_loc: []u8) void {
    const stack_size = 1024 * 10;
    const stack_end = stack_size - self.comptime_code.out.items.len;

    var stack: [stack_size]u8 = undefined;

    @memcpy(stack[stack_end..], self.comptime_code.out.items);

    self.vm.ip = stack_end + self.comptime_code.funcs.items[entry_id].offset;
    self.vm.fuel = 1024;
    self.vm.regs.set(.arg(0, 0), stack_end - return_loc.len);
    self.vm.regs.set(.stack_addr, stack_end - return_loc.len);
    var vm_ctx = Vm.SafeContext{
        .writer = if (false) std.io.getStdErr().writer().any() else std.io.null_writer.any(),
        .color_cfg = .escape_codes,
        .memory = &stack,
        .code_start = 0,
        .code_end = 0,
    };

    while (true) switch (self.vm.run(&vm_ctx) catch unreachable) {
        .tx => break,
        .eca => switch (self.vm.regs.get(.arg(1, 0))) {
            0 => {
                const scope: Types.Id = @enumFromInt(self.vm.regs.get(.arg(1, 1)));
                const ast = self.getFile(scope.file());
                const struct_ast_id: Ast.Id = @bitCast(@as(u32, @truncate(self.vm.regs.get(.arg(1, 2)))));
                const struct_ast = ast.exprs.getTyped(.Struct, struct_ast_id).?;

                const captures = self.arena.allocator().alloc(Types.Id, struct_ast.captures.len()) catch unreachable;
                for (captures, 3..) |*slot, i| {
                    slot.* = @enumFromInt(self.vm.regs.get(.arg(1, i)));
                }

                const res = self.resolveStruct(scope, scope.file(), "", struct_ast_id, struct_ast.fields, struct_ast.captures, captures);
                self.vm.regs.set(.ret(0), @intFromEnum(res));
            },
            else => unreachable,
        },
        else => unreachable,
    };

    //const data = self.arena.allocator().alloc(u8, return_loc.len) catch unreachable;
    @memcpy(return_loc, stack[stack_end - return_loc.len .. stack_end]);
}

pub fn jitExpr(self: *Types, ctx: Codegen.Ctx, value: Ast.Id) struct { u32, Types.Id } {
    var gen = Codegen.init(self.arena.child_allocator, self, .@"comptime");
    defer gen.deinit();

    const id = self.next_func;
    self.next_func += 1;

    const token, const params, _ = gen.beginBuilder(.never, 1, 0);

    params[0] = .int;
    const ptr = gen.bl.addParam(0);

    var ret = gen.emit(ctx.addLoc(ptr), value);
    gen.emitGenericStore(ptr, &ret);

    gen.bl.end(token);

    gen.types.comptime_code.emitFunc(
        @ptrCast(&gen.bl.func),
        .{ .id = id, .entry = true },
    );

    gen.bl.func.reset();

    while (gen.nextTask()) |task| switch (task) {
        .Func => |func| {
            defer gen.bl.func.reset();
            gen.build(func) catch {
                unreachable;
            };

            gen.types.comptime_code.emitFunc(
                @ptrCast(&gen.bl.func),
                .{ .id = func.id },
            );
        },
        .Global => |glob| {
            gen.types.comptime_code.emitData(.{
                .name = glob.name,
                .id = glob.id,
                .value = .{ .init = glob.data },
            });
        },
    };

    _ = gen.types.comptime_code.link(true);

    return .{ id, ret.ty };
}

pub fn evalTy(self: *Types, ctx: Codegen.Ctx, ty_expr: Ast.Id) Types.Id {
    const id, _ = jitExpr(self, ctx.addTy(.type), ty_expr);
    var data: [8]u8 = undefined;
    runVm(self, id, &data);
    return @enumFromInt(@as(u64, @bitCast(data)));
}

pub fn evalGlobal(self: *Types, global: *Types.Global, ty: ?Types.Id, value: Ast.Id) void {
    const id, const fty = jitExpr(self, .{ .scope = global.key.scope, .ty = ty }, value);
    const data = self.arena.allocator().alloc(u8, fty.size(self)) catch unreachable;
    runVm(self, id, data);
    global.data = data;
    global.ty = fty;
}
