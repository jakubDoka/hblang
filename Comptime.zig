const std = @import("std");
const Codegen = @import("Codegen.zig");
const Types = @import("Types.zig");
const Ast = @import("Ast.zig");
const Vm = @import("Vm.zig");

pub fn evalGlobal(self: *Types, global: *Types.Global, ty: ?Types.Id, value: Ast.Id) void {
    var gen = Codegen.init(self.arena.child_allocator, self, .@"comptime");
    defer gen.deinit();

    var fdata = Types.Func{
        .id = self.next_func,
        .key = global.key,
        .name = "!",
        .args = &.{},
        .ret = .never,
    };

    self.next_func += 1;

    const token, const params, _ = gen.beginBuilder(&fdata, 1, 0);

    params[0] = .int;
    const ptr = gen.bl.addParam(0);

    var ret = gen.emit(.{ .scope = global.key.scope, .ty = ty, .loc = ptr }, value);
    gen.emitGenericStore(ptr, &ret);

    gen.bl.end(token);

    gen.types.comptime_code.emitFunc(
        @ptrCast(&gen.bl.func),
        .{ .id = fdata.id, .entry = true },
    );

    //gen.bl.func.fmtUnscheduled(std.io.getStdErr().writer().any(), .escape_codes);

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
    const stack_size = 1024 * 10;
    const stack_end = stack_size - gen.types.comptime_code.out.items.len;

    var stack: [stack_size]u8 = undefined;

    @memcpy(stack[stack_end..], gen.types.comptime_code.out.items);

    gen.types.vm.ip = stack_end + gen.types.comptime_code.funcs.items[fdata.id].offset;
    gen.types.vm.fuel = 1024;
    gen.types.vm.regs.set(.arg(0, 0), stack_end - ret.ty.size(&gen));
    gen.types.vm.regs.set(.stack_addr, stack_end - ret.ty.size(&gen));
    var vm_ctx = Vm.SafeContext{
        .writer = if (false) std.io.getStdErr().writer().any() else std.io.null_writer.any(),
        .color_cfg = .escape_codes,
        .memory = &stack,
        .code_start = 0,
        .code_end = 0,
    };
    const res = gen.types.vm.run(&vm_ctx) catch unreachable;
    std.debug.assert(res == .tx);

    const data = gen.types.arena.allocator().alloc(u8, ret.ty.size(&gen)) catch unreachable;
    @memcpy(data, stack[stack_end - ret.ty.size(&gen) .. stack_end]);

    global.data = data;
    global.ty = ret.ty;
}
