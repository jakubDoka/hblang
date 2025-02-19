const std = @import("std");
const Codegen = @import("Codegen.zig");
const Types = @import("Types.zig");
const Ast = @import("parser.zig");
const Vm = @import("Vm.zig");

const fdata = Types.FuncData{
    .name = .init(0),
    .args = &.{},
    .ret = .never,
    .file = @enumFromInt(0),
    .ast = .zeroSized(.Void),
};

pub fn evalGlobal(self: *Codegen, global: Types.Global, ty: ?Types.Id, value: Ast.Id) void {
    var gen = Codegen.init(self.work_list.allocator, self.types, .@"comptime", self.diagnostics);
    defer gen.deinit();

    const token, const params, _ = gen.beginBuilder(self.file, &fdata, 1, 0);

    params[0] = .int;
    const ptr = gen.bl.addParam(0);

    var ret = gen.emit(.{ .ty = ty, .loc = ptr }, value);
    gen.emitGenericStore(ptr, &ret);

    gen.bl.end(token);

    const id = gen.types.funcs.items.len;
    gen.types.comptime_code.emitFunc(
        @ptrCast(&gen.bl.func),
        .{ .id = @intCast(id), .entry = true },
    );

    gen.types.funcs.append(gen.types.arena.child_allocator, .{
        .name = gen.types.get(global).name,
        .args = &.{},
        .ret = ret.ty,
        .file = self.file,
        .ast = gen.types.get(global).ast,
    }) catch unreachable;

    //gen.bl.func.fmtUnscheduled(std.io.getStdErr().writer().any(), .escape_codes);

    gen.bl.func.reset();

    while (gen.nextTask()) |task| switch (task) {
        .Func => |func| {
            defer gen.bl.func.reset();
            gen.build(gen.file, func) catch {
                unreachable;
            };

            gen.types.comptime_code.emitFunc(
                @ptrCast(&gen.bl.func),
                .{ .id = @intFromEnum(func) },
            );
        },
        .Global => |glob| {
            const g = gen.types.get(glob);
            gen.types.comptime_code.emitData(.{
                .name = gen.ast.tokenSrc(g.name.index),
                .id = @intFromEnum(glob),
                .value = .{ .init = g.data },
            });
        },
    };

    _ = gen.types.comptime_code.link(true);
    const stack_size = 1024 * 10;
    const stack_end = stack_size - gen.types.comptime_code.out.items.len;

    var stack: [stack_size]u8 = undefined;

    @memcpy(stack[stack_end..], gen.types.comptime_code.out.items);

    gen.types.vm.ip = stack_end + gen.types.comptime_code.funcs.items[id].offset;
    gen.types.vm.fuel = 1024;
    gen.types.vm.regs.set(.arg(0, 0), stack_end - ret.ty.size());
    gen.types.vm.regs.set(.stack_addr, stack_end - ret.ty.size());
    var vm_ctx = Vm.SafeContext{
        .writer = if (false) std.io.getStdErr().writer().any() else std.io.null_writer.any(),
        .color_cfg = .escape_codes,
        .memory = &stack,
        .code_start = 0,
        .code_end = 0,
    };
    const res = gen.types.vm.run(&vm_ctx) catch unreachable;
    std.debug.assert(res == .tx);

    const data = gen.types.arena.allocator().alloc(u8, ret.ty.size()) catch unreachable;
    @memcpy(data, stack[stack_end - ret.ty.size() .. stack_end]);

    gen.types.get(global).data = data;
    gen.types.get(global).ty = ret.ty;
}
