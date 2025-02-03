gpa: std.mem.Allocator,
cg: *Codegen,
out: *std.ArrayList(u8),

ir: Codegen.Ir = undefined,
regs: Regs = undefined,
block_order: std.ArrayListUnmanaged(Codegen.Cfg.Id) = .{},
computed: std.ArrayListUnmanaged(Loc) = .{},
blocks: std.ArrayListUnmanaged(Block) = .{},
block_args: std.ArrayListUnmanaged(Loc) = .{},
goto_relocs: std.ArrayListUnmanaged(GotoReloc) = .{},
if_relocs: std.ArrayListUnmanaged(IfReloc) = .{},
ret_relocs: std.ArrayListUnmanaged(u32) = .{},
args: std.ArrayListUnmanaged(Loc) = .{},
tmp_locs: std.ArrayListUnmanaged(Loc) = .{},
funcs: std.ArrayListUnmanaged(Func) = .{},
relocs: struct {
    funcs: std.ArrayListUnmanaged(FuncReloc) = .{},
} = .{},

const std = @import("std");
const root = @import("../root.zig");
const isa = @import("../isa.zig");
const Codegen = @import("../codegen2.zig");
const codegen = @import("../codegen.zig");
const HbvmCg = @This();

pub const Loc = codegen.Loc;
pub const Regs = codegen.Regs;
pub const Error = error{Goto} || std.mem.Allocator.Error;

const Block = struct {
    offset: u32 = std.math.maxInt(u32),
    args: Codegen.Instr.Slice = .{},
};

const GotoReloc = struct {
    to: Codegen.Cfg.Id,
    offset: u32,
};

const IfReloc = struct {
    to: Codegen.Cfg.Id,
    offset: u32,
};

const FuncReloc = struct {
    func: u32,
    offset: u32,
};

const Func = struct {
    base: u32,
    reloc_end: u32,
};

pub fn deinit(self: *HbvmCg) void {
    std.debug.assert(self.block_order.items.len == 0);
    self.block_order.deinit(self.gpa);
    std.debug.assert(self.ret_relocs.items.len == 0);
    self.ret_relocs.deinit(self.gpa);
    std.debug.assert(self.goto_relocs.items.len == 0);
    self.goto_relocs.deinit(self.gpa);
    std.debug.assert(self.if_relocs.items.len == 0);
    self.if_relocs.deinit(self.gpa);
    self.computed.deinit(self.gpa);
    self.args.deinit(self.gpa);
    self.funcs.deinit(self.gpa);
    self.relocs.funcs.deinit(self.gpa);
    std.debug.assert(self.tmp_locs.items.len == 0);
    self.tmp_locs.deinit(self.gpa);
    self.blocks.deinit(self.gpa);
}

pub fn generateFunc(self: *HbvmCg, func_id: usize) !void {
    self.reset();
    const func = &self.cg.ctx.funcs.items[func_id];
    const entry = func_id == 0;
    const base = self.out.items.len;
    self.ir = func.ir;
    defer self.ir.deinit(self.gpa);
    try self.computed.resize(self.gpa, self.ir.cfg.store.items.len);
    try self.blocks.resize(self.gpa, self.ir.cfg.store.items.len);
    for (self.blocks.items) |*block| block.* = .{};

    try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, 0 });
    if (!entry) try self.emit(.st, .{ Regs.ret_addr, Regs.stack_ptr, 0, 0 });

    if (self.cg.sizeOf(func.ret) > 16) _ = self.regs.allocRet().?;

    try self.args.resize(self.gpa, func.args.len);
    var arg_reg: u8 = 2;
    for (func.args.view(self.cg.ctx.allocated.items), self.args.items) |arg_ty, *arg| {
        arg.* = switch (self.cg.sizeOf(arg_ty)) {
            0 => Loc{},
            1...8 => b: {
                const loc = Loc{ .reg = self.regs.alloc() };
                try self.emit(.cp, .{ loc.reg, arg_reg });
                arg_reg += 1;
                break :b loc;
            },
            9...16 => b: {
                const loc = Loc{
                    .reg = self.regs.alloc(),
                    .sec_reg = self.regs.alloc(),
                };
                try self.emit(.brc, .{ loc.reg, arg_reg, 2 });
                arg_reg += 2;
                break :b loc;
            },
            else => b: {
                const loc = Loc{ .reg = self.regs.alloc() };
                try self.emit(.cp, .{ loc.reg, arg_reg });
                break :b loc.toggled("derefed", true);
            },
        };
    }

    try self.ir.computeDomTree(self.gpa, func.entry);

    try self.block_order.ensureTotalCapacity(self.gpa, self.ir.cfg.store.items.len);
    var ctx = struct {
        blocks: *std.ArrayListUnmanaged(Codegen.Cfg.Id),
        pub fn addBlock(s: *@This(), id: Codegen.Cfg.Id) !void {
            s.blocks.appendAssumeCapacity(id);
        }
    }{ .blocks = &self.block_order };
    try self.ir.traverseBlocks(func.entry, &ctx);
    for (self.block_order.items, 0..) |id, i| {
        try self.generateBlock(id, i);
    }
    self.block_order.items.len = 0;

    for (self.args.items) |arg| self.freeValue(arg);

    //self.regs.checkLeaks();
    const stack_size = 0;
    const poped_regs_size = self.regs.free_count * @as(u16, 8) + 8;

    for (self.goto_relocs.items) |reloc| {
        std.debug.print("reloc {d} to {x}\n", .{ reloc.offset, self.blocks.items[reloc.to.index].offset });
        self.writeReloc(i32, @intCast(reloc.offset + 1), @as(i32, @intCast(self.blocks.items[reloc.to.index].offset)) - @as(i32, @intCast(reloc.offset)));
    }
    self.goto_relocs.items.len = 0;

    for (self.if_relocs.items) |reloc|
        self.writeReloc(i16, @intCast(reloc.offset + 3), @intCast(self.blocks.items[reloc.to.index].offset -% reloc.offset));
    self.if_relocs.items.len = 0;

    for (self.ret_relocs.items) |offset|
        self.writeReloc(i32, @intCast(offset + 1), @intCast(self.out.items.len - offset));
    self.ret_relocs.items.len = 0;

    if (entry) {
        self.writeReloc(u64, base + 3, 0 -% @as(u64, stack_size));
        try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, stack_size });
        try self.emit(.tx, .{});
    } else {
        self.writeReloc(u64, base + 3, 0 -% @as(u64, poped_regs_size + stack_size));
        self.writeReloc(u64, base + 3 + 8 + 3, stack_size); // for now
        self.writeReloc(u16, base + 3 + 8 + 3 + 8, poped_regs_size);
        try self.emit(.ld, .{ Regs.ret_addr, Regs.stack_ptr, stack_size, poped_regs_size });
        try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, poped_regs_size });
        try self.emit(.jala, .{ Regs.zero, Regs.ret_addr, 0 });
    }

    try self.funcs.append(self.gpa, .{
        .base = @intCast(base),
        .reloc_end = @intCast(self.relocs.funcs.items.len),
    });
}

pub fn finalize(self: *HbvmCg) void {
    var prev_start: u32 = 0;
    for (self.funcs.items) |func| {
        for (self.relocs.funcs.items[prev_start..func.reloc_end]) |reloc| {
            const dest_offset = self.funcs.items[reloc.func].base;
            self.writeReloc(i32, reloc.offset + 3, @bitCast(dest_offset -% reloc.offset));
        }
        prev_start = func.reloc_end;
    }
}

fn generateBlock(self: *HbvmCg, id: Codegen.Cfg.Id, idx: usize) !void {
    self.blocks.items[id.index].offset = @intCast(self.out.items.len);
    switch (self.ir.cfg.get(id)) {
        .Void => unreachable,
        .Decl => |decl| {
            const loc = try self.generateExpr(null, decl.value);
            self.computed.items[id.index] = loc;
        },
        .Call => |call| {
            std.debug.assert(call.func.tag() == .func);
            const func = self.cg.ctx.funcs.items[call.func.index];
            var arg_reg: Regs.Id = 2;
            for (
                self.ir.view(call.args),
                func.args.view(self.cg.ctx.allocated.items),
            ) |arg, arg_ty| {
                const value = switch (self.cg.sizeOf(arg_ty)) {
                    0 => Loc{},
                    8 => b: {
                        const arg_loc = Loc{ .reg = arg_reg, .flags = .{ .is_borrowed = true } };
                        arg_reg += 1;
                        break :b try self.generateExpr(arg_loc, arg);
                    },
                    else => unreachable,
                };
                try self.tmp_locs.append(self.gpa, value);
            }
            const base = self.tmp_locs.items.len - func.args.len;
            for (self.tmp_locs.items[base..]) |value| self.freeValue(value);
            self.tmp_locs.items.len = base;

            switch (self.cg.sizeOf(func.ret)) {
                0 => {
                    try self.relocs.funcs.append(self.gpa, .{
                        .func = call.func.index,
                        .offset = @intCast(self.out.items.len),
                    });
                    try self.emit(.jal, .{ Regs.ret_addr, Regs.zero, 0 });
                },
                8 => {
                    const ret = self.regs.allocRet();
                    var ret_temp: ?Regs.Id = null;
                    if (ret == null) {
                        ret_temp = self.regs.alloc();
                        try self.emit(.cp, .{ ret_temp.?, Regs.ret });
                    }

                    try self.relocs.funcs.append(self.gpa, .{
                        .func = call.func.index,
                        .offset = @intCast(self.out.items.len),
                    });
                    try self.emit(.jal, .{ Regs.ret_addr, Regs.zero, 0 });

                    if (ret_temp) |r| try self.emit(.swa, .{ r, Regs.ret });

                    self.computed.items[id.index] = .{ .reg = ret orelse ret_temp.? };
                },
                else => unreachable,
            }
        },
        .Goto => |goto| {
            // TODO: collect the ordering instead so that we can eliminate useles jumps
            const block = &self.blocks.items[goto.to.index];
            if (block.args.len != goto.args.len) {
                std.debug.print("block {d} args {any}\n", .{ goto.to.index, goto.args });
                for (self.ir.view(goto.args)) |arg| {
                    try self.block_args.append(self.gpa, try self.generateExpr(null, arg));
                }
                block.args = .{
                    .base = @intCast(self.block_args.items.len - goto.args.len),
                    .len = @intCast(goto.args.len),
                };
            } else {
                for (
                    self.ir.view(goto.args),
                    self.block_args.items[block.args.base..][0..block.args.len],
                ) |arg, dst| {
                    _ = try self.generateExpr(dst.toggled("borrowed", true), arg);
                }
            }

            if (!self.isBefore(idx, goto.to)) {
                try self.goto_relocs.append(self.gpa, .{ .to = goto.to, .offset = @intCast(self.out.items.len) });
                try self.emit(.jmp, .{0});
            }
        },
        .If => |i| {
            std.debug.assert(i.then.args.len == 0);
            std.debug.assert(i.else_.args.len == 0);
            switch (self.ir.instrs.get(i.cond)) {
                inline .@"<=64", .@"==64" => |le, t| {
                    const lhs = try self.generateExpr(null, le.lhs);
                    defer self.freeValue(lhs);
                    const rhs = try self.generateExpr(null, le.rhs);
                    defer self.freeValue(rhs);
                    std.debug.assert(!self.isBefore(idx, i.else_.to));
                    try self.if_relocs.append(self.gpa, .{ .to = i.else_.to, .offset = @intCast(self.out.items.len) });
                    const instr = switch (t) {
                        .@"<=64" => .jgtu,
                        .@"==64" => .jne,
                        else => @compileError("wat"),
                    };
                    try self.emit(instr, .{ lhs.reg, rhs.reg, 0 });
                },
                else => unreachable,
            }
        },
        .Ret => |ret| {
            const rdst = Loc{ .reg = 1, .flags = .{ .is_borrowed = true } };
            self.freeValue(try self.generateExpr(rdst, ret));
            if (idx + 1 != self.block_order.items.len) {
                try self.ret_relocs.append(self.gpa, @intCast(self.out.items.len));
                try self.emit(.jmp, .{0});
            }
        },
    }
}

fn isBefore(self: *HbvmCg, idx: usize, dest: Codegen.Cfg.Id) bool {
    return idx + 1 < self.block_order.items.len and self.block_order.items[idx + 1].index == dest.index;
}

fn generateExpr(self: *HbvmCg, dst: ?Loc, id: Codegen.Instr.Id) !Loc {
    return switch (self.ir.instrs.get(id)) {
        .Void => .{},
        .Arg => b: {
            const loc = self.args.items[id.index].toggled("borrowed", true);
            if (dst) |d| try self.emit(.cp, .{ d.reg, loc.reg });
            break :b dst orelse loc;
        },
        .Li64 => |i| b: {
            const loc = dst orelse Loc{ .reg = self.regs.alloc() };
            try self.emit(.li64, .{ loc.reg, i });
            break :b loc;
        },
        inline .@"+64", .@"-64", .@"*64" => |body, t| b: {
            const lhs = try self.generateExpr(null, body.lhs);
            defer if (dst != null) self.freeValue(lhs);
            const rhs = try self.generateExpr(null, body.rhs);
            const bdst = dst orelse lhs;
            defer self.freeValue(rhs);
            const instr = switch (t) {
                .@"+64" => .add64,
                .@"-64" => .sub64,
                .@"*64" => .mul64,
                else => @compileError("wat"),
            };
            try self.emit(instr, .{ bdst.reg, lhs.reg, rhs.reg });
            break :b bdst;
        },
        .@"<=64", .@"==64" => unreachable,
        .@"/64" => |body| b: {
            const lhs = try self.generateExpr(null, body.lhs);
            defer if (dst != null) self.freeValue(lhs);
            const rhs = try self.generateExpr(null, body.rhs);
            defer self.freeValue(rhs);
            const bdst = dst orelse lhs;
            try self.emit(.diru64, .{ bdst.reg, 0, lhs.reg, rhs.reg });
            break :b bdst;
        },
        .Call => |call| self.computed.items[call.index],
        .BlockArg => |ba| b: {
            std.debug.print("block arg {d} {d}\n", .{ ba.block.index, ba.index });
            const block = &self.blocks.items[ba.block.index];
            const loc = self.block_args.items[block.args.base..][0..block.args.len][ba.index]
                .toggled("borrowed", true);

            if (dst) |d| {
                std.debug.print("block arg {d} {d} need move\n", .{ ba.block.index, ba.index });
                try self.emit(.cp, .{ d.reg, loc.reg });
                break :b d;
            } else break :b loc;
        },
    };
}

fn freeValue(self: *HbvmCg, loc: Loc) void {
    if (loc.flags.is_borrowed) return;
    if (loc.reg == Regs.stack_ptr) {
        unreachable;
    } else if (loc.reg != 0) {
        if (loc.sec_reg != 0) self.regs.free(loc.sec_reg);
        self.regs.free(loc.reg);
    }
}

fn writeReloc(self: *HbvmCg, comptime T: type, offset: usize, value: T) void {
    std.debug.assert(std.mem.allEqual(u8, self.out.items[offset..][0..@sizeOf(T)], 0));
    self.out.items[offset..][0..@sizeOf(T)].* = @bitCast(value);
}

fn reset(self: *HbvmCg) void {
    self.computed.clearRetainingCapacity();
    self.regs = Regs.init(Regs.ret_addr + 1, Regs.stack_ptr - 1);
}

fn emit(self: *HbvmCg, comptime op: isa.Op, args: anytype) !void {
    if (op == .cp and args[0] == args[1]) return;
    try self.out.appendSlice(&isa.pack(op, args));
}
