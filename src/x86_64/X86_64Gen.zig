const std = @import("std");
const Object = @import("../Object.zig");
const root = @import("../root.zig");
const graph = root.backend.graph;
const Func = graph.Func(Node);
const FuncNode = Func.Node;
const Mach = root.backend.Mach;
const Regalloc = root.backend.Regalloc;
const utils = root.utils;

builder: Object,
tmp_body: std.ArrayListUnmanaged(u8) = .{},
gpa: std.mem.Allocator,

const max_alloc_regs = 16;

pub const Node = union(enum) {
    pub const is_basic_block_start: []const Func.Kind = &.{};
    pub const is_mem_op: []const Func.Kind = &.{};
    pub const is_basic_block_end: []const Func.Kind = &.{};
    pub const is_pinned: []const Func.Kind = &.{};

    pub fn isInterned(kind: Func.Kind) bool {
        _ = kind;
        return false;
    }

    pub fn isSwapped(node: *Func.Node) bool {
        _ = node;
        return false;
    }

    pub fn idealize(func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
        _ = func;
        _ = node;
        _ = worklist;
        return null;
    }
};

pub fn emitFunc(self: *@This(), func: *Func, opts: Mach.EmitOptions) void {
    errdefer unreachable;

    opts.optimizations.execute(Node, func);

    const allocs = Regalloc.ralloc(Node, func);

    _ = allocs;

    const id = opts.id;
    const name = opts.name;
    const entry = opts.entry;

    _ = id;
    _ = name;

    std.debug.assert(entry);

    const main_fn = try self.builder.declareFunc(self.gpa, "main", .global);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    //if (self.funcs.items.len <= id) {
    //    const prev_len = self.funcs.items.len;
    //    self.funcs.resize(self.gpa, id + 1) catch unreachable;
    //    @memset(self.funcs.items[prev_len..], .{ .name = "" });
    //}
    //self.funcs.items[id].offset = @intCast(self.out.items.len);
    //self.funcs.items[id].name = name;

    //self.block_offsets = tmp.arena.alloc(i32, func.block_count);
    //self.local_relocs = .initBuffer(tmp.arena.alloc(BlockReloc, func.block_count * 2));
    //self.allocs = allocs;
    //self.ret_count = func.returns.len;

    var visited = std.DynamicBitSet.initEmpty(tmp.arena.allocator(), func.next_id) catch unreachable;
    const postorder = func.collectPostorder(tmp.arena.allocator(), &visited);
    //const is_tail = false; //for (postorder) |bb| {
    //if (bb.base.kind == .CallEnd) break false;
    //} else true;

    //const reg_shift: u8 = 0;
    //for (self.allocs) |*r| r.* += reg_shift;
    const max_reg: u16 = 0; //std.mem.max(u16, self.allocs);
    const used_registers: u8 = 0; //if (self.allocs.len == 0) 0 else @min(max_reg, max_alloc_regs) -|
    // (@intFromEnum(isa.Reg.ret_addr) - @intFromBool(is_tail));

    const used_reg_size = @as(u16, used_registers) * 8;
    const spill_count = (max_reg -| max_alloc_regs) * 8;

    var local_size: i64 = 0;
    if (func.root.outputs().len > 1) {
        local_size += 0;
        //std.debug.assert(func.root.outputs()[1].kind == .Mem);
        //for (func.root.outputs()[1].outputs()) |o| if (o.kind == .Local) {
        //    const extra = o.extra(.Local);
        //    const size = extra.*;
        //    extra.* = @bitCast(local_size);
        //    local_size += @intCast(size);
        //};
        // unreachable;
    }

    const stack_size: i64 = used_reg_size + local_size + spill_count;
    //self.spill_base = @intCast(used_reg_size + local_size);

    prelude: {
        if (used_reg_size != 0) {
            //self.emit(.st, .{ .ret_addr, .stack_addr, -@as(i64, used_reg_size), used_reg_size });
            unreachable;
        }
        if (stack_size != 0) {
            //self.emit(.addi64, .{ .stack_addr, .stack_addr, @as(u64, @bitCast(-stack_size)) });
            unreachable;
        }

        //for (0..func.params.len) |i| {
        //    const argn = for (postorder[0].base.outputs()) |o| {
        //        if (o.kind == .Arg and o.extra(.Arg).* == i) break o;
        //    } else continue; // is dead
        //    if (self.outReg(argn) != isa.Reg.arg(i)) {
        //        self.emit(.cp, .{ self.outReg(argn), isa.Reg.arg(i) });
        //        self.flushOutReg(argn);
        //    }
        //}
        std.debug.assert(func.params.len == 0);
        break :prelude;
    }

    for (postorder, 0..) |bb, i| {
        _ = i;
        //self.block_offsets[bb.base.schedule] = @intCast(self.out.items.len);
        //std.debug.assert(bb.base.schedule == i);
        self.emitBlockBody(tmp.arena.allocator(), &bb.base);
        //const last = bb.base.outputs()[bb.base.output_len - 1];
        //if (last.outputs().len == 0) {
        //    std.debug.assert(last.kind == .Return);
        //    if (stack_size != 0) {
        //        self.emit(.addi64, .{ .stack_addr, .stack_addr, @as(u64, @bitCast(stack_size)) });
        //    }
        //    if (used_reg_size != 0) {
        //        self.emit(.ld, .{ .ret_addr, .stack_addr, -@as(i64, used_reg_size), used_reg_size });
        //    }
        //    if (entry) {
        //        self.emit(.tx, .{});
        //    } else {
        //        self.emit(.jala, .{ .null, .ret_addr, 0 });
        //    }
        //} else if (i + 1 == last.outputs()[@intFromBool(last.isSwapped())].schedule) {
        //    // noop
        //} else if (last.kind == .Never) {
        //    // noop
        //} else if (last.kind == .Trap) {
        //    // noop
        //} else {
        //    std.debug.assert(last.outputs()[0].isBasicBlockStart());
        //    self.local_relocs.appendAssumeCapacity(.{
        //        .dest_block = last.outputs()[@intFromBool(last.isSwapped())].schedule,
        //        .rel = self.reloc(1, .rel32),
        //    });
        //    self.emit(.jmp, .{0});
        //}
    }

    //for (self.local_relocs.items) |lr| {
    //    self.doReloc(lr.rel, self.block_offsets[lr.dest_block]);
    //}

    try self.builder.defineFunc(self.gpa, main_fn, self.tmp_body.items);
    self.tmp_body.items.len = 0;
}

pub fn emitBlockBody(self: *@This(), arena: std.mem.Allocator, block: *FuncNode) void {
    _ = arena;
    for (block.outputs()) |instr| switch (instr.kind) {
        .CInt => {
            const imm64 = instr.extra(.CInt).*;
            var reg_index: u8 = 0;

            var rex: u8 = 0x48;

            if (reg_index >= 8) {
                rex = rex | 0x01;
                reg_index = reg_index - 8;
            }

            const opcode_base = 0xB8;

            const opcode = opcode_base + reg_index;

            self.tmp_body.append(self.gpa, rex) catch unreachable;
            self.tmp_body.append(self.gpa, opcode) catch unreachable;
            self.tmp_body.writer(self.gpa).writeInt(i64, imm64, .little) catch unreachable;
        },
        .Return => {
            const ret_op = 0xc3;
            self.tmp_body.append(self.gpa, ret_op) catch unreachable;
        },
        else => {
            std.debug.panic("{any}", .{instr});
        },
    };
}

pub fn emitData(self: *@This(), opts: Mach.DataOptions) void {
    _ = self;
    _ = opts;
    //unreachable;
}

pub fn finalize(self: *@This()) std.ArrayListUnmanaged(u8) {
    var out = std.ArrayListUnmanaged(u8){};
    self.builder.flush(out.writer(self.gpa).any()) catch unreachable;
    return out;
}

pub fn disasm(self: *@This(), out: std.io.AnyWriter, colors: std.io.tty.Config) void {
    _ = self;
    _ = out;
    _ = colors;
    unreachable;
}

pub fn deinit(self: *@This()) void {
    self.builder.deinit(self.gpa);
    self.tmp_body.deinit(self.gpa);
}
