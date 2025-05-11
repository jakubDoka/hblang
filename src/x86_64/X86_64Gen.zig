const std = @import("std");

const Object = @import("../Object.zig");
const root = @import("../root.zig");
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Regalloc = root.backend.Regalloc;
const utils = root.utils;

const X86_64 = @This();

const Func = graph.Func(Node);
const FuncNode = Func.Node;
builder: Object,
gpa: std.mem.Allocator,
tmp_body: std.ArrayListUnmanaged(u8) = .{},
allocs: []u16 = undefined,

const max_alloc_regs = 16;

pub const Node = union(enum) {
    pub const is_basic_block_start: []const Func.Kind = &.{};
    pub const is_mem_op: []const Func.Kind = &.{};
    pub const is_basic_block_end: []const Func.Kind = &.{};
    pub const is_pinned: []const Func.Kind = &.{};

    pub fn carried(node: *Func.Node) ?usize {
        return if (node.kind == .BinOp) 0 else null;
    }

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

pub fn reg(self: X86_64, node: ?*FuncNode) u16 {
    return self.allocs[node.?.schedule];
}

pub fn emitBinOp(self: *X86_64, opcode: enum(u8) {
    add = 0x01,
    sub = 0x29,
    mov = 0x89,
}, lhs: u16, rhs: u16) void {
    errdefer unreachable;

    var rex: u8 = 0x48;

    if (lhs > 8) rex |= 1;
    if (rhs > 8) rex |= 0b100;

    const mode = 0b11 << 6;
    const args: u8 = @intCast(mode | ((rhs & 0b111) << 3) | (lhs & 0b111));

    try self.tmp_body.appendSlice(self.gpa, &.{ rex, @intFromEnum(opcode), args });
}

pub fn emitFunc(self: *X86_64, func: *Func, opts: Mach.EmitOptions) void {
    errdefer unreachable;

    opts.optimizations.execute(Node, func);

    self.allocs = Regalloc.ralloc(Node, func);

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

pub fn emitBlockBody(self: *X86_64, arena: std.mem.Allocator, block: *FuncNode) void {
    _ = arena;

    errdefer unreachable;

    for (block.outputs()) |instr| switch (instr.kind) {
        .CInt => {
            const imm64 = instr.extra(.CInt).*;
            var reg_index: u8 = @intCast(self.reg(instr));

            var rex: u8 = 0x48;

            if (reg_index >= 8) {
                rex |= 0x01;
                reg_index -= 8;
            }

            const opcode_base = 0xB8;

            const opcode = opcode_base + reg_index;

            try self.tmp_body.appendSlice(self.gpa, &.{ rex, opcode });
            try self.tmp_body.writer(self.gpa).writeInt(i64, imm64, .little);
        },
        .Return => {
            for (instr.dataDeps()[0..1]) |inp| {
                const src = self.reg(inp);
                if (src != 0) self.emitBinOp(.mov, 0, src);
            }

            const ret_op = 0xc3;
            try self.tmp_body.append(self.gpa, ret_op);
        },
        .BinOp => {
            const op = instr.extra(.BinOp).*;
            const dst = self.reg(instr);
            const lhs = self.reg(instr.inputs()[1]);
            const rhs = self.reg(instr.inputs()[2]);

            if (dst != lhs) self.emitBinOp(.mov, dst, lhs);

            switch (op) {
                .iadd => {
                    self.emitBinOp(.add, dst, rhs);
                },
                .isub => {
                    self.emitBinOp(.sub, dst, rhs);
                },
                else => {
                    std.debug.panic("{any}", .{instr});
                },
            }
        },
        .UnOp => {
            const op = instr.extra(.UnOp).*;
            const dst = self.reg(instr);
            const src = self.reg(instr.inputs()[1]);

            switch (op) {
                .uext => {
                    if (dst != src) self.emitBinOp(.mov, dst, src);
                },
                .sext => {
                    if (dst != src) self.emitBinOp(.mov, dst, src);
                },
                else => {
                    std.debug.panic("{any}", .{instr});
                },
            }
        },
        else => {
            std.debug.panic("{any}", .{instr});
        },
    };
}

pub fn emitData(self: *X86_64, opts: Mach.DataOptions) void {
    _ = self;
    _ = opts;
    //unreachable;
}

pub fn finalize(self: *X86_64) std.ArrayListUnmanaged(u8) {
    var out = std.ArrayListUnmanaged(u8){};
    self.builder.flush(out.writer(self.gpa).any()) catch unreachable;
    return out;
}

pub fn disasm(_: *X86_64, opts: Mach.DisasmOpts) void {
    // TODO: maybe we can do this in more platform independend way?
    // Compiling a library in?

    errdefer unreachable;

    var tmp = root.utils.Arena.scrath(null);
    defer tmp.deinit();

    const name = try std.fmt.allocPrint(tmp.arena.allocator(), "{s}.o", .{opts.name});

    try std.fs.cwd().writeFile(.{ .sub_path = name, .data = opts.bin });
    defer std.fs.cwd().deleteFile(name) catch unreachable;

    var dump = std.process.Child.init(&.{ "objdump", "-d", name }, tmp.arena.allocator());
    dump.stdout_behavior = .Pipe;
    try dump.spawn();

    if (opts.colors == .no_color) {
        var buf: [1024 * 4]u8 = undefined;
        while (true) {
            const red = try dump.stdout.?.read(&buf);
            if (red == 0) break;
            try opts.out.writeAll(buf[0..red]);
        }
    } else {
        var buf: [1024 * 4]u8 = undefined;
        while (true) {
            const red = try dump.stdout.?.read(&buf);
            if (red == 0) break;
            try std.io.getStdErr().writeAll(buf[0..red]);
        }
    }

    _ = try dump.wait();
}

pub fn run(_: *X86_64, env: Mach.RunEnv) !usize {
    errdefer unreachable;

    var tmp = root.utils.Arena.scrath(null);
    defer tmp.deinit();

    const name = try std.fmt.allocPrint(tmp.arena.allocator(), "tmp_{s}.o", .{env.name});
    const exe_name = try std.fmt.allocPrint(tmp.arena.allocator(), "./tmp_{s}", .{env.name});

    try std.fs.cwd().writeFile(.{ .sub_path = name, .data = env.code });
    defer std.fs.cwd().deleteFile(name) catch unreachable;

    var compile = std.process.Child.init(
        &.{ "gcc", name, "-o", exe_name },
        tmp.arena.allocator(),
    );
    _ = try compile.spawnAndWait();
    defer std.fs.cwd().deleteFile(exe_name) catch unreachable;

    var run_exe = std.process.Child.init(
        &.{exe_name},
        tmp.arena.allocator(),
    );
    const res = try run_exe.spawnAndWait();

    return res.Exited;
}

pub fn deinit(self: *X86_64) void {
    self.builder.deinit(self.gpa);
    self.tmp_body.deinit(self.gpa);
}
