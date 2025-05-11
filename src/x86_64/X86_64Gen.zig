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
const Move = utils.Move(Reg);

builder: Object,
gpa: std.mem.Allocator,
func_bodies: std.ArrayListUnmanaged(u8) = .{},
func_map: std.ArrayListUnmanaged(FuncData) = .{},
global_relocs: std.ArrayListUnmanaged(GlobalReloc) = .{},
allocs: []u16 = undefined,
ret_count: usize = undefined,
local_relocs: std.ArrayListUnmanaged(Reloc) = undefined,
block_offsets: []u32 = undefined,

pub const Reg = enum(u8) {
    rax,
    rcx,
    rdx,
    rbx,
    rsp,
    rbp,
    rsi,
    rdi,
    r8,
    r9,
    r10,
    r11,
    r12,
    r13,
    r14,
    r15,

    null = 255,

    const system_v = struct {
        const args: []const Reg = &.{ .rdi, .rsi, .rdx, .rcx, .r8, .r9 };
        const caller_saved: []const Reg = &.{ .rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11 };
        const callee_saved: []const Reg = &.{ .rbx, .rbp, .r12, .r13, .r14, .r15 };
    };
};

const max_alloc_regs = 16;

pub const FuncData = struct {
    id: Object.Func = .invalid,
    offset: u32 = 0,
    size: u32 = 0,
};

pub const Reloc = struct {
    offset: u32,
    dest: u32,
    class: enum { rel32 },
    off: u8,
};

pub const GlobalReloc = struct {
    offset: u32,
    dest: u32,
    class: enum { rel32 },
    kind: enum { func },
};

pub const Node = union(enum) {
    pub const is_basic_block_start: []const Func.Kind = &.{};
    pub const is_mem_op: []const Func.Kind = &.{};
    pub const is_basic_block_end: []const Func.Kind = &.{};
    pub const is_pinned: []const Func.Kind = &.{};
    pub const reserved_regs = @as(u64, 1) << @intFromEnum(Reg.rsp);

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

    pub fn clobbers(node: *Func.Node) u64 {
        return switch (node.kind) {
            .Call => comptime b: {
                var vl: u64 = 0;
                for (Reg.system_v.caller_saved) |r| {
                    vl |= @as(u64, 1) << @intFromEnum(r);
                }
                break :b vl;
            },
            else => 0,
        };
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

pub const Opcode = enum(u8) {
    add = 0x01,
    addimm = 0x81,
    sub = 0x29,
    xchg = 0x87,
    mov = 0x89,
    cmp = 0x3b,
    movmr = 0x8b,
};

pub fn rex(lhs: u16, rhs: u16) u8 {
    var rx: u8 = 0x48;

    if (lhs > 8) rx |= 0b001;
    if (rhs > 8) rx |= 0b100;

    return rx;
}

pub fn modrm(mode: u8, rm: u16, rg: u16) u8 {
    return @intCast(mode << 6 | ((rg & 0b111) << 3) | (rm & 0b111));
}

pub fn emitBinOp(self: *X86_64, opcode: Opcode, lhs: u16, rhs: u16) void {
    errdefer unreachable;
    try self.func_bodies.appendSlice(self.gpa, &.{
        rex(lhs, rhs),
        @intFromEnum(opcode),
        modrm(0b11, lhs, rhs),
    });
}

pub fn emitBinOpMem(self: *X86_64, opcode: Opcode, lhs: u16, rhs: u16, offset: u32) void {
    errdefer unreachable;
    try self.func_bodies.appendSlice(self.gpa, &.{
        rex(lhs, 0),
        @intFromEnum(opcode),
        modrm(0b10, lhs, rhs),
    });
    if (lhs == 12) {
        try self.func_bodies.append(self.gpa, 0x24);
    }
    try self.func_bodies.writer(self.gpa).writeInt(u32, offset, .little);
}

pub fn emitImmBinOp(self: *X86_64, opcode: Opcode, lhs: u16, rhs: u32) void {
    errdefer unreachable;
    try self.func_bodies.appendSlice(self.gpa, &.{
        rex(lhs, 0),
        @intFromEnum(opcode),
        modrm(0b11, lhs, 0),
    });
    try self.func_bodies.writer(self.gpa).writeInt(u32, rhs, .little);
}

pub fn emitFunc(self: *X86_64, func: *Func, opts: Mach.EmitOptions) void {
    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    opts.optimizations.execute(Node, func);

    const id = opts.id;
    const entry = opts.entry;
    const name = if (entry) "main" else opts.name;
    const linkage: Object.Linkage = if (entry) .global else .local;

    const ob_id = try self.builder.declareFunc(self.gpa, name, linkage);

    if (id >= self.func_map.items.len) {
        const prev_len = self.func_map.items.len;
        try self.func_map.resize(self.gpa, id + 1);
        @memset(self.func_map.items[prev_len..], .{});
    }
    const prev_len = self.func_bodies.items.len;

    //self.block_offsets = tmp.arena.alloc(i32, func.block_count);
    //self.local_relocs = .initBuffer(tmp.arena.alloc(BlockReloc, func.block_count * 2));

    var visited = std.DynamicBitSet.initEmpty(tmp.arena.allocator(), func.next_id) catch unreachable;
    const postorder = func.collectPostorder(tmp.arena.allocator(), &visited);

    self.allocs = Regalloc.ralloc(Node, func);
    self.ret_count = func.returns.len;
    self.local_relocs = .initBuffer(tmp.arena.alloc(Reloc, 128));
    self.block_offsets = tmp.arena.alloc(u32, postorder.len);

    const reg_shift: u8 = 0;
    for (self.allocs) |*r| r.* += reg_shift;

    var used_regs = std.EnumSet(Reg){};
    for (self.allocs) |a| {
        if (std.meta.intToEnum(Reg, a)) |enm| {
            used_regs.insert(enm);
        } else |_| {
            unreachable;
        }
    }

    var local_size: i64 = 0;
    if (func.root.outputs().len > 1) {
        std.debug.assert(func.root.outputs()[1].kind == .Mem);
        for (func.root.outputs()[1].outputs()) |o| if (o.kind == .Local) {
            const extra = o.extra(.Local);
            const size = extra.*;
            extra.* = @bitCast(local_size);
            local_size += @intCast(size);
        };
    }

    const stack_size: i64 = local_size; //used_reg_size + local_size + spill_count;
    //self.spill_base = @intCast(used_reg_size + local_size);

    prelude: {
        for (Reg.system_v.callee_saved) |r| {
            if (used_regs.contains(r)) {
                if (@intFromEnum(r) >= 8) {
                    try self.func_bodies.append(self.gpa, 0x41);
                }
                const opcode_base = 0x50;
                try self.func_bodies.append(self.gpa, opcode_base + (@intFromEnum(r) & 0b111));
            }
        }

        if (stack_size != 0) {
            // sub rsp, stack_size
            self.emitImmBinOp(
                .addimm,
                @intFromEnum(Reg.rsp),
                @bitCast(@as(i32, @intCast(-stack_size))),
            );
        }

        for (0..func.params.len) |i| {
            const argn = for (postorder[0].base.outputs()) |o| {
                if (o.kind == .Arg and o.extra(.Arg).* == i) break o;
            } else continue; // is dead
            if (self.reg(argn) != @intFromEnum(Reg.system_v.args[i])) {
                self.emitBinOp(.mov, self.reg(argn), @intFromEnum(Reg.system_v.args[i]));
            }
        }

        break :prelude;
    }

    for (postorder, 0..) |bb, i| {
        self.block_offsets[bb.base.schedule] = @intCast(self.func_bodies.items.len);
        std.debug.assert(bb.base.schedule == i);

        self.emitBlockBody(tmp.arena.allocator(), &bb.base);
        const last = bb.base.outputs()[bb.base.output_len - 1];
        if (last.outputs().len == 0) {
            std.debug.assert(last.kind == .Return);

            if (stack_size != 0) {
                self.emitImmBinOp(.addimm, @intFromEnum(Reg.rsp), @intCast(stack_size));
            }

            for (Reg.system_v.callee_saved) |r| {
                if (used_regs.contains(r)) {
                    if (@intFromEnum(r) >= 8) {
                        try self.func_bodies.append(self.gpa, 0x41);
                    }
                    const opcode_base = 0x58;
                    try self.func_bodies.append(self.gpa, opcode_base + (@intFromEnum(r) & 0b111));
                }
            }

            const ret_op = 0xc3;
            try self.func_bodies.append(self.gpa, ret_op);
        } else if (i + 1 == last.outputs()[@intFromBool(last.isSwapped())].schedule) {
            // noop
        } else if (last.kind == .Never) {
            // noop
        } else if (last.kind == .Trap) {
            // noop
        } else {
            std.debug.assert(last.outputs()[0].isBasicBlockStart());
            self.local_relocs.appendAssumeCapacity(.{
                .dest = last.outputs()[@intFromBool(last.isSwapped())].schedule,
                .offset = @intCast(self.func_bodies.items.len),
                .off = 1,
                .class = .rel32,
            });
            try self.func_bodies.appendSlice(self.gpa, &.{ 0xE9, 0, 0, 0, 0 });
        }
    }

    for (self.local_relocs.items) |rl| {
        // TODO: copypasted nono

        // TODO: make the class hold the values directly
        const size = switch (rl.class) {
            .rel32 => 4,
        };

        const dst_offset: i64 = self.block_offsets[rl.dest];
        const jump = dst_offset - rl.offset - size - rl.off; // welp we learned

        @memcpy(
            self.func_bodies.items[rl.offset + rl.off ..][0..size],
            @as(*const [8]u8, @ptrCast(&jump))[0..size],
        );
    }

    self.func_map.items[id] = .{
        .id = ob_id,
        .offset = @intCast(prev_len),
        .size = @intCast(self.func_bodies.items.len - prev_len),
    };
}

fn orderMoves(self: *X86_64, moves: []Move) void {
    utils.orderMoves(self, Reg, moves);
}

pub fn emitSwap(self: *X86_64, lhs: Reg, rhs: Reg) void {
    self.emitBinOp(.xchg, @intFromEnum(lhs), @intFromEnum(rhs));
}

pub fn emitCp(self: *X86_64, dst: Reg, src: Reg) void {
    self.emitBinOp(.mov, @intFromEnum(dst), @intFromEnum(src));
}

pub fn emitBlockBody(self: *X86_64, arena: std.mem.Allocator, block: *FuncNode) void {
    _ = arena;

    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    for (block.outputs()) |instr| switch (instr.kind) {
        .CInt => {
            const imm64 = instr.extra(.CInt).*;
            const reg_index: u8 = @intCast(self.reg(instr));

            const opcode_base = 0xB8;

            const opcode = opcode_base + reg_index;

            try self.func_bodies.appendSlice(self.gpa, &.{ rex(reg_index, 0), opcode });
            try self.func_bodies.writer(self.gpa).writeInt(i64, imm64, .little);
        },
        .MachMove => {},
        .Phi => {},
        .Local => {
            self.emitBinOp(.mov, self.reg(instr), @intFromEnum(Reg.rsp));
            self.emitImmBinOp(.addimm, self.reg(instr), @intCast(instr.extra(.Local).*));
        },
        .Load => {
            std.debug.assert(instr.data_type.size() == 8);

            const dst = self.reg(instr);
            const bse = self.reg(instr.inputs()[2]);

            const offset: u32 = 0;

            self.emitBinOpMem(.movmr, bse, dst, offset);
        },
        .Store => {
            std.debug.assert(instr.data_type.size() == 8);

            const dst = self.reg(instr.inputs()[2]);
            const vl = self.reg(instr.inputs()[3]);

            const offset: u32 = 0;

            std.debug.print("{} {}\n", .{ dst, vl });
            self.emitBinOpMem(.mov, dst, vl, offset);
        },
        .Call => {
            const call = instr.extra(.Call);

            var moves = std.ArrayList(Move).init(tmp.arena.allocator());
            for (instr.dataDeps(), 0..) |arg, i| {
                const dst, const src: Reg = .{ Reg.system_v.args[i], @enumFromInt(self.reg(arg)) };
                if (dst != src) moves.append(.{ dst, src, 0 }) catch unreachable;
            }
            self.orderMoves(moves.items);

            try self.global_relocs.append(self.gpa, .{
                .offset = @intCast(self.func_bodies.items.len),
                .dest = call.id,
                .class = .rel32,
                .kind = .func,
            });
            const opcode = 0xE8;
            try self.func_bodies.appendSlice(self.gpa, &.{ opcode, 0, 0, 0, 0 });

            const cend = for (instr.outputs()) |o| {
                if (o.kind == .CallEnd) break o;
            } else unreachable;
            moves.items.len = 0;
            for (cend.outputs()) |r| {
                if (r.kind == .Ret) {
                    const dst: Reg, const src = .{ @enumFromInt(self.reg(r)), Reg.rax };
                    if (dst != src) moves.append(.{ dst, src, 0 }) catch unreachable;
                }
            }
            self.orderMoves(moves.items);
        },
        .Arg => {},
        .Ret => {},
        .Mem => {},
        .Return => {
            for (instr.dataDeps()[0..self.ret_count]) |inp| {
                const src = self.reg(inp);
                if (src != 0) self.emitBinOp(.mov, 0, src);
            }
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
                .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt, .slt => |t| {
                    self.emitBinOp(.cmp, dst, rhs);

                    const opcode_2: u8 = switch (t) {
                        .eq => 0x94,
                        .ne => 0x95,
                        .ult => 0x9C,
                        .ule => 0x9E,
                        .ugt => 0x9F,
                        .uge => 0x9D,
                        .slt => 0x92,
                        .sle => 0x96,
                        .sgt => 0x97,
                        .sge => 0x93,
                        else => unreachable,
                    };

                    try self.func_bodies.appendSlice(self.gpa, &.{
                        rex(dst, 0),
                        0x0f,
                        opcode_2,
                        modrm(0x11, dst, 0),
                    });
                },
                else => {
                    std.debug.panic("{any}", .{instr});
                },
            }
        },
        .If => {
            self.local_relocs.appendAssumeCapacity(.{
                .dest = instr.outputs()[1].schedule,
                .offset = @intCast(self.func_bodies.items.len),
                .class = .rel32,
                .off = 2,
            });
            try self.func_bodies.appendSlice(self.gpa, &.{ 0x0F, 0x84, 0, 0, 0, 0 });
        },
        .Jmp => if (instr.outputs()[0].kind == .Region or instr.outputs()[0].kind == .Loop) {
            const idx = std.mem.indexOfScalar(?*Func.Node, instr.outputs()[0].inputs(), instr).? + 1;

            var moves = std.ArrayList(Move).init(tmp.arena.allocator());
            for (instr.outputs()[0].outputs()) |o| {
                if (o.isDataPhi()) {
                    std.debug.assert(o.inputs()[idx].?.kind == .MachMove);
                    const dst, const src = .{ self.reg(o), self.reg(o.inputs()[idx].?.inputs()[1]) };
                    if (dst != src) try moves.append(.{ @enumFromInt(dst), @enumFromInt(src), 0 });
                }
            }

            self.orderMoves(moves.items);
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
    errdefer unreachable;

    for (self.global_relocs.items) |rl| {
        switch (rl.kind) {
            .func => {
                const dst_offset: i64 = self.func_map.items[rl.dest].offset;
                const jump = dst_offset - rl.offset - 5; // welp we learned

                // TODO: make the class hold the values directly
                const size = switch (rl.class) {
                    .rel32 => 4,
                };

                @memcpy(
                    self.func_bodies.items[rl.offset + 1 ..][0..size],
                    @as(*const [8]u8, @ptrCast(&jump))[0..size],
                );
            },
        }
    }

    for (self.func_map.items) |f| {
        if (f.id == .invalid) continue;
        const body = self.func_bodies.items[f.offset..][0..f.size];
        try self.builder.defineFunc(self.gpa, f.id, body);
    }

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

    if (res != .Exited) {
        return res.Signal;
    }
    return res.Exited;
}

pub fn deinit(self: *X86_64) void {
    if (std.meta.fields(X86_64).len != 9) @compileError("reminder: deinit");

    self.builder.deinit(self.gpa);
    self.func_bodies.deinit(self.gpa);
    self.global_relocs.deinit(self.gpa);
    self.func_map.deinit(self.gpa);
}
