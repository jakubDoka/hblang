const std = @import("std");

const object = root.object;
const root = @import("hb");
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Regalloc = root.backend.Regalloc;
const utils = root.utils;
const zydis = @import("zydis").exports;

const X86_64 = @This();
const Func = graph.Func(Node);
const FuncNode = Func.Node;
const Move = utils.Move(Reg);

gpa: std.mem.Allocator,
object_format: enum { elf, coff },
func_map: std.ArrayListUnmanaged(Mach.Data.SymIdx) = .{},
global_map: std.ArrayListUnmanaged(Mach.Data.SymIdx) = .{},
memcpy: Mach.Data.SymIdx = .invalid,
out: Mach.Data = .{},
allocs: []u16 = undefined,
ret_count: usize = undefined,
local_relocs: std.ArrayListUnmanaged(Reloc) = undefined,
block_offsets: []u32 = undefined,
local_base: u32 = undefined,

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
    _, // spills

    const system_v = struct {
        const args: []const Reg = &.{ .rdi, .rsi, .rdx, .rcx, .r8, .r9 };
        const caller_saved: []const Reg = &.{ .rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11 };
        const callee_saved: []const Reg = &.{ .rbx, .rbp, .r12, .r13, .r14, .r15 };
    };

    pub fn asZydisOp(self: Reg, size: usize) zydis.ZydisEncoderOperand {
        if (@intFromEnum(self) < @intFromEnum(Reg.r15)) {
            return .{
                .type = zydis.ZYDIS_OPERAND_TYPE_REGISTER,
                .reg = .{ .value = @intCast(switch (size) {
                    1 => zydis.ZYDIS_REGISTER_AL + if (@intFromEnum(self) > 4) @as(u8, 4) else 0,
                    2 => zydis.ZYDIS_REGISTER_AX,
                    4 => zydis.ZYDIS_REGISTER_EAX,
                    8 => zydis.ZYDIS_REGISTER_RAX,
                    else => unreachable,
                } + @intFromEnum(self)) },
            };
        } else {
            return .{
                .type = zydis.ZYDIS_OPERAND_TYPE_MEMORY,
                .mem = .{
                    .base = zydis.ZYDIS_REGISTER_RSP,
                    .size = @intCast(size),
                    .displacement = @as(
                        c_int,
                        @intFromEnum(self) - @intFromEnum(Reg.r15),
                    ) * 8,
                },
            };
        }
    }
};

const max_alloc_regs = 16;

pub const Reloc = struct {
    offset: u32,
    dest: u32,
    class: enum { rel32 },
    off: u8,
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
            .Call, .MemCpy => comptime b: {
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

pub fn getReg(self: X86_64, node: ?*FuncNode) Reg {
    return @enumFromInt(self.allocs[node.?.schedule]);
}

pub fn emitFunc(self: *X86_64, func: *Func, opts: Mach.EmitOptions) void {
    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    opts.optimizations.execute(Node, func);

    const id = opts.id;
    const entry = opts.entry;
    const name = if (entry) "main" else opts.name;
    const linkage: Mach.Data.Linkage = if (entry) .exported else .local;

    const slot = try utils.ensureSlot(&self.func_map, self.gpa, id);
    try self.out.startDefineSym(self.gpa, slot, name, .func, linkage);
    const sym = slot.*;
    defer self.out.endDefineSym(sym);

    //self.block_offsets = tmp.arena.alloc(i32, func.block_count);
    //self.local_relocs = .initBuffer(tmp.arena.alloc(BlockReloc, func.block_count * 2));

    var visited = std.DynamicBitSet.initEmpty(tmp.arena.allocator(), func.next_id) catch unreachable;
    const postorder = func.collectPostorder(tmp.arena.allocator(), &visited);

    self.allocs = Regalloc.ralloc(Node, func);
    self.ret_count = func.returns.len;
    self.local_relocs = .initBuffer(tmp.arena.alloc(Reloc, 128));
    self.block_offsets = tmp.arena.alloc(u32, postorder.len);

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

    const spill_slot_count = std.mem.max(u16, self.allocs) -| (@intFromEnum(Reg.r15) - 1);
    const stack_size: i64 = std.mem.alignForward(i64, local_size, 8) + spill_slot_count * 8; //used_reg_size + local_size + spill_count;
    self.local_base = spill_slot_count * 8;

    prelude: {
        for (Reg.system_v.callee_saved) |r| {
            if (r == .r15) {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_PUSH, .{Tmp{}});
            } else if (used_regs.contains(r)) {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_PUSH, .{r});
            }
        }

        if (stack_size != 0) {
            self.emitInstr(zydis.ZYDIS_MNEMONIC_SUB, .{ Reg.rsp, stack_size });
        }

        for (0..func.params.len) |i| {
            const argn = for (postorder[0].base.outputs()) |o| {
                if (o.kind == .Arg and o.extra(.Arg).* == i) break o;
            } else continue; // is dead
            if (self.getReg(argn) != Reg.system_v.args[i]) {
                self.emitInstr(
                    zydis.ZYDIS_MNEMONIC_MOV,
                    .{ self.getReg(argn), Reg.system_v.args[i] },
                );
            }
        }

        break :prelude;
    }

    for (postorder, 0..) |bb, i| {
        self.block_offsets[bb.base.schedule] = @intCast(self.out.code.items.len);
        std.debug.assert(bb.base.schedule == i);

        self.emitBlockBody(&bb.base);
        const last = bb.base.outputs()[bb.base.output_len - 1];
        if (last.outputs().len == 0) {
            std.debug.assert(last.kind == .Return);

            if (stack_size != 0) {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_ADD, .{
                    Reg.rsp,
                    stack_size,
                });
            }

            var iter = std.mem.reverseIterator(Reg.system_v.callee_saved);
            while (iter.next()) |r| {
                if (r == .r15) {
                    self.emitInstr(zydis.ZYDIS_MNEMONIC_POP, .{Tmp{}});
                } else if (used_regs.contains(r)) {
                    self.emitInstr(zydis.ZYDIS_MNEMONIC_POP, .{r});
                }
            }

            self.emitInstr(zydis.ZYDIS_MNEMONIC_RET, .{});
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
                .offset = @intCast(self.out.code.items.len),
                .off = 1,
                .class = .rel32,
            });
            try self.out.code.appendSlice(self.gpa, &.{ 0xE9, 0, 0, 0, 0 });
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
            self.out.code.items[rl.offset + rl.off ..][0..size],
            @as(*const [8]u8, @ptrCast(&jump))[0..size],
        );
    }
}

fn orderMoves(self: *X86_64, moves: []Move) void {
    utils.orderMoves(self, Reg, moves);
}

pub fn emitSwap(self: *X86_64, lhs: Reg, rhs: Reg) void {
    self.emitInstr(zydis.ZYDIS_MNEMONIC_XCHG, .{ lhs, rhs });
}

pub fn emitCp(self: *X86_64, dst: Reg, src: Reg) void {
    self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ dst, src });
}

pub const SReg = struct { Reg, usize };
pub const BRegOff = struct { Reg, u32, u16 };
pub const Tmp = struct {};

pub fn emitInstr(self: *X86_64, mnemonic: c_uint, args: anytype) void {
    errdefer unreachable;

    const fields = std.meta.fields(@TypeOf(args));

    var buf: [zydis.ZYDIS_MAX_INSTRUCTION_LENGTH]u8 = undefined;
    var len: usize = undefined;
    var req: zydis.ZydisEncoderRequest = undefined;

    req = .{
        .mnemonic = mnemonic,
        .machine_mode = zydis.ZYDIS_MACHINE_MODE_LONG_64,
        .operand_count = fields.len,
    };
    len = @sizeOf(@TypeOf(buf));

    inline for (fields, 0..) |f, i| {
        const val = @field(args, f.name);
        req.operands[i] = switch (f.type) {
            Reg => val.asZydisOp(8),
            Tmp => .{
                .type = zydis.ZYDIS_OPERAND_TYPE_REGISTER,
                .reg = .{ .value = zydis.ZYDIS_REGISTER_R15 },
            },
            SReg => val[0].asZydisOp(val[1]),
            BRegOff => b: {
                var base = val[0].asZydisOp(8);
                if (base.type != zydis.ZYDIS_OPERAND_TYPE_REGISTER) {
                    self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ Tmp{}, val[0] });
                    base = .{
                        .type = zydis.ZYDIS_OPERAND_TYPE_REGISTER,
                        .reg = .{ .value = zydis.ZYDIS_REGISTER_R15 },
                    };
                }
                std.debug.assert(base.reg.value != 0);
                break :b .{
                    .type = zydis.ZYDIS_OPERAND_TYPE_MEMORY,
                    .mem = .{
                        .base = base.reg.value,
                        .displacement = val[1],
                        .size = val[2],
                    },
                };
            },
            i64, i32 => .{
                .type = zydis.ZYDIS_OPERAND_TYPE_IMMEDIATE,
                .imm = .{ .s = val },
            },
            u64, u32 => .{
                .type = zydis.ZYDIS_OPERAND_TYPE_IMMEDIATE,
                .imm = .{ .u = val },
            },
            else => comptime unreachable,
        };
    }

    const status = zydis.ZydisEncoderEncodeInstruction(&req, &buf, &len);
    if (zydis.ZYAN_FAILED(status) != 0) {
        std.debug.print("{x}\n", .{status});
        unreachable;
    }

    try self.out.code.appendSlice(self.gpa, buf[0..len]);
}

pub fn emitBlockBody(self: *X86_64, block: *FuncNode) void {
    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    for (block.outputs()) |instr| {
        switch (instr.extra2()) {
            .CInt => |extra| {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ self.getReg(instr), extra.* });
            },
            .MemCpy => {
                var moves = std.ArrayList(Move).init(tmp.arena.allocator());
                for (instr.dataDeps(), 0..) |arg, i| {
                    const dst, const src: Reg = .{ Reg.system_v.args[i], self.getReg(arg) };
                    if (!std.meta.eql(dst, src)) moves.append(.{ dst, src, 0 }) catch unreachable;
                }
                self.orderMoves(moves.items);

                const opcode = 0xE8;
                try self.out.code.append(self.gpa, opcode);
                const slot = &self.memcpy;
                try self.out.importSym(self.gpa, slot, "memcpy", .func);
                try self.out.addReloc(self.gpa, slot, 4, -4);
                try self.out.code.appendSlice(self.gpa, &.{ 0, 0, 0, 0 });
            },
            .MachMove => {},
            .Phi => {},
            .GlobalAddr => {
                var buf: [zydis.ZYDIS_MAX_INSTRUCTION_LENGTH]u8 = undefined;
                var len: usize = undefined;
                var req: zydis.ZydisEncoderRequest = undefined;

                req = .{
                    .mnemonic = zydis.ZYDIS_MNEMONIC_LEA,
                    .machine_mode = zydis.ZYDIS_MACHINE_MODE_LONG_64,
                    .operand_count = 2,
                };
                len = @sizeOf(@TypeOf(buf));
                req.operands[0] = self.getReg(instr).asZydisOp(8);
                req.operands[1] = .{
                    .type = zydis.ZYDIS_OPERAND_TYPE_MEMORY,
                    .mem = .{
                        .base = zydis.ZYDIS_REGISTER_RIP,
                        .size = 8,
                    },
                };
                const status = zydis.ZydisEncoderEncodeInstruction(&req, &buf, &len);
                if (zydis.ZYAN_FAILED(status) != 0) {
                    std.debug.print("{x}\n", .{status});
                    unreachable;
                }
                try self.out.code.appendSlice(self.gpa, buf[0 .. len - 4]);

                const slot = try utils.ensureSlot(&self.global_map, self.gpa, instr.extra(.GlobalAddr).id);
                try self.out.addReloc(self.gpa, slot, 4, -4);

                try self.out.code.appendSlice(self.gpa, buf[len - 4 .. len]);
            },
            .Local => {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ self.getReg(instr), Reg.rsp });
                self.emitInstr(
                    zydis.ZYDIS_MNEMONIC_ADD,
                    .{ self.getReg(instr), instr.extra(.Local).* + self.local_base },
                );
            },
            .Load => {
                std.debug.assert(instr.data_type.size() == 8);

                const dst = self.getReg(instr);
                const bse = self.getReg(instr.inputs()[2]);

                const offset: u32 = 0;

                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{
                    dst,
                    BRegOff{ bse, offset, 8 },
                });
            },
            .Store => {
                std.debug.assert(instr.data_type.size() == 8);

                const dst = self.getReg(instr.inputs()[2]);
                const vl = self.getReg(instr.inputs()[3]);

                const offset: u32 = 0;

                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ BRegOff{ dst, offset, 8 }, vl });
            },
            .Call => {
                const call = instr.extra(.Call);

                var moves = std.ArrayList(Move).init(tmp.arena.allocator());
                for (instr.dataDeps(), 0..) |arg, i| {
                    const dst, const src: Reg = .{ Reg.system_v.args[i], self.getReg(arg) };
                    if (dst != src) moves.append(.{ dst, src, 0 }) catch unreachable;
                }
                self.orderMoves(moves.items);

                const opcode = 0xE8;
                try self.out.code.append(self.gpa, opcode);
                const slot = try utils.ensureSlot(&self.func_map, self.gpa, call.id);
                try self.out.addReloc(self.gpa, slot, 4, -4);
                try self.out.code.appendSlice(self.gpa, &.{ 0, 0, 0, 0 });

                const cend = for (instr.outputs()) |o| {
                    if (o.kind == .CallEnd) break o;
                } else unreachable;
                moves.items.len = 0;
                for (cend.outputs()) |r| {
                    if (r.kind == .Ret) {
                        const dst: Reg, const src = .{ self.getReg(r), Reg.rax };
                        if (dst != src) moves.append(.{ dst, src, 0 }) catch unreachable;
                    }
                }
                self.orderMoves(moves.items);
            },
            .Arg => {},
            .Ret => {},
            .Mem => {},
            .Never => {},
            .Trap => {
                switch (instr.extra(.Trap).code) {
                    graph.infinite_loop_trap => return,
                    0 => self.emitInstr(zydis.ZYDIS_MNEMONIC_UD2, .{}),
                    else => unreachable,
                }
            },
            .Return => {
                for (instr.dataDeps()[0..self.ret_count]) |inp| {
                    const src = self.getReg(inp);
                    if (src != .rax) self.emitInstr(
                        zydis.ZYDIS_MNEMONIC_MOV,
                        .{ Reg.rax, src },
                    );
                }

                continue;
            },
            .BinOp => {
                const op = instr.extra(.BinOp).*;
                const dst = self.getReg(instr);
                const lhs = self.getReg(instr.inputs()[1]);
                const rhs = self.getReg(instr.inputs()[2]);

                switch (op) {
                    .iadd, .isub, .imul => {
                        if (dst != lhs) {
                            self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ dst, lhs });
                        }
                    },
                    else => {},
                }

                const mnemonic: c_uint = switch (op) {
                    .iadd => zydis.ZYDIS_MNEMONIC_ADD,
                    .isub => zydis.ZYDIS_MNEMONIC_SUB,
                    .imul => zydis.ZYDIS_MNEMONIC_IMUL,

                    .eq => zydis.ZYDIS_MNEMONIC_SETZ,
                    .ne => zydis.ZYDIS_MNEMONIC_SETNZ,

                    .ult => zydis.ZYDIS_MNEMONIC_SETB,
                    .ule => zydis.ZYDIS_MNEMONIC_SETBE,
                    .ugt => zydis.ZYDIS_MNEMONIC_SETNBE,
                    .uge => zydis.ZYDIS_MNEMONIC_SETNB,

                    .slt => zydis.ZYDIS_MNEMONIC_SETL,
                    .sle => zydis.ZYDIS_MNEMONIC_SETLE,
                    .sgt => zydis.ZYDIS_MNEMONIC_SETNLE,
                    .sge => zydis.ZYDIS_MNEMONIC_SETNL,

                    else => unreachable,
                };

                switch (op) {
                    .iadd, .isub, .imul => {
                        self.emitInstr(mnemonic, .{ dst, rhs });
                    },
                    .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt, .slt => {
                        self.emitInstr(zydis.ZYDIS_MNEMONIC_CMP, .{ lhs, rhs });
                        self.emitInstr(mnemonic, .{SReg{ dst, 1 }});
                        self.emitInstr(zydis.ZYDIS_MNEMONIC_MOVZX, .{ dst, SReg{ dst, 1 } });
                    },
                    else => unreachable,
                }
            },
            .If => {
                const cond = self.getReg(instr.inputs()[1]);
                self.emitInstr(zydis.ZYDIS_MNEMONIC_TEST, .{ cond, cond });
                self.local_relocs.appendAssumeCapacity(.{
                    .dest = instr.outputs()[1].schedule,
                    .offset = @intCast(self.out.code.items.len),
                    .class = .rel32,
                    .off = 2,
                });
                // je 0
                try self.out.code.appendSlice(self.gpa, &.{ 0x0F, 0x84, 0, 0, 0, 0 });
            },
            .Jmp => if (instr.outputs()[0].kind == .Region or instr.outputs()[0].kind == .Loop) {
                const idx = std.mem.indexOfScalar(?*Func.Node, instr.outputs()[0].inputs(), instr).? + 1;

                var moves = std.ArrayList(Move).init(tmp.arena.allocator());
                for (instr.outputs()[0].outputs()) |o| {
                    if (o.isDataPhi()) {
                        std.debug.assert(o.inputs()[idx].?.kind == .MachMove);
                        const dst, const src = .{ self.getReg(o), self.getReg(o.inputs()[idx].?.inputs()[1]) };
                        if (dst != src) try moves.append(.{ dst, src, 0 });
                    }
                }

                self.orderMoves(moves.items);
            },
            .UnOp => {
                const op = instr.extra(.UnOp).*;
                const dst = self.getReg(instr);
                const src = self.getReg(instr.inputs()[1]);

                switch (op) {
                    .sext, .uext => {
                        if (dst != src) self.emitInstr(
                            zydis.ZYDIS_MNEMONIC_MOV,
                            .{ dst, src },
                        );
                    },
                    else => {
                        std.debug.panic("{any}", .{instr});
                    },
                }
            },
            else => {
                std.debug.panic("{any}", .{instr});
            },
        }
    }
}

pub fn emitData(self: *X86_64, opts: Mach.DataOptions) void {
    errdefer unreachable;

    const slot = try utils.ensureSlot(&self.global_map, self.gpa, opts.id);
    try self.out.startDefineSym(self.gpa, slot, opts.name, .data, .local);
    defer self.out.endDefineSym(slot.*);

    try self.out.code.appendSlice(self.gpa, opts.value.init);
}

pub fn finalize(self: *X86_64, out: std.io.AnyWriter) void {
    errdefer unreachable;

    try switch (self.object_format) {
        .elf => root.object.elf.flush(self.out, .x86_64, out),
        .coff => unreachable, //root.object.coff.flush(self.out, .x86_64, out),
    };

    self.func_map.items.len = 0;
    self.global_map.items.len = 0;
    self.memcpy = .invalid;
    self.out.reset();
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
    var dump = std.process.Child.init(&.{ "objdump", "-d", "-M", "intel", "-S", name }, tmp.arena.allocator());
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
    const cleanup = true;
    const res = b: {
        errdefer unreachable;

        var tmp = root.utils.Arena.scrath(null);
        defer tmp.deinit();

        const name = try std.fmt.allocPrint(tmp.arena.allocator(), "tmp_{s}.o", .{env.name});
        const exe_name = try std.fmt.allocPrint(tmp.arena.allocator(), "./tmp_{s}", .{env.name});

        try std.fs.cwd().writeFile(.{ .sub_path = name, .data = env.code });
        defer if (cleanup) std.fs.cwd().deleteFile(name) catch unreachable;

        var compile = std.process.Child.init(
            &.{ "gcc", name, "-o", exe_name },
            tmp.arena.allocator(),
        );
        _ = try compile.spawnAndWait();
        defer if (cleanup) std.fs.cwd().deleteFile(exe_name) catch unreachable;

        var run_exe = std.process.Child.init(
            &.{exe_name},
            tmp.arena.allocator(),
        );
        break :b try run_exe.spawnAndWait();
    };

    if (res != .Exited) {
        if (res.Signal == 4) {
            return error.Unreachable;
        } else if (res.Signal == 11) {
            return error.Fucked;
        } else std.debug.panic("{}\n", .{res});
    }
    return res.Exited;
}

pub fn deinit(self: *X86_64) void {
    self.global_map.deinit(self.gpa);
    self.func_map.deinit(self.gpa);
    self.out.deinit(self.gpa);
}
