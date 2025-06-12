const std = @import("std");

const root = @import("hb");
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Regalloc = root.backend.Regalloc;
const utils = root.utils;
const object = root.object;
const zydis = @import("zydis").exports;

const X86_64 = @This();
const Func = graph.Func(Node);
const FuncNode = Func.Node;
const Move = utils.Move(Reg);

gpa: std.mem.Allocator,
object_format: enum { elf, coff },
memcpy: Mach.Data.SymIdx = .invalid,
out: Mach.Data = .{},
allocs: []u16 = undefined,
ret_count: usize = undefined,
local_relocs: std.ArrayListUnmanaged(Reloc) = undefined,
block_offsets: []u32 = undefined,
local_base: u32 = undefined,

const tmp_count = 2;

const syscall = std.math.maxInt(u32);

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
    xmm0,
    xmm1,
    xmm2,
    xmm3,
    xmm4,
    xmm5,
    xmm6,
    xmm7,
    xmm8,
    xmm9,
    xmm10,
    xmm11,
    xmm12,
    xmm13,
    xmm14,
    xmm15,
    _, // spills

    const system_v = struct {
        const syscall_args: []const Reg = &.{ .rax, .rdi, .rsi, .rdx, .r10, .r8, .r9 };
        const args: []const Reg = &.{ .rdi, .rsi, .rdx, .rcx, .r8, .r9 };
        const caller_saved: []const Reg = &.{ .rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11 };
        const callee_saved: []const Reg = &.{ .rbx, .rbp, .r12, .r13, .r14, .r15 };
    };

    // stack slots are separate so that register allocator knows they dont interfere
    //
    pub const set_cap = 128;
    pub const stack_per_mask = (set_cap - (@intFromEnum(Reg.xmm15) + 3)) / 2;

    pub fn floatMask(tmp: *utils.Arena) std.DynamicBitSetUnmanaged {
        var set = std.DynamicBitSetUnmanaged.initFull(tmp.allocator(), set_cap) catch unreachable;
        set.setRangeValue(.{ .start = @intFromEnum(Reg.rax), .end = @intFromEnum(Reg.r15) + 2 }, false);
        set.setRangeValue(.{
            .start = @intFromEnum(Reg.xmm15) + 1,
            .end = @intFromEnum(Reg.xmm15) + 2 + stack_per_mask,
        }, false);
        return set;
    }

    // TODO: fix the explodiated stack frames due to slipped spill slots
    //
    pub fn intMask(tmp: *utils.Arena) std.DynamicBitSetUnmanaged {
        var set = std.DynamicBitSetUnmanaged.initFull(tmp.allocator(), set_cap) catch unreachable;
        set.unset(0);
        set.unset(@intFromEnum(Reg.rsp) + 1);
        set.setRangeValue(.{
            .start = @intFromEnum(Reg.xmm0) + 1,
            .end = @intFromEnum(Reg.xmm15) + 2,
        }, false);
        set.setRangeValue(.{
            .start = @intFromEnum(Reg.xmm15) + 2 + stack_per_mask,
            .end = set_cap,
        }, false);
        return set;
    }

    pub fn asZydisOpReg(self: Reg, size: usize) zydis.ZydisEncoderOperand {
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
    }

    pub fn asZydisOp(self: Reg, size: usize) zydis.ZydisEncoderOperand {
        if (@intFromEnum(self) < @intFromEnum(Reg.r14)) {
            return self.asZydisOpReg(size);
        } else {
            return .{
                .type = zydis.ZYDIS_OPERAND_TYPE_MEMORY,
                .mem = .{
                    .base = zydis.ZYDIS_REGISTER_RSP,
                    .size = @intCast(size),
                    .displacement = @as(
                        c_int,
                        @intFromEnum(self) - @intFromEnum(Reg.r14),
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
    OffsetLoad: extern struct {
        base: graph.Load = .{},
        dis: i32,
    },
    OffsetStore: extern struct {
        base: graph.Store = .{},
        dis: i32,
    },
    ImmOp: extern struct {
        base: graph.BinOp,
        imm: i64,
    },
    InPlaceImmOp: extern struct {
        base: graph.MemCpy = .{},
        op: graph.BinOp,
        dis: i32,
        imm: i64,
    },

    pub const is_basic_block_start: []const Func.Kind = &.{};
    pub const is_mem_op: []const Func.Kind = &.{ .OffsetLoad, .OffsetStore, .InPlaceImmOp };
    pub const is_basic_block_end: []const Func.Kind = &.{};
    pub const is_pinned: []const Func.Kind = &.{};
    pub const reg_count = 32;

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
            .BinOp => switch (node.extra(.BinOp).*) {
                .udiv, .sdiv, .umod, .smod => {
                    var base = @as(u64, 1) << @intFromEnum(Reg.rax);
                    if (node.data_type.size() != 1) {
                        base |= @as(u64, 1) << @intFromEnum(Reg.rdx);
                    }
                    return base;
                },
                .ishl, .ushr, .sshr => @as(u64, 1) << @intFromEnum(Reg.rcx),
                else => 0,
            },
            else => 0,
        };
    }

    pub fn idealize(_: void, func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
        _ = func;
        _ = node;
        _ = worklist;
        return null;
    }

    pub fn regBias(node: *Func.Node) ?u16 {
        return @intFromEnum(switch (node.kind) {
            .Arg => Reg.system_v.args[node.extraConst(.Arg).*],
            else => b: {
                for (node.outputs()) |o| {
                    if (o.kind == .Call) {
                        const idx = std.mem.indexOfScalar(?*Func.Node, o.dataDeps(), node) orelse continue;
                        break :b Reg.system_v.args[idx];
                    }

                    if (o.kind == .Phi and o.inputs()[0].?.kind != .Loop) {
                        return o.regBias();
                    }
                }

                if (node.isSub(graph.BinOp)) {
                    return node.inputs()[1].?.regBias();
                }

                return null;
            },
        });
    }

    pub fn knownOffset(node: *Func.Node) struct { *Func.Node, i64 } {
        return switch (node.extra2()) {
            .ImmOp => |extra| {
                std.debug.assert(extra.base == .iadd or extra.base == .isub);
                return .{ node.inputs()[1].?, if (extra.base == .iadd)
                    extra.imm
                else
                    -extra.imm };
            },
            else => .{ node, 0 },
        };
    }

    pub fn idealizeMach(self: *X86_64, func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
        //if (node.kind == .OffsetStore and node.value().isSub(graph.BinOp) and
        //    node.value().inputs()[1].?.isSub(graph.Load) and
        //    node.value().inputs()[1].?.getStaticOffset() == 0 and
        //    node.value().outputs().len == 1 and
        //    node.value().inputs()[1].?.base() == node.base())
        //{
        //    if (node.value().kind == .ImmOp and switch (node.value().extra(.ImmOp).base) {
        //        .ushr, .ishl, .sshr, .iadd, .isub, .bor, .band, .bxor => true,
        //        else => false,
        //    }) {
        //        worklist.add(node.value());

        //        return func.addNode(
        //            .InPlaceImmOp,
        //            node.data_type,
        //            &.{ node.inputs()[0], node.mem(), node.base() },
        //            .{
        //                .op = node.value().extra(.ImmOp).base,
        //                .dis = node.extra(.OffsetStore).dis,
        //                .imm = node.value().extra(.ImmOp).imm,
        //            },
        //        );
        //    }
        //}

        if (node.kind == .Load) {
            const base, const offset = node.base().knownOffset();
            const res = func.addNode(
                .OffsetLoad,
                node.data_type,
                &.{ node.inputs()[0], node.mem(), base },
                .{ .dis = @intCast(offset) },
            );
            worklist.add(res);
            return res;
        }

        if (node.kind == .Store) {
            const base, const offset = node.base().knownOffset();
            const res = func.addNode(
                .OffsetStore,
                node.data_type,
                &.{ node.inputs()[0], node.mem(), base, node.value() },
                .{ .dis = @intCast(offset) },
            );
            worklist.add(res);
            return res;
        }

        if (node.kind == .OffsetLoad) {
            if (node.base().kind == .GlobalAddr) fold_const_read: {
                const value = self.out.readFromSym(
                    node.base().extra(.GlobalAddr).id,
                    node.extra(.OffsetLoad).dis,
                    node.data_type.size(),
                ) orelse break :fold_const_read;

                return func.addNode(.CInt, node.data_type, &.{null}, value);
            }
        }

        if (node.kind == .BinOp and node.inputs()[1].?.kind == .CInt and node.inputs()[2].?.kind == .CInt) {
            return func.addNode(
                .CInt,
                node.data_type,
                &.{null},
                node.extra(.BinOp).*.eval(
                    node.data_type,
                    node.inputs()[1].?.extra(.CInt).*,
                    node.inputs()[2].?.extra(.CInt).*,
                ),
            );
        }

        if (node.kind == .BinOp and node.inputs()[2].?.kind == .CInt and
            switch (node.extra(.BinOp).*) {
                .udiv, .sdiv, .umod, .smod, .imul => false,
                .band, .bor, .bxor => node.inputs()[2].?.data_type.size() > 1,
                .eq,
                .ne,
                .uge,
                .ule,
                .ugt,
                .ult,
                .sge,
                .sle,
                .sgt,
                .slt,
                => node.inputs()[2].?.data_type.size() > 2,
                else => true,
            })
        {
            if (std.math.cast(i32, node.inputs()[2].?.extra(.CInt).*) != null) {
                return func.addNode(.ImmOp, node.data_type, node.inputs()[0..2], .{
                    .base = node.extra(.BinOp).*,
                    .imm = node.inputs()[2].?.extra(.CInt).*,
                });
            }
        }

        return null;
    }

    pub fn allowedRegsFor(
        node: *Func.Node,
        ids: usize,
        tmp: *utils.Arena,
    ) ?std.DynamicBitSetUnmanaged {
        _ = node;
        _ = ids;

        return Reg.intMask(tmp);
    }

    pub fn getStaticOffset(node: *Func.Node) i64 {
        return switch (node.kind) {
            .OffsetLoad => node.extra(.OffsetLoad).dis,
            .OffsetStore => node.extra(.OffsetStore).dis,
            else => 0,
        };
    }
};

pub fn getReg(self: X86_64, node: ?*FuncNode) Reg {
    return @enumFromInt(self.allocs[node.?.schedule]);
}

pub fn emitFunc(self: *X86_64, func: *Func, opts: Mach.EmitOptions) void {
    errdefer unreachable;

    const id = opts.id;
    const entry = opts.entry;
    const name = if (entry) "main" else opts.name;
    const linkage: Mach.Data.Linkage = if (entry) .exported else opts.linkage;

    try self.out.startDefineFunc(self.gpa, id, name, .func, linkage);
    defer self.out.endDefineFunc(id);

    if (opts.linkage == .imported) return;

    opts.optimizations.execute(Node, self, func);

    var tmp = utils.Arena.scrath(opts.optimizations.arena);
    defer tmp.deinit();

    var visited = std.DynamicBitSet.initEmpty(tmp.arena.allocator(), func.next_id) catch unreachable;
    const postorder = func.collectPostorder(tmp.arena.allocator(), &visited);

    self.allocs = Regalloc.ralloc(Node, func);
    self.ret_count = func.returns.len;
    self.local_relocs = .initBuffer(tmp.arena.alloc(Reloc, 1024 * 10));
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
        var locals = std.ArrayListUnmanaged(*FuncNode).empty;

        std.debug.assert(func.root.outputs()[1].kind == .Mem);
        for (func.root.outputs()[1].outputs()) |o| if (o.kind == .Local) {
            try locals.append(tmp.arena.allocator(), o);
        };

        std.sort.pdq(*FuncNode, locals.items, {}, struct {
            fn isBigger(_: void, lhs: *FuncNode, rhs: *FuncNode) bool {
                return lhs.extra(.Local).* > rhs.extra(.Local).*;
            }
        }.isBigger);

        std.debug.assert(func.root.outputs()[1].kind == .Mem);
        for (locals.items) |o| {
            const extra = o.extra(.Local);
            const size = extra.*;
            extra.* = @bitCast(local_size);
            local_size += @intCast(size);
        }
    }

    const spill_slot_count = if (self.allocs.len == 0) 0 else std.mem.max(u16, self.allocs) -| (@intFromEnum(Reg.r15) - tmp_count);
    var stack_size: i64 = std.mem.alignForward(i64, local_size, 8) + spill_slot_count * 8;

    const padding = std.mem.alignForward(i64, stack_size, 16) - stack_size;

    const has_call = for (postorder) |bb| {
        if (bb.base.kind == .CallEnd) break true;
    } else false;

    if (has_call and padding >= 8) {
        stack_size += padding - 8;
    } else if (has_call) {
        stack_size += padding + 8;
    } else {
        stack_size += padding;
    }

    self.local_base = spill_slot_count * 8;

    prelude: {
        for (Reg.system_v.callee_saved) |r| {
            if (@intFromEnum(r) > @intFromEnum(Reg.r15) - tmp_count and spill_slot_count > 0) {
                const tp = Tmp{@intFromEnum(r) - (@intFromEnum(Reg.r15) - tmp_count + 1)};
                self.emitInstr(zydis.ZYDIS_MNEMONIC_PUSH, .{tp});
            } else if (used_regs.contains(r)) {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_PUSH, .{r});
            }
        }

        if (stack_size != 0) {
            self.emitInstr(zydis.ZYDIS_MNEMONIC_SUB, .{ Reg.rsp, stack_size });
        }

        var moves = std.ArrayList(Move).init(tmp.arena.allocator());
        for (0..func.params.len) |i| {
            const argn = for (postorder[0].base.outputs()) |o| {
                if (o.kind == .Arg and o.extra(.Arg).* == i) break o;
            } else continue; // is dead
            if (self.getReg(argn) != Reg.system_v.args[i]) {
                moves.append(.{ self.getReg(argn), Reg.system_v.args[i], 0 }) catch unreachable;
            }
        }
        self.orderMoves(moves.items);

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
                if (@intFromEnum(r) > @intFromEnum(Reg.r15) - tmp_count and
                    spill_slot_count > 0)
                {
                    const tp = Tmp{@intFromEnum(r) - (@intFromEnum(Reg.r15) - tmp_count + 1)};
                    self.emitInstr(zydis.ZYDIS_MNEMONIC_POP, .{tp});
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
pub const BRegOff = struct { Reg, i32, u16 };
pub const Tmp = struct { u8 };
pub const SizeHint = struct { bytes: u64 };

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

    var tmp_allocs: u8 = tmp_count;

    var size: ?usize = null;
    inline for (fields) |f| {
        const val = @field(args, f.name);
        const op_size: ?usize = switch (f.type) {
            Reg => 8,
            SReg => val[1],
            BRegOff => val[2],
            SizeHint => val.bytes,
            zydis.ZydisEncoderOperand => b: {
                const t = val.mem.size;
                break :b t;
            },
            else => null,
        };

        size = size orelse op_size;
    }

    if (fields.len == 0) size = 0;
    if (mnemonic == zydis.ZYDIS_MNEMONIC_PUSH or
        mnemonic == zydis.ZYDIS_MNEMONIC_POP) size = 8;

    const fsize = size.?;

    inline for (fields, 0..) |f, i| {
        const val = @field(args, f.name);

        req.operands[i] = switch (f.type) {
            Reg => val.asZydisOp(fsize),
            Tmp => @as(Reg, @enumFromInt(@intFromEnum(Reg.r14) + val[0])).asZydisOpReg(fsize),
            SReg => val[0].asZydisOp(val[1]),
            BRegOff => b: {
                var base = val[0].asZydisOp(8);
                if (base.type != zydis.ZYDIS_OPERAND_TYPE_REGISTER) {
                    tmp_allocs -= 1;
                    self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ Tmp{tmp_allocs}, val[0] });
                    base = .{
                        .type = zydis.ZYDIS_OPERAND_TYPE_REGISTER,
                        .reg = .{ .value = @intCast(zydis.ZYDIS_REGISTER_R14 + tmp_allocs) },
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
            comptime_int, i64, i32 => .{
                .type = zydis.ZYDIS_OPERAND_TYPE_IMMEDIATE,
                .imm = .{ .s = val },
            },
            u64, u32 => .{
                .type = zydis.ZYDIS_OPERAND_TYPE_IMMEDIATE,
                .imm = .{ .u = val },
            },
            zydis.ZydisEncoderOperand => val,
            SizeHint => {
                req.operand_count -= 1;
                req.operand_size_hint = @intCast(zydis.ZYDIS_OPERAND_SIZE_HINT_8 + val.bytes);
                continue;
            },
            else => comptime unreachable,
        };
    }

    if (mnemonic == zydis.ZYDIS_MNEMONIC_XCHG and
        req.operands[1].type == zydis.ZYDIS_OPERAND_TYPE_MEMORY)
    {
        std.mem.swap(@TypeOf(req.operands[1]), &req.operands[0], &req.operands[1]);
    }

    const should_flush_to_mem =
        (mnemonic == zydis.ZYDIS_MNEMONIC_MOVZX or
            mnemonic == zydis.ZYDIS_MNEMONIC_MOVSX or
            mnemonic == zydis.ZYDIS_MNEMONIC_IMUL or
            (req.operands[1].type == zydis.ZYDIS_OPERAND_TYPE_IMMEDIATE and
                (mnemonic == zydis.ZYDIS_MNEMONIC_MOV and
                    req.operands[1].imm.u > 0x7fffffff)) or
            mnemonic == zydis.ZYDIS_MNEMONIC_LEA) and
        req.operands[0].type == zydis.ZYDIS_OPERAND_TYPE_MEMORY;
    var prev_oper: zydis.ZydisEncoderOperand = undefined;
    if (should_flush_to_mem) {
        prev_oper = req.operands[0];
        if (mnemonic != zydis.ZYDIS_MNEMONIC_MOVZX and
            mnemonic != zydis.ZYDIS_MNEMONIC_LEA and
            mnemonic != zydis.ZYDIS_MNEMONIC_MOV)
        {
            self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ Tmp{1}, prev_oper });
        }
        req.operands[0] = Reg.r15.asZydisOpReg(req.operands[0].mem.size);
    } else if (fields.len == 2 and
        req.operands[0].type == zydis.ZYDIS_OPERAND_TYPE_MEMORY and
        req.operands[1].type == zydis.ZYDIS_OPERAND_TYPE_MEMORY)
    {
        if (mnemonic == zydis.ZYDIS_MNEMONIC_XCHG) {
            self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ Tmp{0}, req.operands[1] });
            self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ Tmp{1}, req.operands[0] });
            self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ req.operands[0], Tmp{0} });
            self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ req.operands[1], Tmp{1} });
            return;
        }

        self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ Tmp{tmp_allocs -| 1}, req.operands[1] });
        req.operands[1] = @as(Reg, @enumFromInt(@intFromEnum(Reg.r14) + (tmp_allocs -| 1))).asZydisOpReg(req.operands[1].mem.size);
    }

    const status = zydis.ZydisEncoderEncodeInstruction(&req, &buf, &len);
    if (zydis.ZYAN_FAILED(status) != 0) {
        std.debug.print("{x} {s} {} {any}\n", .{ status, zydis.ZydisMnemonicGetString(mnemonic), args, req.operands[0..fields.len] });
        unreachable;
    }

    try self.out.code.appendSlice(self.gpa, buf[0..len]);

    if (should_flush_to_mem) {
        self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ prev_oper, Tmp{1} });
    }
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
                const spilled = req.operands[0].type != zydis.ZYDIS_OPERAND_TYPE_REGISTER;
                if (spilled) {
                    req.operands[0] = .{
                        .type = zydis.ZYDIS_OPERAND_TYPE_REGISTER,
                        .reg = .{ .value = zydis.ZYDIS_REGISTER_R15 },
                    };
                }
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

                try self.out.addGlobalReloc(self.gpa, instr.extra(.GlobalAddr).id, 4, -4);

                try self.out.code.appendSlice(self.gpa, buf[len - 4 .. len]);

                if (spilled) {
                    self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ self.getReg(instr), Tmp{1} });
                }
            },
            .Local => {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_LEA, .{
                    self.getReg(instr),
                    BRegOff{ .rsp, @intCast(instr.extra(.Local).* + self.local_base), 8 },
                });
            },
            .OffsetLoad => |extra| {
                const dst = self.getReg(instr);
                const bse = self.getReg(instr.inputs()[2]);

                const offset: i32 = extra.dis;

                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{
                    SReg{ dst, instr.data_type.size() },
                    BRegOff{ bse, offset, @intCast(instr.data_type.size()) },
                });
            },
            .OffsetStore => |extra| {
                const dst = self.getReg(instr.inputs()[2]);
                const vl = self.getReg(instr.inputs()[3]);

                const offset: i32 = extra.dis;

                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{
                    BRegOff{ dst, offset, @intCast(instr.data_type.size()) },
                    SReg{ vl, instr.data_type.size() },
                });
            },
            .Call => |extra| {
                const call = instr.extra(.Call);

                const call_conv = if (extra.id == syscall)
                    Reg.system_v.syscall_args
                else
                    Reg.system_v.args;

                var moves = std.ArrayList(Move).init(tmp.arena.allocator());
                for (instr.dataDeps(), 0..) |arg, i| {
                    const dst, const src: Reg = .{ call_conv[i], self.getReg(arg) };
                    if (dst != src) moves.append(.{ dst, src, 0 }) catch unreachable;
                }
                self.orderMoves(moves.items);

                if (extra.id == syscall) {
                    self.emitInstr(zydis.ZYDIS_MNEMONIC_SYSCALL, .{});
                } else {
                    const opcode = 0xE8;
                    try self.out.code.append(self.gpa, opcode);
                    try self.out.addFuncReloc(self.gpa, call.id, 4, -4);
                    try self.out.code.appendSlice(self.gpa, &.{ 0, 0, 0, 0 });
                }

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
            .InPlaceImmOp => |extra| {
                const op = extra.op;
                const size = instr.data_type.size();
                const dis = extra.dis;
                const lhs = self.getReg(instr.inputs()[2]);
                const rhs = extra.imm;

                const mnemonic = binopToMnemonic(op);

                switch (op) {
                    .imul => unreachable,
                    .ushr, .ishl, .sshr, .iadd, .isub, .bor, .band, .bxor => {
                        self.emitInstr(mnemonic, .{ BRegOff{ lhs, dis, @intCast(size) }, rhs });
                    },
                    .udiv, .sdiv, .smod, .umod => unreachable,
                    .fadd, .fsub, .fmul, .fdiv, .fgt, .flt, .fge, .fle => unreachable,
                    .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt, .slt => unreachable,
                }
            },
            .ImmOp => |extra| {
                const op = extra.base;
                const size = instr.data_type.size();
                const opsize = instr.inputs()[1].?.data_type.size();
                const dst = self.getReg(instr);
                const lhs = self.getReg(instr.inputs()[1]);
                const rhs = extra.imm;

                const mnemonic = binopToMnemonic(op);

                switch (op) {
                    .imul => unreachable,
                    .ushr, .ishl, .sshr, .iadd, .isub, .bor, .band, .bxor => {
                        if (dst != lhs) {
                            self.emitInstr(
                                zydis.ZYDIS_MNEMONIC_MOV,
                                .{ SReg{ dst, size }, SReg{ lhs, size } },
                            );
                        }
                        self.emitInstr(mnemonic, .{ SReg{ dst, size }, rhs });
                    },
                    .udiv, .sdiv, .smod, .umod => switch (size) {
                        1, 2, 4, 8 => {
                            if (size == 1) {
                                self.emitInstr(
                                    zydis.ZYDIS_MNEMONIC_MOVZX,
                                    .{ Reg.rdx, SReg{ .rdx, 1 } },
                                );
                            } else {
                                self.emitInstr(zydis.ZYDIS_MNEMONIC_XOR, .{ Reg.rdx, Reg.rdx });
                            }

                            self.emitInstr(mnemonic, .{ rhs, SizeHint{ .bytes = size } });

                            const dest_reg: Reg = if (op == .udiv or op == .sdiv) .rax else .rdx;

                            if (dst != dest_reg) self.emitInstr(
                                zydis.ZYDIS_MNEMONIC_MOV,
                                .{ SReg{ dst, size }, SReg{ dest_reg, size } },
                            );
                        },
                        else => unreachable,
                    },
                    .fadd, .fsub, .fmul, .fdiv, .fgt, .flt, .fge, .fle => unreachable,
                    .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt, .slt => {
                        self.emitInstr(zydis.ZYDIS_MNEMONIC_CMP, .{ SReg{ lhs, opsize }, rhs });
                        self.emitInstr(mnemonic, .{SReg{ dst, 1 }});
                        self.emitInstr(zydis.ZYDIS_MNEMONIC_MOVZX, .{ dst, SReg{ dst, 1 } });
                    },
                }
            },
            .BinOp => |extra| {
                const op = extra.*;
                const size = instr.data_type.size();
                const opsize = instr.inputs()[1].?.data_type.size();
                const dst = self.getReg(instr);
                const lhs = self.getReg(instr.inputs()[1]);
                const rhs = self.getReg(instr.inputs()[2]);

                switch (op) {
                    .iadd, .isub, .imul, .bor, .band, .bxor, .ushr, .ishl, .sshr => {
                        if (dst != lhs) {
                            self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ dst, lhs });
                        }
                    },
                    else => {},
                }

                const mnemonic = binopToMnemonic(op);

                switch (op) {
                    .ushr, .ishl, .sshr => {
                        var oper = dst;
                        if (dst == .rcx and rhs != .rcx) {
                            self.emitInstr(zydis.ZYDIS_MNEMONIC_XCHG, .{ SReg{ dst, size }, rhs });
                            oper = rhs;
                        } else if (rhs != .rcx) self.emitInstr(
                            zydis.ZYDIS_MNEMONIC_MOV,
                            .{ SReg{ Reg.rcx, size }, SReg{ rhs, size } },
                        );
                        self.emitInstr(mnemonic, .{ oper, SReg{ .rcx, 1 } });
                        if (dst == .rcx and rhs != .rcx) {
                            self.emitInstr(zydis.ZYDIS_MNEMONIC_XCHG, .{ SReg{ dst, size }, rhs });
                        }
                    },
                    .iadd, .isub, .imul, .bor, .band, .bxor => {
                        self.emitInstr(mnemonic, .{ dst, rhs });
                    },
                    .udiv, .sdiv, .smod, .umod => switch (size) {
                        1, 2, 4, 8 => {
                            // this is kind of fucked but eh,
                            // we need a better support from the regalloc
                            var oper = rhs;
                            if (rhs == .rax and lhs != .rax) {
                                self.emitInstr(zydis.ZYDIS_MNEMONIC_XCHG, .{ SReg{ rhs, size }, lhs });
                                oper = lhs;
                            } else if (lhs != .rax) self.emitInstr(
                                zydis.ZYDIS_MNEMONIC_MOV,
                                .{ SReg{ Reg.rax, size }, SReg{ lhs, size } },
                            );

                            if (size == 1) {
                                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOVZX, .{ Reg.rax, SReg{ .rax, 1 } });
                            } else {
                                std.debug.assert(oper != .rdx);
                                self.emitInstr(zydis.ZYDIS_MNEMONIC_XOR, .{ SReg{ Reg.rdx, size }, Reg.rdx });
                            }
                            std.debug.assert(oper != .rdx);
                            self.emitInstr(mnemonic, .{SReg{ oper, size }});

                            const dest_reg: Reg = if (op == .udiv or op == .sdiv) .rax else .rdx;
                            if (size == 1 and dest_reg == .rdx) {
                                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ SReg{ dst, 1 }, zydis.ZydisEncoderOperand{
                                    .type = zydis.ZYDIS_OPERAND_TYPE_REGISTER,
                                    .reg = .{ .value = zydis.ZYDIS_REGISTER_AH },
                                } });
                            } else {
                                if (dst != dest_reg) self.emitInstr(
                                    zydis.ZYDIS_MNEMONIC_MOV,
                                    .{ SReg{ dst, size }, SReg{ dest_reg, size } },
                                );
                            }

                            if (rhs == .rax and lhs != .rax) {
                                self.emitInstr(zydis.ZYDIS_MNEMONIC_XCHG, .{ SReg{ rhs, size }, lhs });
                            }
                        },
                        else => unreachable,
                    },
                    .fadd, .fsub, .fmul, .fdiv, .fgt, .flt, .fge, .fle => unreachable,
                    .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt, .slt => {
                        self.emitInstr(zydis.ZYDIS_MNEMONIC_CMP, .{ SReg{ lhs, opsize }, SReg{ rhs, opsize } });
                        self.emitInstr(mnemonic, .{SReg{ dst, 1 }});
                        self.emitInstr(zydis.ZYDIS_MNEMONIC_MOVZX, .{ dst, SReg{ dst, 1 } });
                    },
                }
            },
            .If => {
                const cond = self.getReg(instr.inputs()[1]);
                self.emitInstr(zydis.ZYDIS_MNEMONIC_TEST, .{ SReg{ cond, 1 }, SReg{ cond, 1 } });
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
                const size = instr.data_type.size();
                const dst = self.getReg(instr);
                const src_size = instr.inputs()[1].?.data_type.size();
                const src = self.getReg(instr.inputs()[1]);

                if (dst != src) {
                    self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ SReg{ dst, size }, src });
                }

                switch (op) {
                    .ired => {},
                    .sext => switch (src_size) {
                        1, 2 => self.emitInstr(
                            zydis.ZYDIS_MNEMONIC_MOVSX,
                            .{ SReg{ dst, size }, SReg{ dst, src_size } },
                        ),
                        4 => self.emitInstr(
                            zydis.ZYDIS_MNEMONIC_MOVSXD,
                            .{ SReg{ dst, size }, SReg{ dst, src_size } },
                        ),
                        else => unreachable,
                    },
                    .uext => if (instr.inputs()[1].?.data_type.size() == 1) {
                        self.emitInstr(
                            zydis.ZYDIS_MNEMONIC_MOVZX,
                            .{ SReg{ dst, size }, SReg{ dst, 1 } },
                        );
                    } else {
                        self.emitInstr(
                            zydis.ZYDIS_MNEMONIC_MOV,
                            .{ SReg{ dst, instr.inputs()[1].?.data_type.size() }, dst },
                        );
                    },
                    .not => {
                        self.emitInstr(zydis.ZYDIS_MNEMONIC_XOR, .{ SReg{ dst, size }, 1 });
                    },
                    .bnot => {
                        self.emitInstr(zydis.ZYDIS_MNEMONIC_NOT, .{SReg{ dst, size }});
                    },
                    .ineg => {
                        self.emitInstr(zydis.ZYDIS_MNEMONIC_NEG, .{SReg{ dst, size }});
                    },
                    .itf32,
                    .itf64,
                    .fti,
                    .fcst,
                    .cast,
                    .fneg,
                    => std.debug.panic("floating point ops are postponed: {any}", .{instr}),
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

    try self.out.defineGlobal(
        self.gpa,
        opts.id,
        opts.name,
        .data,
        .local,
        opts.value.init,
        opts.readonly,
    );
}

pub fn finalize(self: *X86_64, out: std.io.AnyWriter) void {
    errdefer unreachable;

    try switch (self.object_format) {
        .elf => root.object.elf.flush(self.out, .x86_64, out),
        .coff => unreachable, //root.object.coff.flush(self.out, .x86_64, out),
    };

    self.memcpy = .invalid;
    self.out.reset();
}

pub fn disasm(self: *X86_64, opts: Mach.DisasmOpts) void {
    // TODO: maybe we can do this in more platform independend way?
    // Compiling a library in?

    errdefer unreachable;

    var tmp = root.utils.Arena.scrath(null);
    defer tmp.deinit();

    std.debug.assert(self.object_format == .elf);
    const data = try object.elf.read(opts.bin, tmp.arena.allocator());

    const func_map = b: {
        var map = std.AutoArrayHashMapUnmanaged(usize, []const u8).empty;
        for (data.relocs.items) |r| {
            const target = &data.syms.items[@intFromEnum(r.target)];
            try map.put(tmp.arena.allocator(), r.offset, data.lookupName(target.name));
        }
        break :b map;
    };

    var decoder = zydis.ZydisDecoder{};
    _ = zydis.ZydisDecoderInit(
        &decoder,
        zydis.ZYDIS_MACHINE_MODE_LONG_64,
        zydis.ZYDIS_STACK_WIDTH_64,
    );

    var formatter = zydis.ZydisFormatter{};
    _ = zydis.ZydisFormatterInit(&formatter, zydis.ZYDIS_FORMATTER_STYLE_INTEL);

    for (data.syms.items) |v| {
        const name = data.lookupName(v.name);
        const bytes = data.code.items[v.offset..][0..v.size];
        switch (v.kind) {
            .func => {
                {
                    const fmt, const args = .{ "{s}:\n", .{name} };
                    if (opts.colors == .no_color) {
                        try opts.out.print(fmt, args);
                    } else {
                        try std.io.getStdErr().writer().print(fmt, args);
                    }
                }

                var inst = zydis.ZydisDecodedInstruction{};
                var ops: [zydis.ZYDIS_MAX_OPERAND_COUNT]zydis.ZydisDecodedOperand = undefined;

                const label_map = b: {
                    var map = std.AutoArrayHashMapUnmanaged(usize, usize).empty;

                    var addr: isize = 0;
                    while (addr < bytes.len) : (addr += inst.length) {
                        const uaddr: usize = @intCast(addr);
                        const status = zydis.ZydisDecoderDecodeFull(
                            &decoder,
                            bytes.ptr + uaddr,
                            bytes.len - uaddr,
                            &inst,
                            &ops,
                        );
                        std.debug.assert(zydis.ZYAN_SUCCESS(status));

                        if (inst.mnemonic == zydis.ZYDIS_MNEMONIC_JMP or
                            inst.mnemonic == zydis.ZYDIS_MNEMONIC_JZ)
                        {
                            try map.put(
                                tmp.arena.allocator(),
                                @intCast(addr + ops[0].unnamed_0.imm.value.s + inst.length),
                                map.count(),
                            );
                        }
                    }
                    break :b map;
                };

                var addr: isize = 0;
                while (addr < bytes.len) : (addr += inst.length) {
                    const uaddr: usize = @intCast(addr);
                    var status = zydis.ZydisDecoderDecodeFull(
                        &decoder,
                        bytes.ptr + uaddr,
                        bytes.len - uaddr,
                        &inst,
                        &ops,
                    );
                    std.debug.assert(zydis.ZYAN_SUCCESS(status));

                    var buf: [256]u8 = undefined;
                    status = zydis.ZydisFormatterFormatInstruction(
                        &formatter,
                        &inst,
                        &ops,
                        inst.operand_count_visible,
                        &buf,
                        @sizeOf(@TypeOf(buf)),
                        0,
                        null,
                    );
                    std.debug.assert(zydis.ZYAN_SUCCESS(status));

                    const printed = buf[0..std.mem.indexOfScalar(u8, &buf, 0).?];

                    if (label_map.get(uaddr)) |nm| {
                        const fmt, const args = .{ "{x}:", .{nm} };
                        if (opts.colors == .no_color) {
                            try opts.out.print(fmt, args);
                        } else {
                            try std.io.getStdErr().writer().print(fmt, args);
                        }
                    }

                    if (inst.mnemonic == zydis.ZYDIS_MNEMONIC_JMP or
                        inst.mnemonic == zydis.ZYDIS_MNEMONIC_JZ)
                    {
                        const label = label_map.get(@intCast(addr +
                            ops[0].unnamed_0.imm.value.s + inst.length)).?;
                        const fmt, const args = .{
                            "\t{s} :{}\n",
                            .{ zydis.ZydisMnemonicGetString(inst.mnemonic), label },
                        };
                        if (opts.colors == .no_color) {
                            try opts.out.print(fmt, args);
                        } else {
                            try std.io.getStdErr().writer().print(fmt, args);
                        }
                    } else if (inst.mnemonic == zydis.ZYDIS_MNEMONIC_CALL) {
                        const nm = func_map.get(v.offset + uaddr + 1) orelse continue;
                        const fmt, const args = .{ "\tcall :{s}\n", .{nm} };
                        if (opts.colors == .no_color) {
                            try opts.out.print(fmt, args);
                        } else {
                            try std.io.getStdErr().writer().print(fmt, args);
                        }
                    } else {
                        const fmt, const args = .{ "\t{s}\n", .{printed} };
                        if (opts.colors == .no_color) {
                            try opts.out.print(fmt, args);
                        } else {
                            try std.io.getStdErr().writer().print(fmt, args);
                        }
                    }
                }
            },
            else => {},
        }
    }
}

pub fn run(_: *X86_64, env: Mach.RunEnv) !usize {
    const cleanup = true;
    const res = b: {
        errdefer unreachable;

        var tmp = root.utils.Arena.scrath(null);
        defer tmp.deinit();

        const name = try std.fmt.allocPrint(
            tmp.arena.allocator(),
            "tmp_{s}.o",
            .{env.name},
        );
        const exe_name = try std.fmt.allocPrint(
            tmp.arena.allocator(),
            "./tmp_{s}",
            .{env.name},
        );

        try std.fs.cwd().writeFile(.{ .sub_path = name, .data = env.code });
        defer if (cleanup) std.fs.cwd().deleteFile(name) catch unreachable;

        var compile = std.process.Child.init(
            &.{ "zig", "cc", name, "-o", exe_name },
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
        } else if (res.Signal == 11 or res.Signal == 8) {
            return error.Fucked;
        } else std.debug.panic("{}\n", .{res});
    }
    return res.Exited;
}

pub fn deinit(self: *X86_64) void {
    self.out.deinit(self.gpa);
}

pub fn binopToMnemonic(op: graph.BinOp) zydis.ZydisMnemonic {
    return switch (op) {
        .iadd => zydis.ZYDIS_MNEMONIC_ADD,
        .isub => zydis.ZYDIS_MNEMONIC_SUB,
        .imul => zydis.ZYDIS_MNEMONIC_IMUL,

        .udiv, .umod => zydis.ZYDIS_MNEMONIC_DIV,
        .sdiv, .smod => zydis.ZYDIS_MNEMONIC_IDIV,

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

        .bor => zydis.ZYDIS_MNEMONIC_OR,
        .band => zydis.ZYDIS_MNEMONIC_AND,
        .bxor => zydis.ZYDIS_MNEMONIC_XOR,

        .ushr => zydis.ZYDIS_MNEMONIC_SHR,
        .ishl => zydis.ZYDIS_MNEMONIC_SHL,
        .sshr => zydis.ZYDIS_MNEMONIC_SAR,

        .fadd,
        .fsub,
        .fmul,
        .fdiv,
        .fgt,
        .flt,
        .fge,
        .fle,
        => std.debug.panic("floating point ops are postponed: {}", .{op}),
    };
}
