const std = @import("std");

const root = @import("hb");
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Regalloc = root.backend.Regalloc;
const utils = root.utils;
const object = root.object;
const zydis = @import("zydis").exports;

const X86_64 = @This();
const Func = graph.Func(X86_64);
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
arg_base: u32 = undefined,
local_base: u32 = undefined,
slot_base: c_int = undefined,
builtins: Mach.Builtins = undefined,

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
        const float_args: []const Reg = &.{ .xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7 };
        const args: []const Reg = &.{ .rdi, .rsi, .rdx, .rcx, .r8, .r9 };
        const caller_saved: []const Reg = &.{ .rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11 };
        const callee_saved: []const Reg = &.{ .rbx, .rbp, .r12, .r13, .r14, .r15 };
        const caller_saved_float: []const Reg = &.{
            .xmm0,  .xmm1,  .xmm2,  .xmm3,
            .xmm4,  .xmm5,  .xmm6,  .xmm7,
            .xmm8,  .xmm9,  .xmm10, .xmm11,
            .xmm12, .xmm13, .xmm14, .xmm15,
        };
        const callee_saved_float: []const Reg = &.{};
    };

    pub fn isScalar(self: Reg) bool {
        return @intFromEnum(self) <= @intFromEnum(Reg.r15);
    }

    pub fn isXmm(self: Reg) bool {
        return @intFromEnum(Reg.xmm0) <= @intFromEnum(self) and @intFromEnum(self) <= @intFromEnum(Reg.xmm15);
    }

    pub fn retForDt(dt: graph.DataType) Reg {
        return if (dt.isInt()) .rax else .xmm0;
    }

    pub fn asZydisOpScalar(self: Reg, size: usize) zydis.ZydisEncoderOperand {
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

    pub fn asZydisOpXmm(self: Reg, size: usize) zydis.ZydisEncoderOperand {
        return .{
            .type = zydis.ZYDIS_OPERAND_TYPE_REGISTER,
            .reg = .{ .value = @intCast(switch (size) {
                4 => zydis.ZYDIS_REGISTER_XMM0,
                8 => zydis.ZYDIS_REGISTER_XMM0,
                16 => zydis.ZYDIS_REGISTER_XMM0,
                else => utils.panic("{}", .{size}),
            } + @intFromEnum(self) - @intFromEnum(Reg.xmm0)) },
        };
    }

    pub fn asZydisOp(self: Reg, size: usize, slot_offset: c_int) zydis.ZydisEncoderOperand {
        if (self.isScalar()) {
            return self.asZydisOpScalar(size);
        } else if (self.isXmm()) {
            return self.asZydisOpXmm(size);
        } else {
            return .{
                .type = zydis.ZYDIS_OPERAND_TYPE_MEMORY,
                .mem = .{
                    .base = zydis.ZYDIS_REGISTER_RSP,
                    .size = @intCast(size),
                    .displacement = @as(
                        c_int,
                        @intFromEnum(self) - @intFromEnum(Reg.xmm15) - 1,
                    ) * 8 + slot_offset,
                },
            };
        }
    }
};

pub const Reloc = struct {
    offset: u32,
    dest: u32,
    class: enum { rel32 },
    off: u8,
};

pub const classes = enum {
    pub const StackLoad = extern struct {
        base: OffsetLoad,

        pub const data_dep_offset = 2;
    };
    pub const StackStore = extern struct {
        base: OffsetStore,

        pub const data_dep_offset = 2;
    };
    pub const ConstStackStore = extern struct {
        base: ConstStore,

        pub const data_dep_offset = 2;
    };
    pub const ConstStore = extern struct {
        base: OffsetStore,
        imm: i64,
    };
    pub const OffsetLoad = extern struct {
        base: graph.Load = .{},
        dis: i32,
    };
    pub const OffsetStore = extern struct {
        base: graph.Store = .{},
        dis: i32,
    };
    pub const ImmOp = extern struct {
        base: graph.builtin.BinOp,
        imm: i64,
    };
    pub const CondJump = extern struct {
        base: graph.If = .{},
        op: zydis.ZydisMnemonic,
    };
};

pub const biased_regs = b: {
    var mask: u64 = 0;
    for (Reg.system_v.caller_saved) |r| {
        mask |= @as(u64, 1) << @intFromEnum(r);
    }
    break :b mask;
};

// ================== BINDINGS ==================
pub fn getStaticOffset(node: *Func.Node) i64 {
    return switch (node.kind) {
        .OffsetLoad => node.extra(.OffsetLoad).dis,
        .OffsetStore => node.extra(.OffsetStore).dis,
        .ConstStore => node.extra(.ConstStore).base.dis,
        .StackLoad => node.extra(.StackLoad).base.dis,
        .StackStore => node.extra(.StackStore).base.dis,
        .ConstStackStore => node.extra(.ConstStackStore).base.base.dis,
        else => 0,
    };
}

pub fn knownOffset(node: *Func.Node) struct { *Func.Node, i64 } {
    return switch (node.extra2()) {
        .ImmOp => |extra| {
            std.debug.assert(extra.base.op == .iadd or extra.base.op == .isub);
            return .{ node.inputs()[1].?, if (extra.base.op == .iadd)
                extra.imm
            else
                -extra.imm };
        },
        else => .{ node, 0 },
    };
}

pub fn isInterned(kind: Func.Kind) bool {
    return kind == .OffsetLoad or kind == .StackLoad;
}

pub fn isSwapped(node: *Func.Node) bool {
    _ = node;
    return false;
}

// ================== PEEPHOLES ==================
pub fn idealizeMach(_: *X86_64, func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
    if (Func.idealizeDead({}, func, node, worklist)) |n| return n;

    if (node.kind == .CInt and node.data_type == .f32) {
        const int_const = func.addIntImm(node.sloc, .i32, node.extra(.CInt).value);
        return func.addCast(node.sloc, .f32, int_const);
    }

    if (node.kind == .CInt and node.data_type == .f64) {
        const int_const = func.addIntImm(node.sloc, .i64, node.extra(.CInt).value);
        return func.addCast(node.sloc, .f64, int_const);
    }

    if (node.kind == .Load) {
        const base, const offset = node.base().knownOffset();

        // needs to be done since Loads are interned
        const res = if (base.isStack())
            func.addNode(
                .StackLoad,
                node.sloc,
                node.data_type,
                &.{ node.inputs()[0], node.mem(), base },
                .{ .base = .{ .dis = @intCast(offset) } },
            )
        else
            func.addNode(
                .OffsetLoad,
                node.sloc,
                node.data_type,
                &.{ node.inputs()[0], node.mem(), base },
                .{ .dis = @intCast(offset) },
            );

        worklist.add(res);
        return res;
    }

    if (node.kind == .Store) {
        const base, const offset = node.base().knownOffset();

        store: {
            const mask = if (node.data_type.mask()) |m| (m & 0xffffffff) >> 1 else break :store;
            if (node.value().?.kind == .CInt and (@abs(node.value().?.extra(.CInt).value) <= mask)) {
                const res = func.addNode(
                    .ConstStore,
                    node.sloc,
                    node.data_type,
                    &.{ node.inputs()[0], node.mem(), base },
                    .{
                        .base = .{ .dis = @intCast(offset) },
                        .imm = node.value().?.extra(.CInt).value,
                    },
                );

                if (base.isStack()) {
                    res.kind = .ConstStackStore;
                }

                worklist.add(res);
                return res;
            }
        }

        const res = func.addNode(
            .OffsetStore,
            node.sloc,
            node.data_type,
            &.{ node.inputs()[0], node.mem(), base, node.value() },
            .{ .dis = @intCast(offset) },
        );

        if (base.isStack()) {
            res.kind = .StackStore;
        }

        worklist.add(res);
        return res;
    }

    if (node.kind == .OffsetStore and node.base().isStack()) {
        node.kind = .StackStore;
    }

    if (node.isStack()) elim_local: {
        for (node.outputs()) |use| {
            if (((!use.isStore() or use.value() == node) and !use.isLoad()) or use.isSub(graph.MemCpy)) {
                break :elim_local;
            }
        }

        switch (node.extra2()) {
            .Local => |n| n.no_address = true,
            .StructArg => |n| n.no_address = true,
            else => unreachable,
        }
    }

    if (node.kind == .If) {
        const cond = node.inputs()[1].?;
        if (cond.kind == .BinOp) select_cond_jump: {
            const op: zydis.ZydisMnemonic = switch (cond.extra(.BinOp).op) {
                .ne => zydis.ZYDIS_MNEMONIC_JZ,
                .eq => zydis.ZYDIS_MNEMONIC_JNZ,

                // Unsigned comparisons
                .uge => zydis.ZYDIS_MNEMONIC_JB, // jump if below (opposite of >=)
                .ule => zydis.ZYDIS_MNEMONIC_JNBE, // jump if above (opposite of <=)
                .ugt => zydis.ZYDIS_MNEMONIC_JBE, // jump if below or equal (opposite of >)
                .ult => zydis.ZYDIS_MNEMONIC_JNB, // jump if above or equal (opposite of <)

                // Signed comparisons
                .sge => zydis.ZYDIS_MNEMONIC_JL, // jump if less (opposite of >=)
                .sle => zydis.ZYDIS_MNEMONIC_JNLE, // jump if greater (opposite of <=)
                .sgt => zydis.ZYDIS_MNEMONIC_JLE, // jump if less or equal (opposite of >)
                .slt => zydis.ZYDIS_MNEMONIC_JNL, // jump if greater or equal (opposite of <)

                else => break :select_cond_jump,
            };
            return func.addNode(
                .CondJump,
                node.sloc,
                cond.data_type,
                &.{ node.inputs()[0], cond.inputs()[1], cond.inputs()[2] },
                .{ .op = op },
            );
        }
    }

    if (node.kind == .BinOp and node.inputs()[2].?.kind == .CInt and
        switch (node.extra(.BinOp).op) {
            .udiv, .sdiv, .umod, .smod, .imul, .fadd, .fmul, .fsub, .fdiv, .fgt, .flt, .fge, .fle => false,
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
            => node.inputs()[2].?.data_type.size() > 2 and node.inputs()[2].?.data_type.isInt(),

            else => true,
        })
    {
        if (std.math.cast(i32, node.inputs()[2].?.extra(.CInt).value) != null) {
            return func.addNode(.ImmOp, node.sloc, node.data_type, node.inputs()[0..2], .{
                .base = node.extra(.BinOp).*,
                .imm = node.inputs()[2].?.extra(.CInt).value,
            });
        }
    }

    return null;
}

pub fn idealize(_: *X86_64, func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
    if (node.kind == .MemCpy) {
        const ctrl = node.inputs()[0].?;
        var mem = node.inputs()[1].?;
        const dst = node.inputs()[2].?;
        const src = node.inputs()[3].?;
        const len = node.inputs()[4].?;
        if (len.kind == .CInt and len.extra(.CInt).value <= 16) {
            const size = len.extra(.CInt).value;
            var cursor: u64 = 0;
            var copy_elem = graph.DataType.i64;

            while (cursor != size) {
                while (cursor + copy_elem.size() > size) : (copy_elem =
                    @enumFromInt(@intFromEnum(copy_elem) - 1))
                {}

                const dst_off = func.addFieldOffset(node.sloc, dst, @intCast(cursor));
                const src_off = func.addFieldOffset(node.sloc, src, @intCast(cursor));
                const ld = func.addNode(.Load, node.sloc, copy_elem, &.{ ctrl, mem, src_off }, .{});
                worklist.add(ld);
                mem = func.addNode(.Store, node.sloc, copy_elem, &.{ ctrl, mem, dst_off, ld }, .{});
                worklist.add(mem);

                cursor += copy_elem.size();
            }

            return mem;
        }
    }

    return null;
}

// ================== REGALLOC ==================
const set_cap = 64;
const Set = std.DynamicBitSetUnmanaged;

pub fn floatMask(arena: *utils.Arena) Set {
    var set = Set.initEmpty(arena.allocator(), set_cap) catch unreachable;
    set.setRangeValue(.{ .start = 16, .end = 32 }, true);
    return set;
}

pub fn readIntMask(arena: *utils.Arena) Set {
    var set = Set.initEmpty(arena.allocator(), set_cap) catch unreachable;
    set.setRangeValue(.{ .start = 0, .end = 16 }, true);
    return set;
}

pub fn writeIntMask(arena: *utils.Arena) Set {
    var set = readIntMask(arena);
    set.unset(@intFromEnum(Reg.rsp));
    return set;
}

pub fn splitFloatMask(arena: *utils.Arena) Set {
    var set = Set.initFull(arena.allocator(), set_cap) catch unreachable;
    set.setRangeValue(.{ .start = 0, .end = 16 }, false);
    return set;
}

pub fn splitIntMask(arena: *utils.Arena) Set {
    var set = readSplitIntMask(arena);
    set.unset(@intFromEnum(Reg.rsp));
    return set;
}

pub fn readSplitIntMask(arena: *utils.Arena) Set {
    var set = Set.initFull(arena.allocator(), set_cap) catch unreachable;
    set.setRangeValue(.{ .start = 16, .end = 32 }, false);
    return set;
}

pub fn singleReg(reg: Reg, arena: *utils.Arena) Set {
    var set = Set.initEmpty(arena.allocator(), set_cap) catch unreachable;
    set.set(@intFromEnum(reg));
    return set;
}

pub fn regBias(node: *Func.Node) ?u16 {
    return @intFromEnum(switch (node.extra2()) {
        .Arg => |ext| if (ext.index < Reg.system_v.args.len) Reg.system_v.args[ext.index] else return null,
        else => b: {
            for (node.outputs()) |o| {
                if (o.kind == .Call) {
                    const idx = std.mem.indexOfScalar(?*Func.Node, o.dataDeps(), node) orelse continue;
                    if (o.extra(.Call).id == syscall) {
                        break :b Reg.system_v.syscall_args[idx];
                    } else {
                        break :b if (idx < Reg.system_v.args.len) Reg.system_v.args[idx] else return null;
                    }
                }

                if (o.kind == .Phi and o.inputs()[0].?.kind != .Loop) {
                    return o.regBias();
                }
            }

            if (node.isSub(graph.builtin.BinOp)) {
                return node.inputs()[1].?.regBias();
            }

            return null;
        },
    });
}

pub fn clobbers(node: *Func.Node) u64 {
    return switch (node.kind) {
        .Call, .MemCpy => comptime b: {
            var vl: u64 = 0;
            for (Reg.system_v.caller_saved) |r| {
                vl |= @as(u64, 1) << @intFromEnum(r);
            }
            for (Reg.system_v.caller_saved_float) |r| {
                vl |= @as(u64, 1) << @intFromEnum(r);
            }
            break :b vl;
        },
        .BinOp => switch (node.extra(.BinOp).op) {
            .udiv, .sdiv, .umod, .smod => {
                var base = @as(u64, 1) << @intFromEnum(Reg.rax);
                if (node.data_type.size() != 1) {
                    base |= @as(u64, 1) << @intFromEnum(Reg.rdx);
                }
                return base;
            },
            else => 0,
        },
        else => 0,
    };
}

pub fn regMask(
    node: *Func.Node,
    func: *Func,
    idx: usize,
    arena: *utils.Arena,
) std.DynamicBitSetUnmanaged {
    errdefer unreachable;

    if (node.kind == .MachSplit) {
        if (node.data_type.isFloat()) return splitFloatMask(arena);
        if (idx == 0) return splitIntMask(arena);
        return readSplitIntMask(arena);
    }

    if (node.kind == .Arg) {
        std.debug.assert(idx == 0);
        const index: usize = node.extra(.Arg).index;

        const params = func.signature.params();
        if (params[index] == .Stack) return readIntMask(arena);
        var reg_idx: usize = 0;
        var xmm_idx: usize = 0;
        for (params[0..index]) |p| {
            if (p == .Reg) {
                if (p.Reg.isFloat()) {
                    xmm_idx += 1;
                } else {
                    reg_idx += 1;
                }
            }
        }

        if (params[index].Reg.isFloat()) {
            std.debug.assert(node.data_type.isFloat());
            return singleReg(Reg.system_v.float_args[xmm_idx], arena);
        } else {
            std.debug.assert(node.data_type.isInt());
            return singleReg(Reg.system_v.args[reg_idx], arena);
        }
    }

    if (node.kind == .FramePointer) {
        std.debug.assert(idx == 0);
        return singleReg(.rsp, arena);
    }

    if (node.kind == .Call) {
        std.debug.assert(idx >= 2);
        const extra = node.extra(.Call);
        if (extra.id == syscall) {
            return singleReg(Reg.system_v.syscall_args[idx - 2], arena);
        } else {
            const params = @as(graph.Signature, extra.signature).params();
            if (params[idx - 2] == .Stack) return readIntMask(arena);
            var reg_idx: usize = 0;
            var xmm_idx: usize = 0;
            for (params[0 .. idx - 2]) |p| {
                if (p == .Reg) {
                    if (p.Reg.isFloat()) {
                        xmm_idx += 1;
                    } else {
                        reg_idx += 1;
                    }
                }
            }
            if (params[idx - 2].Reg.isFloat()) {
                std.debug.assert(node.inputs()[idx].?.data_type.isFloat());
                return singleReg(Reg.system_v.float_args[xmm_idx], arena);
            } else {
                std.debug.assert(node.inputs()[idx].?.data_type.isInt());
                return singleReg(Reg.system_v.args[reg_idx], arena);
            }
        }
    }

    if (node.kind == .Return) {
        std.debug.assert(idx == 3);
        if (node.inputs()[idx].?.data_type.isFloat()) return singleReg(.xmm0, arena);
        return singleReg(.rax, arena);
    }

    if (node.data_type.isFloat() and idx == 0) {
        return floatMask(arena);
    }

    if (node.kind == .Ret) {
        std.debug.assert(idx == 0);
        return singleReg(.rax, arena);
    }

    if (node.subclass(graph.builtin.BinOp)) |b| {
        const op = b.ext.op;
        switch (op) {
            .udiv, .sdiv, .smod, .umod => switch (node.data_type.size()) {
                1, 2, 4, 8 => switch (idx) {
                    0 => {
                        return singleReg(
                            if (op == .udiv or op == .sdiv) .rax else .rdx,
                            arena,
                        );
                    },
                    1 => {
                        return singleReg(.rax, arena);
                    },
                    2 => {
                        var set = readIntMask(arena);
                        set.unset(@intFromEnum(Reg.rax));
                        set.unset(@intFromEnum(Reg.rdx));
                        return set;
                    },
                    else => unreachable,
                },
                else => unreachable,
            },
            .ishl, .ushr, .sshr => switch (idx) {
                2 => return singleReg(.rcx, arena),
                else => {},
            },
            else => {},
        }
    }

    if (idx == 0) return writeIntMask(arena);
    if (node.inputs()[idx].?.data_type.isFloat()) {
        return floatMask(arena);
    }
    return readIntMask(arena);
}

pub fn binOpInPlaceSlot(op: graph.BinOp) ?usize {
    return switch (op) {
        .iadd, .isub, .imul, .bor, .band, .bxor, .ushr => 0,
        .ishl, .sshr, .fadd, .fsub, .fmul, .fdiv => 0,
        .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt => null,
        .slt, .udiv, .sdiv, .umod, .smod, .fgt, .flt, .fge, .fle => null,
    };
}

pub fn inPlaceSlot(node: *Func.Node) ?usize {
    return switch (node.extra2()) {
        .ImmOp => |extra| binOpInPlaceSlot(extra.base.op),
        .BinOp => |extra| binOpInPlaceSlot(extra.op),
        .UnOp => |extra| switch (@as(graph.UnOp, extra.op)) {
            .ineg, .bnot, .ired, .not => 0,
            .fneg, .fcst, .sext, .uext, .cast, .itf32, .itf64, .fti => return null,
        },
        else => null,
    };
}

// ================== EMIT ==================

pub fn emitFunc(self: *X86_64, func: *Func, opts: Mach.EmitOptions) void {
    errdefer unreachable;

    const id = opts.id;
    const linkage = opts.linkage;
    const name = if (opts.special == .memcpy)
        "memcpy"
    else if (opts.special == .entry)
        switch (self.object_format) {
            .elf => "_start",
            .coff => "WinMain",
        }
    else
        opts.name;
    self.builtins = opts.builtins;

    try self.out.startDefineFunc(self.gpa, id, name, .func, linkage, opts.is_inline);

    defer self.out.endDefineFunc(id);

    if (opts.linkage == .imported) return;

    if (opts.optimizations.shouldDefer(id, opts.is_inline, X86_64, func, self))
        return;

    opts.optimizations.execute(X86_64, self, func);

    //    if (std.mem.endsWith(u8, opts.name, "unwrap")) {
    //        func.fmtScheduled(
    //            std.io.getStdErr().writer().any(),
    //            std.io.tty.detectConfig(std.io.getStdErr()),
    //        );
    //    }
    //
    var tmp = utils.Arena.scrath(opts.optimizations.arena);
    defer tmp.deinit();

    var visited = std.DynamicBitSet.initEmpty(tmp.arena.allocator(), func.next_id) catch unreachable;
    const postorder = func.collectPostorder(tmp.arena.allocator(), &visited);

    self.allocs = Regalloc.ralloc(X86_64, func);
    self.ret_count = if (func.signature.returns()) |r| r.len else std.math.maxInt(usize);
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
                return @ctz(lhs.extra(.Local).size) > @ctz(rhs.extra(.Local).size);
            }
        }.isBigger);

        std.debug.assert(func.root.outputs()[1].kind == .Mem);
        for (locals.items) |o| {
            const extra = o.extra(.Local);
            const size = extra.size;
            extra.size = @bitCast(local_size);
            local_size += @intCast(size);
        }
    }

    const spill_slot_count = if (self.allocs.len == 0) 0 else std.mem.max(u16, self.allocs) -| 31;
    var stack_size: i64 = std.mem.alignForward(i64, local_size, 8) +
        spill_slot_count * 8;

    var has_call = false;
    var call_slot_size: u64 = 0;
    for (postorder) |bb| {
        if (bb.base.kind == .MemCpy) has_call = true;
        if (bb.base.kind == .CallEnd) {
            const call = bb.base.inputs()[0].?;
            const signature = &call.extra(.Call).signature;
            call_slot_size = @max(signature.stackSize(), call_slot_size);
            has_call = true;
        }
    }

    stack_size += @intCast(call_slot_size);

    const padding = std.mem.alignForward(i64, stack_size, 16) - stack_size;

    if (has_call and padding >= 8) {
        stack_size += padding - 8;
    } else if (has_call) {
        stack_size += padding + 8;
    } else {
        stack_size += padding;
    }

    self.slot_base = @intCast(call_slot_size);
    self.local_base = @intCast(self.slot_base + spill_slot_count * 8);
    self.arg_base = @intCast(stack_size);
    self.arg_base += 8; // call adress

    prelude: {
        for (Reg.system_v.callee_saved) |r| {
            if (used_regs.contains(r)) {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_PUSH, .{r});
                self.arg_base += 8;
            }
        }

        if (stack_size != 0) {
            self.emitInstr(zydis.ZYDIS_MNEMONIC_SUB, .{ Reg.rsp, stack_size });
        }

        var i: usize = 0;
        var f: usize = 0;
        var stack_arg_offset: u64 = 0;
        for (func.signature.params(), 0..) |par, j| {
            defer {
                if (par != .Stack) {
                    if (par.Reg.isInt()) {
                        i += 1;
                    } else {
                        f += 1;
                    }
                }
            }

            const argn = for (postorder[0].base.outputs()) |o| {
                if (o.subclass(graph.Arg)) |sub| if (sub.ext.index == j) break o;
            } else continue; // is dead

            if (par == .Stack) {
                stack_arg_offset = std.mem.alignForward(u64, stack_arg_offset, @as(u64, 1) << par.Stack.alignment);
                argn.extra(.StructArg).spec.size = @intCast(stack_arg_offset);
                stack_arg_offset += par.Stack.size;
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
                if (used_regs.contains(r)) {
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

pub fn emitBlockBody(self: *X86_64, block: *FuncNode) void {
    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    for (block.outputs()) |instr| {
        switch (instr.extra2()) {
            .FramePointer => {},
            .CInt => |extra| {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ self.getReg(instr), extra.value });
            },
            .MemCpy => {
                var moves = std.ArrayList(Move).init(tmp.arena.allocator());
                for (instr.dataDeps(), 0..) |arg, i| {
                    const dst, const src: Reg = .{ Reg.system_v.args[i], self.getReg(arg) };
                    if (!std.meta.eql(dst, src)) moves.append(.init(dst, src)) catch unreachable;
                }
                self.orderMoves(moves.items);

                const opcode = 0xE8;
                try self.out.code.append(self.gpa, opcode);
                if (self.builtins.memcpy == std.math.maxInt(u32)) {
                    if (self.memcpy == .invalid)
                        try self.out.importSym(self.gpa, &self.memcpy, "memcpy", .func);
                    try self.out.addReloc(self.gpa, &self.memcpy, 4, -4);
                } else {
                    try self.out.addFuncReloc(self.gpa, self.builtins.memcpy, 4, -4);
                }
                try self.out.code.appendSlice(self.gpa, &.{ 0, 0, 0, 0 });
            },
            .MachSplit => if (instr.outputs().len != 1 or instr.outputs()[0].kind != .Phi) {
                const dst, const src = .{ self.getReg(instr), self.getReg(instr.inputs()[1]) };
                if (dst == src) continue;
                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ dst, src });
            },
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
                req.operands[0] = self.getReg(instr).asZydisOp(8, self.slot_base);
                req.operands[1] = .{
                    .type = zydis.ZYDIS_OPERAND_TYPE_MEMORY,
                    .mem = .{
                        .base = zydis.ZYDIS_REGISTER_RIP,
                        .size = 8,
                    },
                };
                const status = zydis.ZydisEncoderEncodeInstruction(&req, &buf, &len);
                if (zydis.ZYAN_FAILED(status) != 0) {
                    utils.panic("{x}\n", .{status});
                }
                try self.out.code.appendSlice(self.gpa, buf[0 .. len - 4]);

                try self.out.addGlobalReloc(self.gpa, instr.extra(.GlobalAddr).id, 4, -4);

                try self.out.code.appendSlice(self.gpa, buf[len - 4 .. len]);
            },
            .Local => |extra| if (!extra.no_address) {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_LEA, .{
                    self.getReg(instr),
                    BRegOff{ .rsp, @intCast(instr.extra(.Local).size + self.local_base), 8 },
                });
            },
            .StructArg => |extra| if (!extra.no_address) {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_LEA, .{
                    self.getReg(instr),
                    BRegOff{ .rsp, @intCast(instr.extra(.StructArg).spec.size + self.arg_base), 8 },
                });
            },
            .StackArgOffset => {
                self.emitInstr(zydis.ZYDIS_MNEMONIC_LEA, .{
                    self.getReg(instr),
                    BRegOff{ .rsp, @intCast(instr.extra(.StackArgOffset).offset), 8 },
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
            .ConstStore => |extra| {
                const dst = self.getReg(instr.inputs()[2]);
                const vl = extra.imm;

                const offset: i32 = extra.base.dis;
                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{
                    BRegOff{ dst, offset, @intCast(instr.data_type.size()) },
                    vl,
                });
            },
            .ConstStackStore => |extra| {
                const vl = extra.base.imm;

                const offset: i32 = extra.base.base.dis +
                    @as(i32, @intCast(switch (instr.inputs()[2].?.extra2()) {
                        .Local => |n| n.size + self.local_base,
                        .StructArg => |n| n.spec.size + self.arg_base,
                        else => unreachable,
                    }));
                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{
                    BRegOff{ .rsp, offset, @intCast(instr.data_type.size()) },
                    vl,
                });
            },
            .StackLoad => |extra| {
                const dst = self.getReg(instr);
                const offset: i32 = extra.base.dis +
                    @as(i32, @intCast(switch (instr.inputs()[2].?.extra2()) {
                        .Local => |n| n.size + self.local_base,
                        .StructArg => |n| n.spec.size + self.arg_base,
                        else => unreachable,
                    }));
                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{
                    SReg{ dst, instr.data_type.size() },
                    BRegOff{ .rsp, offset, @intCast(instr.data_type.size()) },
                });
            },
            .StackStore => |extra| {
                const vl = self.getReg(instr.inputs()[3]);
                const offset: i32 = extra.base.dis +
                    @as(i32, @intCast(switch (instr.inputs()[2].?.extra2()) {
                        .Local => |n| n.size + self.local_base,
                        .StructArg => |n| n.spec.size + self.arg_base,
                        else => unreachable,
                    }));

                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{
                    BRegOff{ .rsp, offset, @intCast(instr.data_type.size()) },
                    SReg{ vl, instr.data_type.size() },
                });
            },
            .Call => |extra| {
                const call = instr.extra(.Call);

                const call_conv = if (extra.id == syscall)
                    Reg.system_v.syscall_args
                else
                    Reg.system_v.args;

                const float_conv = Reg.system_v.float_args;

                var moves = std.ArrayList(Move).init(tmp.arena.allocator());
                var i: usize = 0;
                var f: usize = 0;
                for (instr.dataDeps()) |arg| {
                    if (arg.kind == .StackArgOffset) {
                        std.debug.assert(self.slot_base != 0);
                        continue;
                    }

                    var dst: Reg, const src = .{ undefined, self.getReg(arg) };
                    if (arg.data_type.isInt()) {
                        dst = call_conv[i];
                        i += 1;
                    } else {
                        dst = float_conv[f];
                        f += 1;
                    }
                    if (dst != src) moves.append(.init(dst, src)) catch unreachable;
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
                        const dst: Reg, const src = .{ self.getReg(r), Reg.retForDt(r.data_type) };
                        if (dst != src) moves.append(.init(dst, src)) catch unreachable;
                    }
                }
                self.orderMoves(moves.items);
            },
            .Arg, .Ret, .Mem, .Never => {},
            .Trap => {
                switch (instr.extra(.Trap).code) {
                    graph.unreachable_func_trap,
                    graph.infinite_loop_trap,
                    => return,
                    0 => self.emitInstr(zydis.ZYDIS_MNEMONIC_UD2, .{}),
                    else => unreachable,
                }
            },
            .Return => {},
            .ImmOp => |extra| {
                const op = extra.base.op;
                const size = instr.data_type.size();
                const op_dt = instr.inputs()[1].?.data_type;
                const opsize = op_dt.size();
                const dst = self.getReg(instr);
                const lhs = self.getReg(instr.inputs()[1]);
                const rhs = extra.imm;

                const mnemonic = binopToMnemonic(op, instr.data_type);

                switch (op) {
                    .imul => unreachable,
                    .ushr, .ishl, .sshr, .iadd, .isub, .bor, .band, .bxor => {
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
                const op = extra.op;
                const size = instr.data_type.size();
                const op_dt = instr.inputs()[1].?.data_type;
                const opsize = op_dt.size();
                const dst = self.getReg(instr);
                const lhs = self.getReg(instr.inputs()[1]);
                const rhs = self.getReg(instr.inputs()[2]);

                const mnemonic = binopToMnemonic(op, instr.data_type);

                switch (op) {
                    .ushr, .ishl, .sshr => {
                        std.debug.assert(lhs == dst);
                        std.debug.assert(rhs == .rcx);
                        self.emitInstr(mnemonic, .{ SReg{ dst, size }, SReg{ rhs, 1 } });
                    },
                    .fadd, .fsub, .fmul, .fdiv, .iadd, .isub, .imul, .bor, .band, .bxor => {
                        std.debug.assert(lhs == dst);
                        self.emitInstr(mnemonic, .{ SReg{ dst, @max(size, 4) }, rhs });
                    },
                    .udiv, .sdiv, .smod, .umod => switch (size) {
                        1, 2, 4, 8 => {
                            // this is kind of fucked but eh,
                            // we need a better support from the regalloc
                            const oper = rhs;
                            std.debug.assert(lhs == .rax);
                            std.debug.assert(rhs != .rdx);
                            const dest_reg: Reg = if (op == .udiv or op == .sdiv) .rax else .rdx;
                            std.debug.assert(dst == dest_reg);

                            if (size == 1) {
                                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOVZX, .{ Reg.rax, SReg{ .rax, 1 } });
                            } else {
                                self.emitInstr(zydis.ZYDIS_MNEMONIC_XOR, .{ SReg{ Reg.rdx, size }, Reg.rdx });
                            }
                            self.emitInstr(mnemonic, .{SReg{ oper, size }});

                            if (size == 1 and dest_reg == .rdx) {
                                self.emitInstr(zydis.ZYDIS_MNEMONIC_MOV, .{ SReg{ dst, 1 }, zydis.ZydisEncoderOperand{
                                    .type = zydis.ZYDIS_OPERAND_TYPE_REGISTER,
                                    .reg = .{ .value = zydis.ZYDIS_REGISTER_AH },
                                } });
                            }
                        },
                        else => unreachable,
                    },
                    .fgt, .flt, .fge, .fle, .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt, .slt => {
                        const cmp_mnemonic: zydis.ZydisMnemonic = if (op_dt.isInt())
                            zydis.ZYDIS_MNEMONIC_CMP
                        else if (op_dt == .f64)
                            zydis.ZYDIS_MNEMONIC_COMISD
                        else
                            zydis.ZYDIS_MNEMONIC_COMISS;

                        self.emitInstr(cmp_mnemonic, .{ SReg{ lhs, opsize }, SReg{ rhs, opsize } });
                        self.emitInstr(mnemonic, .{SReg{ dst, 1 }});
                        self.emitInstr(zydis.ZYDIS_MNEMONIC_MOVZX, .{ dst, SReg{ dst, 1 } });
                    },
                }
            },
            .If => {
                const cond = self.getReg(instr.inputs()[1]);
                const cond_size = instr.inputs()[1].?.data_type.size();
                self.emitInstr(zydis.ZYDIS_MNEMONIC_TEST, .{ SReg{ cond, cond_size }, SReg{ cond, cond_size } });
                self.local_relocs.appendAssumeCapacity(.{
                    .dest = instr.outputs()[1].schedule,
                    .offset = @intCast(self.out.code.items.len),
                    .class = .rel32,
                    .off = 2,
                });
                self.emitInstr(zydis.ZYDIS_MNEMONIC_JZ, .{ std.math.maxInt(i32), SizeHint{ .bytes = 0 } });
            },
            .CondJump => |extra| {
                const lhs = self.getReg(instr.inputs()[1]);
                const rhs = self.getReg(instr.inputs()[2]);
                const oper_dt = instr.inputs()[1].?.data_type;

                const cmp_mnemonic: zydis.ZydisMnemonic = if (oper_dt.isInt())
                    zydis.ZYDIS_MNEMONIC_CMP
                else if (oper_dt == .f64)
                    zydis.ZYDIS_MNEMONIC_COMISD
                else
                    zydis.ZYDIS_MNEMONIC_COMISS;

                self.emitInstr(cmp_mnemonic, .{ SReg{ lhs, instr.inputs()[1].?.data_type.size() }, rhs });
                self.local_relocs.appendAssumeCapacity(.{
                    .dest = instr.outputs()[1].schedule,
                    .offset = @intCast(self.out.code.items.len),
                    .class = .rel32,
                    .off = 2,
                });
                self.emitInstr(extra.op, .{ std.math.maxInt(i32), SizeHint{ .bytes = 0 } });
            },
            .Jmp => if (instr.outputs()[0].kind == .Region or instr.outputs()[0].kind == .Loop) {
                const idx = std.mem.indexOfScalar(?*Func.Node, instr.outputs()[0].inputs(), instr).? + 1;

                var moves = std.ArrayList(Move).init(tmp.arena.allocator());
                for (instr.outputs()[0].outputs()) |o| {
                    if (o.isDataPhi()) {
                        std.debug.assert(o.inputs()[idx].?.kind == .MachSplit);
                        const dst, const src = .{ self.getReg(o), self.getReg(o.inputs()[idx].?.inputs()[1]) };
                        if (dst != src) try moves.append(.init(dst, src));
                    }
                }

                self.orderMoves(moves.items);
            },
            .UnOp => |extra| {
                const op = extra.op;
                const size = instr.data_type.size();
                const dst = self.getReg(instr);
                const src_dt = instr.inputs()[1].?.data_type;
                const src_size = src_dt.size();
                const src = self.getReg(instr.inputs()[1]);

                std.debug.assert(dst == src or switch (op) {
                    .not, .bnot, .ineg, .ired => false,
                    else => true,
                });

                switch (op) {
                    .ired => {},
                    .sext => switch (src_size) {
                        1, 2 => self.emitInstr(
                            zydis.ZYDIS_MNEMONIC_MOVSX,
                            .{ SReg{ dst, size }, SReg{ src, src_size } },
                        ),
                        4 => self.emitInstr(
                            zydis.ZYDIS_MNEMONIC_MOVSXD,
                            .{ SReg{ dst, size }, SReg{ src, src_size } },
                        ),
                        else => unreachable,
                    },
                    .uext => if (instr.inputs()[1].?.data_type.size() <= 2) {
                        self.emitInstr(
                            zydis.ZYDIS_MNEMONIC_MOVZX,
                            .{ SReg{ dst, size }, SReg{ src, src_size } },
                        );
                    } else {
                        self.emitInstr(
                            zydis.ZYDIS_MNEMONIC_MOV,
                            .{ SReg{ dst, instr.inputs()[1].?.data_type.size() }, src },
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
                    .cast => self.emitInstr(switch (src_size) {
                        4 => zydis.ZYDIS_MNEMONIC_MOVD,
                        8 => zydis.ZYDIS_MNEMONIC_MOVQ,
                        else => unreachable,
                    }, .{ SReg{ dst, size }, SReg{ src, src_size } }),
                    .fti => self.emitInstr(switch (src_dt) {
                        .f32 => zydis.ZYDIS_MNEMONIC_CVTTSS2SI,
                        .f64 => zydis.ZYDIS_MNEMONIC_CVTTSD2SI,
                        else => unreachable,
                    }, .{ SReg{ dst, size }, SReg{ src, size } }),
                    .itf32 => self.emitInstr(zydis.ZYDIS_MNEMONIC_CVTSI2SS, .{ SReg{ dst, size }, SReg{ src, size } }),
                    .itf64 => self.emitInstr(zydis.ZYDIS_MNEMONIC_CVTSI2SD, .{ SReg{ dst, size }, SReg{ src, size } }),
                    .fcst => self.emitInstr(switch (src_dt) {
                        .f32 => zydis.ZYDIS_MNEMONIC_CVTSS2SD,
                        .f64 => zydis.ZYDIS_MNEMONIC_CVTSD2SS,
                        else => unreachable,
                    }, .{ SReg{ dst, size }, SReg{ src, size } }),
                    .fneg => self.emitInstr(switch (src_dt) {
                        .f32 => zydis.ZYDIS_MNEMONIC_XORPS,
                        .f64 => zydis.ZYDIS_MNEMONIC_XORPD,
                        else => unreachable,
                    }, .{ SReg{ dst, size }, SReg{ src, size } }),
                }
            },
            else => {
                utils.panic("{any}", .{instr});
            },
        }
    }
}

pub const SReg = struct { Reg, usize };
pub const BRegOff = struct { Reg, i32, u16 };
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

    var size: ?usize = null;
    inline for (fields) |f| {
        const val = @field(args, f.name);
        const op_size: ?usize = switch (f.type) {
            Reg => 8,
            SReg => val[1],
            BRegOff => val[2],
            SizeHint => val.bytes,
            zydis.ZydisEncoderOperand => b: {
                const t = if (val.type == zydis.ZYDIS_OPERAND_TYPE_MEMORY)
                    val.mem.size
                else
                    8;
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
            Reg => val.asZydisOp(fsize, self.slot_base),
            SReg => val[0].asZydisOp(val[1], self.slot_base),
            BRegOff => b: {
                const base = val[0].asZydisOp(8, self.slot_base);
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

    if (mnemonic == zydis.ZYDIS_MNEMONIC_MOV and
        ((req.operands[0].reg.value >= zydis.ZYDIS_REGISTER_XMM0 and
            req.operands[0].reg.value <= zydis.ZYDIS_REGISTER_XMM15) or
            (req.operands[1].reg.value >= zydis.ZYDIS_REGISTER_XMM0 and
                req.operands[1].reg.value <= zydis.ZYDIS_REGISTER_XMM15)))
    {
        if (size == 16) {
            // FIXME: we need to know if this is 2 doubles of 1 float, who
            // knows what breaks due to this
            req.mnemonic = zydis.ZYDIS_MNEMONIC_MOVUPS;
        } else if (size == 8) {
            req.mnemonic = zydis.ZYDIS_MNEMONIC_MOVSD;
        } else {
            req.mnemonic = zydis.ZYDIS_MNEMONIC_MOVSS;
        }
    }

    if ((mnemonic == zydis.ZYDIS_MNEMONIC_MOVD or
        mnemonic == zydis.ZYDIS_MNEMONIC_MOVQ) and
        req.operands[0].type == zydis.ZYDIS_OPERAND_TYPE_MEMORY and
        !(req.operands[1].reg.value >= zydis.ZYDIS_REGISTER_XMM0 and
            req.operands[1].reg.value <= zydis.ZYDIS_REGISTER_XMM15))
    {
        req.mnemonic = zydis.ZYDIS_MNEMONIC_MOV;
    }

    if (mnemonic == zydis.ZYDIS_MNEMONIC_XCHG and
        req.operands[1].type == zydis.ZYDIS_OPERAND_TYPE_MEMORY)
    {
        std.mem.swap(@TypeOf(req.operands[1]), &req.operands[0], &req.operands[1]);
    }

    const status = zydis.ZydisEncoderEncodeInstruction(&req, &buf, &len);
    if (zydis.ZYAN_FAILED(status) != 0) {
        utils.panic("{x} {s} {} {any}\n", .{ status, zydis.ZydisMnemonicGetString(req.mnemonic), args, req.operands[0..fields.len] });
    }

    try self.out.code.appendSlice(self.gpa, buf[0..len]);
}

pub fn binopToMnemonic(op: graph.BinOp, ty: graph.DataType) zydis.ZydisMnemonic {
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

        .fadd => if (ty == .f64) zydis.ZYDIS_MNEMONIC_ADDSD else zydis.ZYDIS_MNEMONIC_ADDSS,
        .fsub => if (ty == .f64) zydis.ZYDIS_MNEMONIC_SUBSD else zydis.ZYDIS_MNEMONIC_SUBSS,
        .fmul => if (ty == .f64) zydis.ZYDIS_MNEMONIC_MULSD else zydis.ZYDIS_MNEMONIC_MULSS,
        .fdiv => if (ty == .f64) zydis.ZYDIS_MNEMONIC_DIVSD else zydis.ZYDIS_MNEMONIC_DIVSS,

        .flt => zydis.ZYDIS_MNEMONIC_SETB,
        .fle => zydis.ZYDIS_MNEMONIC_SETBE,
        .fgt => zydis.ZYDIS_MNEMONIC_SETNBE,
        .fge => zydis.ZYDIS_MNEMONIC_SETNB,
    };
}

pub fn isJump(mnemonic: zydis.ZydisMnemonic) bool {
    return mnemonic == zydis.ZYDIS_MNEMONIC_JMP or
        mnemonic == zydis.ZYDIS_MNEMONIC_JZ or
        mnemonic == zydis.ZYDIS_MNEMONIC_JNZ or
        mnemonic == zydis.ZYDIS_MNEMONIC_JB or
        mnemonic == zydis.ZYDIS_MNEMONIC_JNBE or
        mnemonic == zydis.ZYDIS_MNEMONIC_JBE or
        mnemonic == zydis.ZYDIS_MNEMONIC_JNB or
        mnemonic == zydis.ZYDIS_MNEMONIC_JL or
        mnemonic == zydis.ZYDIS_MNEMONIC_JNLE or
        mnemonic == zydis.ZYDIS_MNEMONIC_JLE or
        mnemonic == zydis.ZYDIS_MNEMONIC_JNL;
}

pub fn getReg(self: X86_64, node: ?*FuncNode) Reg {
    return @enumFromInt(self.allocs[node.?.schedule]);
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

pub fn emitData(self: *X86_64, opts: Mach.DataOptions) void {
    errdefer unreachable;

    try self.out.defineGlobal(
        self.gpa,
        opts.id,
        opts.name,
        .data,
        .local,
        opts.value.init,
        opts.relocs,
        opts.readonly,
    );
}

pub fn finalize(self: *X86_64, opts: Mach.FinalizeOptions) void {
    errdefer unreachable;

    if (opts.optimizations.finalize(opts.builtins, X86_64, self)) return;

    try switch (self.object_format) {
        .elf => root.object.elf.flush(self.out, .x86_64, opts.output),
        .coff => unreachable, //root.object.coff.flush(self.out, .x86_64, out),
    };

    self.memcpy = .invalid;
    self.out.reset();
}

pub fn deinit(self: *X86_64) void {
    self.out.deinit(self.gpa);
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

                        if (isJump(inst.mnemonic)) {
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

                    if (isJump(inst.mnemonic)) {
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
        compile.stderr_behavior = .Ignore;
        const result = try compile.spawnAndWait();
        if (result != .Exited or result.Exited != 0) {
            compile = std.process.Child.init(
                &.{ "zig", "cc", "-nostdlib", "-static", name, "-o", exe_name },
                tmp.arena.allocator(),
            );
            _ = try compile.spawnAndWait();
        }
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
        } else utils.panic("{}\n", .{res});
    }
    return res.Exited;
}
