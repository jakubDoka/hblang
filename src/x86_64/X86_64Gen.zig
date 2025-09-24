const std = @import("std");

const matcher = @import("x86_64.X86_64Gen");
const root = @import("hb");
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Regalloc = root.backend.Regalloc;
const utils = root.utils;
const object = root.object;

const X86_64Gen = @This();
const Func = graph.Func(X86_64Gen);
const FuncNode = Func.Node;
const Move = utils.Move(Reg);

gpa: *utils.Pool,
object_format: enum { elf, coff },
memcpy: Mach.Data.SymIdx = .invalid,
f32s: Mach.Data.SymIdx = .invalid,
f32index: std.ArrayHashMapUnmanaged(f32, void, CtxF32, false) = .{},
f64s: Mach.Data.SymIdx = .invalid,
f64index: std.ArrayHashMapUnmanaged(f64, void, CtxF64, false) = .{},
out: Mach.Data = .{},
allocs: []const u16 = undefined,
ret_count: usize = undefined,
local_relocs: std.ArrayListUnmanaged(Reloc) = undefined,
block_offsets: []u32 = undefined,
arg_base: u32 = undefined,
local_base: u32 = undefined,
slot_base: c_int = undefined,
builtins: Mach.Builtins = undefined,

const CtxF32 = struct {
    pub fn eql(_: @This(), a: f32, b: f32, _: usize) bool {
        return a == b;
    }
    pub fn hash(_: @This(), key: f32) u32 {
        return @bitCast(key);
    }
};

const CtxF64 = struct {
    pub fn eql(_: @This(), a: f64, b: f64, _: usize) bool {
        return a == b;
    }
    pub fn hash(_: @This(), key: f64) u32 {
        const k: packed struct(u64) {
            a: u32,
            b: u32,
        } = @bitCast(key);
        return k.a ^ k.b;
    }
};

const syscall = root.backend.Machine.max_func;
const max_instruction_size = 15;

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

    pub const no_index = Reg.rsp;
    pub const rip = Reg.rbp;
    pub const no_op_rex = rex(.rax, .rax, .rax, false);

    pub fn isScalar(self: Reg) bool {
        return @intFromEnum(self) <= @intFromEnum(Reg.r15);
    }

    pub fn needRexIfSingleByte(self: Reg) bool {
        return self == .rsp or self == .rbp or self == .rsi or self == .rdi;
    }

    pub fn isXmm(self: Reg) bool {
        return @intFromEnum(Reg.xmm0) <= @intFromEnum(self) and @intFromEnum(self) <= @intFromEnum(Reg.xmm15);
    }

    pub fn normalizeXmm(self: Reg) Reg {
        std.debug.assert(self.isXmm());
        return @enumFromInt(@intFromEnum(self) - 16);
    }

    pub fn isStack(self: Reg) bool {
        return @intFromEnum(self) > @intFromEnum(Reg.xmm15);
    }

    pub fn retForDt(dt: graph.DataType) Reg {
        return if (dt.isInt()) .rax else .xmm0;
    }

    pub fn scalarIndex(self: Reg) u8 {
        std.debug.assert(self.isScalar());
        return @intFromEnum(self) & 7;
    }

    pub fn isExtendedScalar(self: Reg) bool {
        return 8 <= @intFromEnum(self) and @intFromEnum(self) < 16;
    }

    //  public static int modrm(MOD mod, int reg, int m_r) {
    //      if( reg == -1 ) reg=0;  // Missing reg in this flavor
    //      // combine all the bits
    //      assert 0 <= reg  &&  reg < 16;
    //      assert 0 <= m_r  &&  m_r < 16;
    //      return (mod.ordinal() << 6) | ((reg & 0x07) << 3) | m_r & 0x07;
    //  }

    pub const Mod = enum(u2) {
        indirect,
        indirect_disp8,
        indirect_disp32,
        direct,

        pub fn rm(self: Mod, reg: Reg, m_r: Reg) u8 {
            return (@as(u8, @intFromEnum(self)) << 6) |
                ((@intFromEnum(reg) & 7) << 3) |
                (@intFromEnum(m_r) & 7);
        }

        pub fn rmSub(self: Mod, sub: u3, m_r: Reg) u8 {
            return self.rm(@enumFromInt(sub), m_r);
        }

        pub fn fromDis(dis: i64) Mod {
            return switch (dis) {
                0 => .indirect,
                std.math.minInt(i8)...-1, 1...std.math.maxInt(i8) => .indirect_disp8,
                else => .indirect_disp32,
            };
        }
    };

    pub fn sib(base: Reg, index: Reg, scale: u64) u8 {
        std.debug.assert(scale == 1 or scale == 2 or scale == 4 or scale == 8);
        return (@as(u8, std.math.log2_int(u64, scale)) << 6) |
            ((@intFromEnum(index) & 7) << 3) |
            (@intFromEnum(base) & 7);
    }

    pub fn rex(reg: Reg, ptr: Reg, idx: Reg, wide: bool) u8 {
        var res: u8 = 0b01000000;

        if (wide) res |= 0b1000;
        if (@intFromEnum(reg) & 0xf >= 8) res |= 0b0100;
        if (@intFromEnum(ptr) & 0xf >= 8) res |= 0b0001;
        if (@intFromEnum(idx) & 0xf >= 8) res |= 0b0010;

        return res;
    }

    pub const VexOpcodeMap = enum(u8) {
        _0F = 1,
        _0F38 = 2,
        _0F3A = 3,
    };

    pub const VexPrefix = enum(u8) {
        none = 0,
        _66 = 1,
        _F3 = 2,
        _F2 = 3,
    };

    pub fn vex3(
        self: Reg,
        vvvv: Reg,
        rm: Reg,
        map: VexOpcodeMap,
        prefix: VexPrefix,
        wide: bool,
        vector_length: bool,
    ) [3]u8 {
        var vex_bytes: [3]u8 = undefined;

        vex_bytes[0] = 0xC4;

        vex_bytes[1] = 0;
        vex_bytes[1] |= ((~@intFromEnum(self) & 0x08) << 4);
        vex_bytes[1] |= (1 << 6);
        vex_bytes[1] |= ((~@intFromEnum(rm) & 0x08) << 2);
        vex_bytes[1] |= (@intFromEnum(map) & 0x1F);

        vex_bytes[2] = 0;
        vex_bytes[2] |= (if (wide) (1 << 7) else 0);
        vex_bytes[2] |= ((~@intFromEnum(vvvv) & 0x0F) << 3);
        vex_bytes[2] |= (if (vector_length) (1 << 2) else 0);
        vex_bytes[2] |= (@intFromEnum(prefix) & 0x03);

        return vex_bytes;
    }

    pub fn stackOffset(self: Reg, slot_offset: u64) u64 {
        return @as(u64, (@intFromEnum(self) - @intFromEnum(Reg.xmm15) - 1)) * 8 + slot_offset;
    }
};

pub const Reloc = struct {
    offset: u32,
    dest: u32,
    class: enum(u8) { rel32 = 4 },
    off: u8,
};

pub const classes = enum {
    pub const FusedMulAdd = extern struct {};
    pub const RepStosb = extern struct {
        base: graph.Store = .{},
    };
    pub const GlobalLoad = extern struct {
        base: graph.Load = .{},
        dis: i32,
        id: u32,

        pub const data_dep_offset = 2;
    };
    pub const ConstGlobalStore = extern struct {
        base: graph.Store = .{},
        dis: i32,
        id: u32,
        imm: i32,

        pub const data_dep_offset = 2;
    };
    pub const GlobalStore = extern struct {
        base: graph.Store = .{},
        dis: i32,
        id: u32,

        pub const data_dep_offset = 2;
    };
    pub const StackLoad = extern struct {
        base: graph.Load = .{},
        dis: i32,

        pub const data_dep_offset = 2;
    };
    pub const StackStore = extern struct {
        base: graph.Store = .{},
        dis: i32,

        pub const data_dep_offset = 2;
    };
    pub const ConstStackStore = extern struct {
        base: graph.Store = .{},
        dis: i32,
        imm: i32,

        pub const data_dep_offset = 2;
    };
    pub const ConstStore = extern struct {
        base: graph.Store = .{},
        dis: i32,
        imm: i32,
    };
    pub const OffsetLoad = extern struct {
        base: graph.Load = .{},
        dis: i32,
    };
    pub const OffsetStore = extern struct {
        base: graph.Store = .{},
        dis: i32,
    };
    pub const OpLoad = extern struct {
        base: graph.Load = .{},
        op: graph.BinOp,
        dis: i32,
    };
    pub const OpStackLoad = extern struct {
        base: graph.Load = .{},
        op: graph.BinOp,
        dis: i32,

        pub const data_dep_offset = 2;
    };
    pub const OpStore = extern struct {
        base: graph.Store = .{},
        op: graph.BinOp,
        dis: i32,
    };
    pub const OpStackStore = extern struct {
        base: graph.Store = .{},
        op: graph.BinOp,
        dis: i32,

        pub const data_dep_offset = 2;
    };
    pub const ConstOpStackStore = extern struct {
        base: graph.Store = .{},
        op: graph.BinOp,
        dis: i32,
        imm: i32,

        pub const data_dep_offset = 2;
    };
    pub const ConstOpStore = extern struct {
        base: graph.Store = .{},
        op: graph.BinOp,
        imm: i32,
        dis: i32,
    };
    pub const ImmOp = extern struct {
        op: graph.BinOp,
        imm: i32,
    };
    pub const CondJump = extern struct {
        base: graph.If,
        op: graph.BinOp,
    };
    pub const F32 = extern struct {
        imm: f32,

        pub const is_clone = true;
    };
    pub const F64 = extern struct {
        imm: f64,

        pub const is_clone = true;
    };
    pub const StackLea = extern struct {
        dis: i32,

        pub const data_dep_offset = 1;
        pub const is_clone = true;
    };
    pub const IndexLea = extern struct {
        dis: i32,
        scale: u8,
    };
};

pub const biased_regs = b: {
    var mask: u64 = 0;
    for (Reg.system_v.caller_saved) |r| {
        mask |= @as(u64, 1) << @intFromEnum(r);
    }
    break :b mask;
};

pub fn clampI32(value: i64) i64 {
    return std.math.clamp(value, std.math.minInt(i32), std.math.maxInt(i32));
}

pub fn unwrapLocal(local: *Func.Node) *Func.Node {
    return if (local.kind == .Local) local.inputs()[1].? else local;
}

// ================== BINDINGS ==================
pub fn getStaticOffset(node: *Func.Node) i64 {
    return switch (node.extra2()) {
        inline .OffsetLoad,
        .OffsetStore,
        .StackLoad,
        .StackStore,
        .ConstStore,
        .ConstStackStore,
        .GlobalLoad,
        .GlobalStore,
        .ConstGlobalStore,
        .ConstOpStore,
        .ConstOpStackStore,
        .OpLoad,
        .OpStackLoad,
        => |extra| extra.dis,
        else => 0,
    };
}

pub fn knownOffset(node: *Func.Node) struct { *Func.Node, i64 } {
    return switch (node.extra2()) {
        .ImmOp => |extra| {
            if (extra.op != .iadd and extra.op != .isub) {
                return .{ node, 0 };
            }
            return .{ node.inputs()[1].?, if (extra.op == .iadd)
                extra.imm
            else
                -extra.imm };
        },
        .StackLea => |extra| .{ node.inputs()[1].?, extra.dis },
        else => .{ node, 0 },
    };
}

pub fn isInterned(kind: Func.Kind) bool {
    return kind == .OffsetLoad or
        kind == .GlobalLoad or
        kind == .OpLoad or
        kind == .OpStackLoad or
        kind == .StackLoad or
        kind == .StackLea or
        kind == .ImmOp or
        kind == .FusedMulAdd;
}

pub fn isSwapped(node: *Func.Node) bool {
    _ = node;
    return false;
}

pub fn postporcessRepStosb(
    func: *Func,
    final: *Func.Node,
    mem: *Func.Node,
    loop_if: *Func.Node,
    store: *Func.Node,
    worklist: *Func.WorkList,
) void {
    const other_mem_succ = for (mem.outputs()) |o| {
        if (o.get() != store) break o.get();
    } else unreachable;

    std.debug.assert(store.data_type == .i8);

    func.setInputNoIntern(other_mem_succ, 1, final);

    func.setInputNoIntern(
        loop_if,
        1,
        func.addIntImm(store.sloc, .i8, 0),
    );

    worklist.add(loop_if);
}

// ================== PEEPHOLES ==================
pub fn idealizeMach(self: *X86_64Gen, func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
    if (Func.idealizeDead({}, func, node, worklist)) |n| return n;

    if (matcher.idealize(self, func, node, worklist)) |n| return n;

    if (node.kind == .StructArg) elim_local: {
        for (node.outputs()) |us| {
            const use = us.get();
            if (((!use.isStore() or use.value() == node) and !use.isLoad()) or use.isSub(graph.MemCpy)) {
                break :elim_local;
            }
        }

        switch (node.extra2()) {
            .StructArg => |n| n.no_address = true,
            else => unreachable,
        }
    }

    return null;
}

pub fn idealize(_: *X86_64Gen, func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
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
pub const Set = struct {
    bits: Mask,
    comptime bit_length: usize = @bitSizeOf(Mask),

    const Mask = u128;

    pub fn init(bits: Mask) Set {
        return .{ .bits = bits };
    }

    pub fn setIntersection(a: *Set, b: Set) void {
        a.bits &= b.bits;
    }

    pub fn count(s: Set) u16 {
        return @popCount(s.bits);
    }

    pub fn findFirstSet(s: Set) ?u16 {
        if (s.bits == 0) return null;
        return @ctz(s.bits);
    }

    pub fn unset(s: *Set, idx: usize) void {
        s.bits &= ~(@as(Mask, 1) << @intCast(idx));
    }

    pub fn clone(s: Set, _: anytype) !Set {
        return s;
    }
};

pub fn setIntersects(a: Set, b: Set) bool {
    return a.bits & b.bits != 0;
}

pub fn setMasks(s: *Set) []u64 {
    return @ptrCast((&s.bits)[0..1]);
}

pub fn floatMask(_: *utils.Arena) Set {
    return .init(0xFFFF_0000);
}

pub fn readIntMask(_: *utils.Arena) Set {
    return .init(0xFFFF);
}

pub fn writeIntMask(_: *utils.Arena) Set {
    return .init(0xFFFF & ~(@as(Set.Mask, 1) << @intFromEnum(Reg.rsp)));
}

pub fn splitFloatMask(_: *utils.Arena) Set {
    return .init(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_0000);
}

pub fn splitIntMask(arena: *utils.Arena) Set {
    return .init(0xFFFF_FFFF_FFFF_FFFF_FFFF_0000_0000 | writeIntMask(arena).bits);
}

pub fn readSplitIntMask(arena: *utils.Arena) Set {
    return .init(0xFFFF_FFFF_FFFF_FFFF_FFFF_0000_0000 | readIntMask(arena).bits);
}

pub fn singleReg(reg: Reg, _: *utils.Arena) Set {
    return .init(@as(Set.Mask, 1) << @intCast(@intFromEnum(reg)));
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
        .RepStosb => @as(u64, 1) << @intFromEnum(Reg.rdi),
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
) Set {
    errdefer unreachable;

    if (node.kind == .MachSplit or node.kind == .Phi) {
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

    if (node.kind == .MemCpy) {
        std.debug.assert(idx >= 2);
        return singleReg(Reg.system_v.args[idx - 2], arena);
    }

    if (node.kind == .Call) {
        std.debug.assert(idx >= 2);
        const extra = node.extra(.Call);
        if (extra.id == syscall) {
            return singleReg(Reg.system_v.syscall_args[idx - 2], arena);
        } else {
            if (extra.id == graph.indirect_call and idx == 2) {
                return readIntMask(arena);
            }

            const ix = idx - 2 - @intFromBool(extra.id == graph.indirect_call);
            const params = @as(graph.Signature, extra.signature).params();
            if (params[ix] == .Stack) return readIntMask(arena);
            var reg_idx: usize = 0;
            var xmm_idx: usize = 0;
            for (params[0..ix]) |p| {
                if (p == .Reg) {
                    if (p.Reg.isFloat()) {
                        xmm_idx += 1;
                    } else {
                        reg_idx += 1;
                    }
                }
            }
            if (params[ix].Reg.isFloat()) {
                std.debug.assert(node.inputs()[idx].?.data_type.isFloat());
                return singleReg(Reg.system_v.float_args[xmm_idx], arena);
            } else {
                std.debug.assert(node.inputs()[idx].?.data_type.isInt());
                return singleReg(Reg.system_v.args[reg_idx], arena);
            }
        }
    }

    if (node.kind == .RepStosb) {
        switch (idx) {
            2 => return singleReg(Reg.rdi, arena),
            3 => return singleReg(Reg.rax, arena),
            4 => return singleReg(Reg.rcx, arena),
            else => unreachable,
        }
    }

    if (node.kind == .Return) {
        std.debug.assert(idx == 3);
        return singleReg(Reg.retForDt(node.inputs()[idx].?.data_type), arena);
    }

    if (node.kind == .Ret) {
        std.debug.assert(idx == 0);
        return singleReg(Reg.retForDt(node.data_type), arena);
    }

    if (node.data_type.isFloat() and idx == 0) {
        return floatMask(arena);
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
        inline .ImmOp, .BinOp, .OpStackLoad => |extra| binOpInPlaceSlot(extra.op),
        .OpLoad => |extra| if (binOpInPlaceSlot(extra.op)) |f| f + 1 else null,
        .FusedMulAdd => 0,
        .UnOp => |extra| switch (@as(graph.UnOp, extra.op)) {
            .ineg, .bnot, .ired, .not => 0,
            .fneg, .fcst, .sext, .uext, .cast, .itf, .fti => return null,
        },
        else => null,
    };
}

// ================== EMIT ==================

pub fn emitFunc(self: *X86_64Gen, func: *Func, opts: Mach.EmitOptions) void {
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

    const sym = try self.out.startDefineFunc(self.gpa.allocator(), id, name, .func, linkage, opts.is_inline);
    defer self.out.endDefineFunc(id);

    if (opts.linkage == .imported) return;

    if (opts.optimizations.apply(X86_64Gen, func, self, id)) return;

    var tmp = utils.Arena.scrath(if (opts.optimizations == .opts)
        opts.optimizations.opts.arena
    else
        null);
    defer tmp.deinit();

    const postorder = func.gcm.postorder;

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

    const local_size: i64 = func.computeStackLayout(0);

    const spill_slot_count = if (self.allocs.len == 0) 0 else std.mem.max(u16, self.allocs) -| 31;
    var stack_size: i64 = std.mem.alignForward(i64, local_size, 8) +
        spill_slot_count * 8;

    var has_call = false;
    var call_slot_size: u64 = 0;
    for (postorder) |bb| {
        if (bb.base.kind == .MemCpy) has_call = true;
        if (bb.base.kind == .CallEnd) {
            const call = bb.base.inputs()[0].?;
            const signature: *graph.Signature = &call.extra(.Call).signature;
            call_slot_size = @max(signature.stackSize(), call_slot_size);
            has_call = true;
        }
    }

    stack_size += @intCast(call_slot_size);

    var pushed_regs: i64 = 0;
    for (Reg.system_v.callee_saved) |r| {
        if (used_regs.contains(r)) {
            pushed_regs += 1;
        }
    }

    const padding = std.mem.alignForward(i64, stack_size + pushed_regs * 8, 16) - stack_size - pushed_regs * 8;

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
                self.ensureInstrSpace();
                // push r
                self.emitSingleOp(0x50, r);
                self.arg_base += 8;
            }
        }

        sym.stack_size = @intCast(self.arg_base);

        if (stack_size != 0) {
            // sub rsp, stack_size
            self.ensureInstrSpace();
            self.emitImmOp(0x81, 0b101, .rsp, stack_size);
        }

        func.computeStructArgLayout();

        break :prelude;
    }

    for (postorder, 0..) |bb, i| {
        self.block_offsets[bb.base.schedule] = @intCast(self.out.code.items.len);
        std.debug.assert(bb.base.schedule == i);

        self.emitBlockBody(&bb.base);
        const last = bb.base.outputs()[bb.base.output_len - 1].get();
        if (last.outputs().len == 0) {
            std.debug.assert(last.kind == .Return);

            if (stack_size != 0) {
                // add rsp, stack_size
                self.ensureInstrSpace();
                self.emitImmOp(0x81, 0b000, .rsp, stack_size);
            }

            var iter = std.mem.reverseIterator(Reg.system_v.callee_saved);
            while (@as(?Reg, iter.next())) |r| {
                if (used_regs.contains(r)) {
                    // pop r
                    self.ensureInstrSpace();
                    self.emitSingleOp(0x58, r);
                }
            }

            // ret
            self.emitByte(0xc3);
        } else if (i + 1 == last.outputs()[@intFromBool(last.isSwapped())].get().schedule) {
            // noop
        } else if (last.kind == .Never) {
            // noop
        } else if (last.kind == .Trap) {
            // noop
        } else {
            std.debug.assert(last.outputs()[0].get().isBasicBlockStart());
            self.local_relocs.appendAssumeCapacity(.{
                .dest = last.outputs()[@intFromBool(last.isSwapped())].get().schedule,
                .offset = @intCast(self.out.code.items.len),
                .off = 1,
                .class = .rel32,
            });
            // jmp dest
            self.ensureInstrSpace();
            try self.out.code.appendSlice(self.gpa.allocator(), &.{ 0xE9, 0, 0, 0, 0 });
        }
    }

    for (self.local_relocs.items) |rl| {
        const size = @intFromEnum(rl.class);

        const dst_offset: i64 = self.block_offsets[rl.dest];
        const jump = dst_offset - rl.offset - size - rl.off; // welp we learned

        @memcpy(
            self.out.code.items[rl.offset + rl.off ..][0..size],
            @as(*const [8]u8, @ptrCast(&jump))[0..size],
        );
    }
}

pub fn emitBlockBody(self: *X86_64Gen, block: *FuncNode) void {
    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    for (block.outputs()) |in| {
        const instr = in.get();
        const inps = instr.dataDeps();

        self.ensureInstrSpace();

        switch (instr.extra2()) {
            .FramePointer => {},
            .CInt => |extra| {
                if (extra.value == 0) {
                    // xor dst, dst
                    self.emitRegOp(0x31, self.getReg(instr), self.getReg(instr));
                } else {
                    // mov dst, $imm
                    self.emitSingleOp(0xb8, self.getReg(instr));
                    self.emitImm(i64, extra.value);
                }
            },
            inline .F32, .F64 => |extra| {
                const idx = &@field(self, @typeName(@TypeOf(extra.imm)) ++ "index");
                const sym = &@field(self, @typeName(@TypeOf(extra.imm)) ++ "s");

                const ty = @field(graph.DataType, @typeName(@TypeOf(extra.imm)));
                self.emitMemStoreOrLoad(ty, self.getReg(instr), .rip, null, false);
                const res = try idx.getOrPut(self.gpa.allocator(), extra.imm);
                const dis: i31 = @intCast(@intFromPtr(res.key_ptr) - @intFromPtr(idx.entries.bytes));
                try self.out.addReloc(self.gpa.allocator(), sym, .@"4", dis - 4, 4);
            },
            .MemCpy => {
                // call id
                self.emitBytes(&.{ 0xe8, 0, 0, 0, 0 });
                if (self.builtins.memcpy == std.math.maxInt(u32)) {
                    if (self.memcpy == .invalid)
                        try self.out.importSym(self.gpa.allocator(), &self.memcpy, "memcpy", .func);
                    try self.out.addReloc(self.gpa.allocator(), &self.memcpy, .@"4", -4, 4);
                } else {
                    try self.out.addFuncReloc(self.gpa.allocator(), self.builtins.memcpy, .@"4", -4, 4);
                }
            },
            .MachSplit => {
                var lhs, var rhs = .{ self.getReg(instr), self.getReg(inps[0]) };
                if (lhs == rhs) continue;

                if (lhs.isScalar() and rhs.isScalar()) {
                    // mov dst, src
                    self.emitRegOp(0x89, rhs, lhs);
                } else if (lhs.isXmm() and rhs.isXmm()) {
                    // movs[s/d] dst, src
                    self.emitByte(if (instr.data_type == .f32) 0xf3 else 0xf2);
                    self.emitRex(rhs, lhs, .rax, instr.data_type.size());
                    self.emitBytes(&.{ 0x0f, 0x11, Reg.Mod.direct.rm(rhs, lhs) });
                } else b: {
                    const lhs_stack = lhs.isStack();

                    if (lhs_stack and rhs.isStack()) {
                        // push [rsp+dis]
                        self.emitByte(0xff);
                        const lhs_off = lhs.stackOffset(@intCast(self.slot_base));
                        self.emitIndirectAddr(@enumFromInt(0b110), .rsp, .no_index, 1, @intCast(lhs_off));

                        // pop [rsp+dis]
                        self.emitByte(0x8f);
                        const rhs_off = rhs.stackOffset(@intCast(self.slot_base));
                        self.emitIndirectAddr(@enumFromInt(0b000), .rsp, .no_index, 1, @intCast(rhs_off));

                        break :b;
                    }

                    if (lhs_stack) {
                        std.mem.swap(Reg, &lhs, &rhs);
                    }

                    if (lhs.isXmm()) {
                        self.emitByte(if (instr.data_type == .f32) 0xf3 else 0xf2);
                        self.emitRex(lhs, .rsp, .rax, instr.data_type.size());
                        self.emitBytes(&.{ 0x0f, if (lhs_stack) 0x11 else 0x10 });
                    } else {
                        self.emitRex(lhs, .rsp, .rax, instr.data_type.size());
                        self.emitByte(if (lhs_stack) 0x89 else 0x8b);
                    }

                    const offset = rhs.stackOffset(@intCast(self.slot_base));
                    self.emitIndirectAddr(lhs, .rsp, .no_index, 1, @intCast(offset));
                }
            },
            .Phi => {},
            .GlobalAddr => |extra| {
                // lea dst, [rip+reloc]
                const dst = self.getReg(instr);
                self.emitRex(dst, .rax, .rax, 8);
                self.emitByte(0x8d);
                self.emitIndirectAddr(dst, .rip, .no_index, 1, null);

                try self.out.addGlobalReloc(self.gpa.allocator(), extra.id, .@"4", -4, 4);
            },
            .FuncAddr => |extra| {
                // lea dst, [rip+reloc]
                const dst = self.getReg(instr);
                self.emitRex(dst, .rax, .rax, 8);
                self.emitByte(0x8d);
                self.emitIndirectAddr(dst, .rip, .no_index, 1, null);

                try self.out.addFuncReloc(self.gpa
                    .allocator(), extra.id, .@"4", -4, 4);
            },
            .RepStosb => {
                // cld
                // rep stosb
                self.emitBytes(&.{ 0xfc, 0xf3, 0xaa });
            },
            .ConstGlobalStore => |extra| {
                // mov [rip+dis+offset], $vl
                const vl = extra.imm;
                const dis: i31 = @intCast(extra.dis);
                const imm_size: i16 = @intCast(@min(instr.data_type.size(), 4));
                self.emitMemConstStore(instr.data_type, vl, .rip, null);
                try self.out.addGlobalReloc(
                    self.gpa.allocator(),
                    extra.id,
                    .@"4",
                    dis - 4 - imm_size,
                    @intCast(4 + imm_size),
                );
            },
            .GlobalStore => |extra| {
                // mov [rip+dis+offset], src
                const src = self.getReg(inps[0]);
                self.emitMemStoreOrLoad(instr.data_type, src, .rip, null, true);
                const dis: i31 = @intCast(extra.dis);
                try self.out.addGlobalReloc(self.gpa.allocator(), extra.id, .@"4", dis - 4, 4);
            },
            .GlobalLoad => |extra| {
                // mov dst, [rip+dis+offset]
                const dst = self.getReg(instr);
                self.emitMemStoreOrLoad(instr.data_type, dst, .rip, null, false);
                const dis: i31 = @intCast(extra.dis);
                try self.out.addGlobalReloc(self.gpa.allocator(), extra.id, .@"4", dis - 4, 4);
            },
            .LocalAlloc => {},
            .Local => {
                // lea dst, [rsp+dis]
                const dst = self.getReg(instr);
                const dis = instr.inputs()[1].?.extra(.LocalAlloc).size + self.local_base;
                self.emitStackLea(dst, @intCast(dis));
            },
            .IndexLea => {
                // lea dst, [base+dis+index*scale]
                const dst = self.getReg(instr);
                const base = self.getReg(inps[0]);
                const index = self.getReg(inps[1]);
                const scale = instr.extra(.IndexLea).scale;
                const dis = instr.extra(.IndexLea).dis;

                self.emitRex(dst, base, index, 8);
                self.emitByte(0x8d);
                self.emitIndirectAddr(dst, base, index, @as(u64, 1) << @intCast(scale), dis);
            },
            .StackLea => {
                // lea dst, [rsp+dis]
                const dst = self.getReg(instr);
                const dis = @as(i32, @intCast(instr.inputs()[1].?.extra(.LocalAlloc).size + self.local_base)) +
                    instr.extra(.StackLea).dis;
                self.emitStackLea(dst, dis);
            },
            .StructArg => |extra| if (!extra.no_address) {
                // lea dst, [rsp+dis]
                const dst = self.getReg(instr);
                const dis = instr.extra(.StructArg).spec.size + self.arg_base;
                self.emitStackLea(dst, @intCast(dis));
            },
            .StackArgOffset => {
                // lea dst, [rsp+dis]
                const dst = self.getReg(instr);
                const dis = instr.extra(.StackArgOffset).offset;
                self.emitStackLea(dst, @intCast(dis));
            },
            inline .OffsetLoad, .StackLoad => |extra, t| {
                // mov dst, [bse+dis]
                const dst = self.getReg(instr);
                const bse = if (t == .OffsetLoad) self.getReg(inps[0]) else .rsp;
                const dis: i32 = if (t == .OffsetLoad) extra.dis else (extra.dis + self.stackBaseOf(instr));

                self.emitMemStoreOrLoad(instr.data_type, dst, bse, dis, false);
            },
            inline .OffsetStore, .StackStore => |extra, t| {
                // mov [dst+dis], vl
                const dst = if (t == .OffsetStore) self.getReg(inps[0]) else .rsp;
                const vl = if (t == .OffsetStore) self.getReg(inps[1]) else self.getReg(inps[0]);
                const dis: i32 = if (t == .OffsetStore) extra.dis else (extra.dis + self.stackBaseOf(instr));

                self.emitMemStoreOrLoad(instr.data_type, vl, dst, dis, true);
            },
            inline .ConstStore, .ConstStackStore => |extra, t| {
                // mov [dst+dis], $vl
                const dst = if (t == .ConstStore) self.getReg(inps[0]) else .rsp;
                const vl = extra.imm;
                const dis: i32 = if (t == .ConstStore) extra.dis else (extra.dis + self.stackBaseOf(instr));

                self.emitMemConstStore(instr.data_type, vl, dst, dis);
            },
            .Call => |extra| {
                const call = instr.extra(.Call);

                if (extra.id == syscall) {
                    self.emitBytes(&.{ 0x0f, 0x05 });
                } else if (extra.id == graph.indirect_call) {
                    const ptr = self.getReg(inps[0]);
                    // call ptr
                    self.emitRexNoReg(ptr, .rax, 0);
                    self.emitBytes(&.{ 0xff, Reg.Mod.direct.rmSub(0b010, ptr) });
                } else {
                    // call id
                    self.emitBytes(&.{ 0xe8, 0, 0, 0, 0 });

                    try self.out.addFuncReloc(self.gpa.allocator(), call.id, .@"4", -4, 4);
                }
            },
            .Trap => {
                switch (instr.extra(.Trap).code) {
                    graph.unreachable_func_trap,
                    graph.infinite_loop_trap,
                    => return,
                    // ud2
                    0 => self.emitBytes(&.{ 0x0f, 0x0b }),
                    else => unreachable,
                }
            },
            .If => {
                const cond = self.getReg(inps[0]);
                const cond_size = inps[0].data_type.size();

                const opcode: u8 = switch (inps[0].data_type) {
                    .i8 => 0x84,
                    .i16, .i32, .i64 => 0x85,
                    else => unreachable,
                };

                // test cond, cond
                self.emitRex(cond, cond, .rax, cond_size);
                self.emitBytes(&.{ opcode, Reg.Mod.direct.rm(cond, cond) });

                self.local_relocs.appendAssumeCapacity(.{
                    .dest = instr.outputs()[1].get().schedule,
                    .offset = @intCast(self.out.code.items.len),
                    .class = .rel32,
                    .off = 2,
                });
                // jz dest
                self.emitBytes(&.{ 0x0f, 0x84, 0, 0, 0, 0 });
            },
            .CondJump => |extra| {
                const lhs = self.getReg(inps[0]);
                const rhs = self.getReg(inps[1]);
                const oper_dt = inps[0].data_type;

                self.emitBinopCmp(lhs, rhs, oper_dt);

                self.local_relocs.appendAssumeCapacity(.{
                    .dest = instr.outputs()[1].get().schedule,
                    .offset = @intCast(self.out.code.items.len),
                    .class = .rel32,
                    .off = 2,
                });

                // j[op] dst
                self.emitBytes(&.{ 0x0f, jmpCompOp(extra.op), 0, 0, 0, 0 });
            },
            inline .OpLoad, .OpStackLoad => |extra, t| {
                const op = extra.op;
                const op_dt = instr.data_type;
                const dst = self.getReg(instr);
                const lhs = if (t == .OpLoad) self.getReg(inps[1]) else self.getReg(inps[0]);
                const base = if (t == .OpLoad) self.getReg(inps[0]) else .rsp;
                const dis = if (t == .OpLoad) extra.dis else (extra.dis + self.stackBaseOf(instr));

                switch (op) {
                    .iadd, .isub, .bor, .band, .bxor => {
                        std.debug.assert(lhs == dst);

                        if (op_dt == .i16) self.emitByte(0x66);
                        self.emitRexBinop(dst, base, .rax, op_dt.size());
                        const opcode: u8 = switch (op) {
                            .iadd => 0x03,
                            .band => 0x23,
                            .bor => 0x0b,
                            .bxor => 0x33,
                            .isub => 0x2b,
                            else => unreachable,
                        };
                        self.emitByte(opcode);
                        self.emitIndirectAddr(dst, base, .no_index, 1, dis);
                    },
                    else => utils.panic("{}", .{op}),
                }
            },
            inline .OpStore, .OpStackStore => |extra, t| {
                const op = extra.op;
                const base = if (t == .OpStore) self.getReg(inps[0]) else .rsp;
                const rhs = if (t == .OpStore) self.getReg(inps[1]) else self.getReg(inps[0]);
                const dis = if (t == .OpStore) extra.dis else (extra.dis + self.stackBaseOf(instr));

                switch (op) {
                    .iadd, .isub, .bor, .band, .bxor => {
                        if (instr.data_type == .i16) self.emitByte(0x66);
                        self.emitRexBinop(rhs, base, .rax, instr.data_type.size());
                        const opcode: u8 = switch (op) {
                            .iadd => 0x01,
                            .band => 0x21,
                            .bor => 0x09,
                            .bxor => 0x31,
                            .isub => 0x29,
                            else => unreachable,
                        };
                        self.emitByte(opcode);
                        self.emitIndirectAddr(rhs, base, .no_index, 1, dis);
                    },
                    else => utils.panic("{}", .{op}),
                }
            },
            inline .ConstOpStore, .ConstOpStackStore => |extra, t| {
                const op = extra.op;
                const base = if (t == .ConstOpStore) self.getReg(inps[0]) else .rsp;
                const rhs = extra.imm;
                const crhs = std.math.cast(i8, rhs);
                const dis = if (t == .ConstOpStore) extra.dis else (extra.dis + self.stackBaseOf(instr));

                switch (op) {
                    .iadd, .isub, .bor, .band, .bxor => {
                        if (instr.data_type == .i16) self.emitByte(0x66);
                        self.emitRexNoReg(base, .rax, instr.data_type.size());
                        const sub_opcode: u8 = switch (op) {
                            .iadd => 0b000,
                            .band => 0b100,
                            .bor => 0b001,
                            .bxor => 0b110,
                            .isub => 0b101,
                            else => unreachable,
                        };

                        switch (instr.data_type) {
                            .i32, .i64, .i16 => self.emitByte(if (crhs == null) 0x81 else 0x83),
                            .i8 => self.emitByte(0x80),
                            else => utils.panic("{}", .{instr.data_type}),
                        }

                        self.emitIndirectAddr(@enumFromInt(sub_opcode), base, .no_index, 1, dis);

                        if (crhs) |c| {
                            self.emitImm(i8, c);
                        } else {
                            switch (instr.data_type) {
                                .i8 => self.emitImm(i8, @intCast(rhs)),
                                .i16 => self.emitImm(i16, @intCast(rhs)),
                                .i32, .i64 => self.emitImm(i32, @intCast(rhs)),
                                else => unreachable,
                            }
                        }
                    },
                    else => utils.panic("{}", .{op}),
                }
            },
            .ImmOp => |extra| {
                const op = extra.op;
                const op_dt = instr.inputs()[1].?.data_type;
                const dst = self.getReg(instr);
                const lhs = self.getReg(inps[0]);
                const rhs = extra.imm;
                const crhs = std.math.cast(i8, rhs);

                switch (op) {
                    .imul => unreachable,
                    .ushr, .ishl, .sshr => {
                        std.debug.assert(dst == lhs);

                        const opcode: u8 = switch (instr.data_type) {
                            .i8 => 0xC0,
                            .i16, .i32, .i64 => 0xC1,
                            else => unreachable,
                        };

                        const sub_opcode: u3 = switch (op) {
                            .ishl => 0b100,
                            .ushr => 0b101,
                            .sshr => 0b111,
                            else => unreachable,
                        };

                        if (instr.data_type == .i16) self.emitByte(0x66);
                        self.emitRexNoReg(dst, .rax, instr.data_type.size());
                        self.emitBytes(&.{ opcode, Reg.Mod.direct.rmSub(sub_opcode, dst) });
                        self.emitImm(i8, @intCast(rhs));
                    },
                    .iadd, .isub, .bor, .band, .bxor => {
                        std.debug.assert(dst == lhs);

                        if (instr.data_type == .i16) self.emitByte(0x66);
                        self.emitRexNoReg(dst, .rax, instr.data_type.size());

                        const inc_dec_op: u8 = switch (instr.data_type) {
                            .i8 => 0xFE,
                            .i16, .i32, .i64 => 0xFF,
                            else => unreachable,
                        };
                        if (op == .iadd and rhs == 1) {
                            // inc dst
                            self.emitBytes(&.{ inc_dec_op, Reg.Mod.direct.rmSub(0, dst) });
                        } else if (op == .isub and rhs == 1) {
                            // dec dst
                            self.emitBytes(&.{ inc_dec_op, Reg.Mod.direct.rmSub(1, dst) });
                        } else {

                            // op dst, $rhs
                            const opcode: u8 = switch (instr.data_type) {
                                .i8 => 0x80,
                                .i16, .i32, .i64 => if (crhs == null) 0x81 else 0x83,
                                else => unreachable,
                            };

                            const sub_opcode: u3 = switch (op) {
                                .iadd => 0b000,
                                .bor => 0b001,
                                .band => 0b100,
                                .isub => 0b101,
                                .bxor => 0b110,
                                else => unreachable,
                            };

                            if (instr.data_type == .i16) self.emitByte(0x66);
                            self.emitRexNoReg(dst, .rax, instr.data_type.size());
                            self.emitBytes(&.{ opcode, Reg.Mod.direct.rmSub(sub_opcode, dst) });

                            if (crhs) |c| {
                                self.emitImm(i8, c);
                            } else {
                                switch (instr.data_type) {
                                    .i8 => self.emitImm(i8, @intCast(rhs)),
                                    .i16 => self.emitImm(i16, @intCast(rhs)),
                                    .i32, .i64 => self.emitImm(i32, @intCast(rhs)),
                                    else => unreachable,
                                }
                            }
                        }
                    },
                    .udiv, .sdiv, .smod, .umod, .fadd, .fsub => unreachable,
                    .fmul, .fdiv, .fgt, .flt, .fge, .fle => unreachable,
                    .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt, .slt => {
                        // cmp lhs, $rhs
                        const opcode: u8 = switch (op_dt) {
                            .i8 => 0x80,
                            .i16, .i32, .i64 => if (crhs == null) 0x81 else 0x83,
                            else => unreachable,
                        };

                        if (op_dt == .i16) self.emitByte(0x66);
                        self.emitRexNoReg(lhs, .rax, op_dt.size());
                        self.emitBytes(&.{ opcode, Reg.Mod.direct.rmSub(0b111, lhs) });

                        if (crhs) |c| {
                            self.emitImm(i8, c);
                        } else {
                            switch (op_dt) {
                                .i8 => self.emitImm(i8, @intCast(rhs)),
                                .i16 => self.emitImm(i16, @intCast(rhs)),
                                .i32, .i64 => self.emitImm(i32, @intCast(rhs)),
                                else => unreachable,
                            }
                        }

                        // setx dst
                        self.emitRexNoReg(dst, .rax, 1);
                        self.emitBytes(&.{
                            0x0F,
                            setCompOp(op),
                            Reg.Mod.direct.rmSub(0b000, dst),
                        });

                        // movzx dst, al
                        self.emitRex(dst, dst, .rax, 8);
                        self.emitBytes(&.{ 0x0F, 0xB6, Reg.Mod.direct.rm(dst, dst) });
                    },
                }
            },
            .FusedMulAdd => {
                const dst = self.getReg(instr);
                const a = self.getReg(inps[0]);
                const b = self.getReg(inps[1]);
                const c = self.getReg(inps[2]);

                std.debug.assert(instr.data_type == .f32 or instr.data_type == .f64);
                std.debug.assert(dst == a);

                // vfmadd231s[s/d] a, b, c
                const wide = instr.data_type == .f64;
                self.emitBytes(&Reg.vex3(a, b, c, ._0F38, ._66, wide, false));
                self.emitBytes(&.{ 0xB9, Reg.Mod.direct.rm(a, c) });
            },
            .BinOp => |extra| {
                const op = extra.op;
                const size = instr.data_type.size();
                const op_dt = instr.inputs()[1].?.data_type;
                const dst = self.getReg(instr);
                const lhs = self.getReg(inps[0]);
                const rhs = self.getReg(inps[1]);

                switch (op) {
                    .ushr, .ishl, .sshr => {
                        std.debug.assert(lhs == dst);
                        std.debug.assert(rhs == .rcx);

                        if (instr.data_type == .i16) self.emitByte(0x66);
                        self.emitRexBinop(dst, lhs, .rax, instr.data_type.size());

                        const opcode: u8 = switch (instr.data_type) {
                            .i8 => 0xD2,
                            .i16, .i32, .i64 => 0xD3,
                            else => unreachable,
                        };

                        const sub_opcode: u3 = switch (op) {
                            .ishl => 0b100,
                            .ushr => 0b101,
                            .sshr => 0b111,
                            else => unreachable,
                        };

                        self.emitBytes(&.{ opcode, Reg.Mod.direct.rmSub(sub_opcode, lhs) });
                    },
                    .fadd, .fsub, .fmul, .fdiv => {
                        std.debug.assert(lhs == dst);

                        switch (instr.data_type) {
                            .f32 => self.emitByte(0xF3),
                            .f64 => self.emitByte(0xF2),
                            else => unreachable,
                        }
                        self.emitRexBinop(dst, rhs, .rax, size);

                        const opcode: u8 = switch (op) {
                            .fadd => 0x58,
                            .fsub => 0x5c,
                            .fmul => 0x59,
                            .fdiv => 0x5e,
                            else => unreachable,
                        };

                        self.emitBytes(&.{ 0x0F, opcode, Reg.Mod.direct.rm(dst, rhs) });
                    },
                    .imul => {
                        std.debug.assert(lhs == dst);

                        self.emitRexBinop(dst, rhs, .rax, @max(size, 4));
                        self.emitBytes(&.{ 0x0F, 0xAF, Reg.Mod.direct.rm(dst, rhs) });
                    },
                    .iadd, .isub, .bor, .band, .bxor => {
                        std.debug.assert(lhs == dst);

                        self.emitRexBinop(rhs, dst, .rax, @max(size, 4));
                        var opcode: u8 = switch (op) {
                            .iadd => 0x00,
                            .isub => 0x28,
                            .bor => 0x08,
                            .band => 0x20,
                            .bxor => 0x30,
                            else => unreachable,
                        };
                        opcode += 1;

                        self.emitBytes(&.{ opcode, Reg.Mod.direct.rm(rhs, dst) });
                    },
                    .udiv, .sdiv, .smod, .umod => {
                        // this is kind of fucked but eh,
                        // we need a better support from the regalloc
                        std.debug.assert(lhs == .rax);
                        std.debug.assert(rhs != .rdx);
                        const dest_reg: Reg = if (op == .udiv or op == .sdiv) .rax else .rdx;
                        if (dst != dest_reg) {
                            utils.panic("{} {} {} {f}", .{ dst, dest_reg, op, instr });
                        }

                        // div rhs
                        self.prepareDivRegs(op, size);
                        if (instr.data_type == .i16) self.emitByte(0x66);
                        self.emitRexNoReg(rhs, .rax, size);

                        const opcode: u8 = switch (instr.data_type) {
                            .i8 => 0xF6,
                            .i16, .i32, .i64 => 0xF7,
                            else => unreachable,
                        };

                        const sub_opcode: u3 = switch (op) {
                            .udiv, .umod => 0b110,
                            .sdiv, .smod => 0b111,
                            else => unreachable,
                        };

                        self.emitBytes(&.{ opcode, Reg.Mod.direct.rmSub(sub_opcode, rhs) });

                        if (size == 1 and dest_reg == .rdx) {
                            // mov al, ah
                            self.emitBytes(&.{ 0x88, 0xe2 });
                        }
                    },
                    .fgt, .flt, .fge, .fle, .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt, .slt => {
                        self.emitBinopCmp(lhs, rhs, op_dt);

                        // set[op] dst
                        self.emitRexNoReg(dst, .rax, 1);
                        self.emitBytes(&.{
                            0x0F,
                            setCompOp(op),
                            Reg.Mod.direct.rmSub(0b000, dst),
                        });

                        // movzx dst, al
                        self.emitRex(dst, dst, .rax, 8);
                        self.emitBytes(&.{ 0x0F, 0xB6, Reg.Mod.direct.rm(dst, dst) });
                    },
                }
            },
            .UnOp => |extra| {
                const op = extra.op;
                const size = instr.data_type.size();
                var dst = self.getReg(instr);
                const src_dt = inps[0].data_type;
                const src_size = src_dt.size();
                var src = self.getReg(inps[0]);

                std.debug.assert(dst == src or switch (op) {
                    .not, .bnot, .ineg, .ired => false,
                    else => true,
                });

                switch (op) {
                    .ired => {},
                    .sext => {
                        std.debug.assert(src_size < size);

                        if (instr.data_type == .i16) self.emitByte(0x66);
                        const opcode: []const u8 = switch (size << 4 | src_size) {
                            0x21, 0x41, 0x81 => &.{ 0x0F, 0xBE },
                            0x42, 0x82 => &.{ 0x0F, 0xBf },
                            0x84 => &.{0x63},
                            else => unreachable,
                        };

                        const rex = Reg.rex(dst, src, .rax, size == 8);
                        if (rex != Reg.no_op_rex or
                            (src_size == 1 and src.needRexIfSingleByte()))
                        {
                            self.emitByte(rex);
                        }

                        self.emitBytes(opcode);
                        self.emitBytes(&.{Reg.Mod.direct.rm(dst, src)});
                    },
                    .uext => {
                        if (src_size >= size) {
                            utils.panic("{} {f} {f}", .{ src_size, instr, inps[0] });
                        }

                        if (instr.data_type == .i16) self.emitByte(0x66);
                        const opcode: []const u8 = switch (size << 4 | src_size) {
                            0x21, 0x41, 0x81 => &.{ 0x0F, 0xB6 },
                            0x42, 0x82 => &.{ 0x0F, 0xB7 },
                            0x84 => &.{0x89},
                            else => unreachable,
                        };

                        if (src_size == 4) std.mem.swap(Reg, &src, &dst);

                        const rex = Reg.rex(dst, src, .rax, size == 8 and src_size != 4);
                        if (rex != Reg.no_op_rex or
                            (src_size == 1 and src.needRexIfSingleByte()))
                        {
                            self.emitByte(rex);
                        }

                        self.emitBytes(opcode);
                        self.emitBytes(&.{Reg.Mod.direct.rm(dst, src)});
                    },
                    .not => {
                        if (instr.data_type == .i16) self.emitByte(0x66);
                        self.emitRexNoReg(dst, .rax, instr.data_type.size());

                        // op dst, $rhs
                        const opcode: u8 = switch (instr.data_type) {
                            .i8 => 0x80,
                            .i16, .i32, .i64 => 0x83,
                            else => unreachable,
                        };

                        if (instr.data_type == .i16) self.emitByte(0x66);
                        self.emitRexNoReg(dst, .rax, instr.data_type.size());
                        self.emitBytes(&.{ opcode, Reg.Mod.direct.rmSub(0b110, dst) });
                        self.emitImm(i8, 1);
                    },
                    .bnot, .ineg => {
                        // op dst
                        if (instr.data_type == .i16) self.emitByte(0x66);
                        self.emitRexNoReg(dst, .rax, instr.data_type.size());

                        const opcode: u8 = switch (instr.data_type) {
                            .i8 => 0xF6,
                            .i16, .i32, .i64 => 0xF7,
                            else => unreachable,
                        };

                        const sub_opcode: u3 = switch (op) {
                            .bnot => 0b010,
                            .ineg => 0b011,
                            else => unreachable,
                        };

                        self.emitBytes(&.{ opcode, Reg.Mod.direct.rmSub(sub_opcode, dst) });
                    },
                    .cast => {
                        std.debug.assert(src_size == size);
                        std.debug.assert(src_size == 8 or src_size == 4);

                        const opcode: u8 = switch (src_dt) {
                            .f32, .f64 => 0x7e,
                            .i32, .i64 => 0x6e,
                            else => unreachable,
                        };

                        self.emitByte(0x66);
                        self.emitRex(dst, src, .rax, src_size);
                        self.emitBytes(&.{ 0x0f, opcode, Reg.Mod.direct.rm(dst, src) });
                    },
                    .fti => {
                        switch (src_dt) {
                            .f32 => self.emitByte(0xF3),
                            .f64 => self.emitByte(0xF2),
                            else => unreachable,
                        }
                        self.emitRex(dst, src, .rax, size);
                        self.emitBytes(&.{ 0x0F, 0x2C, Reg.Mod.direct.rm(dst, src) });
                    },
                    .itf => {
                        switch (instr.data_type) {
                            .f32 => self.emitByte(0xF3),
                            .f64 => self.emitByte(0xF2),
                            else => unreachable,
                        }
                        self.emitRex(dst, src, .rax, src_size);
                        self.emitBytes(&.{ 0x0F, 0x2A, Reg.Mod.direct.rm(dst, src) });
                    },
                    .fcst => {
                        switch (src_dt) {
                            .f32 => self.emitByte(0xF3),
                            .f64 => self.emitByte(0xF2),
                            else => unreachable,
                        }
                        self.emitRex(dst, src, .rax, 0);
                        self.emitBytes(&.{ 0x0F, 0x5a, Reg.Mod.direct.rm(dst, src) });
                    },
                    .fneg => unreachable,
                }
            },
            .Arg, .Ret, .MemJoin, .Mem, .Never, .Jmp, .Return => {},
            else => {
                utils.panic("{any}", .{instr});
            },
        }
    }
}

pub fn prepareDivRegs(self: *X86_64Gen, mnemonic: graph.BinOp, size: u64) void {
    if (mnemonic == .udiv or mnemonic == .umod) {
        if (size == 1) {
            // movzx rax, al
            self.emitRex(.rax, .rax, .rax, 8);
            self.emitBytes(&.{ 0x0F, 0xB6, Reg.Mod.direct.rm(.rax, .rax) });
        } else {
            // xor rdx, rdx
            if (size == 2) self.emitByte(0x66);
            self.emitRex(.rdx, .rdx, .rax, size);
            self.emitBytes(&.{ 0x31, Reg.Mod.direct.rm(.rdx, .rdx) });
        }
    } else {
        switch (size) {
            // movsx rax, al
            1 => {
                self.emitRex(.rax, .rax, .rax, 8);
                self.emitBytes(&.{ 0x0F, 0xBE, Reg.Mod.direct.rm(.rax, .rax) });
            },
            // cwd
            2 => self.emitBytes(&.{ 0x66, 0x99 }),
            // cdq
            4 => self.emitBytes(&.{0x99}),
            // cqo
            8 => self.emitBytes(&.{ 0x48, 0x99 }),
            else => unreachable,
        }
    }
}

pub const SReg = struct { Reg, usize };
pub const BRegOff = struct { Reg, i32, u16 };
pub const Rip = struct {};
pub const SizeHint = struct { bytes: u64 };

pub fn ensureInstrSpace(self: *X86_64Gen) void {
    self.out.code.ensureUnusedCapacity(
        self.gpa.allocator(),
        max_instruction_size,
    ) catch unreachable;
}

pub fn stackBaseOf(self: *X86_64Gen, instr: *Func.Node) i32 {
    return @intCast(switch (instr.inputs()[2].?.extra2()) {
        .LocalAlloc => |n| n.size + self.local_base,
        .StructArg => |n| n.spec.size + self.arg_base,
        else => utils.panic("{f}", .{instr.inputs()[2].?}),
    });
}

pub fn emitBinopCmp(self: *X86_64Gen, lhs: Reg, rhs: Reg, oper_dt: graph.DataType) void {
    // cmp lhs, rhs
    if (oper_dt == .i16 or oper_dt == .f64) self.emitByte(0x66);
    self.emitRexBinop(lhs, rhs, .rax, oper_dt.size());

    const opcode: []const u8 = switch (oper_dt) {
        .i8 => &.{0x3a},
        .i16, .i32, .i64 => &.{0x3b},
        .f32, .f64 => &.{ 0x0f, 0x2f },
        else => unreachable,
    };

    self.emitBytes(opcode);
    self.emitBytes(&.{Reg.Mod.direct.rm(lhs, rhs)});
}

pub fn emitMemConstStore(
    self: *X86_64Gen,
    dt: graph.DataType,
    vl: i64,
    bse: Reg,
    dis: ?i64,
) void {
    switch (dt) {
        .i16 => self.emitByte(0x66),
        else => {},
    }

    self.emitRexNoReg(bse, .rax, dt.size());

    switch (dt) {
        .i16, .i32, .i64 => self.emitByte(0xc7),
        .i8 => self.emitByte(0xc6),
        else => utils.panic("{}", .{dt}),
    }
    self.emitIndirectAddr(.rax, bse, .no_index, 1, dis);

    switch (dt) {
        .i8 => self.emitImm(i8, @intCast(vl)),
        .i16 => self.emitImm(i16, @intCast(vl)),
        .i32, .i64 => self.emitImm(i32, @intCast(vl)),
        else => unreachable,
    }
}

pub fn emitMemStoreOrLoad(
    self: *X86_64Gen,
    dt: graph.DataType,
    reg: Reg,
    bse: Reg,
    dis: ?i64,
    is_store: bool,
) void {
    switch (dt) {
        .i16 => self.emitByte(0x66),
        .f32 => self.emitByte(0xf3),
        .f64 => self.emitByte(0xf2),
        else => {},
    }
    self.emitRex(reg, bse, .no_index, dt.size());
    self.emitBytes(switch (dt) {
        .i16, .i64, .i32 => &.{if (is_store) 0x89 else 0x8b},
        .i8 => &.{if (is_store) 0x88 else 0x8a},
        .f32, .f64 => &.{ 0x0f, if (is_store) 0x11 else 0x10 },
        else => unreachable,
    });
    self.emitIndirectAddr(reg, bse, .no_index, 1, dis);
}

pub fn emitIndirectAddr(
    self: *X86_64Gen,
    reg: Reg,
    base: Reg,
    index: Reg,
    scale: u64,
    // null if this is relocated
    dis: ?i64,
) void {
    var mod = if (dis) |d| Reg.Mod.fromDis(d) else Reg.Mod.indirect;
    std.debug.assert(mod != .direct);

    const ill_base = base == .rsp or base == .r12;

    if (mod == .indirect and ((base == Reg.rip or base == .r13) and dis != null)) {
        mod = .indirect_disp8;
    }

    if (index != Reg.no_index or ill_base or scale != 1) {
        self.emitByte(mod.rm(reg, .rsp));
        self.emitByte(Reg.sib(base, index, scale));
    } else {
        self.emitByte(mod.rm(reg, base));
    }

    if (dis) |d| switch (mod) {
        .indirect => {},
        .indirect_disp8 => self.emitImm(i8, @intCast(d)),
        .indirect_disp32 => self.emitImm(i32, @intCast(d)),
        else => unreachable,
    } else {
        self.emitImm(i32, 0);
    }
}

pub fn emitRexNoReg(self: *X86_64Gen, ptr: Reg, idx: Reg, reg_size: u64) void {
    const rex = Reg.rex(.rax, ptr, idx, reg_size == 8);
    if (rex != Reg.no_op_rex or (reg_size == 1 and ptr.needRexIfSingleByte())) {
        self.emitByte(rex);
    }
}

pub fn emitRexBinop(self: *X86_64Gen, reg: Reg, ptr: Reg, idx: Reg, reg_size: u64) void {
    const rex = Reg.rex(reg, ptr, idx, reg_size == 8);
    if (rex != Reg.no_op_rex or (reg_size == 1 and
        (reg.needRexIfSingleByte() or ptr.needRexIfSingleByte())))
    {
        self.emitByte(rex);
    }
}

pub fn emitRex(self: *X86_64Gen, reg: Reg, ptr: Reg, idx: Reg, reg_size: u64) void {
    const rex = Reg.rex(reg, ptr, idx, reg_size == 8);
    if (rex != Reg.no_op_rex or (reg_size == 1 and reg.needRexIfSingleByte())) {
        self.emitByte(rex);
    }
}

pub fn emitStackLea(self: *X86_64Gen, dst: Reg, dis: i32) void {
    self.emitRex(dst, .rax, .rax, 8);
    self.emitByte(0x8d);
    self.emitIndirectAddr(dst, .rsp, .no_index, 1, dis);
}

pub fn emitRegOp(self: *X86_64Gen, op: u8, dst: Reg, src: Reg) void {
    self.emitRex(dst, src, .rax, 8);
    self.emitBytes(&.{ op, Reg.Mod.direct.rm(dst, src) });
}

pub fn emitImmOp(self: *X86_64Gen, op: u8, mod: u3, dst: Reg, imm: i64) void {
    const cimm = std.math.cast(i8, imm);
    self.emitBytes(&.{
        Reg.rex(dst, .rax, .rax, true),
        op + @as(u8, if (cimm != null) 2 else 0),
        Reg.Mod.direct.rm(@enumFromInt(mod), dst),
    });
    if (cimm) |c| {
        self.emitImm(i8, c);
    } else {
        self.emitImm(i32, @intCast(imm));
    }
}

pub fn emitSingleOp(self: *X86_64Gen, op_base: u8, dst: Reg) void {
    const opcode = op_base + dst.scalarIndex();
    self.emitBytes(&.{ Reg.rex(.rax, dst, .rax, true), opcode });
}

pub fn emitByte(self: *X86_64Gen, byte: u8) void {
    self.out.code.appendAssumeCapacity(byte);
}

pub fn emitBytes(self: *X86_64Gen, bytes: []const u8) void {
    self.out.code.appendSliceAssumeCapacity(bytes);
}

pub fn emitImm(self: *X86_64Gen, comptime T: type, int: i64) void {
    std.mem.writeInt(
        T,
        self.out.code.addManyAsArrayAssumeCapacity(@sizeOf(T)),
        @truncate(int),
        .little,
    );
}

pub fn jmpCompOp(op: graph.BinOp) u8 {
    // we flip the orientation here with the xor
    return (0x80 + setOff(op)) ^ 0x1;
}

pub fn setCompOp(op: graph.BinOp) u8 {
    return 0x90 + setOff(op);
}

pub fn setOff(op: graph.BinOp) u8 {
    return switch (op) {
        .ult, .flt => 0x2, // SETB,
        .uge, .fge => 0x3, // SETNB,
        .eq => 0x4, // SETZ,
        .ne => 0x5, // SETNZ,
        .ule, .fle => 0x6, // SETBE,
        .ugt, .fgt => 0x7, // SETNBE,
        .slt => 0xc, // SETL,
        .sge => 0xd, // SETNL,
        .sle => 0xe, // SETLE,
        .sgt => 0xf, // SETNLE,

        else => unreachable,
    };
}

pub fn getReg(self: X86_64Gen, node: *FuncNode) Reg {
    return @enumFromInt(self.allocs[node.schedule]);
}

pub fn emitData(self: *X86_64Gen, opts: Mach.DataOptions) void {
    errdefer unreachable;

    try self.out.defineGlobal(
        self.gpa.allocator(),
        opts.id,
        opts.name,
        .local,
        opts.value,
        false,
        opts.relocs,
        opts.readonly,
    );
}

pub fn preLinkHook(self: *X86_64Gen) void {
    errdefer unreachable;
    inline for (.{ "f32", "f64" }) |name| {
        const idx = @field(self, name ++ "index");
        const sym = &@field(self, name ++ "s");

        _ = try self.out.startDefineSym(self.gpa.allocator(), sym, name ++ "s", .data, .local, true, false);
        try self.out.code.appendSlice(self.gpa.allocator(), @ptrCast(idx.entries.items(.key)));
        self.out.endDefineSym(sym.*);
        try self.out.globals.append(self.gpa.allocator(), sym.*);
    }
}

pub fn finalize(self: *X86_64Gen, opts: Mach.FinalizeOptions) void {
    errdefer unreachable;

    defer {
        self.memcpy = .invalid;
        self.f32s = .invalid;
        self.f64s = .invalid;
        self.f32index.clearRetainingCapacity();
        self.f64index.clearRetainingCapacity();
        self.out.reset();
    }

    if (opts.optimizations.finalizeSingleThread(opts.builtins, X86_64Gen, self, opts.logs)) return;

    try switch (self.object_format) {
        .elf => root.object.elf.flush(self.out, .x86_64, opts.output orelse return),
        .coff => unreachable, //root.object.coff.flush(self.out, .x86_64, out),try
    };
}

pub fn deinit(self: *X86_64Gen) void {
    self.out.deinit(self.gpa.allocator());
}

pub fn disasm(self: *X86_64Gen, opts: Mach.DisasmOpts) void {
    errdefer unreachable;

    const zydis = @import("zydis").exports;

    const util = enum {
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
    };

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
                opts.print("{s}:\n", .{name});

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
                        if (!zydis.ZYAN_SUCCESS(status)) {
                            continue;
                        }

                        if (util.isJump(inst.mnemonic)) {
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
                    if (!zydis.ZYAN_SUCCESS(status)) {
                        utils.panic("{any}", .{bytes[uaddr..][0..5]});
                    }

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
                    //std.debug.print("{s}\n", .{printed});

                    if (label_map.get(uaddr)) |nm| {
                        opts.print("{x}:", .{nm});
                    }

                    if (util.isJump(inst.mnemonic)) {
                        const label = label_map.get(@intCast(addr +
                            ops[0].unnamed_0.imm.value.s + inst.length)).?;
                        opts.print("\t{s} :{}\n", .{ zydis.ZydisMnemonicGetString(inst.mnemonic), label });
                    } else if (inst.mnemonic == zydis.ZYDIS_MNEMONIC_CALL) {
                        const nm = func_map.get(v.offset + uaddr + 1) orelse continue;
                        opts.print("\tcall :{s}\n", .{nm});
                    } else {
                        opts.print("\t{s}\n", .{printed});
                    }
                }
            },
            else => {},
        }
    }
}

pub fn run(_: *X86_64Gen, env: Mach.RunEnv) !usize {
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
