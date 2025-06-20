gpa: std.mem.Allocator,
out: Mach.Data = .{},
local_relocs: std.ArrayListUnmanaged(BlockReloc) = undefined,
ret_count: usize = undefined,
block_offsets: []i32 = undefined,
allocs: []u16 = undefined,
spill_base: usize = undefined,
entry: u32 = undefined,

const std = @import("std");
const utils = root.utils;
const root = @import("hb");
const isa = @import("isa.zig");
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Func = graph.Func(HbvmGen);
const Kind = Func.Kind;
const Regalloc = root.backend.Regalloc;
const ExecHeader = root.hbvm.object.ExecHeader;
const Move = utils.Move(isa.Reg);
const HbvmGen = @This();

pub const eca = std.math.maxInt(u32);
pub const tmp_registers = 2;
pub const max_alloc_regs = @intFromEnum(isa.Reg.stack_addr) - 1 - tmp_registers;

const BlockReloc = struct {
    dest_block: u16,
    rel: Reloc,
};

const Reloc = struct {
    offset: i32,
    sub_offset: u8,
    operand: isa.Arg,
};

pub const classes = enum {
    // [?Cfg, lhs]
    pub const ImmBinOp = extern struct {
        op: isa.Op,
        imm: i64,
    };
    // [?Cfg, lhs, rhs]
    pub const IfOp = extern struct {
        base: graph.If = .{},
        op: isa.Op,
        swapped: bool,
    };
    // [?Cfg, mem, ptr]
    pub const StackLd = extern struct {
        base: Ld,
        pub const data_dep_offset = 2;
    };
    // [?Cfg, mem, ptr, value, ...antideps]
    pub const StackSt = extern struct {
        base: St,
        pub const data_dep_offset = 2;
    };
    // [?Cfg, mem, ptr]
    pub const Ld = extern struct {
        base: graph.Load = .{},
        offset: i64,
    };
    // [?Cfg, mem, ptr, value, ...antideps]
    pub const St = extern struct {
        base: graph.Store = .{},
        offset: i64,
    };
    // [?Cfg, mem, src, dst, ...antideps]
    pub const BlockCpy = extern struct {
        base: graph.MemCpy = .{},
        size: u16,
    };
};

pub const reg_mask_cap = 254 + 32;
pub const reg_count = 254;

pub fn knownOffset(node: *Func.Node) struct { *Func.Node, i64 } {
    return switch (node.extra2()) {
        .ImmBinOp => |i| {
            std.debug.assert(i.op == .addi8);
            return .{ node.inputs()[1].?, i.imm };
        },
        else => .{ node, 0 },
    };
}

pub fn regBias(node: *Func.Node) ?u16 {
    return switch (node.kind) {
        .Arg => @intCast(node.extraConst(.Arg).index),
        .StructArg => @intCast(node.extraConst(.StructArg).base.index),
        else => {
            for (node.outputs()) |o| {
                if (o.kind == .Call) {
                    const idx = std.mem.indexOfScalar(?*Func.Node, o.dataDeps(), node) orelse continue;
                    return @intCast(idx);
                }

                if (o.kind == .Phi and o.inputs()[0].?.kind != .Loop) {
                    return o.regBias();
                }
            }
            return null;
        },
    };
}

pub fn clobbers(node: *Func.Node) u64 {
    return switch (node.kind) {
        .Call => (1 << 31) - 1,
        else => 0,
    };
}

pub fn isSwapped(node: *Func.Node) bool {
    return node.kind == .IfOp and node.extra(.IfOp).swapped;
}

pub fn getStaticOffset(node: *Func.Node) i64 {
    return switch (node.kind) {
        .Ld => node.extra(.Ld).offset,
        .St => node.extra(.St).offset,
        .StackLd => node.extra(.StackLd).base.offset,
        .StackSt => node.extra(.StackSt).base.offset,
        else => 0,
    };
}

pub fn isInterned(kind: Func.Kind) bool {
    return kind == .Ld or kind == .StackLd;
}

const Set = std.DynamicBitSetUnmanaged;

pub fn allowedRegsFor(node: *Func.Node, idx: usize, arena: *utils.Arena) ?Set {
    errdefer unreachable;

    if (node.kind == .FramePointer) {
        std.debug.assert(idx == 0);
        var set = try Set.initEmpty(arena.allocator(), reg_mask_cap);
        set.set(@intFromEnum(isa.Reg.stack_addr));
        return set;
    }

    var set = try Set.initFull(arena.allocator(), reg_mask_cap);
    set.unset(0);
    set.setRangeValue(.{ .start = max_alloc_regs, .end = 256 }, false);
    return set;
    //return switch (node.extra2()) {
    //    inline .Ret, .Arg => |id| arg: {
    //        std.debug.assert(idx == 0);
    //        var set = try Set.initEmpty(arena.allocator(), reg_mask_cap);
    //        set.set(id.*);
    //        break :arg set;
    //    },
    //    .Call => switch (idx) {
    //        0, 1 => null,
    //        else => arg: {
    //            var set = try Set.initEmpty(arena.allocator(), reg_mask_cap);
    //            set.set(idx - 1);
    //            break :arg set;
    //        },
    //    },
    //    else => {
    //        var set = try Set.initEmpty(arena.allocator(), reg_mask_cap);
    //        set.setRangeValue(.{ .start = 0, .end = @intFromEnum(isa.Reg.stack_addr) - 1 }, true);
    //        return set;
    //    },
    //};
}

pub fn regKills(node: *Func.Node, arena: *utils.Arena) ?Set {
    errdefer unreachable;
    return switch (node.kind) {
        .Call => clobbers: {
            var set = try Set.initEmpty(arena.allocator(), reg_mask_cap);
            set.setRangeValue(.{ .start = 0, .end = @intFromEnum(isa.Reg.ret_addr) - 1 }, true);
            break :clobbers set;
        },
        else => null,
    };
}

pub fn addSplit(self: *Func, ctrl: *Func.Node, def: *Func.Node) *Func.Node {
    return self.addNode(.Split, def.data_type, &.{ ctrl, def }, .{});
}

pub const i_know_the_api = {};

pub fn emitFunc(self: *HbvmGen, func: *Func, opts: Mach.EmitOptions) void {
    errdefer unreachable;

    const id = opts.id;
    const name = opts.name;
    const entry = opts.linkage == .exported;

    try self.out.startDefineFunc(self.gpa, id, name, .func, opts.linkage, opts.is_inline);
    defer self.out.endDefineFunc(id);

    if (opts.optimizations.shouldDefer(id, opts.is_inline, HbvmGen, func, self))
        return;

    opts.optimizations.execute(HbvmGen, self, func);

    const allocs = Regalloc.ralloc(HbvmGen, func);

    var tmp = utils.Arena.scrath(opts.optimizations.arena);
    defer tmp.deinit();

    self.block_offsets = tmp.arena.alloc(i32, func.gcm.block_count);
    self.local_relocs = .initBuffer(tmp.arena.alloc(BlockReloc, func.gcm.block_count * 2));
    self.allocs = allocs;
    self.ret_count = func.signature.returns().len;

    const is_tail = for (func.gcm.postorder) |bb| {
        if (bb.base.kind == .CallEnd) break false;
    } else true;

    const reg_shift: u8 = 1;
    for (self.allocs) |*r| r.* += reg_shift;
    const max_reg = if (self.allocs.len == 0) 0 else b: {
        var max: u16 = 0;
        for (self.allocs) |r| {
            if (r == 254) continue;
            max = @max(r, max);
        }
        break :b max;
    };
    const used_registers = if (self.allocs.len == 0) 0 else @min(max_reg, max_alloc_regs) -|
        (@intFromEnum(isa.Reg.ret_addr) - @intFromBool(is_tail));

    const used_reg_size = @as(u16, (used_registers + @intFromBool(!is_tail))) * 8;
    const spill_count = (max_reg -| max_regs) * 8;

    var local_size: i64 = 0;
    if (func.root.outputs().len > 1) {
        std.debug.assert(func.root.outputs()[1].kind == .Mem);
        for (func.root.outputs()[1].outputs()) |o| if (o.kind == .Local) {
            const extra = o.extra(.Local);
            const size = extra.size;
            extra.size = @bitCast(local_size);
            local_size += @intCast(size);
        };
    }

    const stack_size: i64 = used_reg_size + local_size + spill_count;
    self.spill_base = @intCast(used_reg_size + local_size);

    prelude: {
        if (used_reg_size != 0) {
            self.emit(.st, .{ .ret_addr, .stack_addr, -@as(i64, used_reg_size), used_reg_size });
        }
        if (stack_size != 0) {
            self.emit(.addi64, .{ .stack_addr, .stack_addr, @as(u64, @bitCast(-stack_size)) });
        }

        var moves = std.ArrayList(Move).init(tmp.arena.allocator());
        for (func.gcm.postorder[0].base.outputs()) |argn| {
            const arg = argn.subclass(graph.Arg) orelse break;
            const dst, const src = .{ self.outReg(argn), isa.Reg.arg(arg.ext.index) };
            if (dst != src) moves.append(.init(dst, src)) catch unreachable;
        }
        self.orderMoves(moves.items);
        break :prelude;
    }

    for (func.gcm.postorder) |bb| {
        if (bb.base.schedule == std.math.maxInt(u16)) {
            utils.panic("{}", .{bb});
        }
    }

    for (func.gcm.postorder, 0..) |bb, i| {
        self.block_offsets[bb.base.schedule] = @intCast(self.out.code.items.len);
        std.debug.assert(bb.base.schedule == i);
        self.emitBlockBody(tmp.arena.allocator(), &bb.base);
        const last = bb.base.outputs()[bb.base.output_len - 1];
        if (last.outputs().len == 0) {
            std.debug.assert(last.kind == .Return);
            if (stack_size != 0) {
                self.emit(.addi64, .{ .stack_addr, .stack_addr, @as(u64, @bitCast(stack_size)) });
            }
            if (used_reg_size != 0) {
                self.emit(.ld, .{ .ret_addr, .stack_addr, -@as(i64, used_reg_size), used_reg_size });
            }
            if (entry) {
                self.emit(.tx, .{});
            } else {
                self.emit(.jala, .{ .null, .ret_addr, 0 });
            }
        } else if (i + 1 == last.outputs()[@intFromBool(last.isSwapped())].schedule) {
            // noop
        } else if (last.kind == .Never) {
            // noop
        } else if (last.kind == .Trap) {
            // noop
        } else {
            std.debug.assert(last.outputs()[@intFromBool(last.isSwapped())]
                .isBasicBlockStart());
            if (last.outputs()[@intFromBool(last.isSwapped())]
                .schedule == std.math.maxInt(u16))
            {
                utils.panic("{} {}\n", .{ last.outputs()[@intFromBool(last.isSwapped())], last });
            }
            self.local_relocs.appendAssumeCapacity(.{
                .dest_block = last.outputs()[@intFromBool(last.isSwapped())].schedule,
                .rel = self.reloc(1, .rel32),
            });
            self.emit(.jmp, .{0});
        }
    }

    for (self.local_relocs.items) |lr| {
        self.doReloc(lr.rel, self.block_offsets[lr.dest_block]);
    }
}

pub fn emitData(self: *HbvmGen, opts: Mach.DataOptions) void {
    errdefer unreachable;

    switch (opts.value) {
        .init => |v| try self.out.defineGlobal(
            self.gpa,
            opts.id,
            opts.name,
            if (opts.value == .init) .data else .prealloc,
            .local,
            v,
            opts.readonly,
        ),
        .uninit => unreachable,
    }
}

pub fn finalize(self: *HbvmGen, opts: Mach.FinalizeOptions) void {
    errdefer unreachable;

    if (opts.optimizations.finalize(HbvmGen, self)) return;

    try root.hbvm.object.flush(self.out, opts.output);

    self.out.reset();
}

pub fn disasm(_: *HbvmGen, opts: Mach.DisasmOpts) void {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    isa.disasm(opts.bin, tmp.arena.allocator(), opts.out, opts.colors) catch unreachable;
}

pub fn run(_: *HbvmGen, env: Mach.RunEnv) !usize {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const stack_size = 1024 * 128;

    var stack: [stack_size]u8 = undefined;

    const code = env.code;

    const head: ExecHeader = @bitCast(code[0..@sizeOf(ExecHeader)].*);
    const stack_end = stack_size - code.len + @sizeOf(ExecHeader);
    @memcpy(stack[stack_end..], code[@sizeOf(ExecHeader)..]);

    var vm = root.hbvm.Vm{};
    vm.ip = stack_end;
    vm.fuel = 1024 * 128;
    @memset(&vm.regs.values, 0);
    vm.regs.set(.stack_addr, stack_end);
    var ctx = root.hbvm.Vm.SafeContext{
        .writer = env.output,
        .symbols = try root.hbvm.object.loadSymMap(tmp.arena.allocator(), code),
        .color_cfg = env.colors,
        .memory = &stack,
        .code_start = stack_end,
        .code_end = stack_end + @as(usize, @intCast(head.code_length)),
    };

    var prng = std.Random.Pcg.init(0);
    var page_cursor: usize = 1;
    const page_size = 1024 * 4;
    while (true) switch (try vm.run(&ctx)) {
        .tx => break,
        .eca => switch (vm.regs.get(.arg(0))) {
            100 => {
                std.debug.assert(vm.regs.get(.arg(1)) == 1);
                std.debug.assert(vm.regs.get(.arg(2)) == 2);
                vm.regs.set(.ret(0), 3);
            },
            3 => switch (vm.regs.get(.arg(1))) {
                2 => switch (ctx.memory[@intCast(vm.regs.get(.arg(2)))]) {
                    0 => {
                        const Msg = extern struct { pad: u8, pages_new: u64 align(1), zeroed: bool };

                        const msg: Msg =
                            @bitCast(ctx.memory[@intCast(vm.regs.get(.arg(2)))..][0..@sizeOf(Msg)].*);

                        const base = page_size * page_cursor;
                        page_cursor += @intCast(msg.pages_new);

                        if (msg.zeroed) @memset(
                            ctx.memory[@intCast(base)..][0..@intCast(msg.pages_new * page_size)],
                            0,
                        );

                        vm.regs.set(.ret(0), base);
                    },
                    7, 1 => {},
                    5 => {
                        const Msg = extern struct { pad: u8, len: u64 align(1), count: u64 align(1), src: u64 align(1), dest: u64 align(1) };
                        const msg: Msg = @bitCast(ctx.memory[@intCast(vm.regs.get(.arg(2)))..][0..@sizeOf(Msg)].*);

                        if (msg.dest > ctx.memory.len or
                            msg.src > ctx.memory.len or
                            msg.dest + msg.len > ctx.memory.len or
                            msg.src + msg.count > ctx.memory.len)
                        {
                            return error.MemOob;
                        }

                        const dst, const src = .{
                            ctx.memory[@intCast(msg.dest)..][0..@intCast(msg.len)],
                            ctx.memory[@intCast(msg.src)..][0..@intCast(msg.count)],
                        };

                        for (0..@intCast(msg.len / msg.count)) |i| {
                            @memcpy(dst[@intCast(i * msg.count)..][0..@intCast(msg.count)], src);
                        }
                    },
                    4, 6 => |v| {
                        const Msg = extern struct { pad: u8, len: u64 align(1), src: u64 align(1), dest: u64 align(1) };
                        const msg: Msg = @bitCast(ctx.memory[@intCast(vm.regs.get(.arg(2)))..][0..@sizeOf(Msg)].*);

                        if (msg.dest > ctx.memory.len or
                            msg.src > ctx.memory.len or
                            msg.dest + msg.len > ctx.memory.len or
                            msg.src + msg.len > ctx.memory.len)
                        {
                            return error.MemOob;
                        }

                        const dst, const src = .{
                            ctx.memory[@intCast(msg.dest)..][0..@intCast(msg.len)],
                            ctx.memory[@intCast(msg.src)..][0..@intCast(msg.len)],
                        };

                        if (v == 4) {
                            @memcpy(dst, src);
                        } else {
                            if (msg.src < msg.dest) {
                                std.mem.copyBackwards(u8, dst, src);
                            } else {
                                std.mem.copyForwards(u8, dst, src);
                            }
                        }
                    },
                    else => |v| utils.panic("{}", .{v}),
                },
                7 => utils.panic("I don't think I will", .{}),
                1 => {
                    const LogLevel = enum(u8) {
                        Error,
                        Warn,
                        Info,
                        Debug,
                        Trace,
                    };
                    const Msg = extern struct { level: LogLevel, str_ptr: u64 align(1), str_len: u64 align(1) };
                    const msg: Msg = @bitCast(ctx.memory[@intCast(vm.regs.get(.arg(2)))..][0..@sizeOf(Msg)].*);
                    const str = ctx.memory[@intCast(msg.str_ptr)..][0..@intCast(msg.str_len)];

                    env.logs.print("{s}\n", .{str}) catch {};
                },
                4 => {
                    const dest = ctx.memory[@intCast(vm.regs.get(.arg(3)))..][0..@intCast(vm.regs.get(.arg(4)))];
                    prng.fill(dest);
                },
                else => |v| utils.panic("{}", .{v}),
            },
            else => unreachable,
        },
        else => unreachable,
    };

    return @intCast(vm.regs.get(.ret(0)));
}

pub fn deinit(self: *HbvmGen) void {
    self.out.deinit(self.gpa);
    self.* = undefined;
}

pub fn doReloc(self: *HbvmGen, rel: Reloc, dest: i64) void {
    const jump = dest - rel.offset;
    const location: usize = @intCast(rel.offset + rel.sub_offset);

    const size: usize = switch (rel.operand) {
        .rel32 => 4,
        .rel16 => 2,
        else => unreachable,
    };

    @memcpy(self.out.code.items[location..][0..size], @as(*const [8]u8, @ptrCast(&jump))[0..size]);
}

pub fn emitBlockBody(self: *HbvmGen, tmp: std.mem.Allocator, node: *Func.Node) void {
    errdefer unreachable;
    for (node.outputs()) |no| {
        const inps = no.dataDeps();
        switch (no.extra2()) {
            .FramePointer => {},
            .CInt => |extra| {
                switch (no.data_type) {
                    inline .i8, .i16, .i32, .i64 => |t| self.emit(
                        @field(isa.Op, "l" ++ @tagName(t)),
                        .{ self.outReg(no), @truncate(@as(u64, @bitCast(extra.*))) },
                    ),
                    else => utils.panic("{}\n", .{no.data_type}),
                }
                self.flushOutReg(no);
            },
            .CFlt32 => {
                self.emit(.li32, .{ self.outReg(no), @bitCast(no.extra(.CFlt32).*) });
                self.flushOutReg(no);
            },
            .CFlt64 => {
                self.emit(.li64, .{ self.outReg(no), @bitCast(no.extra(.CFlt64).*) });
                self.flushOutReg(no);
            },
            .Arg => {},
            .GlobalAddr => |extra| {
                try self.out.addGlobalReloc(self.gpa, extra.id, 4, 3);
                self.emit(.lra, .{ self.outReg(no), .null, 0 });
            },
            .Local => |extra| if (!extra.no_address) {
                self.emit(.addi64, .{ self.outReg(no), .stack_addr, extra.size });
            },
            .Ld => |extra| {
                const size: u16 = @intCast(no.data_type.size());
                const off = extra.offset;
                self.emit(.ld, .{ self.outReg(no), self.inReg(0, inps[0]), off, size });
                self.flushOutReg(no);
            },
            .St => |extra| {
                const size: u16 = @intCast(no.data_type.size());
                const off = extra.offset;
                self.emit(.st, .{ self.outReg(inps[1]), self.inReg(0, inps[0]), off, size });
            },
            .StackLd => |extra| {
                const size: u16 = @intCast(no.data_type.size());
                const off = @as(i64, @intCast(no.inputs()[2].?.extra(.Local).size)) + extra.base.offset;
                self.emit(.ld, .{ self.outReg(no), .stack_addr, off, size });
                self.flushOutReg(no);
            },
            .StackSt => |extra| {
                const size: u16 = @intCast(no.data_type.size());
                const off = @as(i64, @intCast(no.inputs()[2].?.extra(.Local).size)) + extra.base.offset;
                self.emit(.st, .{ self.outReg(inps[0]), .stack_addr, off, size });
            },
            .BlockCpy => {
                // not a mistake, the bmc is retarded
                self.emit(.bmc, .{ self.inReg(0, inps[1]), self.inReg(1, inps[0]), no.extra(.BlockCpy).size });
            },
            .BinOp => |extra| {
                const mone = std.math.maxInt(u64);

                var op: isa.Op = switch (extra.op) {
                    .iadd => .add8,
                    .fadd => .fadd32,
                    .isub => .sub8,
                    .fsub => .fsub32,
                    .imul => .mul8,
                    .fmul => .fmul32,
                    .udiv, .umod => .diru8,
                    .sdiv, .smod => .dirs8,
                    .fdiv => .fdiv32,
                    .ishl => .slu8,
                    .ushr => .sru8,
                    .sshr => .srs8,
                    .bor => .@"or",
                    .band => .@"and",
                    .bxor => .xor,
                    .fge, .flt => .fcmplt32,
                    .fgt, .fle => .fcmpgt32,
                    .eq, .ne, .uge, .ule, .ugt, .ult => .cmpu,
                    .sge, .sle, .sgt, .slt => .cmps,
                };

                switch (extra.op) {
                    .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt, .slt, .bor, .band, .bxor => {},
                    .fadd, .fsub, .fmul, .fdiv, .fge, .fle, .fgt, .flt => op = @enumFromInt(@intFromEnum(op) +
                        (@intFromEnum(inps[0].?.data_type) - @intFromEnum(graph.DataType.f32))),
                    else => op = @enumFromInt(@intFromEnum(op) +
                        (@intFromEnum(no.data_type) - @intFromEnum(graph.DataType.i8))),
                }

                const lhs, const rhs = .{ self.inReg(0, no.inputs()[1]), self.inReg(1, no.inputs()[2]) };
                switch (extra.op) {
                    .udiv, .sdiv => self.emitLow("RRRR", op, .{ self.outReg(no), .null, lhs, rhs }),
                    .umod, .smod => self.emitLow("RRRR", op, .{ .null, self.outReg(no), lhs, rhs }),
                    else => self.emitLow("RRR", op, .{ self.outReg(no), lhs, rhs }),
                }

                switch (extra.op) {
                    .fge, .fle => self.emit(.not, .{ self.outReg(no), self.outReg(no) }),
                    else => {},
                }

                extra_comparison_instrs: {
                    const compare_to: u64 = switch (extra.op) {
                        .eq, .ne => 0,
                        .ugt, .sgt, .ule, .sle => 1,
                        .ult, .slt, .uge, .sge => mone,
                        else => break :extra_comparison_instrs,
                    };
                    self.emit(.cmpui, .{ self.outReg(no), self.outReg(no), compare_to });
                    switch (extra.op) {
                        .eq, .ugt, .sgt, .ult, .slt => {
                            self.emit(.not, .{ self.outReg(no), self.outReg(no) });
                        },
                        .ne, .uge, .sge, .ule, .sle => {
                            self.emit(.andi, .{ self.outReg(no), self.outReg(no), 1 });
                        },
                        else => {},
                    }
                }

                self.flushOutReg(no);
            },
            .UnOp => |extra| {
                switch (extra.op) {
                    .sext => {
                        const op: isa.Op = @enumFromInt(@intFromEnum(isa.Op.sxt8) +
                            (@intFromEnum(inps[0].?.data_type) - @intFromEnum(graph.DataType.i8)));
                        self.emitLow("RR", op, .{ self.outReg(no), self.inReg(0, inps[0]) });
                    },
                    .uext => {
                        const mask = (@as(u64, 1) << @intCast(inps[0].?.data_type.size() * 8)) - 1;
                        self.emit(.andi, .{ self.outReg(no), self.inReg(0, inps[0]), mask });
                    },
                    // TODO: idealize to nothing
                    .ired => self.emit(.cp, .{ self.outReg(no), self.inReg(0, inps[0]) }),
                    .ineg => self.emit(.neg, .{ self.outReg(no), self.inReg(0, inps[0]) }),
                    .fneg => if (no.data_type == .f32) {
                        self.emit(.fsub32, .{ self.outReg(no), .null, self.inReg(0, inps[0]) });
                    } else {
                        self.emit(.fsub64, .{ self.outReg(no), .null, self.inReg(0, inps[0]) });
                    },
                    .not => self.emit(.not, .{ self.outReg(no), self.inReg(0, inps[0]) }),
                    .bnot => self.emit(.xori, .{ self.outReg(no), self.inReg(0, inps[0]), std.math.maxInt(u64) }),
                    .fti => if (inps[0].?.data_type == .f32) {
                        self.emit(.fti32, .{ self.outReg(no), self.inReg(0, inps[0]), 0 });
                    } else {
                        std.debug.assert(inps[0].?.data_type == .f64);
                        self.emit(.fti64, .{ self.outReg(no), self.inReg(0, inps[0]), 0 });
                    },
                    .itf32 => self.emit(.itf32, .{ self.outReg(no), self.inReg(0, inps[0]) }),
                    .itf64 => self.emit(.itf64, .{ self.outReg(no), self.inReg(0, inps[0]) }),
                    .fcst => if (no.data_type == .f32) {
                        self.emit(.fc64t32, .{ self.outReg(no), self.inReg(0, inps[0]), 0 });
                    } else {
                        std.debug.assert(no.data_type == .f64);
                        self.emit(.fc32t64, .{ self.outReg(no), self.inReg(0, inps[0]) });
                    },
                    .cast => unreachable,
                }
                self.flushOutReg(no);
            },
            .ImmBinOp => |extra| {
                const alloc = self.outReg(no);

                if (extra.op == .ori or extra.op == .andi or extra.op == .xori) {
                    self.emitLow(
                        "RRD",
                        extra.op,
                        .{ alloc, self.inReg(0, inps[0]), @as(u64, @bitCast(extra.imm)) },
                    );
                } else {
                    const chars = "BHWD";
                    const types = .{ u8, u16, u32, u64 };
                    switch (no.data_type) {
                        inline .i8, .i16, .i32, .i64 => |t| {
                            const idx = @intFromEnum(t) - @intFromEnum(graph.DataType.i8);
                            self.emitLow(
                                "RR" ++ chars[idx..][0..1],
                                @enumFromInt(@intFromEnum(extra.op) + idx),
                                .{ alloc, self.inReg(0, inps[0]), @as(types[idx], @truncate(@as(u64, @bitCast(extra.imm)))) },
                            );
                        },
                        else => unreachable,
                    }
                }
                self.flushOutReg(no);
            },
            .IfOp => |extra| {
                std.debug.assert(
                    no.outputs()[@intFromBool(!extra.swapped)].schedule !=
                        std.math.maxInt(u16),
                );
                self.local_relocs.appendAssumeCapacity(.{
                    .dest_block = no.outputs()[@intFromBool(!extra.swapped)].schedule,
                    .rel = self.reloc(3, .rel16),
                });
                self.emitLow("RRP", extra.op, .{ self.inReg(0, inps[0]), self.inReg(1, inps[1]), 0 });
            },
            .If => {
                std.debug.assert(no.outputs()[1].schedule != std.math.maxInt(u16));
                self.local_relocs.appendAssumeCapacity(.{
                    .dest_block = no.outputs()[1].schedule,
                    .rel = self.reloc(3, .rel16),
                });
                self.emit(.jeq, .{ self.inReg(0, inps[0]), .null, 0 });
            },
            .Call => |extra| {
                var moves = std.ArrayList(Move).init(tmp);
                for (inps, 0..) |arg, i| {
                    const dst, const src = .{ isa.Reg.arg(i), self.inReg(0, arg) };
                    if (dst != src) moves.append(.init(dst, src)) catch unreachable;
                }
                self.orderMoves(moves.items);

                if (extra.id == eca) {
                    self.emit(.eca, .{});
                } else {
                    try self.out.addFuncReloc(self.gpa, extra.id, 4, 3);
                    self.emit(.jal, .{ .ret_addr, .null, 0 });
                }

                const cend = for (no.outputs()) |o| {
                    if (o.kind == .CallEnd) break o;
                } else unreachable;

                moves.items.len = 0;
                for (cend.outputs()) |r| {
                    if (r.kind == .Ret) {
                        const dst, const src = .{ self.outReg(r), isa.Reg.ret(r.extra(.Ret).index) };
                        if (dst != src) moves.append(.init(dst, src)) catch unreachable;
                    }
                }
                self.orderMoves(moves.items);
            },
            .Jmp => if (no.outputs()[0].kind == .Region or no.outputs()[0].kind == .Loop) {
                const idx = std.mem.indexOfScalar(?*Func.Node, no.outputs()[0].inputs(), no).? + 1;

                var moves = std.ArrayList(Move).init(tmp);
                for (no.outputs()[0].outputs()) |o| {
                    if (o.isDataPhi()) {
                        std.debug.assert(o.inputs()[idx].?.kind == .MachMove);
                        const dst, const src = .{ self.outReg(o), self.inRegNoLoad(0, o.inputs()[idx].?.inputs()[1]) };
                        if (dst != src) moves.append(.init(dst, src)) catch unreachable;
                    }
                }

                self.orderMoves(moves.items);
            },
            .Return => {
                if (Func.isDead(no.inputs()[0])) return;
                var moves = std.ArrayList(Move).init(tmp);
                for (inps[0..self.ret_count], 0..) |inp, i| {
                    const dst, const src = .{ isa.Reg.ret(i), self.inReg(0, inp) };
                    if (dst != src) moves.append(.init(dst, src)) catch unreachable;
                }
                self.orderMoves(moves.items);
            },
            .Trap => |extra| {
                switch (extra.code) {
                    graph.infinite_loop_trap => return,
                    0 => self.emit(.un, .{}),
                    1 => self.emit(.tx, .{}),
                    else => unreachable,
                }
            },
            .Never, .MachMove, .Mem, .Ret, .Phi => {},
            else => |e| utils.panic("{any}", .{e}),
        }
    }
}

fn orderMoves(self: *HbvmGen, moves: []Move) void {
    utils.orderMoves(self, isa.Reg, moves);
}

pub fn emitSwap(self: *HbvmGen, lhs: isa.Reg, rhs: isa.Reg) void {
    self.emit(.swa, .{ lhs, rhs });
}

pub fn emitCp(self: *HbvmGen, dst: isa.Reg, src: isa.Reg) void {
    self.emit(.cp, .{ dst, src });
}

const max_regs = @intFromEnum(isa.Reg.max);

fn inReg(self: *HbvmGen, i: usize, n: ?*Func.Node) isa.Reg {
    std.debug.assert(i < tmp_registers);
    if (self.allocs[n.?.schedule] < max_regs) {
        return @enumFromInt(self.allocs[n.?.schedule]);
    } else {
        const idx = (self.allocs[n.?.schedule] - max_regs) * 8;
        const reg: isa.Reg = @enumFromInt(max_alloc_regs + i);
        self.emit(.ld, .{ reg, .stack_addr, @intCast(idx + self.spill_base), 8 });
        return reg;
    }
}

fn inRegNoLoad(self: *HbvmGen, i: usize, n: ?*Func.Node) isa.Reg {
    std.debug.assert(i < tmp_registers);
    if (self.allocs[n.?.schedule] < max_regs) {
        return @enumFromInt(self.allocs[n.?.schedule]);
    } else {
        unreachable;
    }
}

fn outReg(self: HbvmGen, n: ?*Func.Node) isa.Reg {
    if (self.allocs[n.?.schedule] < max_regs) {
        return @enumFromInt(self.allocs[n.?.schedule]);
    } else {
        return @enumFromInt(max_alloc_regs);
    }
}

fn flushOutReg(self: *HbvmGen, n: ?*Func.Node) void {
    if (self.allocs[n.?.schedule] < max_regs) {} else {
        const idx = (self.allocs[n.?.schedule] - max_regs) * 8;
        const reg: isa.Reg = @enumFromInt(max_alloc_regs);
        self.emit(.st, .{ reg, .stack_addr, @intCast(idx + self.spill_base), 8 });
    }
}

fn emit(self: *HbvmGen, comptime op: isa.Op, args: isa.TupleOf(isa.ArgsOf(op))) void {
    self.emitLow(isa.spec[@intFromEnum(op)][1], op, args);
}

fn emitLow(self: *HbvmGen, comptime arg_str: []const u8, op: isa.Op, args: isa.TupleOf(isa.ArgsOfStr(arg_str))) void {
    if (!std.mem.eql(u8, isa.spec[@intFromEnum(op)][1], arg_str)) utils.panic("{} {s} {s}", .{ op, arg_str, isa.spec[@intFromEnum(op)][1] });
    self.out.code.append(self.gpa, @intFromEnum(op)) catch unreachable;
    self.out.code.appendSlice(self.gpa, std.mem.asBytes(&isa.packTo(isa.ArgsOfStr(arg_str), args))) catch unreachable;
}

pub fn reloc(self: *HbvmGen, sub_offset: u8, arg: isa.Arg) Reloc {
    return .{ .offset = @intCast(self.out.code.items.len), .sub_offset = sub_offset, .operand = arg };
}

pub fn idealizeMach(self: *HbvmGen, func: *Func, node: *Func.Node, work: *Func.WorkList) ?*Func.Node {
    const inps = node.inputs();

    if (Func.idealizeDead({}, func, node, work)) |n| return n;

    if (node.kind == .BinOp) {
        const op: graph.BinOp = node.extra(.BinOp).op;

        if (inps[2].?.kind == .CInt) b: {
            var imm = inps[2].?.extra(.CInt).value;

            const instr: isa.Op = switch (op) {
                .iadd => .addi8,
                .imul => .muli8,
                .isub => m: {
                    imm *= -1;
                    break :m .addi8;
                },
                .bor => .ori,
                .bxor => .xori,
                .band => .andi,
                else => break :b,
            };

            return func.addNode(
                .ImmBinOp,
                node.data_type,
                &.{ null, node.inputs()[1] },
                .{ .op = instr, .imm = imm },
            );
        }
    }

    if (node.kind == .UnOp and node.extra(.UnOp).op == .cast) return inps[1];

    if (node.kind == .If) {
        if (inps[1].?.kind == .BinOp) b: {
            work.add(inps[1].?);
            const op = inps[1].?.extra(.BinOp).op;
            const instr: isa.Op, const swap = switch (op) {
                .ule => .{ .jgtu, false },
                .uge => .{ .jltu, false },
                .ult => .{ .jltu, true },
                .ugt => .{ .jgtu, true },

                .sle => .{ .jgts, false },
                .sge => .{ .jlts, false },
                .slt => .{ .jlts, true },
                .sgt => .{ .jgts, true },

                .eq => .{ .jne, false },
                .ne => .{ .jeq, false },
                else => break :b,
            };
            const op_inps = inps[1].?.inputs();

            return func.addNode(.IfOp, .top, &.{ inps[0], op_inps[1], op_inps[2] }, .{
                .op = instr,
                .swapped = swap,
            });
        }

        if (inps[1].?.data_type != .i64) {
            const new = func.addUnOp(.uext, .i64, inps[1].?);
            work.add(new);
            _ = func.setInput(node, 1, new);
        }
    }

    if (node.kind == .MemCpy) {
        if (inps[4].?.kind == .CInt) {
            return func.addNode(
                .BlockCpy,
                .top,
                &.{ inps[0], inps[1], inps[2], inps[3] },
                .{ .size = @intCast(inps[4].?.extra(.CInt).value) },
            );
        }
    }

    if (node.kind == .Store) {
        const base, const offset = node.base().knownOffset();
        const st = func.addNode(
            .St,
            node.data_type,
            &.{ inps[0], inps[1], base, inps[3] },
            .{ .offset = offset },
        );

        if (base.isStack()) {
            st.kind = .StackSt;
        }

        work.add(st);
        return st;
    }

    if (node.kind == .St and node.base().isStack()) {
        node.kind = .StackSt;
    }

    if (node.kind == .Load) {
        const base, const offset = node.base().knownOffset();
        const ld = if (base.isStack())
            func.addNode(
                .StackLd,
                node.data_type,
                &.{ inps[0], inps[1], base },
                .{ .base = .{ .offset = offset } },
            )
        else
            func.addNode(
                .Ld,
                node.data_type,
                &.{ inps[0], inps[1], base },
                .{ .offset = offset },
            );
        work.add(ld);
        return ld;
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

    return Func.idealize(self, func, node, work);
}

pub fn idealize(_: *HbvmGen, func: *Func, node: *Func.Node, work: *Func.WorkList) ?*Func.Node {
    const inps = node.inputs();

    if (node.kind == .BinOp) {
        const op: graph.BinOp = node.extra(.BinOp).op;

        if (op.isCmp() and !op.isFloat()) {
            const ext_op: graph.UnOp = if (op.isSigned()) .sext else .uext;
            inline for (inps[1..3], 1..) |inp, i| {
                if (inp.?.data_type.size() != 8) {
                    const new = func.addUnOp(ext_op, .i64, inp.?);
                    work.add(new);
                    _ = func.setInput(node, i, new);
                }
            }
        }
    }

    if (node.kind == .UnOp) {
        const op: graph.UnOp = node.extra(.UnOp).op;
        if (op == .not and inps[1].?.data_type != .i64) {
            const new = func.addUnOp(.uext, .i64, inps[1].?);
            work.add(new);
            _ = func.setInput(node, 1, new);
        }
    }

    return null;
}
