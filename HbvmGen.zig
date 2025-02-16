out: std.ArrayList(u8),
local_relocs: std.ArrayList(BlockReloc) = undefined,
global_relocs: std.ArrayList(GloblReloc),
funcs: std.ArrayList(FuncData),
block_offsets: []i32 = undefined,
allocs: []u8 = undefined,

const std = @import("std");
const isa = @import("isa.zig");
const graph = @import("graph.zig");
const Mach = @import("Mach.zig");
const Func = graph.Func(Node);
const Kind = Func.Kind;
const Regalloc = @import("Regalloc.zig");
const HbvmGen = @This();

pub const dir = "inputs";

const FuncData = struct {
    name: []const u8,
    offset: u32 = 0,
};

const GloblReloc = struct {
    rel: Reloc,
    dest: u32,
};

const BlockReloc = struct {
    dest_block: u16,
    rel: Reloc,
};

const Reloc = struct {
    offset: i32,
    sub_offset: u8,
    operand: isa.Arg,
};

pub const Node = union(enum) {
    // [?Cfg, lhs]
    ImmBinOp: extern struct {
        op: isa.Op,
        imm: i64,
    },
    // [?Cfg, lhs, rhs]
    IfOp: extern struct {
        base: graph.Cfg = .{},
        op: isa.Op,
        swapped: bool,
    },
    // [?Cfg, mem, ptr]
    Ld: extern struct {
        base: graph.Load = .{},
        offset: i64,
    },
    // [?Cfg, mem, ptr, value, ...antideps]
    St: extern struct {
        base: graph.Store = .{},
        offset: i64,
    },
    // [?Cfg, mem, src, dst, ...antideps]
    BlockCpy: extern struct {
        base: graph.MemCpy = .{},
        size: u16,
    },

    pub const idealize = HbvmGen.idealize;

    pub const is_basic_block_end: []const Kind = &.{.IfOp};
    pub const is_mem_op: []const Kind = &.{ .BlockCpy, .St, .Ld };

    pub fn isSwapped(node: *Func.Node) bool {
        return node.kind == .IfOp and node.extra(.IfOp).swapped;
    }

    pub const i_know_the_api = {};
};

pub fn init(out: std.ArrayList(u8)) HbvmGen {
    return .{
        .out = out,
        .global_relocs = .init(out.allocator),
        .funcs = .init(out.allocator),
    };
}

pub fn deinit(self: *HbvmGen) void {
    self.global_relocs.deinit();
    self.funcs.deinit();
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

    @memcpy(self.out.items[location..][0..size], @as(*const [8]u8, @ptrCast(&jump))[0..size]);
}

pub fn link(self: *HbvmGen) void {
    for (self.global_relocs.items) |r| {
        self.doReloc(r.rel, self.funcs.items[r.dest].offset);
    }
    self.global_relocs.items.len = 0;
}

pub fn finalize(self: *HbvmGen) std.ArrayList(u8) {
    self.link();

    defer self.deinit();
    return self.out;
}

pub fn disasm(self: *HbvmGen, out: std.io.AnyWriter, colors: std.io.tty.Config) void {
    self.link();

    var arena = std.heap.ArenaAllocator.init(self.out.allocator);
    defer arena.deinit();
    var map = std.AutoHashMap(u32, []const u8).init(arena.allocator());
    for (self.funcs.items) |gf| {
        map.put(gf.offset, gf.name) catch unreachable;
    }
    isa.disasm(self.out.items, arena.allocator(), &map, out, colors) catch unreachable;
}

pub fn emitFunc(self: *HbvmGen, func: *Func, opts: Mach.EmitOptions) void {
    opts.optimizations.execute(Node, func);

    const allocs = Regalloc.ralloc(Node, func);

    const id = opts.id;
    const name = opts.name;

    const tmp, const lock = func.beginTmpAlloc();
    defer lock.unlock();

    if (self.funcs.items.len <= id) {
        self.funcs.resize(id + 1) catch unreachable;
    }
    self.funcs.items[id].offset = @intCast(self.out.items.len);
    self.funcs.items[id].name = name;

    self.block_offsets = tmp.alloc(i32, func.block_count) catch unreachable;
    self.local_relocs = .init(tmp);
    self.allocs = allocs;

    var visited = std.DynamicBitSet.initEmpty(tmp, func.next_id) catch unreachable;
    const postorder = func.collectPostorder(tmp, &visited);
    const is_tail = for (postorder) |bb| {
        if (bb.base.kind == .CallEnd) break false;
    } else true;

    const reg_shift: u8 = if (is_tail) 12 else 31;
    for (self.allocs) |*r| r.* += reg_shift;
    const used_registers = if (self.allocs.len == 0) 0 else std.mem.max(u8, self.allocs) -| 31;

    const used_reg_size = @as(u16, (used_registers + @intFromBool(!is_tail))) * 8;

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

    const stack_size: i64 = used_reg_size + local_size;

    prelude: {
        if (used_registers != 0) {
            self.emit(.st, .{ .ret_addr, .stack_addr, -@as(i64, used_reg_size), used_reg_size });
        }
        if (stack_size != 0) {
            self.emit(.addi64, .{ .stack_addr, .stack_addr, @as(u64, @bitCast(-stack_size)) });
        }

        for (0..func.params.len) |i| {
            const argn = for (postorder[0].base.outputs()) |o| {
                if (o.kind == .Arg and o.extra(.Arg).* == i) break o;
            } else continue; // is dead
            self.emit(.cp, .{ self.reg(argn), isa.Reg.arg(i) });
        }
        break :prelude;
    }

    for (postorder, 0..) |bb, i| {
        self.block_offsets[bb.base.schedule] = @intCast(self.out.items.len);
        std.debug.assert(bb.base.schedule == i);
        self.emitBlockBody(tmp, &bb.base);
        const last = bb.base.outputs()[bb.base.output_len - 1];
        if (last.outputs().len == 0) {
            std.debug.assert(last.kind == .Return);
            if (stack_size != 0) {
                self.emit(.addi64, .{ .stack_addr, .stack_addr, @as(u64, @bitCast(stack_size)) });
            }
            if (used_registers != 0) {
                self.emit(.ld, .{ .ret_addr, .stack_addr, -@as(i64, used_reg_size), used_reg_size });
            }
            if (id == 0) {
                self.emit(.tx, .{});
            } else {
                self.emit(.jala, .{ .null, .ret_addr, 0 });
            }
        } else if (i + 1 == last.outputs()[0].schedule) {
            // noop
        } else {
            std.debug.assert(last.outputs()[0].isBasicBlockStart());
            self.local_relocs.append(.{
                .dest_block = last.outputs()[@intFromBool(last.isSwapped())].schedule,
                .rel = self.reloc(1, .rel32),
            }) catch unreachable;
            self.emit(.jmp, .{0});
        }
    }

    for (self.local_relocs.items) |lr| {
        self.doReloc(lr.rel, self.block_offsets[lr.dest_block]);
    }
}

pub fn emitBlockBody(self: *HbvmGen, tmp: std.mem.Allocator, node: *Func.Node) void {
    for (node.outputs()) |no| {
        const inps = no.dataDeps();
        switch (no.kind) {
            .CInt => {
                const extra = no.extra(.CInt);
                self.emit(.li64, .{ self.reg(no), @as(u64, @bitCast(extra.*)) });
            },
            .Arg => {},
            .Local => {
                const extra = no.extra(.Local);
                self.emit(.addi64, .{ self.reg(no), .stack_addr, extra.* });
            },
            .Load => {
                const size: u16 = @intCast(no.data_type.size());
                if (inps[0].?.kind == .Local) {
                    self.emit(.ld, .{ self.reg(no), .stack_addr, @as(i64, @bitCast(inps[0].?.extra(.Local).*)), size });
                } else {
                    self.emit(.ld, .{ self.reg(no), self.reg(inps[0]), 0, size });
                }
            },
            .Ld => {
                const size: u16 = @intCast(no.data_type.size());
                const off = no.extra(.Ld).offset;
                if (inps[0].?.kind == .Local) {
                    self.emit(.ld, .{ self.reg(no), .stack_addr, @as(i64, @bitCast(inps[0].?.extra(.Local).*)) + off, size });
                } else {
                    self.emit(.ld, .{ self.reg(no), self.reg(inps[0]), off, size });
                }
            },
            .Store => {
                const size: u16 = @intCast(no.data_type.size());
                if (inps[0].?.kind == .Local) {
                    self.emit(.st, .{ self.reg(inps[1]), .stack_addr, @as(i64, @bitCast(inps[0].?.extra(.Local).*)), size });
                } else {
                    self.emit(.st, .{ self.reg(inps[1]), self.reg(inps[0]), 0, size });
                }
            },
            .St => {
                const size: u16 = @intCast(no.data_type.size());
                const off = no.extra(.St).offset;
                if (inps[0].?.kind == .Local) {
                    self.emit(.st, .{ self.reg(inps[1]), .stack_addr, @as(i64, @bitCast(inps[0].?.extra(.Local).*)) + off, size });
                } else {
                    self.emit(.st, .{ self.reg(inps[1]), self.reg(inps[0]), off, size });
                }
            },
            .BlockCpy => {
                // not a mistake, the bmc is retarded
                self.emit(.bmc, .{ self.reg(inps[1]), self.reg(inps[0]), no.extra(.BlockCpy).size });
            },
            .BinOp => {
                const mone = std.math.maxInt(u64);
                const extra = no.extra(.BinOp);
                switch (extra.*) {
                    .iadd => switch (no.data_type) {
                        .i8 => self.binop(.add8, no),
                        .i16 => self.binop(.add16, no),
                        .i32 => self.binop(.add32, no),
                        .int => self.binop(.add64, no),
                        else => unreachable,
                    },
                    .isub => switch (no.data_type) {
                        .i8 => self.binop(.sub8, no),
                        .i16 => self.binop(.sub16, no),
                        .i32 => self.binop(.sub32, no),
                        .int => self.binop(.sub64, no),
                        else => unreachable,
                    },
                    .imul => switch (no.data_type) {
                        .i8 => self.binop(.mul8, no),
                        .i16 => self.binop(.mul16, no),
                        .i32 => self.binop(.mul32, no),
                        .int => self.binop(.mul64, no),
                        else => unreachable,
                    },
                    .udiv => {
                        const args = .{ self.reg(no), .null, self.reg(inps[0]), self.reg(inps[1]) };
                        switch (no.data_type) {
                            .i8 => self.emit(.diru8, args),
                            .i16 => self.emit(.diru16, args),
                            .i32 => self.emit(.diru32, args),
                            .int => self.emit(.diru64, args),
                            else => unreachable,
                        }
                    },
                    .sdiv => {
                        const args = .{ self.reg(no), .null, self.reg(inps[0]), self.reg(inps[1]) };
                        switch (no.data_type) {
                            .i8 => self.emit(.dirs8, args),
                            .i16 => self.emit(.dirs16, args),
                            .i32 => self.emit(.dirs32, args),
                            .int => self.emit(.dirs64, args),
                            else => unreachable,
                        }
                    },
                    .eq => {
                        self.binop(.cmpu, no);
                        self.emit(.cmpui, .{ self.reg(no), self.reg(no), 0 });
                        self.emit(.not, .{ self.reg(no), self.reg(no) });
                    },
                    .ne => {
                        self.binop(.cmpu, no);
                        self.emit(.cmpui, .{ self.reg(no), self.reg(no), 0 });
                    },
                    .ule => {
                        self.binop(.cmpu, no);
                        self.emit(.cmpui, .{ self.reg(no), self.reg(no), 1 });
                    },
                    .sle => {
                        self.binop(.cmps, no);
                        self.emit(.cmpui, .{ self.reg(no), self.reg(no), 1 });
                    },
                    .uge => {
                        self.binop(.cmpu, no);
                        self.emit(.cmpui, .{ self.reg(no), self.reg(no), mone });
                    },
                    .sge => {
                        self.binop(.cmps, no);
                        self.emit(.cmpui, .{ self.reg(no), self.reg(no), mone });
                    },
                    .ugt => {
                        self.binop(.cmpu, no);
                        self.emit(.cmpui, .{ self.reg(no), self.reg(no), 1 });
                        self.emit(.not, .{ self.reg(no), self.reg(no) });
                    },
                    .sgt => {
                        self.binop(.cmps, no);
                        self.emit(.cmpui, .{ self.reg(no), self.reg(no), 1 });
                        self.emit(.not, .{ self.reg(no), self.reg(no) });
                    },
                    .ult => {
                        self.binop(.cmpu, no);
                        self.emit(.cmpui, .{ self.reg(no), self.reg(no), mone });
                        self.emit(.not, .{ self.reg(no), self.reg(no) });
                    },
                    .slt => {
                        self.binop(.cmps, no);
                        self.emit(.cmpui, .{ self.reg(no), self.reg(no), mone });
                        self.emit(.not, .{ self.reg(no), self.reg(no) });
                    },
                }
            },
            .UnOp => {
                const extra = no.extra(.UnOp);
                switch (extra.*) {
                    .sext => {
                        switch (inps[0].?.data_type) {
                            .i8 => self.emit(.sxt8, .{ self.reg(no), self.reg(inps[0]) }),
                            .i16 => self.emit(.sxt16, .{ self.reg(no), self.reg(inps[0]) }),
                            .i32 => self.emit(.sxt32, .{ self.reg(no), self.reg(inps[0]) }),
                            else => unreachable,
                        }
                    },
                    .uext => {
                        const mask = (@as(u64, 1) << @intCast(inps[0].?.data_type.size() * 8)) - 1;
                        self.emit(.andi, .{ self.reg(no), self.reg(inps[0]), mask });
                    },
                    .neg => {
                        self.emit(.neg, .{ self.reg(no), self.reg(inps[0]) });
                    },
                }
            },
            .ImmBinOp => {
                const alloc = self.reg(no);
                const extra = no.extra(.ImmBinOp);
                switch (extra.op) {
                    inline .addi64, .muli64 => |t| {
                        self.emit(t, .{ alloc, self.reg(inps[0]), @as(u64, @bitCast(extra.imm)) });
                    },
                    else => unreachable,
                }
            },
            .IfOp => {
                self.local_relocs.append(.{
                    .dest_block = no.outputs()[1].schedule,
                    .rel = self.reloc(3, .rel16),
                }) catch unreachable;
                const extra = no.extra(.IfOp);
                const args = .{ self.reg(inps[0]), self.reg(inps[1]), 0 };
                switch (extra.op) {
                    inline .jgtu, .jltu, .jlts, .jgts, .jne, .jeq => |op| self.emit(op, args),
                    else => unreachable,
                }
            },
            .If => {
                self.local_relocs.append(.{
                    .dest_block = no.outputs()[1].schedule,
                    .rel = self.reloc(3, .rel16),
                }) catch unreachable;
                self.emit(.jeq, .{ self.reg(inps[0]), .null, 0 });
            },
            .Call => {
                const extra = no.extra(.Call);
                for (inps, 0..) |arg, i| {
                    self.emit(.cp, .{ isa.Reg.arg(i), self.reg(arg) });
                }

                self.global_relocs.append(.{
                    .dest = extra.id,
                    .rel = self.reloc(3, .rel32),
                }) catch unreachable;
                self.emit(.jal, .{ .ret_addr, .null, 0 });
            },
            .Mem => {},
            .Ret => {
                self.emit(.cp, .{ self.reg(no), .ret });
            },
            .Jmp => if (no.outputs()[0].kind == .Region or no.outputs()[0].kind == .Loop) {
                const idx = std.mem.indexOfScalar(?*Func.Node, no.outputs()[0].inputs(), no).? + 1;

                const Move = struct { isa.Reg, isa.Reg, u8 };
                var moves = std.ArrayList(Move).init(tmp);
                for (no.outputs()[0].outputs()) |o| {
                    if (o.kind == .Phi and o.data_type != .mem) {
                        std.debug.assert(o.inputs()[idx].?.kind == .MachMove);
                        const dst, const src = .{ self.reg(o), self.reg(o.inputs()[idx].?.inputs()[1]) };
                        if (dst != src) moves.append(.{ dst, src, 0 }) catch unreachable;
                    }
                }

                // code makes sure all moves are ordered so that register is only moved
                // into after all its uses
                //
                // in case of cycles, swaps are used instead in which case the conflicting
                // move is removed and remining moves are replaced with swaps

                const cycle_sentinel = 255;

                var reg_graph = std.EnumArray(isa.Reg, isa.Reg).initFill(.null);
                for (moves.items) |m| {
                    reg_graph.set(m[0], m[1]);
                }

                o: for (moves.items) |*m| {
                    var c = m[1];
                    while (c != m[0]) {
                        c = reg_graph.get(c);
                        m[2] += 1;
                        if (c == .null) continue :o;
                    }

                    reg_graph.set(c, .null);
                    m[2] = cycle_sentinel;
                }

                std.sort.pdq(Move, moves.items, {}, struct {
                    fn lt(_: void, lhs: Move, rhs: Move) bool {
                        return rhs[2] < lhs[2];
                    }
                }.lt);

                for (moves.items) |*m| {
                    if (m[2] == cycle_sentinel) {
                        while (reg_graph.get(m[1]) != .null) {
                            self.emit(.swa, .{ m[0], m[1] });
                            m[0] = m[1];
                            std.mem.swap(isa.Reg, reg_graph.getPtr(m[1]), &m[1]);
                        }
                        reg_graph.set(m[1], m[1]);
                    } else if (reg_graph.get(m[1]) != m[1]) {
                        self.emit(.cp, .{ m[0], m[1] });
                    }
                }
            },
            .MachMove => {
                //std.debug.assert(no.outputs()[0].kind == .Phi);
                //self.emit(.cp, .{ self.reg(no.outputs()[0]), self.reg(inps[0]) });
            },
            .Phi => {},
            .Return => {
                std.debug.assert(inps.len < 2);
                if (inps.len != 0) {
                    self.emit(.cp, .{ .ret, self.reg(inps[0]) });
                }
            },
            else => std.debug.panic("{any}", .{no.kind}),
        }
    }
}

fn binop(self: *HbvmGen, comptime op: isa.Op, n: *Func.Node) void {
    self.emit(op, .{ self.reg(n), self.reg(n.inputs()[1]), self.reg(n.inputs()[2]) });
}

fn reg(self: HbvmGen, n: ?*Func.Node) isa.Reg {
    return @enumFromInt(self.allocs[n.?.schedule]);
}

fn emit(self: *HbvmGen, comptime op: isa.Op, args: anytype) void {
    self.out.appendSlice(&isa.pack(op, args)) catch unreachable;
}

pub fn reloc(self: *HbvmGen, sub_offset: u8, arg: isa.Arg) Reloc {
    return .{ .offset = @intCast(self.out.items.len), .sub_offset = sub_offset, .operand = arg };
}

pub fn idealize(func: *Func, node: *Func.Node, work: *Func.WorkList) ?*Func.Node {
    const inps = node.inputs();

    if (node.kind == .If) {
        if (inps[1].?.kind == .BinOp) b: {
            work.add(inps[1].?);
            const op = inps[1].?.extra(.BinOp).*;
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

            return func.addNode(.IfOp, &.{ inps[0], op_inps[1], op_inps[2] }, .{
                .op = instr,
                .swapped = swap,
            });
        }
    }

    if (node.kind == .BinOp) {
        const op = node.extra(.BinOp).*;

        if (inps[2].?.kind == .CInt) b: {
            var imm = inps[2].?.extra(.CInt).*;

            const instr: isa.Op = switch (op) {
                .iadd => .addi64,
                .imul => .muli64,
                .isub => m: {
                    imm *= -1;
                    break :m .addi64;
                },
                else => break :b,
            };

            return func.addTypedNode(
                .ImmBinOp,
                node.data_type,
                &.{ null, node.inputs()[1] },
                .{ .op = instr, .imm = imm },
            );
        }
    }

    if (node.kind == .MemCpy) {
        if (inps[4].?.kind == .CInt) {
            return func.addNode(.BlockCpy, &.{ inps[0], inps[1], inps[2], inps[3] }, .{ .size = @intCast(inps[4].?.extra(.CInt).*) });
        }
    }

    if (node.kind == .Store) {
        if (node.base().kind == .ImmBinOp) {
            return func.addTypedNode(
                .St,
                node.data_type,
                &.{ inps[0], inps[1], node.base().inputs()[1], inps[3] },
                .{ .offset = node.base().extra(.ImmBinOp).imm },
            );
        }
    }

    if (node.kind == .Load) {
        if (node.base().kind == .ImmBinOp) {
            return func.addTypedNode(
                .Ld,
                node.data_type,
                &.{ inps[0], inps[1], node.base().inputs()[1] },
                .{ .offset = node.base().extra(.ImmBinOp).imm },
            );
        }
    }

    return null;
}
