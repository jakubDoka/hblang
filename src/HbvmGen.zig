out: std.ArrayList(u8),
funcs: std.ArrayList(FuncData),
global_lookup: std.ArrayList(u32),
globals: std.ArrayList(GlobalData),
globals_appended: usize = 0,
global_relocs: std.ArrayList(GloblReloc),
local_relocs: std.ArrayList(BlockReloc) = undefined,
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

pub const eca = std.math.maxInt(u32);
pub const dir = "inputs";

const GlobalData = struct {
    name: []const u8,
    ptr: ?[*]const u8 = null,
    size: u32,
    offset: u32 = 0,
};

const FuncData = struct {
    name: []const u8,
    offset: u32 = 0,
};

const GloblReloc = struct {
    rel: Reloc,
    dest: u32,
    kind: enum { func, global },
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

pub fn emitFunc(self: *HbvmGen, func: *Func, opts: Mach.EmitOptions) void {
    opts.optimizations.execute(Node, func);

    const allocs = Regalloc.ralloc(Node, func);

    const id = opts.id;
    const name = opts.name;
    const entry = opts.entry;

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
            self.emit(.cp, .{ self.reg(argn), isa.Reg.arg(func.returns.len, i) });
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
            if (entry) {
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

pub fn emitData(self: *HbvmGen, opts: Mach.DataOptions) void {
    if (self.global_lookup.items.len <= opts.id) {
        self.global_lookup.resize(opts.id + 1) catch unreachable;
    }

    self.global_lookup.items[opts.id] = @intCast(self.globals.items.len);
    self.globals.append(switch (opts.value) {
        .init => |v| .{ .ptr = v.ptr, .size = @intCast(v.len), .name = opts.name },
        .uninit => |size| .{ .size = @intCast(size), .name = opts.name },
    }) catch unreachable;
}

pub fn finalize(self: *HbvmGen) std.ArrayList(u8) {
    _ = self.link(false);

    defer self.deinit();
    return self.out;
}

pub fn disasm(self: *HbvmGen, out: std.io.AnyWriter, colors: std.io.tty.Config) void {
    const code_len = self.link(false);

    var arena = std.heap.ArenaAllocator.init(self.out.allocator);
    defer arena.deinit();
    var map = std.AutoHashMap(u32, []const u8).init(arena.allocator());
    for (self.funcs.items) |gf| {
        map.put(gf.offset, gf.name) catch unreachable;
    }
    for (self.globals.items) |gf| {
        map.put(gf.offset, gf.name) catch unreachable;
    }
    isa.disasm(self.out.items[0..code_len], arena.allocator(), &map, out, colors) catch unreachable;
}

pub fn init(gpa: std.mem.Allocator) HbvmGen {
    return .{
        .out = .init(gpa),
        .global_relocs = .init(gpa),
        .global_lookup = .init(gpa),
        .funcs = .init(gpa),
        .globals = .init(gpa),
    };
}

pub fn deinit(self: *HbvmGen) void {
    self.global_relocs.deinit();
    self.funcs.deinit();
    self.globals.deinit();
    self.global_lookup.deinit();
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

pub fn link(self: *HbvmGen, push_uninit_memory: bool) usize {
    for (self.globals.items[self.globals_appended..]) |*ig| {
        const value = ig.ptr orelse continue;
        ig.offset = @intCast(self.out.items.len);
        self.out.appendSlice(value[0..ig.size]) catch unreachable;
    }

    var cursor = self.out.items.len;
    for (self.globals.items[self.globals_appended..]) |*ug| {
        if (ug.ptr != null) continue;
        ug.offset = @intCast(cursor);
        cursor += ug.size;
    }
    if (push_uninit_memory) self.out.resize(cursor) catch unreachable;

    for (self.global_relocs.items) |r| {
        const offset = switch (r.kind) {
            .func => self.funcs.items[r.dest].offset,
            .global => self.globals.items[self.global_lookup.items[r.dest]].offset,
        };
        self.doReloc(r.rel, offset);
    }

    self.global_relocs.items.len = 0;
    self.globals_appended = self.globals.items.len;

    var data_size: usize = 0;
    for (self.globals.items[0..self.globals_appended]) |g| if (push_uninit_memory or g.ptr != null) {
        data_size += g.size;
    };

    return self.out.items.len - data_size;
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
            .GlobalAddr => {
                const extra = no.extra(.GlobalAddr);
                self.global_relocs.append(.{
                    .kind = .global,
                    .dest = extra.id,
                    .rel = self.reloc(3, .rel32),
                }) catch unreachable;
                self.emit(.lra, .{ self.reg(no), .null, 0 });
            },
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
                const extra = no.extra(.BinOp).*;

                var op: isa.Op = switch (extra) {
                    .iadd => .add8,
                    .isub => .sub8,
                    .imul => .mul8,
                    .udiv => .diru8,
                    .sdiv => .dirs8,
                    .eq, .ne, .uge, .ule, .ugt, .ult => .cmpu,
                    .sge, .sle, .sgt, .slt => .cmps,
                };

                switch (extra) {
                    .eq, .ne, .uge, .ule, .ugt, .ult, .sge, .sle, .sgt, .slt => {},
                    else => op = @enumFromInt(@intFromEnum(op) +
                        (@intFromEnum(no.data_type) - @intFromEnum(graph.DataType.i8))),
                }

                const lhs, const rhs = .{ self.reg(no.inputs()[1]), self.reg(no.inputs()[2]) };
                switch (extra) {
                    .udiv, .sdiv => self.emitLow("RRRR", op, .{ self.reg(no), .null, lhs, rhs }),
                    else => self.emitLow("RRR", op, .{ self.reg(no), lhs, rhs }),
                }

                extra_comparison_instrs: {
                    const compare_to: u64 = switch (extra) {
                        .eq, .ne => 0,
                        .ugt, .sgt, .ule, .sle => 1,
                        .ult, .slt, .uge, .sge => mone,
                        else => break :extra_comparison_instrs,
                    };
                    self.emit(.cmpui, .{ self.reg(no), self.reg(no), compare_to });
                    switch (extra) {
                        .eq, .ugt, .sgt, .ult, .slt => {
                            self.emit(.not, .{ self.reg(no), self.reg(no) });
                        },
                        else => {},
                    }
                }
            },
            .UnOp => {
                const extra = no.extra(.UnOp);
                switch (extra.*) {
                    .sext => {
                        const op: isa.Op = @enumFromInt(@intFromEnum(isa.Op.sxt8) +
                            (@intFromEnum(inps[0].?.data_type) - @intFromEnum(graph.DataType.i8)));
                        self.emitLow("RR", op, .{ self.reg(no), self.reg(inps[0]) });
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

                const chars = "BHWD";
                const types = .{ u8, u16, u32, u64 };
                switch (no.data_type) {
                    inline .i8, .i16, .i32, .int => |t| {
                        const idx = @intFromEnum(t) - @intFromEnum(graph.DataType.i8);
                        self.emitLow(
                            "RR" ++ chars[idx..][0..1],
                            extra.op,
                            .{ alloc, self.reg(inps[0]), @as(types[idx], @truncate(@as(u64, @bitCast(extra.imm)))) },
                        );
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
                self.emitLow("RRP", extra.op, .{ self.reg(inps[0]), self.reg(inps[1]), 0 });
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
                    self.emit(.cp, .{ isa.Reg.arg(extra.ret_count, i), self.reg(arg) });
                }

                if (extra.id == eca) {
                    self.emit(.eca, .{});
                } else {
                    self.global_relocs.append(.{
                        .dest = extra.id,
                        .kind = .func,
                        .rel = self.reloc(3, .rel32),
                    }) catch unreachable;
                    self.emit(.jal, .{ .ret_addr, .null, 0 });
                }
            },
            .Mem => {},
            .Ret => {
                const idx = no.extra(.Ret).*;
                self.emit(.cp, .{ self.reg(no), isa.Reg.ret(idx) });
            },
            .Jmp => if (no.outputs()[0].kind == .Region or no.outputs()[0].kind == .Loop) {
                const idx = std.mem.indexOfScalar(?*Func.Node, no.outputs()[0].inputs(), no).? + 1;

                const Depth = u8;

                const Move = struct { isa.Reg, isa.Reg, Depth };
                var moves = std.ArrayList(Move).init(tmp);
                for (no.outputs()[0].outputs()) |o| {
                    if (o.isDataPhi()) {
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

                const cycle_sentinel = std.math.maxInt(Depth);

                var reg_graph = std.EnumArray(isa.Reg, isa.Reg).initFill(.null);
                for (moves.items) |m| {
                    reg_graph.set(m[0], m[1]);
                }

                o: for (moves.items) |*m| {
                    var seen = std.EnumSet(isa.Reg).initEmpty();
                    var c = m[1];
                    while (c != m[0]) {
                        c = reg_graph.get(c);
                        m[2] += 1;
                        if (c == .null or seen.contains(c)) continue :o;
                        seen.insert(c);
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
                std.debug.assert(inps.len < 3);
                for (inps, 0..) |inp, i| {
                    self.emit(.cp, .{ isa.Reg.ret(i), self.reg(inp) });
                }
            },
            else => std.debug.panic("{any}", .{no.kind}),
        }
    }
}

fn reg(self: HbvmGen, n: ?*Func.Node) isa.Reg {
    return @enumFromInt(self.allocs[n.?.schedule]);
}

fn emit(self: *HbvmGen, comptime op: isa.Op, args: isa.TupleOf(isa.ArgsOf(op))) void {
    self.emitLow(isa.spec[@intFromEnum(op)][1], op, args);
}

fn emitLow(self: *HbvmGen, comptime arg_str: []const u8, op: isa.Op, args: isa.TupleOf(isa.ArgsOfStr(arg_str))) void {
    std.debug.assert(std.mem.eql(u8, isa.spec[@intFromEnum(op)][1], arg_str));
    self.out.append(@intFromEnum(op)) catch unreachable;
    self.out.appendSlice(std.mem.asBytes(&isa.packTo(isa.ArgsOfStr(arg_str), args))) catch unreachable;
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
