out: *std.ArrayList(u8),
types: *Types,
relocs: std.ArrayList(BlockReloc) = undefined,
global_relocs: std.ArrayList(GloblReloc),
funcs: std.ArrayList(FuncData),
block_offsets: []i32 = undefined,
allocs: []u8 = undefined,

const std = @import("std");
const isa = @import("isa.zig");
const Func = @import("Func.zig");
const Types = @import("Types.zig");
const Regalloc = @import("Regalloc.zig");
const HbvmGen = @This();

pub const dir = "inputs";

pub const MachKind = enum(u16) {
    ImmBinOp = @typeInfo(Func.BuiltinNodeKind).@"enum".fields.len,
};

const FuncData = struct {
    offset: u32 = 0,
};

const GloblReloc = struct {
    rel: Reloc,
    dest: Types.Func,
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

pub const JointKind = b: {
    var builtin = @typeInfo(Func.NodeKind);
    const mach = @typeInfo(MachKind);
    builtin.@"enum".fields = builtin.@"enum".fields ++ mach.@"enum".fields;
    break :b @Type(builtin);
};

pub const Mach = union(MachKind) {
    ImmBinOp: extern struct {
        op: isa.Op,
        imm: i64,

        pub fn format(self: *const @This(), comptime _: anytype, _: anytype, writer: anytype) !void {
            try writer.print("{s}({d})", .{ @tagName(self.op), self.imm });
        }
    },

    pub const idealize = HbvmGen.idealize;
};

pub fn init(types: *Types, out: *std.ArrayList(u8)) HbvmGen {
    return .{
        .out = out,
        .types = types,
        .global_relocs = .init(out.allocator),
        .funcs = .init(out.allocator),
    };
}

pub fn deinit(self: *HbvmGen) void {
    self.global_relocs.deinit();
    self.funcs.deinit();
    self.* = undefined;
}

pub fn finalize(self: *HbvmGen) void {
    for (self.global_relocs.items) |r| {
        const dest: i64 = self.funcs.items[@intFromEnum(r.dest)].offset;
        const jump = dest - r.rel.offset;
        const location: usize = @intCast(r.rel.offset + r.rel.sub_offset);

        const size: usize = switch (r.rel.operand) {
            .rel32 => 4,
            .rel16 => 2,
            else => unreachable,
        };

        @memcpy(self.out.items[location..][0..size], @as(*const [8]u8, @ptrCast(&jump))[0..size]);
    }
}

pub fn emitFunc(self: *HbvmGen, func: *Func, id: Types.Func, allocs: []u8) void {
    const fdata = self.types.get(id);
    const tmp = func.beginTmpAlloc();

    self.funcs.resize(self.types.funcs.items.len) catch unreachable;
    self.funcs.items[@intFromEnum(id)].offset = @intCast(self.out.items.len);

    self.block_offsets = tmp.alloc(i32, func.block_count) catch unreachable;
    self.relocs = .init(tmp);
    self.allocs = allocs;

    const reg_shift: u8 = if (fdata.tail) 12 else 31;
    for (self.allocs) |*r| r.* += reg_shift;

    var visited = std.DynamicBitSet.initEmpty(tmp, func.next_id) catch unreachable;
    var stack = std.ArrayList(Func.Frame).init(tmp);
    const postorder = func.collectPostorder(tmp, &stack, &visited);

    for (fdata.args, 0..) |arg, i| {
        std.debug.assert(arg == .uint);
        const argn = for (postorder[0].base.outputs()) |o| {
            if (o.kind == .Arg and o.extra(.Arg).* == i) break o;
        } else unreachable;
        self.emit(.cp, .{ self.reg(argn), isa.Reg.arg(i) });
    }

    for (postorder, 0..) |bb, i| {
        std.debug.assert(postorder.len - bb.base.schedule - 1 == i);
        self.emitBlockBody(&bb.base);
        const last = bb.base.outputs()[bb.base.output_len - 1];
        if (postorder.len == i + 1) {
            // noop
        } else if (last.output_len == 1 and i + 1 == (postorder.len - last.outputs()[0].schedule - 1)) {
            // noop
        } else {
            std.debug.assert(Func.isBasicBlockStart(last.outputs()[0].kind));
            unreachable;
            //self.relocs.append(.{
            //    .dest_block = bb.base.outputs()[0].schedule,
            //    .rel = self.reloc(1, .rel32),
            //}) catch unreachable;
            //self.emit(.jmp, .{0});
        }
    }

    if (id == .main) {
        self.emit(.tx, .{});
    } else {
        self.emit(.jala, .{ .null, .ret_addr, 0 });
    }
}

pub fn emitBlockBody(self: *HbvmGen, node: *Func.Node) void {
    self.block_offsets[node.schedule] = @intCast(self.relocs.items.len);

    for (node.outputs()) |no| {
        const inps = no.inputs();
        const kind: JointKind = @enumFromInt(@intFromEnum(no.kind));
        switch (kind) {
            .CInt => {
                const extra = no.extra(.CInt);
                self.emit(.li64, .{ self.reg(no), @as(u64, @bitCast(extra.*)) });
            },
            .Arg => {},
            .Return => {
                self.emit(.cp, .{ .ret, self.reg(inps[1]) });
            },
            .BinOp => {
                const extra = no.extra(.BinOp);
                switch (extra.*) {
                    .@"+" => self.binop(.add64, no),
                    .@"-" => self.binop(.sub64, no),
                    .@"*" => self.binop(.mul64, no),
                    .@"/" => self.emit(.dirs64, .{ self.reg(no), .null, self.reg(inps[1]), self.reg(inps[2]) }),
                    else => std.debug.panic("{any}", .{extra.*}),
                }
            },
            .Call => {
                const extra = no.extra(.Call);
                for (inps[1..], 0..) |arg, i| {
                    self.emit(.cp, .{ isa.Reg.arg(i), self.reg(arg) });
                }

                self.global_relocs.append(.{
                    .dest = extra.id,
                    .rel = self.reloc(3, .rel32),
                }) catch unreachable;
                self.emit(.jal, .{ .ret_addr, .null, 0 });
            },
            .Ret => {
                self.emit(.cp, .{ self.reg(no), .ret });
            },
            .ImmBinOp => {
                const alloc = self.reg(no);
                const extra = no.machExtra(Mach, .ImmBinOp);
                switch (extra.op) {
                    inline .addi64, .muli64 => |t| {
                        self.emit(t, .{ alloc, self.reg(inps[1]), @as(u64, @bitCast(extra.imm)) });
                    },
                    else => unreachable,
                }
            },
            else => std.debug.panic("{any}", .{kind}),
        }
    }
}

fn binop(self: HbvmGen, comptime op: isa.Op, n: *Func.Node) void {
    self.emit(op, .{ self.reg(n), self.reg(n.inputs()[1]), self.reg(n.inputs()[2]) });
}

fn reg(self: HbvmGen, n: ?*Func.Node) isa.Reg {
    return @enumFromInt(self.allocs[n.?.schedule]);
}

fn emit(self: HbvmGen, comptime op: isa.Op, args: anytype) void {
    self.out.appendSlice(&isa.pack(op, args)) catch unreachable;
}

pub fn filter(_: @This(), node: *Func.Node) bool {
    return Func.isCfg(node.kind);
}

pub fn reloc(self: *HbvmGen, sub_offset: u8, arg: isa.Arg) Reloc {
    return .{ .offset = @intCast(self.out.items.len), .sub_offset = sub_offset, .operand = arg };
}

pub fn idealize(func: *Func, node: *Func.Node) ?*Func.Node {
    const inps = node.inputs();
    if (node.kind == .BinOp) {
        const op = node.extra(.BinOp).*;

        if (inps[2].?.kind == .CInt) b: {
            var imm = inps[2].?.extra(.CInt).*;

            const instr: isa.Op = switch (op) {
                .@"+" => .addi64,
                .@"*" => .muli64,
                .@"-" => m: {
                    imm *= -1;
                    break :m .addi64;
                },
                else => break :b,
            };

            return func.addMachNode(Mach, .ImmBinOp, &.{ null, node.inputs()[1] }, .{
                .op = instr,
                .imm = imm,
            });
        }
    }

    return null;
}
