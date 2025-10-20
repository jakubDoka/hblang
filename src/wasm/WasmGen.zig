const std = @import("std");

const root = @import("hb");
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Regalloc = root.backend.Regalloc;
const utils = root.utils;
const object = root.wasm.object;
const matcher = @import("wasm.WasmGen");

const WasmGen = @This();
const Func = graph.Func(WasmGen);
const opb = object.opb;

gpa: std.mem.Allocator,
mach: Mach = .init(WasmGen),
indirect_signatures: std.ArrayList(u8) = .empty,
indirect_signature_count: u64 = 0,
stack_size: u64 = 1024 * 128,
ctx: *Ctx = undefined,

pub fn loadDatatype(node: *Func.Node) graph.DataType {
    return switch (node.extra2()) {
        inline .SignedLoad,
        .SignedStackLoad,
        .UnsignedLoad,
        .UnsignedStackLoad,
        => |extra| extra.src_ty,
        else => node.data_type,
    };
}

pub const Set = std.DynamicBitSetUnmanaged;

pub fn setMasks(set: *Set) []Set.MaskInt {
    return graph.setMasks(set.*);
}

pub fn setIntersects(a: Set, b: Set) bool {
    return for (graph.setMasks(a), graph.setMasks(b)) |aa, bb| {
        if (aa & bb != 0) return true;
    } else false;
}

pub const i_know_the_api = {};

pub fn isDef(self: *Func.Node) bool {
    return self.id != on_stack_id and
        self.kind != .GetLocal and
        self.kind != .WrapI64 and
        self.kind != .StackAddr;
}

pub const on_stack_id = std.math.maxInt(u16);
pub const uses_tee_id = on_stack_id - 1;

pub const ScopeRange = struct {
    kind: enum { loop, block },
    range: [2]u16,
    signifier: *Func.Node,

    pub fn format(slf: *const @This(), writer: *std.Io.Writer) !void {
        try writer.print("{s} {any} {f}", .{
            @tagName(slf.kind),
            slf.range,
            slf.signifier,
        });
    }
};

pub const Ctx = struct {
    start_pos: usize,
    buf: std.Io.Writer.Allocating,
    allocs: []u16 = undefined,
    scope_stack: std.ArrayListUnmanaged(ScopeRange) = undefined,
    stack_base: u64 = undefined,
    arg_base: u32 = undefined,
};

pub const classes = enum {
    pub const WStore = extern struct {
        base: graph.Store = .{},
        offset: i64,
    };
    pub const StackStore = extern struct {
        base: graph.Store = .{},
        offset: i64,
        pub const data_dep_offset = 2;
    };
    pub const WLoad = extern struct {
        base: graph.Load = .{},
        offset: i64,
    };
    pub const UnsignedLoad = extern struct {
        base: graph.Load = .{},
        src_ty: graph.DataType,
        offset: i64,
    };
    pub const SignedLoad = extern struct {
        base: graph.Load = .{},
        src_ty: graph.DataType,
        offset: i64,
    };
    pub const StackLoad = extern struct {
        base: graph.Load = .{},
        offset: i64,
        pub const data_dep_offset = 2;
    };
    pub const UnsignedStackLoad = extern struct {
        base: graph.Load = .{},
        src_ty: graph.DataType,
        offset: i64,
        pub const data_dep_offset = 2;
    };
    pub const SignedStackLoad = extern struct {
        base: graph.Load = .{},
        src_ty: graph.DataType,
        offset: i64,
        pub const data_dep_offset = 2;
    };
    pub const GetLocal = extern struct {};
    pub const WrapI64 = extern struct {};
    pub const StackAddr = extern struct {};
    pub const Eqz = extern struct {};
};

pub fn isSwapped(node: *Func.Node) bool {
    return node.kind == .If;
}

pub fn idealize(self: *WasmGen, func: *Func, node: *Func.Node, work: *Func.WorkList) ?*Func.Node {
    _ = self;
    const inps = node.inputs();

    if (node.kind == .BinOp) {
        const op: graph.BinOp = node.extra(.BinOp).op;

        if (op.isCmp() and !op.isFloat()) {
            const ext_op: graph.UnOp = if (op.isSigned()) .sext else .uext;
            inline for (inps[1..3], 1..) |inp, i| {
                if (inp.?.data_type.size() < 4) {
                    const new = func.addUnOp(node.sloc, ext_op, .i32, inp.?);
                    work.add(new);
                    _ = func.setInput(node, i, new);
                }
            }
        }
    }

    if (node.kind == .UnOp) {
        const op: graph.UnOp = node.extra(.UnOp).op;

        if (op == .ineg) {
            return func.addBinOp(
                node.sloc,
                .isub,
                node.data_type,
                func.addIntImm(node.sloc, node.data_type, 0),
                node.inputs()[1].?,
            );
        }

        if (op == .bnot) {
            return func.addBinOp(
                node.sloc,
                .bxor,
                node.data_type,
                func.addIntImm(node.sloc, node.data_type, -1),
                node.inputs()[1].?,
            );
        }
    }

    return null;
}

pub fn idealizeMach(self: *WasmGen, func: *Func, node: *Func.Node, work: *Func.WorkList) ?*Func.Node {
    if (matcher.idealize(self, func, node, work)) |n| return n;

    return null;
}

const set_cap = 256;
const group_cap: usize = 64;

pub fn typeMaskOffset(ty: graph.DataType) usize {
    return group_cap * @as(usize, switch (dataTypeToWasmType(ty)) {
        .i32 => 0,
        .i64 => 1,
        .f32 => 2,
        .f64 => 3,
        else => unreachable,
    });
}

pub fn typeMask(ty: graph.DataType, arena: *utils.Arena) Set {
    errdefer unreachable;

    var mask = try Set.initEmpty(arena.allocator(), set_cap);

    mask.setRangeValue(.{ .start = typeMaskOffset(ty), .end = typeMaskOffset(ty) + group_cap }, true);

    return mask;
}

pub fn regMask(
    node: *Func.Node,
    func: *Func,
    idx: usize,
    arena: *utils.Arena,
) Set {
    errdefer unreachable;

    if (node.kind == .Arg) {
        std.debug.assert(idx == 0);

        var mask = try Set.initEmpty(arena.allocator(), set_cap);

        var pos: usize = 0;
        for (func.signature.params()[0..node.extra(.Arg).index]) |param| {
            if (param == .Reg and dataTypeToWasmType(param.Reg) == dataTypeToWasmType(node.data_type)) {
                pos += 1;
            }
        }

        mask.set(pos + typeMaskOffset(node.data_type));

        return mask;
    }

    if (idx == 0) {
        std.debug.assert(node.isDef());
        return typeMask(node.data_type, arena);
    }

    return try Set.initFull(arena.allocator(), set_cap);
}

pub fn dataTypeToWasmType(ty: graph.DataType) object.Type {
    return switch (ty) {
        .i32, .i16, .i8 => .i32,
        .i64 => .i64,
        .f32 => .f32,
        .f64 => .f64,
        else => unreachable,
    };
}

pub fn encodeFnType(writer: *std.Io.Writer, ty: graph.Signature) void {
    errdefer unreachable;

    var params_len: u32 = 0;
    for (ty.params()) |param| {
        if (param == .Reg) params_len += 1;
    }

    var results_len: u32 = 0;
    for (ty.returns() orelse &.{}) |param| {
        if (param == .Reg) results_len += 1;
    }

    try writer.writeByte(0x60);

    try writer.writeUleb128(params_len);
    for (ty.params()) |param| {
        if (param == .Reg) {
            try writer.writeByte(dataTypeToWasmType(param.Reg).raw());
        }
    }

    try writer.writeUleb128(results_len);
    for (ty.returns() orelse &.{}) |param| {
        if (param == .Reg) {
            try writer.writeByte(dataTypeToWasmType(param.Reg).raw());
        }
    }
}

const Stacker = struct {
    gen: *WasmGen,
    index: usize,
    func: *Func,
    block: *Func.CfgNode,
    second_round: bool,

    pub fn recoverTree(self: *@This()) bool {
        const instr = self.block.base.outputs()[self.index].get();

        if (instr.kind == .Phi or instr.kind == .WrapI64 or instr.kind == .GetLocal) {
            return undefined;
        }

        var dataDeps = instr.dataDeps();

        if (dataDeps.len != 0 and instr.kind == .BinOp and instr.extra(.BinOp).op.isComutative() and
            dataDeps[0].schedule > dataDeps[1].schedule)
        {
            for (dataDeps[0..], 1..) |dep, j| {
                const idx = dep.posOfOutput(j, instr);
                dep.outputs()[idx] = .init(instr, 3 - j, null);
            }
            std.mem.swap(*Func.Node, &dataDeps[0], &dataDeps[1]);
        }

        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        dataDeps = tmp.arena.dupe(*Func.Node, dataDeps);

        const is_indirect = instr.kind == .Call and instr.extra(.Call).id == graph.indirect_call;

        // in case of indirect calls, first argument becomes the last
        if (is_indirect) {
            std.mem.rotate(*Func.Node, dataDeps, dataDeps.len - 1);
        }

        var iter = std.mem.reverseIterator(dataDeps);
        var i: usize = dataDeps.len;
        const sentinel = 100;
        var ret_idx: usize = sentinel;
        while (@as(?*Func.Node, iter.next())) |def| {
            i -= 1;
            defer instr.input_ordered_len -= 1;

            if (def.kind == .StackArgOffset and instr.kind == .Call) continue;

            var appended: usize = 0;

            const needs_load = b: {
                if (def.kind == .Arg or def.kind == .Phi) break :b true;

                if (def.kind == .Ret) {
                    if (true) break :b true;

                    if (ret_idx == sentinel) {
                        ret_idx = def.extra(.Ret).index;
                    } else {
                        if (ret_idx != def.extra(.Ret).index + 1) break :b true;
                        ret_idx -= 1;

                        // NOTE: we dont need to check for 0 since we would not
                        // find more rets anyway
                    }
                }
                // NOTE: rets are the last thing in the block, and we dont care
                // about Mem so nothing else to handle

                if (def.cfg0() != self.block) break :b true;

                if (def.schedule != self.index - 1) break :b true;

                var count: usize = 0;
                for (def.outputs()) |o| {
                    if (o.get().hasUseFor(o.pos(), def)) count += 1;
                }

                if (count > 1) break :b true;

                break :b false;
            };

            if (needs_load) {
                _ = self.func.addNode(.GetLocal, def.sloc, def.data_type, &.{ &self.block.base, def }, .{});
                appended += 1;
            }

            const needs_wrap =
                instr.kind == .MemCpy or
                (instr.isStore() and dataDeps.len != 1 and i == 0) or
                (is_indirect and i == dataDeps.len - 1) or
                instr.isLoad();
            if (needs_wrap) {
                _ = self.func.addNode(.WrapI64, def.sloc, .top, &.{&self.block.base}, .{});
                appended += 1;
            }

            const to_rotate = self.block.base.outputs()[self.index..];
            std.mem.rotate(Func.Node.Out, to_rotate, to_rotate.len - appended);

            if (!needs_load) {
                def.id = on_stack_id;
                self.index -= 1;
                _ = self.recoverTree();
            }
        }

        if (!self.second_round and switch (instr.kind) {
            .StackLoad, .StackStore, .SignedStackLoad, .UnsignedStackLoad => true,
            else => false,
        }) {
            _ = self.func.addNode(.StackAddr, .none, .top, &.{&self.block.base}, .{});
            const to_rotate = self.block.base.outputs()[self.index..];
            std.mem.rotate(Func.Node.Out, to_rotate, to_rotate.len - 1);
        }

        return undefined;
    }

    pub fn recoverBlockTrees(self: *@This()) void {
        for (self.block.base.outputs(), 0..) |out, i| {
            out.get().schedule = @intCast(i);
        }

        while (self.index > 0) {
            self.index -= 1;
            _ = self.recoverTree();
        }
    }
};

pub fn emitFunc(self: *WasmGen, func: *Func, opts: Mach.EmitOptions) void {
    errdefer unreachable;

    const id = opts.id;
    const linkage = opts.linkage;
    const name = if (opts.special == .memcpy)
        "memcpy"
    else if (opts.special == .entry)
        "main"
    else
        opts.name;

    const sym = try self.mach.out.startDefineFunc(self.gpa, id, name, .func, linkage, opts.is_inline);
    _ = sym;
    defer self.mach.out.endDefineFunc(id);

    // For inport, we smuggle the signature with the function
    if (opts.linkage == .imported) {
        var ctx = Ctx{
            .start_pos = self.mach.out.code.items.len,
            .buf = .fromArrayList(self.gpa, &self.mach.out.code),
        };
        defer self.mach.out.code = ctx.buf.toArrayList();

        encodeFnType(&ctx.buf.writer, func.signature);
        return;
    }

    if (opts.optimizations.opts.mode == .release) {
        opts.optimizations.opts.optimizeRelease(WasmGen, self, func);
    } else {
        opts.optimizations.opts.optimizeDebug(WasmGen, self, func);
    }

    var ctx = Ctx{
        .start_pos = self.mach.out.code.items.len,
        .buf = .fromArrayList(self.gpa, &self.mach.out.code),
    };
    defer self.mach.out.code = ctx.buf.toArrayList();

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const loop_ranges, const changed = func.backshiftLoopBodies(tmp.arena);

    self.ctx = &ctx;

    func.computeStructArgLayout();

    // NOTE: this is inneficient and we make more locals then we need but its
    // also simple and lets me focus on one problem at a time, just generate
    // wasm that works.

    // backpatch later
    try self.ctx.buf.writer.writeInt(u32, 0, .little);

    encodeFnType(&self.ctx.buf.writer, func.signature);

    self.ctx.buf.writer
        .buffer[self.ctx.start_pos..][0..4].* =
        @bitCast(@as(u32, @intCast(self.ctx.buf.writer.end -
        self.ctx.start_pos - @sizeOf(u32))));

    for (0..2) |i| {
        for (func.gcm.postorder) |block| {
            var stacker = Stacker{
                .gen = self,
                .index = block.base.outputs().len,
                .func = func,
                .block = block,
                .second_round = i != 0,
            };
            stacker.recoverBlockTrees();
        }

        if (false) {
            for (func.gcm.postorder) |block| {
                std.debug.print("{f}\n", .{block});
                for (block.base.outputs()) |out| {
                    std.debug.print("  {f}\n", .{out.get()});
                }
            }
        }

        var rloc = Regalloc{};
        self.ctx.allocs = rloc.ralloc(WasmGen, func);

        if (rloc.inserted_splits == 0) break;
    } else unreachable;

    // Discover TEE oportunities
    for (func.gcm.postorder) |bb| {
        var outs = bb.base.outputs();
        var i: usize = 0;
        while (i < outs.len - 1) : (i += 1) {
            const curr = outs[i];
            const next = outs[i + 1];

            if (next.get().kind == .GetLocal and
                next.get().inputs()[1].? == curr.get() and
                curr.get().kind != .Phi and curr.get().kind != .Arg and
                curr.get().kind != .Ret)
            {
                std.mem.rotate(Func.Node.Out, outs[i..], 1);
                func.kill(next.get());
                outs = bb.base.outputs();
                curr.get().id = uses_tee_id;
            }
        }
    }

    const LocalCounts = struct {
        i32: usize = 0,
        i64: usize = 0,
        f32: usize = 0,
        f64: usize = 0,

        pub fn get(slf: *@This(), ty: graph.DataType) *usize {
            return switch (dataTypeToWasmType(ty)) {
                .vec, .fnc => unreachable,
                inline else => |t| &@field(slf, @tagName(t)),
            };
        }
    };

    var param_counts: LocalCounts = .{};
    var seen = try Set.initEmpty(tmp.arena.allocator(), set_cap);
    const new_allocs = tmp.arena.alloc(u16, set_cap);

    var params_len: u32 = 0;
    for (func.signature.params(), 0..) |param, i| {
        if (param == .Reg) {
            for (func.gcm.postorder[0].base.outputs()) |out| {
                if (out.get().kind == .Arg and out.get().extra(.Arg).index == i) {
                    out.get().extra(.Arg).index = params_len;
                    break;
                }
            }

            const cnt = param_counts.get(param.Reg);
            seen.set(typeMaskOffset(param.Reg) + cnt.*);
            new_allocs[typeMaskOffset(param.Reg) + cnt.*] = @intCast(params_len);
            cnt.* += 1;

            params_len += 1;
        }
    }

    var counters: LocalCounts = .{};

    func.gcm.instr_count = 0;

    for (func.gcm.postorder) |block| {
        for (block.base.outputs()) |out| {
            const instr = out.get();

            if (!instr.isDef()) {
                continue;
            }

            const alloc = self.ctx.allocs[instr.schedule];

            if (instr.kind == .Arg) continue;

            if (seen.isSet(alloc)) continue;
            seen.set(alloc);

            const cnt = counters.get(instr.data_type);
            new_allocs[alloc] = @intCast(cnt.*);
            cnt.* += 1;
        }
    }

    var local_group_count: usize = 0;
    inline for (std.meta.fields(@TypeOf(counters))) |field| {
        local_group_count += @intFromBool(@field(counters, field.name) != 0);
    }

    try self.ctx.buf.writer.writeUleb128(local_group_count);
    inline for (std.meta.fields(@TypeOf(counters))) |field| {
        if (@field(counters, field.name) != 0) {
            try self.ctx.buf.writer
                .writeUleb128(@field(counters, field.name));
            try self.ctx.buf.writer
                .writeByte(@field(object.Type, field.name).raw());
        }
    }

    var cursor: usize = 0;
    inline for (std.meta.fields(@TypeOf(counters))) |field| {
        const fld = @field(counters, field.name);
        @field(counters, field.name) = cursor;
        cursor += fld;
    }

    for (func.gcm.postorder) |block| {
        for (block.base.outputs()) |out| {
            const instr = out.get();

            if (!instr.isDef()) continue;

            if (instr.id == on_stack_id) {
                continue;
            }

            const base = counters.get(instr.data_type).*;
            const param_count = param_counts.get(instr.data_type).*;
            const alloc = self.ctx.allocs[instr.schedule];

            const prefix = if (alloc - typeMaskOffset(instr.data_type) < param_count) 0 else params_len + base;

            self.ctx.allocs[instr.schedule] = @intCast(prefix + new_allocs[self.ctx.allocs[instr.schedule]]);
        }
    }

    const frame_alignment = 8;

    var stack_size = func.computeStackLayout(0);
    stack_size = std.mem.alignForward(i64, stack_size, frame_alignment);

    _, const call_slot_size = func.computeCallSlotSize();

    self.ctx.stack_base = call_slot_size;
    stack_size += @intCast(call_slot_size);
    self.ctx.arg_base = @intCast(stack_size);

    if (stack_size != 0) {
        try self.ctx.buf.writer.writeByte(opb(.global_get));
        try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);

        try self.ctx.buf.writer.writeByte(opb(.i64_const));
        try self.ctx.buf.writer.writeSleb128(stack_size);

        try self.ctx.buf.writer.writeByte(opb(.i64_sub));

        try self.ctx.buf.writer.writeByte(opb(.global_set));
        try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);
    }

    var scope_ranges = tmp.arena.makeArrayList(ScopeRange, func.gcm.postorder.len);

    for (loop_ranges) |lr| {
        scope_ranges.appendAssumeCapacity(.{
            .kind = .loop,
            .range = lr,
            .signifier = &func.gcm.postorder[lr[0]].base,
        });
    }

    for (func.gcm.postorder) |rbb| {
        if ((rbb.base.kind == .Then or rbb.base.kind == .Else) and
            rbb.base.inputs()[0].?.kind == .If)
        {
            const if_schedule = rbb.base.inputs()[0].?.inputs()[0].?.schedule;
            if (if_schedule != rbb.base.schedule - 1) {
                scope_ranges.appendAssumeCapacity(.{
                    .kind = .block,
                    .range = .{
                        if_schedule,
                        rbb.base.schedule - 1,
                    },
                    .signifier = rbb.base.inputs()[0].?,
                });
            }
        }

        if (rbb.base.kind == .Region) {
            for (rbb.base.inputs()) |inp| {
                std.debug.assert(inp.?.kind == .Jmp);
                const pred = inp.?.inputs()[0].?;
                if (pred.schedule + 1 != rbb.base.schedule) {
                    scope_ranges.appendAssumeCapacity(.{
                        .kind = .block,
                        .range = .{
                            pred.schedule,
                            rbb.base.schedule - 1,
                        },
                        .signifier = pred,
                    });
                }
            }
        }
    }

    std.sort.pdq(ScopeRange, scope_ranges.items, {}, enum {
        fn lessThenFn(_: void, a: ScopeRange, b: ScopeRange) bool {
            return a.range[1] > b.range[1];
        }
    }.lessThenFn);

    const log_cfg = false;

    if (log_cfg) {
        std.debug.print("{}\n", .{changed});

        for (scope_ranges.items) |lr| {
            std.debug.print("{f}\n", .{lr});
        }
    }

    for (scope_ranges.items) |*sr| {
        while (func.gcm.postorder[sr.range[0]].base.kind == .CallEnd) sr.range[0] -= 1;
    }

    for (scope_ranges.items) |*sr| {
        std.debug.assert(sr.range[0] <= sr.range[1]);

        if (sr.kind == .loop) continue;
        for (scope_ranges.items) |*osr| {
            if (sr == osr) continue;
            if (sr.range[0] >= osr.range[0] and sr.range[0] <= osr.range[1] and sr.range[1] > osr.range[1]) {
                sr.range[0] = osr.range[0];
            }
        }
    }

    if (log_cfg) {
        func.fmtScheduledLog();
        for (scope_ranges.items) |lr| {
            std.debug.print("{f}\n", .{lr});
        }
    }

    self.ctx.scope_stack = tmp.arena.makeArrayList(ScopeRange, scope_ranges.items.len);

    for (func.gcm.postorder, 0..) |bb, i| {
        for (scope_ranges.items) |sr| {
            // longer range comes first so we should not have overlaping
            // elements on the stack
            if (sr.range[0] == i) {
                switch (sr.kind) {
                    .loop => try self.ctx.buf.writer.writeByte(opb(.loop)),
                    .block => try self.ctx.buf.writer.writeByte(opb(.block)),
                }
                try self.ctx.buf.writer.writeByte(0x40);
                if (log_cfg) std.debug.print("start: {s}\n", .{@tagName(sr.kind)});
                self.ctx.scope_stack.appendAssumeCapacity(sr);
            }
        }

        if (log_cfg) std.debug.print("{f}\n", .{bb});

        for (bb.base.outputs()) |out| {
            const instr = out.get();

            if (instr.kind == .Return) {
                if (stack_size != 0) {
                    try self.ctx.buf.writer.writeByte(opb(.i64_const));
                    try self.ctx.buf.writer.writeSleb128(stack_size);

                    try self.ctx.buf.writer.writeByte(opb(.global_get));
                    try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);

                    try self.ctx.buf.writer.writeByte(opb(.i64_add));

                    try self.ctx.buf.writer.writeByte(opb(.global_set));
                    try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);
                }
            }

            if (log_cfg) std.debug.print("  {f}\n", .{instr});
            self.emitInstr(instr);
        }

        while (self.ctx.scope_stack.items.len > 0 and self.ctx.scope_stack.getLast().range[1] == i) {
            const sr = self.ctx.scope_stack.pop().?;
            try self.ctx.buf.writer.writeByte(opb(.end));
            if (log_cfg) std.debug.print("end: {s}\n", .{@tagName(sr.kind)});
        }
    }

    std.debug.assert(self.ctx.scope_stack.items.len == 0);

    try self.ctx.buf.writer.writeByte(opb(.@"unreachable"));
    try self.ctx.buf.writer.writeByte(opb(.end));
}

pub fn selectUnsignedLoadOp(src_ty: graph.DataType) u8 {
    return switch (src_ty) {
        .i8 => opb(.i64_load8_u),
        .i16 => opb(.i64_load16_u),
        .i32 => opb(.i64_load32_u),
        else => unreachable,
    };
}

// assuming we are sign extending
pub fn selectSignedLoadOp(dest_ty: graph.DataType, src_ty: graph.DataType) u8 {
    return switch (src_ty) {
        .i8 => switch (dest_ty) {
            .i16, .i32 => opb(.i32_load8_s),
            .i64 => opb(.i64_load8_s),
            else => unreachable,
        },
        .i16 => switch (dest_ty) {
            .i32 => opb(.i32_load16_s),
            .i64 => opb(.i64_load16_s),
            else => unreachable,
        },
        .i32 => b: {
            std.debug.assert(dest_ty == .i64);
            break :b opb(.i64_load32_s);
        },
        else => unreachable,
    };
}

pub fn selectStoreOp(ty: graph.DataType) u8 {
    return switch (ty) {
        .i32 => opb(.i32_store),
        .i64 => opb(.i64_store),
        .f32 => opb(.f32_store),
        .f64 => opb(.f64_store),
        .i8 => opb(.i32_store8),
        .i16 => opb(.i32_store16),
        else => unreachable,
    };
}

pub fn selectLoadOp(ty: graph.DataType) u8 {
    return switch (ty) {
        .i32 => opb(.i32_load),
        .i64 => opb(.i64_load),
        .f32 => opb(.f32_load),
        .f64 => opb(.f64_load),
        .i8 => opb(.i32_load8_u),
        .i16 => opb(.i32_load16_u),
        else => unreachable,
    };
}

pub fn emitMemArg(self: *WasmGen, ty: graph.DataType, offset: i64) void {
    errdefer unreachable;

    const alignment = std.math.log2_int(u64, ty.size());
    try self.ctx.buf.writer.writeUleb128(alignment);
    try self.ctx.buf.writer.writeSleb128(offset);
}

pub fn emitInstr(self: *WasmGen, instr: *Func.Node) void {
    errdefer unreachable;

    const inps: []*Func.Node = @ptrCast(instr.inputs()[1..]);

    switch (instr.extra2()) {
        .GetLocal => {
            if (!inps[0].isDef()) {
                utils.panic("{f}", .{inps[0]});
            }

            try self.ctx.buf.writer.writeByte(opb(.local_get));
            try self.ctx.buf.writer.writeUleb128(self.regOf(inps[0]));
        },
        .WrapI64 => {
            try self.ctx.buf.writer.writeByte(opb(.i32_wrap_i64));
        },
        .StackAddr => {
            try self.ctx.buf.writer.writeByte(opb(.global_get));
            try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);
            try self.ctx.buf.writer.writeByte(opb(.i32_wrap_i64));
        },
        .CInt => |extra| {
            switch (dataTypeToWasmType(instr.data_type)) {
                .i32 => {
                    // TODO: this is incorrect we need to refactor the comptime eval
                    // to preserve signed byts
                    try self.ctx.buf.writer.writeByte(opb(.i32_const));
                    const value: u32 = @truncate(@as(u64, @bitCast(extra.value)));
                    try self.ctx.buf.writer.writeSleb128(@as(i32, @bitCast(value)));
                },
                .i64 => {
                    try self.ctx.buf.writer.writeByte(opb(.i64_const));
                    try self.ctx.buf.writer
                        .writeSleb128(@as(i64, @bitCast(@as(u64, @bitCast(extra.value)))));
                },
                .f32 => {
                    try self.ctx.buf.writer.writeByte(opb(.f32_const));
                    try self.ctx.buf.writer.writeAll(std.mem.asBytes(&extra.value)[0..4]);
                },
                .f64 => {
                    try self.ctx.buf.writer.writeByte(opb(.f64_const));
                    try self.ctx.buf.writer.writeAll(std.mem.asBytes(&extra.value));
                },
                else => utils.panic("{}", .{instr.data_type}),
            }

            self.emitLocalStore(instr);
        },
        .Eqz => {
            //self.emitLocalLoad(inps[0]);

            const op_ty = dataTypeToWasmType(inps[0].data_type);
            try self.ctx.buf.writer.writeByte(switch (op_ty) {
                .i32 => opb(.i32_eqz),
                .i64 => opb(.i64_eqz),
                else => utils.panic("{}", .{op_ty}),
            });

            self.emitLocalStore(instr);
        },
        .UnOp => |extra| {
            //self.emitLocalLoad(inps[0]);
            const op_ty = dataTypeToWasmType(inps[0].data_type);
            const op_code: u8 = switch (extra.op) {
                .sext => switch (inps[0].data_type) {
                    .i8 => switch (instr.data_type) {
                        .i32, .i16 => opb(.i32_extend8_s),
                        .i64 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_extend8_s));
                            break :b opb(.i64_extend_i32_s);
                        },
                        else => unreachable,
                    },
                    .i16 => switch (instr.data_type) {
                        .i32 => opb(.i32_extend16_s),
                        .i64 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_extend16_s));
                            break :b opb(.i64_extend_i32_s);
                        },
                        else => unreachable,
                    },
                    .i32 => opb(.i64_extend_i32_s),
                    else => unreachable,
                },
                .ired => switch (inps[0].data_type) {
                    .i64 => switch (instr.data_type) {
                        .i32, .i16, .i8 => opb(.i32_wrap_i64),
                        else => utils.panic("{} {}", .{ instr.data_type, inps[0].data_type }),
                    },
                    else => unreachable,
                },
                .uext => switch (inps[0].data_type) {
                    .i8 => switch (instr.data_type) {
                        .i16, .i32 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_const));
                            try self.ctx.buf.writer.writeSleb128(0xFF);
                            break :b opb(.i32_and);
                        },
                        .i64 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_const));
                            try self.ctx.buf.writer.writeSleb128(0xFF);

                            try self.ctx.buf.writer.writeByte(opb(.i32_and));

                            break :b opb(.i64_extend_i32_u);
                        },
                        else => unreachable,
                    },
                    .i16 => switch (instr.data_type) {
                        .i32 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_const));
                            try self.ctx.buf.writer.writeSleb128(0xFFFF);

                            break :b opb(.i32_and);
                        },
                        .i64 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_const));
                            try self.ctx.buf.writer.writeSleb128(0xFFFF);
                            try self.ctx.buf.writer.writeByte(opb(.i32_and));

                            break :b opb(.i64_extend_i32_u);
                        },
                        else => unreachable,
                    },
                    .i32 => opb(.i64_extend_i32_u),
                    else => unreachable,
                },
                .fti => switch (inps[0].data_type) {
                    .f32 => switch (instr.data_type) {
                        .i32 => opb(.i32_trunc_f32_s),
                        .i64 => opb(.i64_trunc_f32_s),
                        else => utils.panic("{}", .{instr.data_type}),
                    },
                    .f64 => switch (instr.data_type) {
                        .i32 => opb(.i32_trunc_f64_s),
                        .i64 => opb(.i64_trunc_f64_s),
                        else => utils.panic("{}", .{instr.data_type}),
                    },
                    else => utils.panic("{}", .{inps[0].data_type}),
                },
                .itf => switch (inps[0].data_type) {
                    .i32 => switch (instr.data_type) {
                        .f32 => opb(.f32_convert_i32_s),
                        .f64 => opb(.f64_convert_i32_s),
                        else => utils.panic("{}", .{instr.data_type}),
                    },
                    .i64 => switch (instr.data_type) {
                        .f32 => opb(.f32_convert_i64_s),
                        .f64 => opb(.f64_convert_i64_s),
                        else => utils.panic("{}", .{instr.data_type}),
                    },
                    else => utils.panic("{}", .{inps[0].data_type}),
                },
                .fcst => switch (instr.data_type) {
                    .f32 => opb(.f32_demote_f64),
                    .f64 => opb(.f32_promote_f64),
                    else => utils.panic("{}", .{op_ty}),
                },
                .not => switch (op_ty) {
                    .i32 => opb(.i32_eqz),
                    .i64 => opb(.i64_eqz),
                    else => utils.panic("{}", .{op_ty}),
                },
                .ineg, .bnot => unreachable,
                .fneg => switch (op_ty) {
                    .f32 => opb(.f32_neg),
                    .f64 => opb(.f64_neg),
                    else => utils.panic("{}", .{op_ty}),
                },
                .cast => switch (op_ty) {
                    .i32 => switch (instr.data_type) {
                        .f32 => opb(.f32_reinterpret_i32),
                        else => utils.panic("{}", .{instr.data_type}),
                    },
                    .i64 => switch (instr.data_type) {
                        .f64 => opb(.f64_reinterpret_i64),
                        else => {
                            utils.panic("{}", .{instr.data_type});
                        },
                    },
                    .f32 => switch (instr.data_type) {
                        .i32 => opb(.i32_reinterpret_f32),
                        else => utils.panic("{}", .{instr.data_type}),
                    },
                    .f64 => switch (instr.data_type) {
                        .i64 => opb(.i64_reinterpret_f64),
                        else => utils.panic("{}", .{instr.data_type}),
                    },
                    else => utils.panic("{}", .{op_ty}),
                },
            };
            try self.ctx.buf.writer.writeByte(op_code);

            self.emitLocalStore(instr);
        },
        .BinOp => |extra| {
            // self.emitLocalLoad(inps[0]);
            // self.emitLocalLoad(inps[1]);

            const utl = enum {
                fn selectOp(op_ty: object.Type, prefix: anytype, name: anytype) u8 {
                    return switch (op_ty) {
                        inline @field(object.Type, @tagName(prefix) ++ "32"),
                        @field(object.Type, @tagName(prefix) ++ "64"),
                        => |t| opb(@field(object.Op, @tagName(t) ++ "_" ++ @tagName(name))),
                        else => utils.panic("{}", .{op_ty}),
                    };
                }
            };

            const op_ty = dataTypeToWasmType(instr.data_type);
            const oper_ty = dataTypeToWasmType(inps[0].data_type);
            const op_code: u8 = switch (extra.op) {
                .iadd => utl.selectOp(op_ty, .i, .add),
                .isub => utl.selectOp(op_ty, .i, .sub),
                .imul => utl.selectOp(op_ty, .i, .mul),
                .udiv => utl.selectOp(op_ty, .i, .div_u),
                .sdiv => utl.selectOp(op_ty, .i, .div_s),
                .umod => utl.selectOp(op_ty, .i, .rem_u),
                .smod => utl.selectOp(op_ty, .i, .rem_s),
                .bor => utl.selectOp(op_ty, .i, .@"or"),
                .band => utl.selectOp(op_ty, .i, .@"and"),
                .bxor => utl.selectOp(op_ty, .i, .xor),
                .ishl => utl.selectOp(op_ty, .i, .shl),
                .ushr => utl.selectOp(op_ty, .i, .shr_u),
                .sshr => utl.selectOp(op_ty, .i, .shr_s),
                .eq => switch (oper_ty) {
                    inline .i32, .i64, .f32, .f64 => |t| opb(@field(object.Op, @tagName(t) ++ "_eq")),
                    else => utils.panic("{}", .{oper_ty}),
                },
                .ne => switch (oper_ty) {
                    inline .i32, .i64, .f32, .f64 => |t| opb(@field(object.Op, @tagName(t) ++ "_ne")),
                    else => utils.panic("{}", .{oper_ty}),
                },
                .ult => utl.selectOp(oper_ty, .i, .lt_u),
                .ugt => utl.selectOp(oper_ty, .i, .gt_u),
                .ule => utl.selectOp(oper_ty, .i, .le_u),
                .uge => utl.selectOp(oper_ty, .i, .ge_u),
                .sge => utl.selectOp(oper_ty, .i, .ge_s),
                .sle => utl.selectOp(oper_ty, .i, .le_s),
                .sgt => utl.selectOp(oper_ty, .i, .gt_s),
                .slt => utl.selectOp(oper_ty, .i, .lt_s),
                .fadd => utl.selectOp(op_ty, .f, .add),
                .fsub => utl.selectOp(op_ty, .f, .sub),
                .fmul => utl.selectOp(op_ty, .f, .mul),
                .fdiv => utl.selectOp(op_ty, .f, .div),
                .fge => utl.selectOp(oper_ty, .f, .ge),
                .flt => utl.selectOp(oper_ty, .f, .lt),
                .fgt => utl.selectOp(oper_ty, .f, .gt),
                .fle => utl.selectOp(oper_ty, .f, .le),
            };
            try self.ctx.buf.writer.writeByte(op_code);

            self.emitLocalStore(instr);
        },
        .WStore => |extra| {
            try self.ctx.buf.writer.writeByte(selectStoreOp(instr.data_type));
            self.emitMemArg(instr.data_type, extra.offset);
        },
        .StackStore => |extra| {
            const offset = @as(i64, @intCast(instr.base().extra(.LocalAlloc).size +
                self.ctx.stack_base)) + extra.offset;

            try self.ctx.buf.writer.writeByte(selectStoreOp(instr.data_type));
            self.emitMemArg(instr.data_type, offset);
        },
        .WLoad => |extra| {
            try self.ctx.buf.writer.writeByte(selectLoadOp(instr.data_type));
            self.emitMemArg(instr.data_type, extra.offset);

            self.emitLocalStore(instr);
        },
        .UnsignedLoad => |extra| {
            try self.ctx.buf.writer.writeByte(selectUnsignedLoadOp(extra.src_ty));
            self.emitMemArg(extra.src_ty, extra.offset);

            self.emitLocalStore(instr);
        },
        .SignedLoad => |extra| {
            try self.ctx.buf.writer.writeByte(selectSignedLoadOp(instr.data_type, extra.src_ty));
            self.emitMemArg(extra.src_ty, extra.offset);

            self.emitLocalStore(instr);
        },
        .StackLoad => |extra| {
            const offset = @as(i64, @intCast(instr.base().extra(.LocalAlloc).size +
                self.ctx.stack_base)) + extra.offset;

            try self.ctx.buf.writer.writeByte(selectLoadOp(instr.data_type));
            self.emitMemArg(instr.data_type, offset);

            self.emitLocalStore(instr);
        },
        .UnsignedStackLoad => |extra| {
            const offset = @as(i64, @intCast(instr.base().extra(.LocalAlloc).size +
                self.ctx.stack_base)) + extra.offset;

            try self.ctx.buf.writer.writeByte(selectUnsignedLoadOp(extra.src_ty));
            self.emitMemArg(extra.src_ty, offset);

            self.emitLocalStore(instr);
        },
        .SignedStackLoad => |extra| {
            const offset = @as(i64, @intCast(instr.base().extra(.LocalAlloc).size +
                self.ctx.stack_base)) + extra.offset;

            try self.ctx.buf.writer.writeByte(selectSignedLoadOp(instr.data_type, extra.src_ty));
            self.emitMemArg(extra.src_ty, offset);

            self.emitLocalStore(instr);
        },
        .StackArgOffset => |extra| {
            const offset = extra.offset;

            try self.ctx.buf.writer.writeByte(opb(.i64_const));
            try self.ctx.buf.writer.writeSleb128(offset);

            try self.ctx.buf.writer.writeByte(opb(.global_get));
            try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);

            try self.ctx.buf.writer.writeByte(opb(.i64_add));

            self.emitLocalStore(instr);
        },
        .Local => {
            const offset = inps[0].extra(.LocalAlloc).size +
                self.ctx.stack_base;

            try self.ctx.buf.writer.writeByte(opb(.i64_const));
            try self.ctx.buf.writer.writeSleb128(offset);

            try self.ctx.buf.writer.writeByte(opb(.global_get));
            try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);

            try self.ctx.buf.writer.writeByte(opb(.i64_add));

            self.emitLocalStore(instr);
        },
        .StructArg => |extra| {
            const offset = extra.spec.size + self.ctx.arg_base;

            try self.ctx.buf.writer.writeByte(opb(.i64_const));
            try self.ctx.buf.writer.writeSleb128(offset);

            try self.ctx.buf.writer.writeByte(opb(.global_get));
            try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);

            try self.ctx.buf.writer.writeByte(opb(.i64_add));

            self.emitLocalStore(instr);
        },
        .FuncAddr => |extra| {
            try self.ctx.buf.writer.writeByte(opb(.i64_const));

            self.mach.out.code = self.ctx.buf.toArrayList();
            try self.mach.out.addFuncReloc(self.gpa, extra.id, .@"4", object.fn_ptr_addend, 0);
            self.ctx.buf = .fromArrayList(self.gpa, &self.mach.out.code);

            try self.ctx.buf.writer.writeUleb128(std.math.maxInt(object.RelocInt));

            self.emitLocalStore(instr);
        },
        .GlobalAddr => |extra| {
            try self.ctx.buf.writer.writeByte(opb(.global_get));

            self.mach.out.code = self.ctx.buf.toArrayList();
            try self.mach.out.addGlobalReloc(self.gpa, extra.id, .@"4", object.normal_addend, 0);
            self.ctx.buf = .fromArrayList(self.gpa, &self.mach.out.code);

            try self.ctx.buf.writer.writeUleb128(std.math.maxInt(object.RelocInt));

            self.emitLocalStore(instr);
        },
        .MemCpy => {
            // memory.copy
            try self.ctx.buf.writer.writeByte(opb(.prefix_fc));
            try self.ctx.buf.writer.writeUleb128(10);

            try self.ctx.buf.writer.writeUleb128(0);
            try self.ctx.buf.writer.writeUleb128(0);
        },
        .Call => |extra| {
            if (extra.id == graph.indirect_call) {
                try self.ctx.buf.writer.writeByte(opb(.call_indirect));
                try self.ctx.buf.writer.writeUleb128(self.indirect_signature_count);
                try self.ctx.buf.writer.writeUleb128(0); // table index

                var writer = std.Io.Writer.Allocating.fromArrayList(self.gpa, &self.indirect_signatures);
                encodeFnType(&writer.writer, extra.signature);
                self.indirect_signatures = writer.toArrayList();
                self.indirect_signature_count += 1;
            } else {
                try self.ctx.buf.writer.writeByte(opb(.call));
                self.mach.out.code = self.ctx.buf.toArrayList();
                try self.mach.out.addFuncReloc(self.gpa, extra.id, .@"4", object.normal_addend, 0);
                self.ctx.buf = .fromArrayList(self.gpa, &self.mach.out.code);
                try self.ctx.buf.writer.writeUleb128(std.math.maxInt(object.RelocInt));
            }

            const ret = extra.signature.returns() orelse return;
            var dropped = false;
            for (0..ret.len) |i| {
                for (instr.outputs()[0].get().outputs()) |out| {
                    if (out.get().kind == .Ret) {
                        if (out.get().id == on_stack_id) {
                            std.debug.assert(!dropped);
                            break;
                        }

                        if (out.get().extra(.Ret).index == ret.len - 1 - i) {
                            self.emitLocalStore(out.get());
                            dropped = true;
                            break;
                        }
                    }
                } else {
                    try self.ctx.buf.writer.writeByte(opb(.drop));
                    dropped = true;
                }
            }
        },
        .If => {
            var iter = std.mem.reverseIterator(self.ctx.scope_stack.items);
            var j: usize = 0;
            const label_id = while (iter.next()) |sr| : (j += 1) {
                if (sr.signifier == instr and sr.kind == .block) {
                    break j;
                }
            } else unreachable;

            if (inps[0].data_type == .i64) {
                try self.ctx.buf.writer.writeByte(opb(.i32_wrap_i64));
            }

            try self.ctx.buf.writer.writeByte(opb(.br_if));
            try self.ctx.buf.writer.writeUleb128(label_id);
        },
        .MachSplit => {
            self.emitLocalStore(instr);
        },
        .Jmp => {
            const region = instr.outputs()[0];
            //for (region.get().outputs()) |out| {
            //    if (out.get().isDataPhi()) {
            //        try self.ctx.buf.writer.writeByte(opb(.local_get));
            //        try self.ctx.buf.writer.writeUleb128(self.regOf(out.get().inputs()[1 + region.pos()]));
            //        try self.ctx.buf.writer.writeByte(opb(.local_set));
            //        try self.ctx.buf.writer.writeUleb128(self.regOf(out.get()));
            //    }
            //}

            const pred = instr.inputs()[0].?;

            if (region.get().kind == .Loop and region.pos() == 1) {
                var iter = std.mem.reverseIterator(self.ctx.scope_stack.items);
                var j: usize = 0;
                const label_id = while (iter.next()) |sr| : (j += 1) {
                    if (sr.signifier == region.get()) {
                        break j;
                    }
                } else unreachable;

                try self.ctx.buf.writer.writeByte(opb(.br));
                try self.ctx.buf.writer.writeUleb128(label_id);
            }

            if (region.get().kind == .Region and pred.schedule + 1 != region.get().schedule) {
                var iter = std.mem.reverseIterator(self.ctx.scope_stack.items);
                var j: usize = 0;
                const label_id = while (iter.next()) |sr| : (j += 1) {
                    if (sr.signifier == pred) {
                        break j;
                    }
                } else unreachable;

                try self.ctx.buf.writer.writeByte(opb(.br));
                try self.ctx.buf.writer.writeUleb128(label_id);
            }
        },
        .Return => {
            //for (instr.dataDeps()) |d| {
            //    self.emitLocalLoad(d);
            //}

            try self.ctx.buf.writer.writeByte(opb(.@"return"));
        },
        .Phi, .Mem, .Ret, .Arg, .Never => {},
        .Trap => |extra| {
            switch (extra.code) {
                graph.unreachable_func_trap => {},
                graph.infinite_loop_trap => {},
                0 => try self.ctx.buf.writer.writeByte(opb(.@"unreachable")),
                else => utils.panic("{}", .{extra.code}),
            }
        },
        else => {
            utils.panic("unhandled op {f}", .{instr});
        },
    }
}

pub fn regOf(self: *WasmGen, node: ?*Func.Node) u16 {
    return self.ctx.allocs[node.?.schedule];
}

pub fn emitData(self: *WasmGen, opts: Mach.DataOptions) void {
    errdefer unreachable;

    try self.mach.out.defineGlobal(
        self.gpa,
        opts.id,
        opts.name,
        .local,
        opts.value,
        false,
        opts.relocs,
        opts.readonly,
        opts.thread_local,
        object.fn_ptr_addend,
    );
}

pub fn emitLocalStore(self: *WasmGen, for_instr: *Func.Node) void {
    if (for_instr.id == on_stack_id) {
        return;
    }

    errdefer unreachable;

    if (for_instr.id == uses_tee_id) {
        try self.ctx.buf.writer.writeByte(opb(.local_tee));
    } else {
        try self.ctx.buf.writer.writeByte(opb(.local_set));
    }
    try self.ctx.buf.writer.writeUleb128(self.regOf(for_instr));
}

pub fn finalize(self: *WasmGen, opts: Mach.FinalizeOptions) void {
    self.mach.out.deduplicate();
    self.mach.out.elimitaneDeadCode();

    root.wasm.object.flush(
        self.mach.out,
        opts.output orelse return,
        self.stack_size,
        self.indirect_signatures.items,
        self.indirect_signature_count,
    ) catch unreachable;

    self.mach.out.reset();
    self.indirect_signatures.items.len = 0;
    self.indirect_signature_count = 0;
}

pub fn disasm(_: *WasmGen, opts: Mach.DisasmOpts) void {
    if (utils.freestanding) unreachable;

    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var child = std.process.Child.init(&.{ "wasm2wat", "--no-check", "-" }, tmp.arena.allocator());
    child.stdout_behavior = .Pipe;
    child.stderr_behavior = .Pipe;
    child.stdin_behavior = .Pipe;

    try child.spawn();

    {
        const stdin = child.stdin.?;
        defer stdin.close();

        child.stdin = null;

        var writer = stdin.writer(&.{});
        try writer.interface.writeAll(opts.bin);
        try writer.interface.flush();
    }

    var stdout = std.ArrayList(u8).empty;
    var stderr = std.ArrayList(u8).empty;
    try child.collectOutput(tmp.arena.allocator(), &stdout, &stderr, 1024 * 1024);

    const term = try child.wait();
    if (term != .Exited or term.Exited != 0) {
        std.debug.print("{s}\n", .{stderr.items});
        if (std.mem.indexOf(u8, stderr.items, ": error:")) |idx| {
            const idx_in = std.fmt.parseInt(usize, stderr.items[0..idx], 16) catch unreachable;

            for (0..std.mem.alignBackward(usize, opts.bin.len, 16) / 16) |i| {
                std.debug.print("{x:0>4} ", .{i * 16});
                var slicer = opts.bin[i * 16 ..];
                for (0..4) |j| {
                    std.debug.print("{x} ", .{
                        slicer[@min(j * 4, slicer.len)..@min(j * 4 + 4, slicer.len)],
                    });
                }
                std.debug.print("\n", .{});
            }

            if (false) {
                var reader = std.io.Reader{
                    .buffer = tmp.arena.dupe(u8, opts.bin),
                    .end = opts.bin.len,
                    .seek = idx_in,
                    .vtable = undefined,
                };

                std.debug.print("{x}\n", .{reader.takeLeb128(i32) catch unreachable});
            }
        } else {
            std.debug.print("{x}\n", .{opts.bin});
            unreachable;
        }
    }

    if (opts.out) |out| {
        try out.writeAll(stdout.items);
        try out.flush();
    }
}

pub fn run(_: *WasmGen, env: Mach.RunEnv) !usize {
    if (utils.freestanding) unreachable;

    const cleanup = false;

    var tmp = root.utils.Arena.scrath(null);
    defer tmp.deinit();
    var stdout = std.ArrayList(u8).empty;
    var stderr = std.ArrayList(u8).empty;
    const res = b: {
        errdefer unreachable;

        const name = try std.fmt.allocPrint(
            tmp.arena.allocator(),
            "tmp_{s}.wasm",
            .{env.name},
        );

        try std.fs.cwd().writeFile(.{ .sub_path = name, .data = env.code });
        defer if (cleanup) std.fs.cwd().deleteFile(name) catch unreachable;

        var compile = std.process.Child.init(
            &.{ "wasm-interp", name, "-r", "main" },
            tmp.arena.allocator(),
        );

        compile.stderr_behavior = .Pipe;
        compile.stdout_behavior = .Pipe;

        try compile.spawn();

        try compile.collectOutput(tmp.arena.allocator(), &stdout, &stderr, 1024 * 1024);

        break :b try compile.wait();
    };

    if (res.Exited != 0) {
        std.debug.print("{s}\n", .{stdout.items});
        std.debug.print("{s}\n", .{stderr.items});
        return error.WasmInterpError;
    }

    if (std.mem.startsWith(u8, stdout.items, "main() => error: unreachable executed")) {
        return error.Unreachable;
    }

    if (std.mem.startsWith(u8, stdout.items, "main() => error: out of bounds")) {
        return error.OutOfBounds;
    }

    if (std.mem.startsWith(u8, stdout.items, "main() => error: indirect call signature mismatch")) {
        return error.IndirectCallSignatureMismatch;
    }

    const exe_prefix = "main() => i64:";
    if (!std.mem.startsWith(u8, stdout.items, exe_prefix)) {
        utils.panic("{s}\n", .{stdout.items});
    }
    std.debug.assert(std.mem.endsWith(u8, stdout.items, "\n"));
    stdout.items = stdout.items[exe_prefix.len .. stdout.items.len - 1];

    return std.fmt.parseInt(usize, stdout.items, 10) catch unreachable;
}

pub fn deinit(self: *WasmGen) void {
    self.mach.out.deinit(self.gpa);
    self.indirect_signatures.deinit(self.gpa);
    self.* = undefined;
}
