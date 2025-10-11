const std = @import("std");

const root = @import("hb");
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Regalloc = root.backend.Regalloc;
const utils = root.utils;
const object = root.wasm.object;

const WasmGen = @This();
const Func = graph.Func(WasmGen);
const opb = object.opb;

gpa: std.mem.Allocator,
mach: Mach = .init(WasmGen),
stack_size: u64 = 1024 * 128,
func_ids: std.ArrayList(Mach.Data.SymIdx) = .empty,
func_id_counter: u32 = 0,
global_ids: std.ArrayList(Mach.Data.SymIdx) = .empty,
global_id_counter: u32 = 1,
ctx: *Ctx = undefined,

pub const i_know_the_api = {};
pub const Set = struct {
    pub fn count(_: Set) usize {
        return 100;
    }

    pub fn setIntersection(_: Set, _: Set) void {}
};

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

pub const classes = enum {};

pub fn idealize(self: *WasmGen, func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
    _ = node;
    _ = worklist;
    _ = self;
    _ = func;

    return null;
}

pub fn regMask(
    node: *Func.Node,
    func: *Func,
    idx: usize,
    arena: *utils.Arena,
) Set {
    _ = node;
    _ = func;
    _ = idx;
    _ = arena;

    return .{};
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

pub fn addFuncId(self: *WasmGen, id: u32) u32 {
    errdefer unreachable;

    const fid = self.func_id_counter;
    const slot = try utils.ensureSlot(&self.func_ids, self.gpa, id);

    if (slot.* != .invalid) return @intFromEnum(slot.*);

    slot.* = @enumFromInt(fid);
    self.func_id_counter += 1;

    return fid;
}

// TODO: deduplicate
pub fn addGlobalId(self: *WasmGen, id: u32) u32 {
    errdefer unreachable;

    const fid = self.global_id_counter;
    const slot = try utils.ensureSlot(&self.global_ids, self.gpa, id);

    if (slot.* != .invalid) return @intFromEnum(slot.*);

    slot.* = @enumFromInt(fid);
    self.global_id_counter += 1;

    return fid;
}

pub fn emitFunc(self: *WasmGen, func: *Func, opts: Mach.EmitOptions) void {
    errdefer unreachable;

    const id = opts.id;
    const linkage = opts.linkage;
    const name = if (opts.special == .memcpy)
        "memcpy"
    else if (opts.special == .entry)
        "_start"
    else
        opts.name;

    const sym = try self.mach.out.startDefineFunc(self.gpa, id, name, .func, linkage, opts.is_inline);
    _ = sym;
    defer self.mach.out.endDefineFunc(id);

    if (opts.linkage == .exported) {
        _ = self.addFuncId(id);
    }

    // TDDO: actually make the release mode work
    opts.optimizations.opts.optimizeDebug(WasmGen, self, func);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const loop_ranges, _ = func.backshiftLoopBodies(tmp.arena);

    var ctx = Ctx{
        .start_pos = self.mach.out.code.items.len,
        .buf = .fromArrayList(self.gpa, &self.mach.out.code),
    };
    defer self.mach.out.code = ctx.buf.toArrayList();

    self.ctx = &ctx;

    func.computeStructArgLayout();

    // NOTE: this is inneficient and we make more locals then we need but its
    // also simple and lets me focus on one problem at a time, just generate
    // wasm that works.

    // backpatch later
    try self.ctx.buf.writer.writeInt(u32, 0, .little);

    var params_len: u32 = 0;
    for (func.signature.params(), 0..) |param, i| {
        if (param == .Reg) {
            for (func.gcm.postorder[0].base.outputs()) |out| {
                if (out.get().kind == .Arg and out.get().extra(.Arg).index == i) {
                    out.get().extra(.Arg).index = params_len;
                    break;
                }
            }
            params_len += 1;
        }
    }

    var results_len: u32 = 0;
    for (func.signature.returns() orelse &.{}) |param| {
        if (param == .Reg) results_len += 1;
    }

    try self.ctx.buf.writer.writeByte(0x60);

    try self.ctx.buf.writer.writeUleb128(params_len);
    for (func.signature.params()) |param| {
        if (param == .Reg) {
            try self.ctx.buf.writer.writeByte(dataTypeToWasmType(param.Reg).raw());
        }
    }

    try self.ctx.buf.writer.writeUleb128(results_len);
    for (func.signature.returns() orelse &.{}) |param| {
        if (param == .Reg) {
            try self.ctx.buf.writer.writeByte(dataTypeToWasmType(param.Reg).raw());
        }
    }

    self.ctx.buf.writer
        .buffer[self.ctx.start_pos..][0..4].* =
        @bitCast(@as(u32, @intCast(self.ctx.buf.writer.end -
        self.ctx.start_pos - @sizeOf(u32))));

    var counters: struct {
        i32: usize = 0,
        i64: usize = 0,
        f32: usize = 0,
        f64: usize = 0,
    } = .{};

    func.gcm.instr_count = 0;

    for (func.gcm.postorder) |block| {
        for (block.base.outputs()) |out| {
            if (!out.get().isDef()) continue;

            out.get().schedule = func.gcm.instr_count;
            func.gcm.instr_count += 1;

            if (out.get().kind == .Arg) continue;

            switch (dataTypeToWasmType(out.get().data_type)) {
                .fnc, .vec => unreachable,
                inline else => |ty| @field(counters, @tagName(ty)) += 1,
            }
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

    self.ctx.allocs = tmp.arena.alloc(u16, params_len + cursor);

    for (func.gcm.postorder) |block| {
        for (block.base.outputs()) |out| {
            const instr = out.get();

            if (!instr.isDef()) continue;

            if (instr.kind == .Arg) {
                self.ctx.allocs[instr.schedule] =
                    @intCast(instr.extra(.Arg).index);
                continue;
            }

            const prev = switch (dataTypeToWasmType(instr.data_type)) {
                .fnc, .vec => unreachable,
                inline else => |ty| @field(counters, @tagName(ty)),
            };

            self.ctx.allocs[instr.schedule] = @intCast(params_len + prev);

            switch (dataTypeToWasmType(instr.data_type)) {
                .fnc, .vec => unreachable,
                inline else => |ty| @field(counters, @tagName(ty)) += 1,
            }
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
        try self.ctx.buf.writer.writeUleb128(stack_size);

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
        if (rbb.base.kind == .Then or rbb.base.kind == .Else) {
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

    for (scope_ranges.items) |*sr| {
        if (sr.kind == .loop) continue;
        for (scope_ranges.items) |*osr| {
            if (sr == osr) continue;
            if (sr.range[0] >= osr.range[0] and sr.range[0] <= osr.range[1] and sr.range[1] > osr.range[1]) {
                sr.range[0] = osr.range[0];
            }
        }
    }

    const log_cfg = false;

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
                    try self.ctx.buf.writer.writeUleb128(stack_size);

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

    try self.ctx.buf.writer.writeByte(opb(.@"unreachable"));
    try self.ctx.buf.writer.writeByte(opb(.end));
}

pub fn emitInstr(self: *WasmGen, instr: *Func.Node) void {
    errdefer unreachable;

    const inps = instr.dataDeps();

    switch (instr.extra2()) {
        .CInt => |extra| {
            switch (dataTypeToWasmType(instr.data_type)) {
                .i32 => {
                    try self.ctx.buf.writer.writeByte(opb(.i32_const));
                    const value: u32 = @truncate(@as(u64, @bitCast(extra.value)));
                    try self.ctx.buf.writer.writeSleb128(value);
                },
                .i64 => {
                    try self.ctx.buf.writer.writeByte(opb(.i64_const));
                    try self.ctx.buf.writer
                        .writeSleb128(@as(u64, @bitCast(extra.value)));
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

            try self.ctx.buf.writer.writeByte(opb(.local_set));
            try self.ctx.buf.writer.writeUleb128(self.regOf(instr));
        },
        .UnOp => |extra| {
            try self.ctx.buf.writer.writeByte(opb(.local_get));
            try self.ctx.buf.writer.writeUleb128(self.regOf(inps[0]));
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
                        .i32 => 0xC1,
                        .i64 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_extend16_s));
                            break :b opb(.i64_extend_i32_s);
                        },
                        else => unreachable,
                    },
                    .i32 => 0xAC,
                    else => unreachable,
                },
                .uext => switch (inps[0].data_type) {
                    .i8 => switch (instr.data_type) {
                        .i16, .i32 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_const));
                            try self.ctx.buf.writer.writeUleb128(0xFF);
                            break :b opb(.i32_and);
                        },
                        .i64 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_const));
                            try self.ctx.buf.writer.writeUleb128(0xFF);

                            try self.ctx.buf.writer.writeByte(opb(.i32_and));

                            break :b opb(.i64_extend_i32_u);
                        },
                        else => unreachable,
                    },
                    .i16 => switch (instr.data_type) {
                        .i32 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_const));
                            try self.ctx.buf.writer.writeUleb128(0xFFFF);

                            break :b opb(.i32_and);
                        },
                        .i64 => b: {
                            try self.ctx.buf.writer.writeByte(opb(.i32_const));
                            try self.ctx.buf.writer.writeUleb128(0xFFFF);
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
                    else => utils.panic("{}", .{extra.op}),
                },
                else => utils.panic("{}", .{extra.op}),
            };
            try self.ctx.buf.writer.writeByte(op_code);

            try self.ctx.buf.writer.writeByte(opb(.local_set));
            try self.ctx.buf.writer.writeUleb128(self.regOf(instr));
        },
        .BinOp => |extra| {
            try self.ctx.buf.writer.writeByte(opb(.local_get));
            try self.ctx.buf.writer.writeUleb128(self.regOf(inps[0]));

            try self.ctx.buf.writer.writeByte(opb(.local_get));
            try self.ctx.buf.writer.writeUleb128(self.regOf(inps[1]));

            const op_ty = dataTypeToWasmType(instr.data_type);
            const oper_ty = dataTypeToWasmType(inps[0].data_type);
            const op_code: u8 = switch (extra.op) {
                .iadd => switch (op_ty) {
                    .i32 => opb(.i32_add),
                    .i64 => opb(.i64_add),
                    else => utils.panic("{}", .{op_ty}),
                },
                .isub => switch (op_ty) {
                    .i32 => opb(.i32_sub),
                    .i64 => opb(.i64_sub),
                    else => utils.panic("{}", .{op_ty}),
                },
                .imul => switch (instr.data_type) {
                    .i32 => opb(.i32_mul),
                    .i64 => opb(.i64_mul),
                    else => utils.panic("{}", .{op_ty}),
                },
                .band => switch (instr.data_type) {
                    .i32 => opb(.i32_and),
                    .i64 => opb(.i64_and),
                    else => utils.panic("{}", .{op_ty}),
                },
                .ne => switch (oper_ty) {
                    .i32 => opb(.i32_ne),
                    .i64 => opb(.i64_ne),
                    .f32 => opb(.f32_ne),
                    .f64 => opb(.f64_ne),
                    else => utils.panic("{}", .{oper_ty}),
                },
                .eq => switch (oper_ty) {
                    .i32 => opb(.i32_eq),
                    .i64 => opb(.i64_eq),
                    .f32 => opb(.f32_eq),
                    .f64 => opb(.f64_eq),
                    else => utils.panic("{}", .{oper_ty}),
                },
                .ult => switch (oper_ty) {
                    .i32 => opb(.i32_lt_u),
                    .i64 => opb(.i64_lt_u),
                    else => utils.panic("{}", .{oper_ty}),
                },
                .ugt => switch (oper_ty) {
                    .i32 => opb(.i32_gt_u),
                    .i64 => opb(.i64_gt_u),
                    else => utils.panic("{}", .{oper_ty}),
                },
                .ule => switch (oper_ty) {
                    .i32 => opb(.i32_le_u),
                    .i64 => opb(.i64_le_u),
                    else => utils.panic("{}", .{oper_ty}),
                },
                .udiv => switch (instr.data_type) {
                    .i32 => opb(.i32_div_u),
                    .i64 => opb(.i64_div_u),
                    else => utils.panic("{}", .{op_ty}),
                },
                .sdiv => switch (instr.data_type) {
                    .i32 => opb(.i32_div_s),
                    .i64 => opb(.i64_div_s),
                    else => utils.panic("{}", .{op_ty}),
                },
                .fadd => switch (instr.data_type) {
                    .f32 => opb(.f32_add),
                    .f64 => opb(.f64_add),
                    else => utils.panic("{}", .{op_ty}),
                },
                .fsub => switch (instr.data_type) {
                    .f32 => opb(.f32_sub),
                    .f64 => opb(.f64_sub),
                    else => utils.panic("{}", .{op_ty}),
                },
                .fmul => switch (instr.data_type) {
                    .f32 => opb(.f32_mul),
                    .f64 => opb(.f64_mul),
                    else => utils.panic("{}", .{op_ty}),
                },
                .fdiv => switch (instr.data_type) {
                    .f32 => opb(.f32_div),
                    .f64 => opb(.f64_div),
                    else => utils.panic("{}", .{op_ty}),
                },
                else => utils.panic("{}", .{extra.op}),
            };
            try self.ctx.buf.writer.writeByte(op_code);

            try self.ctx.buf.writer.writeByte(opb(.local_set));
            try self.ctx.buf.writer.writeUleb128(self.regOf(instr));
        },
        .Store => {
            // TODO: we can emit specialized stores

            try self.ctx.buf.writer.writeByte(opb(.local_get));
            try self.ctx.buf.writer.writeUleb128(self.regOf(inps[0]));

            try self.ctx.buf.writer.writeByte(opb(.i32_wrap_i64));

            try self.ctx.buf.writer.writeByte(opb(.local_get));
            try self.ctx.buf.writer.writeUleb128(self.regOf(inps[1]));

            const op_code: u8 = switch (instr.data_type) {
                .i32 => opb(.i32_store),
                .i64 => opb(.i64_store),
                .f32 => opb(.f32_store),
                .f64 => opb(.f64_store),
                .i8 => opb(.i32_store8),
                .i16 => opb(.i32_store16),
                else => unreachable,
            };
            try self.ctx.buf.writer.writeByte(op_code);
            const alignment = std.math.log2_int(usize, instr.data_type.size());
            try self.ctx.buf.writer.writeUleb128(alignment);
            try self.ctx.buf.writer.writeByte(0);
        },
        .Load => {
            // TODO: we can emit specialized loads, maybe even sign extension

            // local.get addr
            try self.ctx.buf.writer.writeByte(opb(.local_get));
            try self.ctx.buf.writer.writeUleb128(self.regOf(inps[0]));
            // i32.wrap_i64
            try self.ctx.buf.writer.writeByte(opb(.i32_wrap_i64));
            // i64.load[size]_u (align: size, offset: 0)
            const op_code: u8 = switch (instr.data_type) {
                .i32 => opb(.i32_load),
                .i64 => opb(.i64_load),
                .f32 => opb(.f32_load),
                .f64 => opb(.f64_load),
                .i8 => opb(.i32_load8_u),
                .i16 => opb(.i32_load16_u),
                else => unreachable,
            };
            try self.ctx.buf.writer.writeByte(op_code);
            const alignment = std.math.log2_int(usize, instr.data_type.size());
            try self.ctx.buf.writer.writeUleb128(alignment);
            try self.ctx.buf.writer.writeUleb128(0);

            try self.ctx.buf.writer.writeByte(opb(.local_set));
            try self.ctx.buf.writer.writeUleb128(self.regOf(instr));
        },
        .StackArgOffset => |extra| {
            const offset = extra.offset;

            try self.ctx.buf.writer.writeByte(opb(.i64_const));
            try self.ctx.buf.writer.writeUleb128(offset);

            try self.ctx.buf.writer.writeByte(opb(.global_get));
            try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);

            try self.ctx.buf.writer.writeByte(opb(.i64_add));

            try self.ctx.buf.writer.writeByte(opb(.local_set));
            try self.ctx.buf.writer.writeUleb128(self.regOf(instr));
        },
        .Local => {
            const offset = instr.inputs()[1].?.extra(.LocalAlloc).size +
                self.ctx.stack_base;

            try self.ctx.buf.writer.writeByte(opb(.i64_const));
            try self.ctx.buf.writer.writeUleb128(offset);

            try self.ctx.buf.writer.writeByte(opb(.global_get));
            try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);

            try self.ctx.buf.writer.writeByte(opb(.i64_add));

            try self.ctx.buf.writer.writeByte(opb(.local_set));
            try self.ctx.buf.writer.writeUleb128(self.regOf(instr));
        },
        .StructArg => |extra| {
            const offset = extra.spec.size + self.ctx.arg_base;

            try self.ctx.buf.writer.writeByte(opb(.i64_const));
            try self.ctx.buf.writer.writeUleb128(offset);

            try self.ctx.buf.writer.writeByte(opb(.global_get));
            try self.ctx.buf.writer.writeUleb128(object.stack_pointer_id);

            try self.ctx.buf.writer.writeByte(opb(.i64_add));

            try self.ctx.buf.writer.writeByte(opb(.local_set));
            try self.ctx.buf.writer.writeUleb128(self.regOf(instr));
        },
        .GlobalAddr => |extra| {
            const id = self.addGlobalId(extra.id);
            try self.mach.out.addPlaceholderGlobalReloc(self.gpa, extra.id);

            try self.ctx.buf.writer.writeByte(opb(.global_get));
            try self.ctx.buf.writer.writeUleb128(id);

            try self.ctx.buf.writer.writeByte(opb(.local_set));
            try self.ctx.buf.writer.writeUleb128(self.regOf(instr));
        },
        .MemCpy => {
            for (inps) |inp| {
                try self.ctx.buf.writer.writeByte(opb(.local_get));
                try self.ctx.buf.writer.writeUleb128(self.regOf(inp));
                try self.ctx.buf.writer.writeByte(opb(.i32_wrap_i64));
            }

            // memory.copy
            try self.ctx.buf.writer.writeByte(opb(.prefix_fc));
            try self.ctx.buf.writer.writeUleb128(10);

            try self.ctx.buf.writer.writeUleb128(0);
            try self.ctx.buf.writer.writeUleb128(0);
        },
        .Call => |extra| {
            for (inps) |inp| {
                if (inp.kind == .StackArgOffset) {
                    continue;
                }

                try self.ctx.buf.writer.writeByte(opb(.local_get));
                try self.ctx.buf.writer.writeUleb128(self.regOf(inp));
            }

            try self.ctx.buf.writer.writeByte(opb(.call));
            try self.ctx.buf.writer.writeUleb128(self.addFuncId(extra.id));
            try self.mach.out.addPlaceholderFuncReloc(self.gpa, extra.id);

            const ret = extra.signature.returns() orelse return;
            for (0..ret.len) |i| {
                for (instr.outputs()[0].get().outputs()) |out| {
                    if (out.get().kind == .Ret and out.get().extra(.Ret).index == ret.len - 1 - i) {
                        try self.ctx.buf.writer.writeByte(opb(.local_set));
                        try self.ctx.buf.writer.writeUleb128(self.regOf(out.get()));
                    }
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

            try self.ctx.buf.writer.writeByte(opb(.local_get));
            try self.ctx.buf.writer.writeUleb128(self.regOf(inps[0]));

            try self.ctx.buf.writer.writeByte(opb(.i32_eqz));
            try self.ctx.buf.writer.writeByte(opb(.br_if));
            try self.ctx.buf.writer.writeUleb128(label_id);
        },
        .Jmp => {
            const region = instr.outputs()[0];
            for (region.get().outputs()) |out| {
                if (out.get().isDataPhi()) {
                    try self.ctx.buf.writer.writeByte(opb(.local_get));
                    try self.ctx.buf.writer.writeUleb128(self.regOf(out.get().inputs()[1 + region.pos()]));
                    try self.ctx.buf.writer.writeByte(opb(.local_set));
                    try self.ctx.buf.writer.writeUleb128(self.regOf(out.get()));
                }
            }

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
            for (instr.dataDeps()) |d| {
                try self.ctx.buf.writer.writeByte(opb(.local_get));
                try self.ctx.buf.writer.writeUleb128(self.regOf(d));
            }

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
    );
}

pub fn finalize(self: *WasmGen, opts: Mach.FinalizeOptions) void {
    // TODO: relocations are not emitted properly
    // the function ids get hardcoded
    //
    //self.mach.out.deduplicate();
    self.mach.out.elimitaneDeadCode();

    root.wasm.object.flush(
        self.mach.out,
        opts.output orelse return,
        self.stack_size,
    ) catch unreachable;

    self.mach.out.reset();
    self.global_ids.items.len = 0;
    self.global_id_counter = 0;
    self.func_ids.items.len = 0;
    self.func_id_counter = 0;
}

pub fn disasm(_: *WasmGen, opts: Mach.DisasmOpts) void {
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
        std.debug.print("{x}\n", .{opts.bin});
    }

    if (opts.out) |out| {
        try out.writeAll(stdout.items);
        try out.flush();
    }
}

pub fn run(_: *WasmGen, env: Mach.RunEnv) !usize {
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
        std.debug.print("{s}\n", .{stderr.items});
        return error.WasmInterpError;
    }

    if (std.mem.startsWith(u8, stdout.items, "main() => error: unreachable executed")) {
        return error.Unreachable;
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
    self.func_ids.deinit(self.gpa);
    self.global_ids.deinit(self.gpa);
    self.* = undefined;
}
