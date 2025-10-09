const std = @import("std");

const root = @import("hb");
const graph = root.backend.graph;
const Mach = root.backend.Machine;
const Regalloc = root.backend.Regalloc;
const utils = root.utils;
const object = root.wasm.object;

const WasmGen = @This();
const Func = graph.Func(WasmGen);

gpa: std.mem.Allocator,
mach: Mach = .init(WasmGen),
func_ids: std.ArrayList(Mach.Data.SymIdx) = .empty,
func_id_counter: u32 = 0,
ctx: *Ctx = undefined,

pub const i_know_the_api = {};
pub const Set = struct {
    pub fn count(_: Set) usize {
        return 100;
    }

    pub fn setIntersection(_: Set, _: Set) void {}
};

pub const Ctx = struct {
    start_pos: usize,
    buf: std.Io.Writer.Allocating,
    allocs: []u16 = undefined,
};

pub const classes = enum {};

pub fn idealize(self: *WasmGen, func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
    _ = node; // autofix
    _ = worklist; // autofix
    _ = self; // autofix
    _ = func; // autofix

    return null;
}

pub fn regMask(
    node: *Func.Node,
    func: *Func,
    idx: usize,
    arena: *utils.Arena,
) Set {
    _ = node; // autofix
    _ = func; // autofix
    _ = idx; // autofix
    _ = arena; // autofix

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

    _ = self.addFuncId(id);

    opts.optimizations.opts.optimizeDebug(WasmGen, self, func);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var ctx = Ctx{
        .start_pos = self.mach.out.code.items.len,
        .buf = .fromArrayList(self.gpa, &self.mach.out.code),
    };
    defer self.mach.out.code = ctx.buf.toArrayList();

    self.ctx = &ctx;

    // backpatch later
    try self.ctx.buf.writer.writeInt(u32, 0, .little);

    var params_len: u32 = 0;
    for (func.signature.params()) |param| {
        if (param == .Reg) params_len += 1;
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
            if (!out.get().isDef() or out.get().kind == .Arg) continue;

            out.get().schedule = func.gcm.instr_count;
            func.gcm.instr_count += 1;

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

    self.ctx.allocs = tmp.arena.alloc(u16, cursor);

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

            self.ctx.allocs[instr.schedule] =
                @intCast(prev + func.signature.params().len);

            switch (dataTypeToWasmType(instr.data_type)) {
                .fnc, .vec => unreachable,
                inline else => |ty| @field(counters, @tagName(ty)) += 1,
            }
        }
    }

    // NOTE: this is inneficient and we make more locals then we need but its
    // also simple and lets me focus on one problem at a time, just generate
    // wasm that works.

    // TODO: other cfg, we will need to carefully order the blocks
    std.debug.assert(func.gcm.postorder.len == 1);

    for (func.gcm.postorder) |block| {
        for (block.base.outputs()) |out| {
            const instr = out.get();
            self.emitInstr(instr);
        }
    }

    try self.ctx.buf.writer.writeByte(0x0b);
}

pub fn emitInstr(self: *WasmGen, instr: *Func.Node) void {
    errdefer unreachable;

    switch (instr.extra2()) {
        .CInt => |extra| {
            switch (dataTypeToWasmType(instr.data_type)) {
                .i64 => {
                    try self.ctx.buf.writer.writeByte(0x42);
                    try self.ctx.buf.writer
                        .writeUleb128(@as(u64, @bitCast(extra.value)));
                    try self.ctx.buf.writer.writeByte(0x21);
                    try self.ctx.buf.writer.writeUleb128(self.regOf(instr));
                },
                else => utils.panic("{}", .{instr.data_type}),
            }
        },
        .Return => {
            for (instr.dataDeps()) |d| {
                try self.ctx.buf.writer.writeByte(0x20);
                try self.ctx.buf.writer.writeUleb128(self.regOf(d));
            }

            try self.ctx.buf.writer.writeByte(0x0f);
        },
        else => {
            utils.panic("unhandled op {f}", .{instr});
        },
    }
}

pub fn regOf(self: *WasmGen, node: *Func.Node) u16 {
    return self.ctx.allocs[node.schedule];
}

pub fn emitData(self: *WasmGen, opts: Mach.DataOptions) void {
    _ = opts;
    _ = self;
    //unreachable;
}

pub fn finalize(self: *WasmGen, opts: Mach.FinalizeOptions) void {
    root.wasm.object.flush(
        self.mach.out,
        opts.output orelse return,
    ) catch unreachable;
}

pub fn disasm(_: *WasmGen, opts: Mach.DisasmOpts) void {
    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var child = std.process.Child.init(&.{ "wasm2wat", "-" }, tmp.arena.allocator());
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

    const exe_prefix = "main() => i64:";
    std.debug.assert(std.mem.startsWith(u8, stdout.items, exe_prefix));
    std.debug.assert(std.mem.endsWith(u8, stdout.items, "\n"));
    stdout.items = stdout.items[exe_prefix.len .. stdout.items.len - 1];

    return std.fmt.parseInt(usize, stdout.items, 10) catch unreachable;
}

pub fn deinit(self: *WasmGen) void {
    self.mach.out.deinit(self.gpa);
    self.func_ids.deinit(self.gpa);
    self.* = undefined;
}
