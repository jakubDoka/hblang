gpa: std.mem.Allocator,
cx_stack: std.ArrayListUnmanaged(ItemCtx) = .{},
files: []const Ast = &.{},
cx: ItemCtx = .{},
ct: struct {
    vm: Vm,
    stack: [*]u8,
},
tys: struct {
    computed: std.AutoHashMapUnmanaged(Symbol, Ty) = .{},
    funcs: std.ArrayListUnmanaged(Func) = .{},
    structs: std.ArrayListUnmanaged(Struct) = .{},
    allocated: std.ArrayListUnmanaged(Ty) = .{},
    scratch: std.ArrayListUnmanaged(Ty) = .{},
} = .{},
comp_stack: std.ArrayListUnmanaged(Ty) = .{},
value_buf: std.ArrayListUnmanaged(Value) = .{},
output: struct {
    code: std.ArrayListUnmanaged(u8) = .{},
    funcs: std.ArrayListUnmanaged(ItemReloc) = .{},
} = .{},
variables: std.ArrayListUnmanaged(Variable) = .{},
ret_relocs: std.ArrayListUnmanaged(i16) = .{},
stack_relocs: std.ArrayListUnmanaged(i16) = .{},
loops: std.ArrayListUnmanaged(Loop) = .{},
loop_relocs: std.ArrayListUnmanaged(i16) = .{},
errors: std.ArrayListUnmanaged(u8) = .{},

const std = @import("std");
const root = @import("root.zig");
const isa = @import("isa.zig");
const Ast = @import("parser.zig");
const Vm = @import("vm.zig");
const Lexer = @import("lexer.zig");
const Codegen = @This();

pub const File = u32;
pub const Offset = u32;
pub const Size = u32;

const vm_stack_size = 1024 * 1024 * 2;
const root_file = 0;
const debug = @import("builtin").mode == .Debug;

// ## DECLS

const Error = error{ Return, LoopControl, TooLongTuple } || std.mem.Allocator.Error;

pub const Ty = root.TaggedIndex(u32, enum { builtin, func, pointer, @"struct" });
pub const Namespace = root.TaggedIndex(u32, enum { file });

pub const Symbol = struct {
    const Item = u32;

    ns: Namespace,
    item: Item,

    fn init(ns: Namespace, item: Item) Symbol {
        return .{ .ns = ns, .item = item };
    }
};

pub const Tuple = packed struct(u32) {
    const Len = u4;
    const Base = std.meta.Int(.unsigned, @bitSizeOf(u32) - @bitSizeOf(Len));

    len: Len,
    base: Base,

    pub fn init(base: usize, len: usize) !Tuple {
        if (base > std.math.maxInt(Base)) return error.TooLongTuple;
        return .{ .len = @intCast(len), .base = @intCast(base) };
    }

    pub fn view(self: Tuple, slice: []const Ty) []const Ty {
        return slice[self.base..][0..self.len];
    }
};

pub const Struct = struct {
    file: File,
    field_names: Ast.Slice,
    field_types: Tuple,
};

const Loop = struct {
    var_base: u16,
    reloc_base: u16,
    back_jump_offset: i16,
};

const Variable = struct {
    name: Ast.Ident,
    value: Value,
};

const ItemReloc = struct {
    to: u32,
    offset: u32,
};

const Func = struct {
    file: File,
    decl: Ast.Id,
    args: Tuple,
    ret: Ty,
    base: u32 = std.math.maxInt(u32),
    size: u32 = std.math.maxInt(u32),
};

pub const Stack = struct {
    height: Offset = 0,
    max_height: Offset = 0,
    meta: std.ArrayListUnmanaged(Meta) = .{},

    const Id = u32;

    const Meta = struct {
        size: Size,
        offset: Offset = 0,
        rc: u32 = 1,
        trace: root.StaticTrace,
    };
};

pub const Regs = struct {
    frees: [254]Id = undefined,
    free_count: u8 = 0,
    next: u8,
    min: u8,
    max: u8,
    ret_used: bool = false,

    allocs: if (debug) [10]AllocData else void = undefined,
    alloc_count: if (debug) u8 else void = if (debug) 0,
    pub const Id = u8;
    pub const zero = 0;
    pub const ret = 1;
    pub const ret_addr = 31;
    pub const stack_ptr = 254;

    const AllocData = struct {
        id: Id,
        trace: root.StaticTrace,
    };

    pub fn init(start: u8, end: u8) Regs {
        return .{ .next = start, .max = end, .min = start };
    }

    pub fn allocRet(self: *Regs) ?Id {
        if (self.ret_used) return null;
        if (debug) self.addAlloc(@returnAddress(), ret);
        self.ret_used = true;
        return ret;
    }

    pub fn alloc(self: *Regs) Id {
        if (self.free_count != 0) {
            self.free_count -= 1;
            if (debug) self.addAlloc(@returnAddress(), self.frees[self.free_count]);
            return self.frees[self.free_count];
        }
        if (self.next == self.max) std.debug.panic("Runned out of registers, bummer.", .{});
        defer self.next += 1;
        if (debug) self.addAlloc(@returnAddress(), self.next);
        return self.next;
    }

    pub fn addAlloc(self: *Regs, return_addr: usize, reg: Id) void {
        self.allocs[self.alloc_count] = .{
            .id = reg,
            .trace = root.StaticTrace.init(return_addr),
        };
        self.alloc_count += 1;
    }

    pub fn free(self: *Regs, reg: Id) void {
        if (debug) {
            for (self.frees[0..self.free_count]) |r| {
                std.debug.assert(r != reg);
            }

            const index = for (self.allocs[0..self.alloc_count], 0..) |r, i| {
                if (r.id == reg) break i;
            } else std.debug.panic("Could not find reg in allocs: {d}", .{reg});

            self.alloc_count -= 1;
            std.mem.swap(AllocData, &self.allocs[index], &self.allocs[self.alloc_count]);
        }

        if (reg == ret) {
            self.ret_used = false;
            return;
        }

        self.frees[self.free_count] = reg;
        self.free_count += 1;
    }

    pub fn checkLeaks(self: *Regs) void {
        if (debug) {
            for (self.allocs[0..self.alloc_count]) |*alloc_data| {
                std.debug.print("leaked reg: {d}\n", .{alloc_data.id});
                alloc_data.trace.dump();
            }
        }
        if (self.free_count != self.next - self.min)
            std.debug.panic("Not all registers freed: {d} != {d}", .{ self.free_count, self.next - self.min });
    }
};

const ItemCtx = struct {
    ret: ?Ty = null,
    snap: Snapshot = .{},
    regs: Regs = Regs.init(Regs.ret_addr + 1, Regs.stack_ptr - 1),
    stack: Stack = .{},
    cond_op_ctx: ?*CondOp = null,

    const CondOp = struct {
        size: u8 = 0,
        invert: bool = false,
    };
};

pub const Loc = struct {
    flags: packed struct(u8) {
        is_comptime: bool = false,
        is_derefed: bool = false,
        is_borrowed: bool = false,
        _: u5 = undefined,
    } = .{},
    reg: Regs.Id = 0,
    sec_reg: Regs.Id = 0,
    stack: Stack.Id = undefined, // active is `self.reg == stack_ptr`
    offset: Offset = 0,

    const PackedStack = extern struct {
        id: Stack.Id,
        offset: Offset,
    };

    pub fn hasConsecutiveRegs(self: Loc) bool {
        std.debug.assert(self.sec_reg != 0);
        return self.reg == self.sec_reg -| 1;
    }

    pub fn toggled(self: Loc, comptime flag: []const u8, value: bool) Loc {
        var loc = self;
        // std.debug.assert(@field(loc.flags, "is_" ++ flag) != value);
        @field(loc.flags, "is_" ++ flag) = value;
        return loc;
    }

    pub fn offseted(self: Loc, by: Offset) Loc {
        var loc = self;
        loc.offset += by;
        return loc;
    }

    pub fn psi(self: Loc, offset: Offset) i64 {
        return @bitCast(PackedStack{ .id = self.stack, .offset = self.offset + offset });
    }

    pub fn psu(self: Loc, offset: Offset) u64 {
        return @bitCast(PackedStack{ .id = self.stack, .offset = self.offset + offset });
    }
};

const Value = struct {
    ty: Ty = buty(.void),
    loc: Loc = .{},

    fn toggled(self: Value, comptime flag: []const u8, value: bool) Value {
        return .{ .ty = self.ty, .loc = self.loc.toggled(flag, value) };
    }
};

const Snapshot = struct {
    code: usize = 0,
    funcs: usize = 0,
};

const Ctx = struct {
    ty: ?Ty = null,
    loc: ?Loc = null,
};

// ## FUNCTIONS

pub fn init(gpa: std.mem.Allocator) !Codegen {
    var vm = Vm{};
    const stack = try gpa.alloc(u8, vm_stack_size);
    vm.regs[Regs.stack_ptr] = @intFromPtr(stack.ptr[stack.len..]);

    return .{
        .gpa = gpa,
        .ct = .{
            .vm = vm,
            .stack = stack.ptr,
        },
    };
}

pub fn deinit(self: *Codegen) void {
    self.gpa.free(self.ct.stack[0..vm_stack_size]);
    self.tys.funcs.deinit(self.gpa);
    self.tys.structs.deinit(self.gpa);
    self.tys.computed.deinit(self.gpa);
    self.tys.allocated.deinit(self.gpa);
    std.debug.assert(self.tys.scratch.items.len == 0);
    self.tys.scratch.deinit(self.gpa);
    std.debug.assert(self.comp_stack.items.len == 0);
    self.comp_stack.deinit(self.gpa);
    self.output.code.deinit(self.gpa);
    self.output.funcs.deinit(self.gpa);
    std.debug.assert(self.variables.items.len == 0);
    self.variables.deinit(self.gpa);
    std.debug.assert(self.value_buf.items.len == 0);
    self.value_buf.deinit(self.gpa);
    std.debug.assert(self.ret_relocs.items.len == 0);
    self.ret_relocs.deinit(self.gpa);
    std.debug.assert(self.loop_relocs.items.len == 0);
    self.loop_relocs.deinit(self.gpa);
    std.debug.assert(self.loops.items.len == 0);
    self.loops.deinit(self.gpa);
    self.cx.stack.meta.deinit(self.gpa);
    std.debug.assert(self.stack_relocs.items.len == 0);
    self.stack_relocs.deinit(self.gpa);
}

pub fn generate(self: *Codegen) !void {
    _ = try self.findOrDeclare(Ast.Pos.init(0), root_file, "main");
    try self.generateFunc(true, 0);
    try self.completeCallGraph(0);
    try self.link();
}

fn link(self: *Codegen) !void {
    for (self.output.funcs.items) |func_reloc|
        self.relocateJump(self.tys.funcs.items[func_reloc.to].base, func_reloc.offset, 3);
}

fn relocateJump(self: *Codegen, to: anytype, offset: u32, sub_offset: u4) void {
    const Repr = std.meta.Int(.signed, @bitSizeOf(@TypeOf(to)));
    const jump = @as(Repr, @intCast(to)) - @as(Repr, @intCast(offset));
    self.writeReloc(Repr, offset + sub_offset, jump);
}

fn writeLocalReloc(self: *Codegen, comptime T: type, offset: usize, value: T) void {
    self.writeReloc(T, self.cx.snap.code + offset, value);
}

fn takeLocal(self: *Codegen, comptime T: type, offset: usize) T {
    const range = &self.output.code.items[self.cx.snap.code + offset ..][0..@sizeOf(T)].*;
    var value: T = undefined;
    value = @bitCast(range.*);
    @memset(range, 0);
    return value;
}

fn writeReloc(self: *Codegen, comptime T: type, offset: usize, value: T) void {
    std.debug.assert(std.mem.allEqual(u8, self.output.code.items[offset..][0..@sizeOf(T)], 0));
    self.output.code.items[offset..][0..@sizeOf(T)].* = @bitCast(value);
}

fn completeCallGraph(self: *Codegen, base: usize) !void {
    while (self.comp_stack.items.len > base) {
        const ty = self.comp_stack.pop();
        switch (ty.tag()) {
            .func => try self.generateFunc(false, ty.index),
            else => |v| std.debug.panic("unhandled call graph type: {any}", .{v}),
        }
    }
}

fn allocStack(self: *Codegen, size_data: anytype) !Loc {
    const size: Size = switch (@TypeOf(size_data)) {
        Ty => self.sizeOf(size_data),
        else => @intCast(size_data),
    };

    const s = &self.cx.stack;
    try s.meta.append(self.gpa, .{
        .size = size,
        .trace = root.StaticTrace.init(@returnAddress()),
    });
    // TODO: handle alignment
    s.height += size;
    s.max_height = @max(s.max_height, s.height);
    return .{
        .reg = Regs.stack_ptr,
        .stack = @intCast(s.meta.items.len - 1),
        .flags = .{ .is_derefed = true },
    };
}

fn checkStackLeaks(self: *Codegen) void {
    if (!debug) return;
    var leaked: usize = 0;
    for (self.cx.stack.meta.items) |*meta| {
        if (meta.rc != 0) {
            std.debug.print("leaked stack: {d}\n", .{meta.trace.index});
            meta.trace.dump();
            leaked += 1;
        }
    }
    std.debug.assert(leaked == 0);
}

fn generateFunc(self: *Codegen, comptime entry: bool, id: usize) !void {
    var func = &self.tys.funcs.items[id];
    const ast = self.files[func.file];
    self.cx.ret = func.ret;
    self.cx.snap = self.snapshot();
    self.cx.regs = Regs.init(Regs.ret_addr + 1, Regs.stack_ptr - 1);
    const decl = ast.exprs.getTyped(.Fn, func.decl).?;

    try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, 0 });
    if (!entry) try self.emit(.st, .{ Regs.ret_addr, Regs.stack_ptr, 0, 0 });

    if (self.sizeOf(func.ret) > 16) _ = self.cx.regs.allocRet().?;

    var arg_reg: u8 = 2;
    for (
        func.args.view(self.tys.allocated.items),
        ast.exprs.view(decl.args),
    ) |arg_ty, arg_decl_id| {
        const arg_decl = ast.exprs.getTyped(.Arg, arg_decl_id).?;
        const msg = "Compiled does not (yes) support patterns here";
        const bindings = ast.exprs.getTyped(.Ident, arg_decl.bindings) orelse
            try self.report(Ast.Payload(.Ident){}, func.file, arg_decl.bindings, msg, .{});
        const loc = switch (self.sizeOf(arg_ty)) {
            0 => Loc{},
            1...8 => b: {
                const loc = Loc{ .reg = self.cx.regs.alloc() };
                try self.emit(.cp, .{ loc.reg, arg_reg });
                arg_reg += 1;
                break :b loc;
            },
            9...16 => b: {
                const loc = Loc{
                    .reg = self.cx.regs.alloc(),
                    .sec_reg = self.cx.regs.alloc(),
                };
                try self.emit(.brc, .{ loc.reg, arg_reg, 2 });
                arg_reg += 2;
                break :b loc;
            },
            else => b: {
                const loc = Loc{ .reg = self.cx.regs.alloc() };
                try self.emit(.cp, .{ loc.reg, arg_reg });
                break :b loc.toggled("derefed", true);
            },
        };
        try self.variables.append(self.gpa, .{
            .name = bindings.id,
            .value = .{ .ty = arg_ty, .loc = loc },
        });
    }

    if (try catchUnreachable(self.generateExpr(func.file, .{}, decl.body)) != null) {
        try self.report({}, func.file, decl.body, "fuction does not return", .{});
    }

    func = &self.tys.funcs.items[id];
    for (self.variables.items[self.variables.items.len - func.args.len ..]) |variable|
        self.freeValue(variable.value);
    self.variables.items.len -= func.args.len;

    inline for (std.meta.fields(Snapshot)[1..]) |field| {
        const start = @field(self.cx.snap, field.name);
        for (@field(self.output, field.name).items[start..]) |*reloc|
            reloc.offset += @as(u32, @intCast(self.cx.snap.code));
    }

    const stack_size = self.cx.stack.max_height;
    const poped_regs_size = self.cx.regs.free_count * @as(u16, 8) + 8;
    self.cx.regs.checkLeaks();
    self.checkStackLeaks();

    const ret_offset = self.localOffset();
    for (self.ret_relocs.items) |offset| {
        self.writeLocalReloc(i32, @intCast(offset + 1), ret_offset - offset);
    }
    self.ret_relocs.items.len = 0;

    for (self.stack_relocs.items) |offset| {
        const packed_stack = self.takeLocal(Loc.PackedStack, @intCast(offset + 3));
        const meta = &self.cx.stack.meta.items[packed_stack.id];
        const final_offset = Vm.toSigned(64, stack_size) -
            Vm.toSigned(64, meta.offset - packed_stack.offset);
        self.writeLocalReloc(i64, @intCast(offset + 3), final_offset);
    }
    self.stack_relocs.items.len = 0;
    self.cx.stack.height = 0;
    self.cx.stack.max_height = 0;
    self.cx.stack.meta.items.len = 0;

    func.base = @intCast(self.cx.snap.code);
    func.size = @intCast(self.output.code.items.len - func.base);

    if (entry) {
        self.writeLocalReloc(u64, 3, 0 -% @as(u64, stack_size));
        try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, stack_size });
        try self.emit(.tx, .{});
    } else {
        self.writeLocalReloc(u64, 3, 0 -% @as(u64, poped_regs_size + stack_size));
        self.writeLocalReloc(u64, 3 + 8 + 3, stack_size); // for now
        self.writeLocalReloc(u16, 3 + 8 + 3 + 8, poped_regs_size);
        try self.emit(.ld, .{ Regs.ret_addr, Regs.stack_ptr, stack_size, poped_regs_size });
        try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, poped_regs_size });
        try self.emit(.jala, .{ Regs.zero, Regs.ret_addr, 0 });
    }
}

fn emit(self: *Codegen, comptime op: isa.Op, args: anytype) !void {
    if (op == .cp and args[0] == args[1]) return;
    try self.output.code.appendSlice(self.gpa, &isa.pack(op, args));
}

pub fn catchUnreachable(res: anytype) Error!?@typeInfo(@TypeOf(res)).ErrorUnion.payload {
    return res catch |e| switch (e) {
        error.Return, error.LoopControl => null,
        else => e,
    };
}

fn generateExpr(self: *Codegen, file: File, ctx: Ctx, id: Ast.Id) Error!Value {
    const ast = self.files[file];
    switch (ast.exprs.get(id)) {
        .Void, .Comment => return .{},
        .Block => |block| {
            const scope_frame = self.variables.items.len;
            defer {
                for (self.variables.items[scope_frame..]) |variable|
                    self.freeValue(variable.value);
                self.variables.items.len = scope_frame;
            }
            for (ast.exprs.view(block.stmts)) |stmt| {
                self.freeValue(try self.generateExpr(file, .{}, stmt));
            }
            return .{};
        },
        .Ctor => |c| {
            const explicit_ty = if (c.ty.tag() != .Void)
                try self.resolveTy(file, c.ty)
            else
                null;
            const ty = explicit_ty orelse ctx.ty orelse
                try self.report(buty(.void), file, c.pos, "Cant infer type of the struct", .{});
            if (ty.tag() != .@"struct") {
                try self.report({}, file, c.pos, "Can only construct structs", .{});
                return .{};
            }
            const ctor_fields = ast.exprs.view(c.fields);
            const dst = ctx.loc orelse try self.allocStack(ty);

            for (ctor_fields) |field_id| {
                const ctor_field_ast = ast.exprs.getTyped(.CtorField, field_id).?;
                const fty, const offset =
                    try self.fieldOffset(file, ctor_field_ast.pos, ty.index, ctor_field_ast.pos);
                var field_dst = dst.offseted(offset);
                field_dst.flags.is_borrowed = true;
                const fctx = .{ .ty = fty, .loc = field_dst };
                _ = try self.generateExpr(file, fctx, ctor_field_ast.value);
            }

            return .{ .ty = ty, .loc = dst };
        },
        .If => |i| {
            const const_ctx = Ctx{ .ty = buty(.bool) };
            var cond_op_ctx = ItemCtx.CondOp{};
            var cond: Value = undefined;
            {
                self.cx.cond_op_ctx = &cond_op_ctx;
                defer self.cx.cond_op_ctx = null;
                cond = try self.generateExpr(file, const_ctx, i.cond);
            }

            const cond_jump_offset = self.localOffset() - cond_op_ctx.size;
            const then, const else_ = if (cond_op_ctx.invert)
                .{ i.else_, i.then }
            else
                .{ i.then, i.else_ };
            if (cond_op_ctx.size == 0) {
                try self.emit(.jeq, .{ cond.loc.reg, 0, 0 });
                self.freeValue(cond);
            }

            const then_value = try self.handleReturn(self.generateExpr(file, .{}, then));
            if (then_value) |v| self.freeValue(v);
            var skip_then_dest = self.localOffset();

            var else_value: ?Value = .{};
            if (else_.tag() != .Void) {
                const else_jump_offset = self.localOffset();
                if (then_value != null) {
                    try self.emit(.jmp, .{0});
                    skip_then_dest += isa.instrSize(.jmp);
                }

                else_value = try self.handleReturn(self.generateExpr(file, .{}, else_));
                if (else_value) |v| self.freeValue(v);

                if (then_value != null) {
                    const skip_else_dest = self.localOffset();
                    self.writeLocalReloc(i32, @intCast(else_jump_offset + 1), skip_else_dest - else_jump_offset);
                }
            }

            const offset = skip_then_dest - cond_jump_offset;
            self.writeLocalReloc(i16, @intCast(cond_jump_offset + 3), offset);

            if (then_value == null and else_value == null) return error.Return;
            return .{};
        },
        .Loop => |l| {
            try self.loops.append(self.gpa, .{
                .var_base = @intCast(self.variables.items.len),
                .reloc_base = @intCast(self.loop_relocs.items.len),
                .back_jump_offset = self.localOffset(),
            });

            const ret = try catchUnreachable(self.generateExpr(file, .{}, l.body));
            if (ret) |r| self.freeValue(r);

            const loop = self.loops.pop();

            if (ret != null) {
                const back_jump_offset = loop.back_jump_offset - self.localOffset();
                try self.emit(.jmp, .{back_jump_offset});
            }

            if (self.loop_relocs.items.len == loop.reloc_base) return error.Return;

            const end = self.localOffset();
            for (self.loop_relocs.items[loop.reloc_base..]) |reloc|
                self.writeLocalReloc(i32, @intCast(reloc + 1), end - reloc);
            self.loop_relocs.items.len = loop.reloc_base;
            return .{};
        },
        .Break => |b| {
            if (self.loops.items.len == 0) {
                try self.report({}, file, b, "break outside of loop", .{});
                return .{};
            }
            try self.loop_relocs.append(self.gpa, self.localOffset());
            try self.emit(.jmp, .{0});
            return error.LoopControl;
        },
        .Continue => |c| {
            if (self.loops.items.len == 0) {
                try self.report({}, file, c, "continue outside of loop", .{});
                return .{};
            }
            const loop = self.loops.items[self.loops.items.len - 1];
            try self.emit(.jmp, .{loop.back_jump_offset - self.localOffset()});
            return error.LoopControl;
        },
        .Return => |ret| {
            // TODO: dettect functon calls in the expression to avoid this
            const retCtx = Ctx{
                .ty = self.cx.ret,
                .loc = switch (self.sizeOf(self.cx.ret.?)) {
                    0 => Loc{},
                    1...8 => .{ .reg = self.cx.regs.allocRet() orelse
                        self.cx.regs.alloc() },
                    9...16 => unreachable,
                    else => .{ .reg = Regs.ret, .flags = .{ .is_derefed = true } },
                },
            };
            const value = try self.generateExpr(file, retCtx, ret.value);
            self.freeValue(value);
            return error.Return;
        },
        .Call => |call| {
            const todo = "TODO: handle the complex function expression";
            const called = ast.exprs.getTyped(.Ident, call.called) orelse
                try self.report(Ast.Payload(.Ident){}, file, call.called, todo, .{});
            const func_id = try self.findOrDeclare(called.pos, file, called.id);
            std.debug.assert(func_id.tag() == .func);
            const func = self.tys.funcs.items[func_id.index];

            var arg_reg: u8 = 2;
            for (ast.exprs.view(call.args), 0..) |arg, i| {
                const arg_ty = func.args.view(self.tys.allocated.items)[i];
                const value = switch (self.sizeOf(arg_ty)) {
                    0 => Value{},
                    1...8 => b: {
                        const arg_ctx = Ctx{
                            .ty = arg_ty,
                            .loc = .{ .reg = arg_reg, .flags = .{ .is_borrowed = true } },
                        };
                        arg_reg += 1;
                        break :b try self.generateExpr(file, arg_ctx, arg);
                    },
                    9...16 => b: {
                        const arg_ctx = Ctx{ .ty = arg_ty, .loc = .{
                            .reg = arg_reg,
                            .sec_reg = arg_reg + 1,
                            .flags = .{ .is_borrowed = true },
                        } };
                        arg_reg += 2;
                        break :b try self.generateExpr(file, arg_ctx, arg);
                    },
                    else => {
                        const arg_ctx = Ctx{ .ty = arg_ty };
                        const value = try self.generateExpr(file, arg_ctx, arg);
                        try self.value_buf.append(self.gpa, value);
                        std.debug.assert(value.loc.flags.is_derefed);
                        if (value.loc.reg == Regs.stack_ptr) {
                            try self.stack_relocs.append(self.gpa, self.localOffset());
                            try self.emit(.addi64, .{ arg_reg, Regs.stack_ptr, value.loc.psu(0) });
                        } else unreachable;
                        arg_reg += 1;
                        continue;
                    },
                };
                try self.value_buf.append(self.gpa, value);
            }
            const base = self.value_buf.items.len - ast.exprs.view(call.args).len;
            for (self.value_buf.items[base..]) |value| self.freeValue(value);
            self.value_buf.items.len = base;

            switch (self.sizeOf(func.ret)) {
                0 => {
                    try self.addReloc("func", func_id.index);
                    try self.emit(.jal, .{ Regs.ret_addr, Regs.zero, 0 });
                    return .{};
                },
                1...8 => {
                    const ret = self.cx.regs.allocRet();
                    var ret_temp: ?Regs.Id = null;
                    if (ret == null and (ctx.loc == null or ctx.loc.?.reg != Regs.ret)) {
                        ret_temp = self.cx.regs.alloc();
                        try self.emit(.cp, .{ ret_temp.?, Regs.ret });
                    }

                    try self.addReloc("func", func_id.index);
                    try self.emit(.jal, .{ Regs.ret_addr, Regs.zero, 0 });

                    if (ret_temp) |r| try self.emit(.swa, .{ r, Regs.ret });

                    const final_ret = if (ret) |r|
                        Loc{ .reg = r }
                    else if (ret_temp) |r|
                        Loc{ .reg = r }
                    else if (ctx.loc) |l|
                        l.toggled("borrowed", true)
                    else
                        unreachable;

                    return self.assignToCtx(file, call, ctx, .{
                        .ty = func.ret,
                        .loc = final_ret,
                    });
                },
                9...16 => unreachable,
                else => if (ctx.loc) |l| {
                    _ = l;
                    unreachable;
                } else {
                    const ret = self.cx.regs.allocRet();
                    var ret_temp: ?Regs.Id = null;
                    if (ret == null) {
                        ret_temp = self.cx.regs.alloc();
                        try self.emit(.cp, .{ ret_temp.?, Regs.ret });
                    }

                    const ret_loc = try self.allocStack(func.ret);
                    try self.stack_relocs.append(self.gpa, self.localOffset());
                    try self.emit(.addi64, .{ Regs.ret, Regs.stack_ptr, ret_loc.psu(0) });

                    try self.addReloc("func", func_id.index);
                    try self.emit(.jal, .{ Regs.ret_addr, Regs.zero, 0 });

                    if (ret_temp) |r| try self.emit(.swa, .{ r, Regs.ret });
                    if (ret) |r| self.cx.regs.free(r);

                    return .{ .ty = func.ret, .loc = ret_loc };
                },
            }
        },
        .Ident => |i| {
            const variable = &self.variables.items[i.id.index];

            if (i.id.last and
                (self.loops.items.len == 0 or self.loops.getLast().var_base <= i.id.index))
            {
                defer variable.value = .{};
                return self.assignToCtx(file, i, ctx, variable.value);
            }

            return try self.assignToCtx(file, i, ctx, variable.value.toggled("borrowed", true));
        },
        .Integer => |i| {
            const int_token = Lexer.peek(ast.source, i.index);
            const int_value = std.fmt.parseInt(u64, int_token.view(ast.source), 10) catch |e|
                try self.report(@as(u64, 0), file, i, "Could not parse integer: {any}", .{e});
            if (ctx.loc) |loc| if (loc.flags.is_derefed) {
                const src = Loc{ .reg = self.cx.regs.alloc() };
                try self.emit(.li64, .{ src.reg, int_value });
                return self.assignToCtx(file, i, ctx, .{
                    .ty = ctx.ty orelse buty(.int),
                    .loc = src,
                });
            } else {
                try self.emit(.li64, .{ loc.reg, int_value });
                return .{ .ty = ctx.ty orelse buty(.int), .loc = loc };
            } else {
                const loc = Loc{ .reg = self.cx.regs.alloc() };
                try self.emit(.li64, .{ loc.reg, int_value });
                return .{ .ty = ctx.ty orelse buty(.int), .loc = loc };
            }
        },
        .UnOp => |u| return try self.generateUnOp(file, ctx, u),
        .BinOp => |b| if (b.op.innerOp()) |iop| {
            var mb = b;
            mb.op = iop;
            return try self.generateBinOp(file, ctx, mb, true);
        } else {
            return try self.generateBinOp(file, ctx, b, false);
        },
        .Field => |f| {
            var base = try self.generateExpr(file, .{}, f.base);
            if (base.ty.tag() == .pointer) {
                try self.ensureLoaded(&base);
                base.ty = self.tys.allocated.items[base.ty.index];
                base.loc = base.loc.toggled("derefed", true);
            }

            if (base.ty.tag() != .@"struct") {
                try self.report({}, file, f.field, "Cant acces fields on this", .{});
                // TODO: log type
                return .{};
            }

            const ty, const offset =
                try self.fieldOffset(file, f.field, base.ty.index, f.field);
            const value = Value{ .ty = ty, .loc = base.loc.offseted(offset) };
            return try self.assignToCtx(file, f, ctx, value);
        },
        else => |v| std.debug.panic("unhandled expr: {any}", .{v}),
    }
}

fn fieldOffset(
    self: *Codegen,
    file: File,
    pos: anytype,
    stru_id: usize,
    field: anytype,
) !struct { Ty, Offset } {
    const stru = self.tys.structs.items[stru_id];
    const ast = self.files[stru.file];
    const ctrot_field_name = switch (@TypeOf(field)) {
        Ast.Pos => Lexer.peekStr(ast.source, field.index),
        else => @compileError("wat"),
    };
    var offset: Offset = 0;
    const msg = "struct does not have {s} field";
    const dummy = .{ buty(.void), @as(Offset, 0) };
    return for (
        ast.exprs.view(stru.field_names),
        stru.field_types.view(self.tys.allocated.items),
    ) |name, field_ty| {
        offset = root.alignTo(offset, self.alignOf(field_ty));
        const field_ast = ast.exprs.getTyped(.CtorField, name).?;
        if (std.mem.eql(
            u8,
            ctrot_field_name,
            Lexer.peekStr(ast.source, field_ast.pos.index),
        )) break .{ field_ty, offset };
        offset += self.sizeOf(field_ty);
    } else try self.report(dummy, file, pos, msg, .{ctrot_field_name});
}

fn generateUnOp(self: *Codegen, file: File, ctx: Ctx, payload: std.meta.TagPayload(Ast.Expr, .UnOp)) !Value {
    switch (payload.op) {
        .@"&" => {
            const ty = if (ctx.ty) |ty| self.derefTy(ty) else null;
            var oper = try self.generateExpr(file, .{ .ty = ty }, payload.oper);
            oper.ty = ctx.ty orelse try self.makePtr(oper.ty);
            if (!oper.loc.flags.is_derefed) {
                try self.report({}, file, payload.oper, "cannot take address of a value", .{});
                return .{};
            }
            return try self.assignToCtx(file, payload, ctx, oper.toggled("derefed", false));
        },
        .@"*" => {
            const ty = if (ctx.ty) |ty| try self.makePtr(ty) else null;
            var oper = try self.generateExpr(file, .{ .ty = ty }, payload.oper);
            try self.ensureLoaded(&oper);
            oper.ty = ctx.ty orelse self.derefTy(oper.ty).?;
            return try self.assignToCtx(file, payload, ctx, oper.toggled("derefed", true));
        },
        else => |v| std.debug.panic("undandeld unop: {any}", .{v}),
    }
}

fn assignToCtx(self: *Codegen, file: File, pos: anytype, ctx: Ctx, src: Value) !Value {
    const dst = ctx.loc orelse return src;
    try self.assign(file, pos, .{ .ty = ctx.ty orelse src.ty, .loc = dst }, src);
    self.freeValue(src);
    return .{ .ty = src.ty, .loc = dst };
}

fn fieldMask(size: Size, offset: Offset) u64 {
    return (@as(u64, 1) << @intCast(size * 8)) - 1 << @intCast(offset * 8);
}

// TODO: change signature to take a size/type instead
fn assign(self: *Codegen, file: File, origin: anytype, pdst: Value, psrc: Value) !void {
    if (!try self.assertMoveTypes(file, origin, pdst.ty, psrc.ty)) return;
    try self.assignUnchecked(pdst.loc, psrc);
}

fn assignUnchecked(self: *Codegen, pdst: Loc, psrc: Value) !void {
    var dst, var src, const size = .{ pdst, psrc.loc, self.sizeOf(psrc.ty) };
    if (size == 0) return;

    if (!dst.flags.is_derefed and !src.flags.is_derefed) {
        std.debug.assert(src.offset + size <= 16);
        std.debug.assert(src.offset + size <= 8 or src.sec_reg != 0);
        std.debug.assert(dst.offset + size <= 16);
        std.debug.assert(dst.offset + size <= 8 or dst.sec_reg != 0);

        if (size == 8) b: {
            const src_reg = if (src.offset == 0)
                src.reg
            else if (src.offset == 8)
                src.sec_reg
            else
                break :b;

            const dst_reg = if (dst.offset == 0)
                dst.reg
            else if (dst.offset == 8)
                dst.sec_reg
            else
                break :b;

            return try self.emit(.cp, .{ dst_reg, src_reg });
        }

        if (size == 16) {
            if (src.hasConsecutiveRegs() and dst.hasConsecutiveRegs()) {
                return try self.emit(.brc, .{ dst.reg, src.reg, 2 });
            }

            try self.emit(.cp, .{ dst.reg, src.reg });
            try self.emit(.cp, .{ dst.sec_reg, src.sec_reg });
            return;
        }

        if (src.offset == 0 and size == 8) {
            return try self.emit(.cp, .{ dst.reg, src.reg });
        } else if (src.offset == 0 and size == 16) {
            return try self.emit(.brc, .{ dst.reg, src.reg, 2 });
        } else if (src.offset == 8 and size == 8) {
            return try self.emit(.cp, .{ dst.reg, src.sec_reg });
        }

        const needs_copy = src.flags.is_borrowed;
        const lcopied = needs_copy and (src.offset > 0 or dst.offset > 0 or size < 8);
        const rcopied = needs_copy and (src.offset + size > 8 or dst.offset + size > 8) and
            (src.offset + size < 16 or dst.offset + size < 16 or size < 8);

        const ldest = if (lcopied) self.cx.regs.alloc() else src.reg;
        defer if (lcopied) self.cx.regs.free(ldest);
        const rdest = if (rcopied) self.cx.regs.alloc() else src.sec_reg;
        defer if (rcopied) self.cx.regs.free(rdest);

        const overflowing_src_size = src.offset + size -| 8;
        if ((src.offset > 0 or size < 8) and src.offset < 8) {
            const mask = fieldMask(size - overflowing_src_size, src.offset);
            try self.emit(.andi, .{ ldest, ldest, mask });
        }
        if (overflowing_src_size > 0 and overflowing_src_size < 8) {
            const mask = fieldMask(overflowing_src_size, 0);
            try self.emit(.andi, .{ rdest, rdest, mask });
        }

        const offset_diff = @as(i8, @intCast(dst.offset)) - @as(i8, @intCast(src.offset));
        // FIXME: in some cases the generated code is wasteful
        if (offset_diff > 0) {
            const diff: u8 = @intCast(offset_diff);
            if (rcopied) {
                try self.emit(.slui64, .{ rdest, rdest, diff });
                if (lcopied) {
                    const tmp = self.cx.regs.alloc();
                    defer self.cx.regs.free(tmp);
                    const mask = fieldMask(diff, dst.offset - diff);
                    try self.emit(.andi, .{ tmp, rdest, mask });
                    const back_shift: u8 = @intCast((dst.offset + size) % 8 - diff);
                    try self.emit(.srui64, .{ rdest, rdest, back_shift });
                    try self.emit(.@"or", .{ rdest, rdest, tmp });
                }
            }
            if (lcopied) try self.emit(.slui64, .{ ldest, ldest, diff });
        } else if (offset_diff < 0) {
            const diff: u8 = @intCast(-offset_diff);
            if (lcopied) {
                try self.emit(.srui64, .{ ldest, ldest, diff });
                if (rcopied) {
                    const tmp = self.cx.regs.alloc();
                    defer self.cx.regs.free(tmp);
                    const mask = fieldMask(diff, 0);
                    try self.emit(.andi, .{ tmp, rdest, mask });
                    const back_shift: u8 = @intCast((dst.offset + size) % 8 - diff);
                    try self.emit(.slui64, .{ rdest, rdest, back_shift });
                    try self.emit(.@"or", .{ rdest, rdest, tmp });
                }
            }
            if (rcopied) try self.emit(.srui64, .{ rdest, rdest, diff });
        }

        const overflowing_dst_size = dst.offset + size -| 8;
        if ((src.offset > 0 or size < 8) and src.offset < 8) {
            const mask = ~fieldMask(size - overflowing_dst_size, src.offset);
            try self.emit(.andi, .{ dst.reg, dst.reg, mask });
            try self.emit(.@"or", .{ dst.reg, dst.reg, ldest });
        }
        if (overflowing_dst_size > 0 and overflowing_dst_size < 8) {
            const mask = ~fieldMask(overflowing_dst_size, 0);
            try self.emit(.andi, .{ dst.reg, dst.reg, mask });
            try self.emit(.@"or", .{ dst.reg, dst.reg, rdest });
        }
    } else if (dst.flags.is_derefed and src.flags.is_derefed) {
        var dts_ptr_reg: ?Regs.Id = null;
        defer if (dts_ptr_reg) |reg| self.cx.regs.free(reg);
        const dst_ptr = if (dst.reg == Regs.stack_ptr) b: {
            try self.stack_relocs.append(self.gpa, self.localOffset());
            dts_ptr_reg = self.cx.regs.alloc();
            try self.emit(.addi64, .{ dts_ptr_reg.?, Regs.stack_ptr, dst.psu(0) });
            break :b dts_ptr_reg.?;
        } else dst.reg;

        var src_ptr_reg: ?Regs.Id = null;
        defer if (src_ptr_reg) |reg| self.cx.regs.free(reg);
        const src_ptr = if (src.reg == Regs.stack_ptr) b: {
            try self.stack_relocs.append(self.gpa, self.localOffset());
            src_ptr_reg = self.cx.regs.alloc();
            try self.emit(.addi64, .{ src_ptr_reg.?, Regs.stack_ptr, src.psu(0) });
            break :b src_ptr_reg.?;
        } else src.reg;

        try self.emit(.bmc, .{ dst_ptr, src_ptr, size });
    } else if (dst.flags.is_derefed) {
        if (dst.reg == Regs.stack_ptr) {
            try self.stack_relocs.append(self.gpa, self.localOffset());
            std.debug.assert(size <= 8);
            try self.emit(.st, .{ src.reg, Regs.stack_ptr, dst.psi(0), size });
        } else {
            try self.emit(.st, .{ src.reg, dst.reg, dst.offset, 8 });
        }
    } else {
        if (src.reg == Regs.stack_ptr) {
            try self.stack_relocs.append(self.gpa, self.localOffset());
            if (size <= 8 or dst.hasConsecutiveRegs()) {
                try self.emit(.ld, .{ dst.reg, Regs.stack_ptr, src.psi(0), size });
            } else {
                try self.emit(.ld, .{ dst.reg, dst.sec_reg, src.psi(0), 8 });
                try self.stack_relocs.append(self.gpa, self.localOffset());
                try self.emit(.ld, .{ dst.sec_reg, Regs.stack_ptr, src.psi(8), size - 8 });
            }
        } else {
            try self.emit(.ld, .{ dst.reg, src.reg, src.offset, 8 });
        }
    }
}

fn assertMoveTypes(self: *Codegen, file: File, pos: anytype, dst: Ty, src: Ty) !bool {
    const msg = "types dont match, expected {any}, got {any}";
    if (dst.tag() != src.tag())
        return try self.report(false, file, pos, msg, .{
            TD.init(self, dst),
            TD.init(self, src),
        });

    return true;
}

const TD = struct {
    codegen: *Codegen,
    ty: Ty,

    fn init(codegen: *Codegen, ty: Ty) @This() {
        return .{ .codegen = codegen, .ty = ty };
    }

    pub fn format(
        slf: @This(),
        comptime _: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        try slf.codegen.fmtTy(slf.ty, writer);
    }
};

fn fmtTy(self: *Codegen, ty: Ty, writer: anytype) !void {
    switch (ty.tag()) {
        .func => unreachable,
        .builtin => {
            const tok: Lexer.Lexeme = @enumFromInt(ty.index);
            try writer.writeAll(tok.repr());
        },
        .pointer => {
            try writer.writeAll("^");
            try self.fmtTy(self.tys.allocated.items[ty.index], writer);
        },
        .@"struct" => {
            const stru = self.tys.structs.items[ty.index];
            const ast = self.files[stru.file];
            try writer.writeAll("struct {");
            for (
                ast.exprs.view(stru.field_names),
                stru.field_types.view(self.tys.allocated.items),
            ) |ast_field, ty_field| {
                const field = ast.exprs.getTyped(.CtorField, ast_field).?;
                try writer.writeAll(Lexer.peekStr(ast.source, field.pos.index));
                try writer.writeAll(": ");
                try self.fmtTy(ty_field, writer);
            }
        },
    }
}

fn derefTy(self: *Codegen, ty: Ty) ?Ty {
    if (ty.tag() != .pointer) return null;
    return self.tys.allocated.items[ty.index];
}

fn generateBinOp(
    self: *Codegen,
    file: File,
    ctx: Ctx,
    payload: Ast.Payload(.BinOp),
    comptime fold: bool,
) !Value {
    const ast = self.files[file];
    switch (payload.op) {
        .@"=" => {
            const lhs = try self.generateExpr(file, .{}, payload.lhs);
            defer self.freeValue(lhs);
            _ = try self.generateExpr(file, .{ .ty = lhs.ty, .loc = lhs.loc }, payload.rhs);
            return .{};
        },
        .@":=" => {
            const msg = "destructuring is not (yet) allowed";
            const lhs = ast.exprs.getTyped(.Ident, payload.lhs) orelse
                try self.report(Ast.Payload(.Ident){}, file, payload.lhs, msg, .{});
            var rhs = try self.generateExpr(file, .{}, payload.rhs);
            try self.ensureOwned(&rhs);
            if (lhs.id.referenced) {
                std.debug.assert(!rhs.loc.flags.is_derefed);
                const size = self.sizeOf(rhs.ty);
                self.cx.regs.free(rhs.loc.reg);
                const stack = try self.allocStack(size);
                try self.stack_relocs.append(self.gpa, self.localOffset());
                try self.emit(.st, .{ rhs.loc.reg, Regs.stack_ptr, stack.psi(0), size });
                rhs.loc = stack;
            }
            try self.variables.append(self.gpa, .{ .name = lhs.id, .value = rhs });
            return .{};
        },
        inline .@"+", .@"-", .@"*" => |op| {
            const instr = switch (op) {
                .@"+" => .add64,
                .@"-" => .sub64,
                .@"*" => .mul64,
                else => |v| @compileError("unhandled binop: " ++ @tagName(v)),
            };

            if (fold) {
                const lhs = try self.generateExpr(file, .{}, payload.lhs);
                var rhs = try self.generateExpr(file, .{ .ty = lhs.ty }, payload.rhs);
                try self.ensureLoaded(&rhs);
                defer self.freeValue(rhs);
                if (lhs.loc.flags.is_derefed or lhs.loc.offset != 0 or self.sizeOf(lhs.ty) < 8) {
                    var loaded = lhs;
                    loaded.loc.flags.is_borrowed = true;
                    try self.ensureOwned(&loaded);
                    defer self.freeValue(loaded);
                    try self.emit(instr, .{ loaded.loc.reg, loaded.loc.reg, rhs.loc.reg });
                    try self.assignUnchecked(lhs.loc, loaded);
                } else {
                    try self.emit(instr, .{ lhs.loc.reg, lhs.loc.reg, rhs.loc.reg });
                }
                return .{};
            } else {
                var lhs = try self.generateExpr(file, .{ .ty = ctx.ty }, payload.lhs);
                try self.ensureLoaded(&lhs);
                defer if (ctx.loc != null) self.freeValue(lhs);
                if (ctx.loc == null) try self.ensureOwned(&lhs);
                const dst = ctx.loc orelse lhs.loc;
                var rhs = try self.generateExpr(file, .{ .ty = lhs.ty }, payload.rhs);
                try self.ensureLoaded(&rhs);
                defer self.freeValue(rhs);
                try self.emit(instr, .{ dst.reg, lhs.loc.reg, rhs.loc.reg });
                return .{ .ty = lhs.ty, .loc = dst };
            }
        },
        .@"/" => {
            var lhs = try self.generateExpr(file, .{ .ty = ctx.ty }, payload.lhs);
            defer if (ctx.loc != null) self.freeValue(lhs);
            if (ctx.loc == null) try self.ensureOwned(&lhs);
            const dst = ctx.loc orelse lhs.loc;
            const rhs = try self.generateExpr(file, .{ .ty = lhs.ty }, payload.rhs);
            defer self.freeValue(rhs);
            try self.emit(.diru64, .{ dst.reg, 0, lhs.loc.reg, rhs.loc.reg });
            return .{ .ty = lhs.ty, .loc = dst };
        },
        inline .@"<=", .@"<", .@"==", .@"!=" => |op| {
            if (self.cx.cond_op_ctx) |op_ctx| {
                self.cx.cond_op_ctx = null;
                const instr, const invert = switch (op) {
                    .@"<=" => .{ .jgtu, false },
                    .@"<" => .{ .jgtu, true },
                    .@"==" => .{ .jeq, true },
                    .@"!=" => .{ .jne, true },
                    else => @compileError("wat"),
                };
                op_ctx.size = @intCast(isa.instrSize(instr));
                op_ctx.invert = invert;

                var lhs = try self.generateExpr(file, .{}, payload.lhs);
                try self.ensureLoaded(&lhs);
                defer self.freeValue(lhs);
                var rhs = try self.generateExpr(file, .{ .ty = lhs.ty }, payload.rhs);
                try self.ensureLoaded(&rhs);
                defer self.freeValue(rhs);

                try self.emit(instr, .{ lhs.loc.reg, rhs.loc.reg, 0 });

                return .{};
            }

            const dst = ctx.loc orelse Loc{ .reg = self.cx.regs.alloc() };
            std.debug.assert(!dst.flags.is_derefed);
            var lhs = try self.generateExpr(file, .{ .loc = dst }, payload.lhs);
            try self.ensureLoaded(&lhs);
            var rhs = try self.generateExpr(file, .{ .ty = lhs.ty }, payload.rhs);
            try self.ensureLoaded(&rhs);
            defer self.freeValue(rhs);

            const against = switch (op) {
                .@"<=" => 1,
                .@"==", .@"!=" => 0,
                .@"<" => Vm.toUnsigned(64, -1),
                else => @compileError("wat"),
            };
            try self.emit(.cmpu, .{ dst.reg, dst.reg, rhs.loc.reg });
            try self.emit(.cmpui, .{ dst.reg, dst.reg, against });
            switch (op) {
                .@"<", .@"==" => try self.emit(.not, .{ dst.reg, dst.reg }),
                else => {},
            }
            return .{ .ty = buty(.bool), .loc = dst };
        },
        else => |v| std.debug.panic("unhandled binop: {s}", .{@tagName(v)}),
    }
}

fn ensureLoaded(self: *Codegen, value: *Value) !void {
    const size = self.sizeOf(value.ty);
    if ((!value.loc.flags.is_derefed and value.loc.offset == 0) or size == 0) {
        std.debug.assert(!value.loc.flags.is_derefed);
        return;
    }
    const loc = Loc{ .reg = self.cx.regs.alloc() };
    try self.assignUnchecked(loc, value.*);
    self.freeValue(value.*);
    value.loc = loc;
}

fn ensureOwned(self: *Codegen, value: *Value) !void {
    if (!value.loc.flags.is_borrowed) return;
    std.debug.assert(self.sizeOf(value.ty) <= 8);
    const loc = Loc{ .reg = self.cx.regs.alloc() };
    try self.assignUnchecked(loc, value.*);
    value.loc = loc;
}

fn handleReturn(self: *Codegen, value: Error!Value) Error!?Value {
    return value catch |e| switch (e) {
        error.Return => {
            try self.ret_relocs.append(self.gpa, self.localOffset());
            try self.emit(.jmp, .{0});
            return null;
        },
        error.LoopControl => return null,
        error.OutOfMemory, error.TooLongTuple => return e,
    };
}

fn tryAllocZst(self: *Codegen, ty: ?Ty) ?Regs.Id {
    if (self.sizeOf(ty orelse return null) == 0) return Regs.zero;
    return null;
}

fn sizeOf(self: *Codegen, ty: Ty) Size {
    return switch (ty.tag()) {
        .builtin => switch (@as(Lexer.Lexeme, @enumFromInt(ty.index))) {
            .void => 0,
            .int => @sizeOf(u64),
            else => std.debug.panic("unhandled builtin type: {s}", .{@tagName(ty.tag())}),
        },
        .pointer => @sizeOf(u64),
        .@"struct" => {
            const stru = self.tys.structs.items[ty.index];
            var size: Size = 0;
            for (stru.field_types.view(self.tys.allocated.items)) |fty| {
                size = root.alignTo(size, self.alignOf(fty));
                size += self.sizeOf(fty);
            }
            return size;
        },
        else => |v| std.debug.panic("unhandled type: {s}", .{@tagName(v)}),
    };
}

fn alignOf(self: *Codegen, ty: Ty) Size {
    return switch (ty.tag()) {
        .@"struct" => {
            const stru = self.tys.structs.items[ty.index];
            var alignment: Size = 1;
            for (stru.field_types.view(self.tys.allocated.items)) |fty| {
                alignment = @max(alignment, self.alignOf(fty));
            }
            return alignment;
        },
        else => self.sizeOf(ty),
    };
}

fn localOffset(self: *Codegen) i16 {
    return @intCast(self.output.code.items.len - self.cx.snap.code);
}

fn addReloc(self: *Codegen, comptime kind: []const u8, id: u32) !void {
    const offset = self.localOffset();
    try @field(self.output, kind ++ "s").append(self.gpa, .{
        .to = id,
        .offset = @intCast(offset),
    });
}

fn freeValue(self: *Codegen, value: Value) void {
    self.freeLoc(value.loc);
}

fn freeLoc(self: *Codegen, loc: Loc) void {
    if (loc.flags.is_borrowed) return;
    if (loc.reg == Regs.stack_ptr)
        self.freeStack(loc.stack)
    else if (loc.reg != 0) {
        if (loc.sec_reg != 0) self.cx.regs.free(loc.sec_reg);
        self.cx.regs.free(loc.reg);
    }
}

fn freeStack(self: *Codegen, stack: Stack.Id) void {
    const meta = &self.cx.stack.meta.items[stack];
    meta.rc -= 1;
    if (meta.rc == 0) {
        meta.offset = self.cx.stack.height;
        self.cx.stack.height -= meta.size;
    }
}

pub fn buty(ty: Lexer.Lexeme) Ty {
    return Ty.init(.builtin, @intFromEnum(ty));
}

fn snapshot(self: *Codegen) Snapshot {
    var snap: Snapshot = undefined;
    inline for (std.meta.fields(Snapshot)) |field|
        @field(snap, field.name) = @field(self.output, field.name).items.len;
    return snap;
}

fn findOrDeclare(self: *Codegen, pos: Ast.Pos, file: File, query: anytype) Error!Ty {
    const ast = self.files[file];

    const msg = "Could not find declaration for {s}";
    const decl, const ident = if (@TypeOf(query) == Ast.Ident) b: {
        const decl = ast.decls[query.index];
        const expr = ast.exprs.getTyped(.BinOp, decl.expr).?;
        std.debug.assert(expr.op == .@":=");
        break :b .{ expr.rhs, decl.name };
    } else for (ast.exprs.view(ast.items)) |id| {
        const expr = ast.exprs.getTyped(.BinOp, id) orelse continue;
        std.debug.assert(expr.op == .@":=");
        const name = ast.exprs.getTyped(.Ident, expr.lhs).?;

        if (!switch (@TypeOf(query)) {
            Ast.Pos => query.index == name.id.index,
            else => Ast.cmp(name.pos.index, ast.source, query),
        }) continue;

        break .{ expr.rhs, name.id };
    } else return try self.report(buty(.void), file, pos, msg, .{
        switch (@TypeOf(query)) {
            Ast.Ident => Lexer.peekStr(ast.source, pos.index),
            else => query,
        },
    });

    const sym = Symbol{ .ns = Namespace.init(.file, file), .item = @bitCast(ident) };
    if (self.tys.computed.get(sym)) |id| return id;

    switch (ast.exprs.get(decl)) {
        .Fn => |f| {
            const func = Func{
                .file = file,
                .decl = decl,
                .args = try self.makeTuple(.Arg, file, f.args),
                .ret = try self.resolveTy(file, f.ret),
            };
            const id = Ty.init(.func, self.tys.funcs.items.len);
            try self.tys.funcs.append(self.gpa, func);
            if (@TypeOf(query) == Ast.Ident or !std.mem.eql(u8, query, "main"))
                try self.comp_stack.append(self.gpa, id);
            try self.tys.computed.put(self.gpa, sym, id);
            return id;
        },
        .Struct => |s| {
            const stru = Struct{
                .file = file,
                .field_names = s.fields,
                .field_types = try self.makeTuple(.CtorField, file, s.fields),
            };
            const id = Ty.init(.@"struct", self.tys.structs.items.len);
            try self.tys.structs.append(self.gpa, stru);
            return id;
        },
        else => |v| std.debug.panic("unhandled declaration: {any}", .{v}),
    }
}

fn makeTuple(self: *Codegen, comptime kind: Ast.Kind, file: File, args: Ast.Slice) !Tuple {
    const ast = self.files[file];
    const arg_exprs = ast.exprs.view(args);
    for (arg_exprs) |id| {
        const arg = ast.exprs.getTyped(kind, id).?;
        const typ = switch (kind) {
            .Arg => arg.ty,
            .CtorField => arg.value,
            else => @compileError("wat"),
        };
        try self.tys.scratch.append(self.gpa, try self.resolveTy(file, typ));
    }

    var prev_len = self.tys.scratch.items.len - arg_exprs.len;
    try self.tys.allocated.appendSlice(self.gpa, self.tys.scratch.items[prev_len..]);
    self.tys.scratch.items.len = prev_len;
    prev_len = self.tys.allocated.items.len - arg_exprs.len;

    const raw_view: *[]const Ty.Repr = @ptrCast(&self.tys.allocated.items);
    const allocate_types = raw_view.*[prev_len..];
    std.debug.assert(allocate_types.len == ast.exprs.view(args).len);
    const index = std.mem.indexOf(Ty.Repr, raw_view.*, allocate_types) orelse prev_len;
    raw_view.len = @max(prev_len, index + allocate_types.len);
    return try Tuple.init(index, allocate_types.len);
}

fn resolveTy(self: *Codegen, file: File, ty: Ast.Id) !Ty {
    const ast = self.files[file];
    return switch (ast.exprs.get(ty)) {
        .Buty => |b| Ty.init(.builtin, @intFromEnum(b.bt)),
        .UnOp => |u| try self.makePtr(try self.resolveTy(file, u.oper)),
        .Ident => |i| try self.findOrDeclare(i.pos, file, i.id),
        else => |v| std.debug.panic("unhandled type expression: {any}", .{v}),
    };
}

fn makePtr(self: *Codegen, ty: Ty) !Ty {
    if (std.mem.indexOfScalar(u32, @ptrCast(self.tys.allocated.items), @bitCast(ty))) |idx|
        return Ty.init(.pointer, idx);
    try self.tys.allocated.append(self.gpa, ty);
    return Ty.init(.pointer, self.tys.allocated.items.len - 1);
}

fn report(self: *Codegen, ph: anytype, file: u32, origin: anytype, comptime fmt: []const u8, args: anytype) !@TypeOf(ph) {
    const pos = self.files[file].posOf(origin);
    const line, const col = self.files[file].lineCol(pos.index);
    try self.errors.writer(self.gpa).print(
        "{s}:{d}:{d}: " ++ fmt,
        .{ self.files[file].path, line, col } ++ args,
    );
    return ph;
}

fn testSnippet(comptime name: []const u8) !void {
    const code = root.findReadmeSnippet(name) catch unreachable;
    try testFmt(name, name ++ ".hb", code);
    try testCodegen(name, code);
}

fn testCodegen(comptime name: []const u8, code: []const u8) !void {
    const gpa = std.testing.allocator;

    var ast = try Ast.init(name ++ ".hb", code, gpa);
    defer ast.deinit(gpa);

    const files = [_]Ast{ast};

    var codegen = try Codegen.init(gpa);
    defer codegen.deinit();

    codegen.files = &files;

    try codegen.generate();

    var output = std.ArrayList(u8).init(gpa);
    defer output.deinit();

    const not_terminated, const exec_log = if (codegen.errors.items.len != 0) b: {
        try output.appendSlice("\nERRORS\n");
        try output.appendSlice(codegen.errors.items);
        break :b .{ {}, std.ArrayList(u8).init(gpa) };
    } else b: {
        try output.writer().print("\nDISASM\n", .{});
        try isa.disasm(codegen.output.code.items, &output, false);

        var exec_log = std.ArrayList(u8).init(gpa);
        errdefer exec_log.deinit();
        try exec_log.writer().print("EXECUTION\n", .{});
        codegen.ct.vm.fuel = 10000;
        codegen.ct.vm.ip = @intFromPtr(codegen.output.code.items.ptr);
        codegen.ct.vm.log_buffer = &exec_log;
        var ctx = Vm.UnsafeCtx{};
        const ntrm = std.testing.expectEqual(.tx, codegen.ct.vm.run(&ctx));

        try output.writer().print("\nREGISTERS\n", .{});
        try output.writer().print("$1: {d}\n", .{codegen.ct.vm.regs[1]});

        break :b .{ ntrm, exec_log };
    };
    defer exec_log.deinit();

    const old, const new = .{ "tests/" ++ name ++ ".temp.old.txt", name ++ ".temp.new.txt" };

    const update = std.process.getEnvVarOwned(gpa, "PT_UPDATE") catch "";
    defer gpa.free(update);
    if (update.len > 1) {
        try std.fs.cwd().writeFile(.{
            .sub_path = old,
            .data = std.mem.trim(u8, output.items, "\n"),
        });

        not_terminated catch {
            std.debug.print("\n{s}\n", .{exec_log.items});
        };
    } else {
        try std.fs.cwd().writeFile(.{
            .sub_path = new,
            .data = std.mem.trim(u8, output.items, "\n"),
        });
        const err = runDiff(gpa, old, new);
        try std.fs.cwd().deleteFile(new);

        not_terminated catch {
            std.debug.print("\n{s}\n", .{exec_log.items});
            std.debug.print("\n{s}\n", .{output.items});
        };

        err catch {
            std.debug.print("\n{s}\n", .{exec_log.items});
            std.debug.print("\n{s}\n", .{output.items});
        };

        try err;
    }

    try not_terminated;
}

pub fn testFmt(comptime name: []const u8, path: []const u8, code: []const u8) !void {
    const gpa = std.testing.allocator;

    var ast = try Ast.init(path, code, gpa);
    defer ast.deinit(gpa);

    const ast_overhead = @as(f64, @floatFromInt(ast.exprs.store.items.len)) /
        @as(f64, @floatFromInt(ast.source.len));
    if (ast_overhead > 3.0) {
        std.debug.print(
            "\n{s} is too large ({d} bytes, {any} ratio)\n",
            .{ name, ast.source.len, ast_overhead },
        );
    }

    var fmtd = std.ArrayList(u8).init(gpa);
    defer fmtd.deinit();

    try ast.fmt(&fmtd);

    const old, const new = .{ name ++ ".temp.old.txt", name ++ ".temp.new.txt" };

    try std.fs.cwd().writeFile(.{ .sub_path = new, .data = std.mem.trim(u8, fmtd.items, "\n") });
    try std.fs.cwd().writeFile(.{ .sub_path = old, .data = std.mem.trim(u8, code, "\n") });
    const err = runDiff(gpa, old, new);
    try std.fs.cwd().deleteFile(old);
    try std.fs.cwd().deleteFile(new);

    try err;
}

pub fn runDiff(gpa: std.mem.Allocator, old: []const u8, new: []const u8) !void {
    var child = std.process.Child.init(&.{ "diff", "--unified", "--color", old, new }, gpa);
    child.stdout_behavior = .Pipe;
    child.stderr_behavior = .Pipe;

    try child.spawn();

    const stdout = try child.stderr.?.readToEndAlloc(gpa, 1024 * 10);
    defer gpa.free(stdout);
    const stderr = try child.stdout.?.readToEndAlloc(gpa, 1024 * 10);
    defer gpa.free(stderr);

    const exit = (try child.wait()).Exited;
    if (exit != 0) {
        const new_data = try std.fs.cwd().readFileAlloc(gpa, new, 1024 * 1024);
        defer gpa.free(new_data);
        const old_data = try std.fs.cwd().readFileAlloc(gpa, old, 1024 * 1024);
        defer gpa.free(old_data);
        const new_line_count: isize = @intCast(std.mem.count(u8, new_data, "\n"));
        const old_line_count: isize = @intCast(std.mem.count(u8, old_data, "\n"));
        std.debug.print("line count change: {d}\n", .{new_line_count - old_line_count});
        if (stdout.len > 0) std.debug.print("stdout:\n{s}", .{stdout});
        if (stderr.len > 0) std.debug.print("stderr:\n{s}", .{stderr});
    }
    try std.testing.expectEqual(0, exit);
}

test "main-fn" {
    try testSnippet("main-fn");
}

test "arithmetic" {
    try testSnippet("arithmetic");
}

test "functions" {
    try testSnippet("functions");
}

test "comments" {
    try testSnippet("comments");
}

test "if-statements" {
    try testSnippet("if-statements");
}

test "variables" {
    try testSnippet("variables");
}

test "loops" {
    try testSnippet("loops");
}

test "pointers" {
    try testSnippet("pointers");
}

test "register-ownership" {
    try testSnippet("register-ownership");
}

test "structs" {
    try testSnippet("structs");
}
