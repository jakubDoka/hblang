const std = @import("std");
const hb = @import("hb");
const utils = hb.utils;
const Lexer = hb.frontend.Lexer;
const BBuilder = hb.backend.Builder;
const BNode = BBuilder.BuildNode;
const graph = hb.backend.graph;
const Types = hb.frontend.Types;
const File = hb.frontend.DeclIndex.File;
const Loader = hb.frontend.DeclIndex.Loader;
const Abi = hb.frontend.Abi;
const Machine = hb.backend.Machine;
const Vm = hb.hbvm.Vm;

const print = (std.debug).print;
const Codegen = @This();

types: *Types,
loops: ?*Loop = null,
file: File.Id,
scope: Types.AnyScopeRef,
cmptime_values: std.ArrayList(Types.ComptimeValue) = .empty,
name: Types.Scope.NamePos = .empty,
vars: std.MultiArrayList(VEntry) = .empty,
defers: std.ArrayList(u32) = .empty,
frozen_vars: usize = 0,
var_pins: BBuilder.Pins,
ret_ty: Types.Id,
ret_ref: ?*BNode = null,
bl: BBuilder,
target: Types.Target = .runtime,

pub const undeclared_prefix: u8 = 0;

pub const ComptimeEca = enum {
    alloc_global,
    type_info,
    Type,
};

pub const Loop = struct {
    prev: ?*Loop,
    defer_frame: usize,
    name: []const u8,
    state: union(enum) {
        cmptime: struct {
            kind: enum { broken, continued, falltrough } = .falltrough,
            pos: u32 = std.math.maxInt(u32),
        },
        runtime: struct {
            bl: BBuilder.Loop,
        },
    },
};

pub const Ctx = struct {
    ty: ?Types.Id = null,
    in_if_or_while: bool = false,
    loc: ?*BNode = null,
};

pub const VEntry = struct {
    prefix: u8,
    variable: Variable,
};

pub const Variable = struct {
    ty: Types.Id,
    meta: packed struct {
        kind: enum(u2) { value, ptr, empty, cmptime },
        pos: u30,
    },
    value: u32 = std.math.maxInt(u32),
};

pub const Value = struct {
    ty: Types.Id,
    tag: std.meta.Tag(Node),
    value_: extern union {
        idx: usize,
        node: *BNode,
    },

    pub const voidv = unit(.void);
    pub const never = unit(.never);

    pub fn load(self: Value, pos: u32, gen: *Codegen) *BNode {
        return switch (self.normalized(pos, gen)) {
            .empty => if (self.ty == .never)
                gen.bl.addUninit(gen.sloc(pos), .top)
            else {
                gen.report(pos, "BUG", .{}) catch {};
                unreachable;
            },
            .value => |v| v,
            .ptr => |p| {
                if (self.ty == .never) {
                    return gen.bl.addUninit(gen.sloc(pos), .top);
                }

                const ty = gen.types.abi
                    .categorizeAssumeReg(self.ty, gen.types);
                const ld = gen.emitArbitraryLoad(pos, p, ty, self.ty.size(gen.types));
                return gen.bl.peep(ld);
            },
        };
    }

    pub fn peep(self: *Value, codegen: *Codegen) void {
        return switch (self.node()) {
            .variable, .empty => {},
            .value => self.value_.node = codegen.bl.peep(self.value_.node),
            .ptr => self.value_.node = codegen.bl.peep(self.value_.node),
        };
    }

    pub fn node(self: Value) Node {
        return switch (self.tag) {
            .empty => .empty,
            .variable => .{ .variable = self.value_.idx },
            .value => .{ .value = self.value_.node },
            .ptr => .{ .ptr = self.value_.node },
        };
    }

    pub fn asPtr(self: Value, pos: u32, gen: *Codegen) !*BNode {
        const no_address_msg = "the value is not" ++
            " referncable, it has no address, use `#<expr>` to force a spill";

        return switch (self.normalized(pos, gen)) {
            .empty => gen.bl.addUninit(gen.sloc(pos), .i64),
            .value => return gen.report(pos, no_address_msg, .{}),
            .ptr => |p| p,
        };
    }

    pub fn normalize(self: *Value, gen: *Codegen) void {
        if (self.tag != .empty and self.ty.size(gen.types) == 0) {
            // TODO: release the node
            self.tag = .empty;
            self.value_ = undefined;
        }
    }

    pub fn normalized(self: Value, pos: u32, gen: *Codegen) NormalizedNode {
        return switch (self.node()) {
            .empty => .empty,
            .variable => |i| {
                const slot: *Variable = &gen.vars.items(.variable)[i];

                if (slot.value == std.math.maxInt(u32)) {
                    gen.report(
                        pos,
                        "use of uninitialized variable",
                        .{},
                    ) catch return gen.emitUninit(pos, self.ty);
                }

                const cata = self.ty.category(gen.types);

                return switch (slot.meta.kind) {
                    .empty => .empty,
                    .cmptime => {
                        const val = gen.cmptime_values.items[slot.value];
                        return gen.ctValueToNorm(pos, slot.ty, val);
                    },
                    .value => .{ .value = if (gen.frozen_vars > i)
                        gen.bl.addStub(gen.sloc(pos), cata.Scalar)
                    else
                        gen.bl.getScopeValue(slot.value) },
                    .ptr => .{ .ptr = if (gen.frozen_vars > i)
                        gen.bl.addStub(gen.sloc(pos), .i64)
                    else
                        gen.var_pins.getValue(slot.value) },
                };
            },
            .value => |v| .{ .value = v },
            .ptr => |p| .{ .ptr = p },
        };
    }

    pub fn ptr(ty: Types.Id, nod: *BNode) Value {
        return .{ .ty = ty, .tag = .ptr, .value_ = .{ .node = nod } };
    }

    pub fn value(ty: Types.Id, val: *BNode) Value {
        return .{ .ty = ty, .tag = .value, .value_ = .{ .node = val } };
    }

    pub fn variable(ty: Types.Id, idx: usize) Value {
        return .{ .ty = ty, .tag = .variable, .value_ = .{ .idx = idx } };
    }

    pub fn unit(ty: Types.Id) Value {
        return .{ .ty = ty, .tag = .empty, .value_ = undefined };
    }
};

// Long Lived
pub const LLValue = struct {
    value: Value,
    pos: u32,
    checksum: if (graph.is_debug) ?*BNode else void,

    pub fn init(pos: u32, value: Value) LLValue {
        switch (value.node()) {
            .empty, .variable => {},
            .value, .ptr => |p| _ = p.lock(),
        }

        return .{
            .value = value,
            .pos = pos,
            .checksum = if (graph.is_debug) switch (value.node()) {
                .empty, .variable => null,
                .value, .ptr => |p| p,
            },
        };
    }

    pub fn normalize(self: *LLValue, gen: *Codegen) void {
        self.tmpUnlock();
        self.value.normalize(gen);
        self.tmpLock();
    }

    pub fn set(self: *LLValue, to: Value) void {
        self.tmpUnlock();
        self.value = to;
        self.tmpLock();
    }

    pub fn peep(self: *LLValue, gen: *Codegen) void {
        self.tmpUnlock();
        self.value.peep(gen);
        self.tmpLock();
    }

    pub fn dupe(self: *LLValue) LLValue {
        self.tmpLock();
        return self.*;
    }

    pub fn tmpUnlock(self: *LLValue) void {
        switch (self.value.node()) {
            .empty, .variable => {},
            .value, .ptr => |p| {
                if (graph.is_debug) std.debug.assert(p == self.checksum);
                BNode.Lock.unlock(.{ .node = p });
            },
        }
    }

    pub fn tmpLock(self: *LLValue) void {
        switch (self.value.node()) {
            .empty, .variable => {},
            .value, .ptr => |p| {
                if (graph.is_debug) self.checksum = p;
                _ = p.lock();
            },
        }
    }

    pub fn deinitKeep(self: *LLValue) void {
        self.tmpUnlock();
        self.* = undefined;
    }

    pub fn deinit(self: *LLValue, gen: *Codegen) void {
        switch (self.value.node()) {
            .empty, .variable => {},
            .value, .ptr => |p| {
                if (graph.is_debug) std.debug.assert(p == self.checksum);
                BNode.Lock.unlock(.{ .node = p });
                if (p.outputs().len == 0) {
                    gen.bl.func.kill(p);
                }
            },
        }
        self.* = undefined;
    }

    pub fn load(self: LLValue, cg: *Codegen) *BNode {
        return self.value.load(self.pos, cg);
    }
};

pub const NormalizedNode = union(enum) {
    empty,
    value: *BNode,
    ptr: *BNode,
};

pub const Node = union(enum) {
    empty,
    variable: usize,
    value: *BNode,
    ptr: *BNode,
};

pub const Error = error{Report};
pub const UnreachableErr = error{Unreachable} || Error;

pub const UnitError = error{SyntaxError} || UnreachableErr;
pub const SuffixError = error{SyntaxError} || UnreachableErr;

pub fn init(
    slot: *Codegen,
    types: *Types,
    scope: Types.AnyScopeRef,
    ret_ty: Types.Id,
    gpa: std.mem.Allocator,
) void {
    slot.bl = .init(gpa);
    slot.* = .{
        .bl = slot.bl,
        .types = types,
        .scope = scope,
        .file = scope.data().scope(types).file,
        .var_pins = slot.bl.addPins(),
        .ret_ty = ret_ty,
    };
}

pub fn emitDefers(self: *Codegen, base: usize) void {
    var iter = std.mem.reverseIterator(self.defers.items[base..]);
    while (iter.next()) |e| {
        var lex = Lexer.init(self.file.get(self.types).source, e);
        _ = self.typedExpr(.void, .{}, &lex) catch {};
    }
}

pub fn emitUninitValue(self: *Codegen, pos: u32, ty: Types.Id) Value {
    return switch (self.emitUninit(pos, ty)) {
        .value => .value(ty, self.bl.addUninit(self.sloc(pos), .i64)),
        .ptr => .ptr(ty, self.bl.addUninit(self.sloc(pos), .i64)),
        .empty => .unit(ty),
    };
}

pub fn emitUninit(self: *Codegen, pos: u32, ty: Types.Id) NormalizedNode {
    const slc = self.sloc(pos);

    return switch (ty.category(self.types)) {
        .Imaginary, .Impossible => .empty,
        .Scalar => |s| .{ .value = self.bl.addUninit(slc, s) },
        .Stack => .{ .ptr = self.bl.addUninit(slc, .i64) },
    };
}

pub fn prepareForFunc(self: *Codegen, fnid: Types.FuncId) void {
    self.bl.func.reset();
    self.scope = .nany(fnid);
    self.file = self.scope.data().scope(self.types).file;
    self.var_pins = self.bl.addPins();
    self.ret_ty = fnid.get(self.types).ret;
}

pub fn deinit(self: *Codegen) void {
    self.bl.deinit();
    self.* = undefined;
}

pub fn sloc(self: *Codegen, pos: u32) graph.Sloc {
    return .{ .namespace = self.file.index(), .index = pos };
}

pub fn lookupIdent(self: *Codegen, scope: Types.AnyScopeRef, name: []const u8) ?Value {
    return self.lookupIdentLow(scope, name, false);
}

pub fn lookupIdentDotted(self: *Codegen, scope: Types.AnyScopeRef, name: []const u8) ?Value {
    return self.lookupIdentLow(scope, name, true);
}

pub fn lookupIdentLow(
    self: *Codegen,
    scope: Types.AnyScopeRef,
    name: []const u8,
    dotted: bool,
) ?Value {
    const scope_meta = scope.data().scope(self.types);
    const file = scope_meta.file.get(self.types);

    if (hb.frontend.DeclIndex.filePrefixLookup(
        self.vars.items(.prefix),
        Variable,
        self.vars.items(.variable),
        file.source,
        name,
    )) |variable| {
        return .variable(variable.ty, utils.indexOfPtr(
            Variable,
            self.vars.items(.variable),
            variable,
        ));
    }

    var dt = dotted;
    var scope_cursor = scope.data();
    while (true) {
        if (scope_cursor == .Enum and dt) {
            const en = scope_cursor.Enum.get(self.types);
            if (en.lookupField(self.types, name)) |field| {
                return .value(.nany(scope_cursor.Enum), self.bl.addIntImm(
                    self.sloc(en.decls.fields.items(.offset)[field]),
                    .memUnitForAlign(en.getLayout(self.types).spec.alignmentBytes(), false),
                    en.getLayout(self.types).fields[field],
                ));
            }
        }

        dt = false;

        if (scope_cursor.downcast(Types.UnorderedScope)) |us| {
            if (us.decls(self.types).lookup(file.source, name)) |vl| {
                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();

                const pos, const path = vl.collectPath(tmp.arena, file.source);

                var global_mem = Types.Global{
                    .scope = .{
                        .parent = scope_cursor.upcast(Types.Parent).pack(),
                        .file = scope_meta.file,
                        .name_pos = @enumFromInt(vl.root),
                    },
                    .ty = .never,
                    .readonly = file.isComptime(vl.offset),
                };

                var global = &global_mem;

                const slot = self.types.global_index.intern(self.types, global);

                if (!slot.found_existing) {
                    slot.key_ptr.* = self.types.globals
                        .push(&self.types.arena, global_mem);
                }

                const global_id = slot.key_ptr.*;
                global = self.types.globals.at(global_id);

                if (!slot.found_existing) {
                    var lex = Lexer.init(file.source, pos);

                    var ty: ?Types.Id = null;
                    if (lex.eatMatch(.@":")) {
                        ty = self.typ(&lex) catch return null;
                        _ = lex.slit(.@"=");
                    } else {
                        _ = lex.slit(.@":=");
                    }

                    var tmpc = self.types.tmpCheckpoint();
                    defer tmpc.deinit();

                    var global_gen: Codegen = undefined;
                    global_gen.init(
                        self.types,
                        scope_cursor.pack(),
                        .never,
                        tmpc.allocator(),
                    );
                    global_gen.name = @enumFromInt(vl.offset);
                    global_gen.target = .cmptime;

                    global_gen.evalGlobal(&lex, ty, global_id);
                }

                var glb = Value.ptr(global.ty, self.bl.addGlobalAddr(
                    self.sloc(vl.offset),
                    @intFromEnum(global_id),
                ));

                for (path) |p| {
                    const scope_ty = self.peval(vl.offset, glb, Types.Id) catch return null;
                    const scpe = scope_ty.data().downcast(Types.UnorderedScope) orelse {
                        self.types.report(
                            scope.data().scope(self.types).file,
                            vl.offset,
                            "{} is not an unordered scope (struct, enum," ++
                                " union), so it can't be destructured",
                            .{scope_ty},
                        );

                        return null;
                    };

                    glb = self.lookupIdentDotted(
                        scpe.upcast(Types.AnyScope).pack(),
                        p,
                    ) orelse return null;
                }

                return glb;
            }
        }

        if (scope_cursor.captures(self.types).lookup(file.source, name)) |r| {
            const pos, const ty, const value = r;
            if (value) |vl| {
                return self.ctValueToValue(pos, ty, vl);
            } else {
                return switch (ty.category(self.types)) {
                    .Impossible => .never,
                    .Imaginary => .unit(ty),
                    .Scalar => .value(ty, self.bl.addStub(self.sloc(pos), .i64)),
                    .Stack => .ptr(ty, self.bl.addStub(self.sloc(pos), .i64)),
                };
            }
        }

        scope_cursor = scope_cursor.scope(self.types)
            .parent.data().downcast(Types.AnyScope) orelse break;
    }

    return null;
}

pub const comptime_gen_mode = Machine.OptOptions{ .mode = .debug };
pub const comptime_only_fn = Machine.max_func - 1;

pub fn evalGlobal(self: *Codegen, lex: *Lexer, ty: ?Types.Id, global_id: Types.GlobalId) void {
    const global = self.types.globals.at(global_id);

    if (lex.eatMatch(.idk)) {
        global.uninit = true;

        if (global.readonly) {
            self.report(lex.cursor, "readonly uninitialized global is nonsense", .{}) catch {};
        }

        global.ty = ty orelse .never;
        if (ty == null) self.report(lex.cursor, "cant infer the type of the uninit" ++
            " variable, use <name>: <type> = idk", .{}) catch {};

        self.types.ct_backend.mach.emitData(.{
            .id = @intFromEnum(global_id),
            .value = .{ .uninit = global.ty.size(self.types) },
            .readonly = false,
            .thread_local = true,
            .uuid = @splat(0),
        });

        return;
    }

    if (lex.eatMatch(.@"@thread_local_storage")) {
        _ = self.expect(lex, .@"(", "to keep the directive syntax consistent") catch {};
        _ = self.expect(lex, .@")", "to keep the directive syntax consistent") catch {};

        global.ty = ty orelse .never;
        if (ty == null) self.report(lex.cursor, "cant infer the type of the thread" ++
            " local, use <name>: <type> = @thread_local_storage()", .{}) catch {};

        if (global.readonly) {
            self.report(lex.cursor, "readonly thread local is nonsense", .{}) catch {};
        }

        self.types.ct_backend.mach.emitData(.{
            .id = @intFromEnum(global_id),
            .value = .{ .uninit = global.ty.size(self.types) },
            .readonly = false,
            .thread_local = true,
            .uuid = @splat(0),
        });

        return;
    }

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const prev_errored = self.types.errored;
    const until = self.types.func_queue.getPtr(.cmptime).items.len;
    const relocs_until = self.types.ct_backend.mach.out.relocs.items.len;
    var sigbl, const token = self.bl.begin(.systemv, tmp.arena);
    const pos = lex.cursor;

    const ret_addr = sigbl.addParam(&self.bl, self.sloc(lex.cursor), .{ .Reg = .i64 }, 0);

    sigbl.end(&self.bl, &.{});

    const value = self.expr(
        .{ .loc = ret_addr, .ty = ty },
        lex,
    ) catch return;

    if (self.types.errored > prev_errored) {
        return;
    }

    self.emitGenericStore(pos, ret_addr, value);

    self.bl.end(token);

    // TODO: use free list for these
    const reserved = self.types.funcs.push(&self.types.arena, .{
        .scope = global.scope,
        .captures = undefined,
        .params = undefined,
        .args = undefined,
        .ret = undefined,
        .pos = undefined,
    });

    self.emitToBackend(reserved, &self.types.ct_backend.mach, comptime_gen_mode);

    self.types.ct_backend.mach.emitData(.{
        .id = @intFromEnum(global_id),
        .value = .{ .uninit = value.ty.size(self.types) },
        .readonly = global.readonly,
        .thread_local = false,
        .uuid = @splat(0),
    });

    global.ty = value.ty;

    if (self.emitCtFuncs(until, relocs_until)) return;

    const global_sym = self.types.ct_backend.mach.out
        .getGlobalSym(@intFromEnum(global_id)).?;

    self.types.vm.regs.set(.arg(0), global_sym.offset);
    self.runVm(self.sloc(pos), reserved);
}

pub fn runVm(self: *Codegen, slc: graph.Sloc, func: Types.FuncId) void {
    const log = @import("options").log_ct_exec;
    if (log) {
        self.types.reportSloc(slc, "executing this", .{});
        self.types.errored -= 1;
    }
    var stderr = if (log) std.fs.File.stderr().writer(&.{});
    var vm_ctx = Vm.SafeContext{
        .writer = if (log) &stderr.interface else null,
        .color_cfg = .escape_codes,
        .memory = self.types.ct_backend.mach.out.code.allocatedSlice(),
        .code_start = 0,
        .code_end = 0,
    };

    const regs = &self.types.vm.regs;

    if (@intFromEnum(func) == comptime_only_fn) {
        self.types.vm.ip = Types.stack_size - 2;
        self.types.vm.fuel = 2;
    } else {
        const func_sym = self.types.ct_backend.mach.out
            .getFuncSym(@intFromEnum(func)).?;

        self.types.vm.ip = func_sym.offset;
        self.types.vm.fuel = 1024;
        // return to hardcoded tx
        regs.set(.ret_addr, Types.stack_size - 1);
    }

    while (true) switch (self.types.vm.run(&vm_ctx) catch |err| {
        self.reportSloc(slc, "the comptime execution failed: {}", .{err}) catch
            return;
    }) {
        .tx => break,
        .eca => {
            switch (@as(ComptimeEca, @enumFromInt(regs.get(.arg(0))))) {
                .Type => {
                    const tyun = self.types.builtins.type_union;
                    const size = Types.Id.nany(tyun).size(self.types);
                    const slot = regs.get(.stack_addr);
                    const tag_layout = tyun.get(self.types).getLayout(self.types).tagLayout().?;

                    var mem = vm_ctx.memory[slot..][0..@intCast(size)];

                    const value: Types.Id = d: switch (@as(
                        std.meta.Tag(Types.Data),
                        @enumFromInt(mem[tag_layout.offset..][0]),
                    )) {
                        .Builtin => .never,
                        .Pointer => self.types.pointerTo(@enumFromInt(@as(u32, @bitCast(mem[0..4].*)))),
                        .Slice => self.types.sliceOf(@enumFromInt(@as(u32, @bitCast(mem[0..4].*)))),
                        .Option => self.types.optionOf(@enumFromInt(@as(u32, @bitCast(mem[0..4].*)))),
                        .Array => self.types.arrayOf(
                            @enumFromInt(@as(u32, @bitCast(mem[0..4].*))),
                            @intCast(@as(u64, @bitCast(mem[8..][0..8].*))),
                        ),
                        .FuncTy => {
                            const ptr: u64 = @bitCast(mem[0..][Types.Slice.ptr_offset..][0..8].*);
                            const len: u64 = @bitCast(mem[0..][Types.Slice.len_offset..][0..8].*);
                            // TODO: make the memory in the vm aligned
                            const args: []align(1) Types.Id = @ptrCast(vm_ctx.memory[ptr..][0 .. len * @sizeOf(Types.Id)]);
                            const ret: Types.Id = @enumFromInt(@as(u32, @bitCast(mem[16..][0..4].*)));

                            var tmp = utils.Arena.scrath(null);
                            defer tmp.deinit();

                            const aligned_args = tmp.arena.alloc(Types.Id, args.len);
                            @memcpy(aligned_args, args);

                            break :d self.types.funcTyOf(aligned_args, ret);
                        },
                        else => |e| utils.panic("{}", .{e}),
                    };

                    regs.set(.ret(0), value.raw());
                },
                .type_info => {
                    const slot = regs.get(.arg(1));
                    const ty: Types.Id = @enumFromInt(regs.get(.arg(2)));
                    const tyun = self.types.builtins.type_union;
                    const tag_layout = tyun.get(self.types).getLayout(self.types).tagLayout().?;
                    const size = Types.Id.nany(tyun).size(self.types);

                    var mem = vm_ctx.memory[slot..][0..@intCast(size)];
                    mem[tag_layout.offset..][0] = @intFromEnum(ty.data());

                    switch (ty.data()) {
                        .Builtin => {},
                        .Option => |o| {
                            mem[0..4].* = std.mem.toBytes(o.get(self.types).inner);
                        },
                        .Pointer => |p| {
                            mem[0..4].* = std.mem.toBytes(p.get(self.types).*);
                        },
                        .Slice => |s| {
                            mem[0..4].* = std.mem.toBytes(s.get(self.types).*);
                        },
                        .Array => |a| {
                            mem[0..16].* = std.mem.toBytes(a.get(self.types).*);
                        },
                        .FuncTy => |f| {
                            const arg_slc = f.get(self.types).args;

                            _, const memr = self.addSliceGlobal(.type, arg_slc.len, mem[0..16]);

                            @memcpy(memr, @as([]const u8, @ptrCast(arg_slc)));

                            mem[16..][0..4].* = std.mem.toBytes(f.get(self.types).ret);
                        },
                        .Struct => |s| {
                            const layout = s.get(self.types).getLayout(self.types);
                            mem[0..][0..8].* = std.mem.toBytes(@as(u64, layout.spec.alignmentBytes()));

                            const struct_field = self.types.builtins.struct_field;
                            _, const fields_mem = self.addSliceGlobal(.nany(struct_field), layout.fields.len, mem[8..][0..16]);

                            for (0..layout.fields.len) |i| {
                                const base = i * Types.Id.nany(struct_field).size(self.types);
                                const field = layout.fields[i];

                                const field_off: u32 = s.get(self.types).decls.fields.items(.offset)[i];
                                const field_name = Lexer.peekStr(s.get(self.types)
                                    .scope.file.get(self.types).source, field_off);

                                _, const name_mem = self.addSliceGlobal(.u8, field_name.len, fields_mem[base..][0..16]);
                                @memcpy(name_mem, field_name);

                                fields_mem[base..][16..][0..4].* = std.mem.toBytes(field.ty);
                                fields_mem[base..][24..][0..8].* = std.mem.toBytes(@as(u64, field.offset));
                                fields_mem[base..][32..][0..8].* = std.mem.toBytes(@as(u64, 0));
                            }

                            self.addDecls(s, mem[24..][0..16]);
                        },
                        .Enum => |e| {
                            const layout = e.get(self.types).getLayout(self.types);

                            mem[0..][0..4].* = std.mem.toBytes(layout.backingInteger());

                            const enum_field = self.types.builtins.enum_field;
                            _, const fields_mem = self.addSliceGlobal(.nany(enum_field), layout.fields.len, mem[8..][0..16]);

                            for (0..layout.fields.len) |i| {
                                const base = i * Types.Id.nany(enum_field).size(self.types);
                                const field = layout.fields[i];

                                const field_off: u32 = e.get(self.types).decls.fields.items(.offset)[i];
                                const field_name = Lexer.peekStr(e.get(self.types)
                                    .scope.file.get(self.types).source, field_off);

                                _, const name_mem = self.addSliceGlobal(.u8, field_name.len, fields_mem[base..][0..16]);
                                @memcpy(name_mem, field_name);

                                fields_mem[base..][16..][0..8].* = std.mem.toBytes(field);
                            }

                            self.addDecls(e, mem[24..][0..16]);
                        },
                        .Union => |u| {
                            const layout = u.get(self.types).getLayout(self.types);
                            mem[0..][0..8].* = std.mem.toBytes(@as(u64, 0));
                            if (layout.tag) |t| {
                                mem[0..][0..4].* = std.mem.toBytes(Types.Id.nany(t));
                                mem[4..][0] = 1;
                            }

                            const struct_field = self.types.builtins.struct_field;
                            _, const fields_mem = self.addSliceGlobal(.nany(struct_field), layout.fields.len, mem[8..][0..16]);

                            for (0..layout.fields.len) |i| {
                                const base = i * Types.Id.nany(struct_field).size(self.types);
                                const field = layout.fields[i];

                                const field_off: u32 = u.get(self.types).decls.fields.items(.offset)[i];
                                const field_name = Lexer.peekStr(u.get(self.types)
                                    .scope.file.get(self.types).source, field_off);

                                _, const name_mem = self.addSliceGlobal(.u8, field_name.len, fields_mem[base..][0..16]);
                                @memcpy(name_mem, field_name);

                                fields_mem[base..][16..][0..4].* = std.mem.toBytes(field);
                            }

                            self.addDecls(u, mem[24..][0..16]);
                        },
                    }
                },
                .alloc_global => {
                    const len = regs.get(.arg(1 + Types.Slice.len_offset / 8));
                    const ptr = regs.get(.arg(1 + Types.Slice.ptr_offset / 8));
                    const elem: Types.Id = @enumFromInt(regs.get(.arg(3)));

                    const spill, const mem = self.addSliceGlobal(elem, len, @ptrCast(regs.values[1..3]));
                    spill.get(self.types).readonly = false; // TODO: make this configurable

                    @memcpy(mem, vm_ctx.memory[@intCast(ptr)..][0..mem.len]);
                },
            }
        },
        else => unreachable, // TODO
    };
}

pub fn addDecls(self: *Codegen, e: anytype, slot: *[16]u8) void {
    const edecls = e.get(self.types).decls;
    _, const decl_mem = self.addSliceGlobal(self.types.sliceOf(.u8), edecls.entries.len, slot);

    for (0..edecls.entries.len) |i| {
        const base = i * 16;
        const decl_off = edecls.entries.get(i).offset.offset;
        const decl_name = Lexer.peekStr(e.get(self.types)
            .scope.file.get(self.types).source, decl_off);

        _, const name_mem = self.addSliceGlobal(.u8, decl_name.len, decl_mem[base..][0..16]);
        @memcpy(name_mem, decl_name);
    }
}

pub fn addSliceGlobal(self: *Codegen, elem: Types.Id, len: usize, dest: *[16]u8) struct { Types.GlobalId, []u8 } {
    const bty = self.types.arrayOf(elem, @intCast(len));
    const storage = self.createComptimeSpill(bty);
    const sym = storage.get(self.types).data.sym(self.types);

    dest[Types.Slice.ptr_offset..][0..8].* = std.mem.toBytes(@as(u64, sym.offset));
    dest[Types.Slice.len_offset..][0..8].* = std.mem.toBytes(@as(u64, len));

    return .{ storage, storage.get(self.types).data.get(self.types) };
}

pub fn emitCtFuncs(self: *Codegen, until: usize, relocs_until: usize) bool {
    var failed = false;

    var tmp = self.types.tmpCheckpoint();
    defer tmp.deinit();

    var gen: Codegen = undefined;
    gen.init(self.types, self.scope, .never, tmp.allocator());
    gen.target = .cmptime;

    while (self.types.nextFunc(.cmptime, until)) |fnid| {
        gen.prepareForFunc(fnid);
        gen.emitFunc(fnid) catch {
            failed = true;
            continue;
        };
        gen.emitToBackend(fnid, &self.types.ct_backend.mach, comptime_gen_mode);
    }

    if (!failed) {
        hb.hbvm.object.jitLink(self.types.ct_backend.mach.out, relocs_until);
    }

    return failed;
}

pub fn emitGenericStore(self: *Codegen, pos: u32, dest: *BNode, value: Value) void {
    switch (value.normalized(pos, self)) {
        .empty => {},
        .value => |v| {
            self.bl.addStore(self.sloc(pos), dest, v.data_type, v);
        },
        .ptr => |p| {
            self.bl.addFixedMemCpy(
                self.sloc(pos),
                dest,
                p,
                value.ty.size(self.types),
            );
        },
    }
}

pub fn emitFunc(self: *Codegen, fnid: Types.FuncId) error{Failed}!void {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const stypes = self.types;

    const prev_erred = stypes.errored;

    const func = fnid.get(stypes);

    self.vars = .empty;
    self.var_pins = self.bl.addPins();
    self.ret_ty = func.ret;

    var buf = Abi.Buf{};
    const ret_cata = self.types.abi.categorize(func.ret, self.types, &buf);

    var sigbl, const token = self.bl.begin(stypes.abi.cc, tmp.arena);

    const file = func.scope.file.get(stypes);
    self.file = func.scope.file;

    if (self.types.abi.isRetByRef(ret_cata)) {
        self.ret_ref = sigbl.addParam(
            &self.bl,
            self.sloc(func.pos),
            .{ .Reg = .i64 },
            func.ret.raw(),
        );
    }

    var lex = Lexer.init(file.source, func.pos);

    const arg_iter = lex.list(.@",", .@")");
    var param_idx: usize = 0;
    var arg_idx: usize = 0;
    while (arg_iter.next()) : (arg_idx += 1) {
        const name, const cmptime = lex.eatIdent() orelse unreachable;
        _ = lex.slit(.@":");
        lex.skipExpr() catch unreachable;

        const ty = func.args[arg_idx];

        if (cmptime) {
            const index = self.defineVariable(name);

            const slot: *Variable = &self.vars.items(.variable)[index];
            const is_cmptime = slot.meta.kind == .cmptime;

            std.debug.assert(slot.value == std.math.maxInt(u32));
            std.debug.assert(is_cmptime);

            slot.ty = ty;

            self.cmptime_values.append(
                self.bl.arena(),
                func.params[param_idx].value,
            ) catch unreachable;
            slot.value = @intCast(self.cmptime_values.items.len - 1);

            param_idx += 1;
        } else {
            var bf = Abi.Buf{};
            const splits = self.types.abi.categorize(ty, self.types, &bf).?;

            const slc = self.sloc(name.pos);

            const value: Value = if (splits.len == 0)
                .unit(ty)
            else if (splits.len == 2) b: {
                const stack_slot = self.bl.addLocal(
                    self.sloc(name.pos),
                    ty.size(self.types),
                    @intFromEnum(ty),
                );

                self.bl.addStore(
                    slc,
                    stack_slot,
                    splits[0].Reg,
                    sigbl.addParam(&self.bl, slc, splits[0], ty.raw()),
                );
                // TDOD: this bugs out if we overflow regs in the middle, fix this
                self.emitArbitraryStore(
                    name.pos,
                    self.bl.addFieldOffset(slc, stack_slot, splits[0].Reg.size()),
                    sigbl.addParam(&self.bl, slc, splits[0], ty.raw()),
                    ty.size(self.types) - splits[0].Reg.size(),
                );

                break :b .ptr(ty, stack_slot);
            } else b: {
                const param = sigbl.addParam(&self.bl, slc, splits[0], ty.raw());
                break :b if (param.kind == .Arg) .value(ty, param) else .ptr(ty, param);
            };

            _ = self.pushVariable(name, value) catch unreachable;
        }
    }

    sigbl.end(&self.bl, ret_cata);

    if (func.linkage == .imported) return;

    _ = lex.slit(.@":");
    _ = self.typ(&lex) catch .never;

    const ret_pos = lex.cursor;

    if (!self.branchExpr(&lex)) {
        const rets = ret_cata orelse {
            self.report(ret_pos, "function should never return since" ++
                " `{}` is uninhabited", .{func.ret}) catch return error.Failed;
        };

        if (rets.len != 0) {
            self.report(ret_pos, "the return value is not empty, but" ++
                " function implicitly returns", .{}) catch return error.Failed;
        }
    }

    if (prev_erred < stypes.errored) return error.Failed;

    self.popScope(0);
    self.bl.end(token);
}

pub fn emitToBackend(
    self: *Codegen,
    fnid: Types.FuncId,
    backend: *Machine,
    opts: Machine.OptOptions,
) void {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const prev_err_count = self.types.errored;

    if (fnid.get(self.types).linkage != .imported) {
        for (self.bl.func.getSyms().outputs()) |sym| {
            switch (sym.get().extra2()) {
                .GlobalAddr => |extra| {
                    if (self.target == .cmptime) continue;

                    var queue = std.ArrayList(Types.GlobalId).empty;
                    queue.append(tmp.arena.allocator(), @enumFromInt(extra.id)) catch unreachable;

                    while (queue.pop()) |global| {
                        if (global.get(self.types).runtime_emmited) continue;

                        var relocs = std.ArrayList(Machine.DataOptions.Reloc).empty;
                        self.types.collectGlobalRelocs(global, &relocs, tmp.arena, false);

                        for (relocs.items) |reloc| {
                            if (reloc.is_func) {
                                const func: Types.FuncId = @enumFromInt(reloc.target);
                                func.get(self.types).queue(.runtime, self.types);
                            } else {
                                const oglob: Types.GlobalId = @enumFromInt(reloc.target);
                                queue.append(tmp.arena.allocator(), oglob) catch unreachable;
                            }
                        }

                        global.get(self.types).runtime_emmited = true;
                        backend.emitData(.{
                            .id = @intFromEnum(global),
                            .name = global.get(self.types)
                                .fmt(self.types).toString(tmp.arena),
                            // NOTE: this can get optimized to .uninit if the
                            // content is all zero
                            .value = .{ .init = global.get(self.types)
                                .data.get(self.types) },
                            .readonly = global.get(self.types).readonly,
                            .thread_local = false,
                            .relocs = relocs.items,
                            .uuid = @splat(0),
                        });
                    }
                },
                inline .Call, .FuncAddr => |extra| {
                    if (extra.id == comptime_only_fn) {
                        if (self.target == .cmptime) continue;
                        self.reportSloc(sym.get().sloc, "the comptime only" ++
                            " directive is getting compiled into the runtime", .{}) catch {};
                        continue;
                    }

                    const fid: Types.FuncId = @enumFromInt(extra.id);
                    fid.get(self.types).queue(self.target, self.types);
                },
                else => utils.panic("{f}", .{sym}),
            }
        }
    }

    if (prev_err_count < self.types.errored) return;

    backend.emitFunc(&self.bl.func, .{
        .id = @intFromEnum(fnid),
        .files = self.types.line_indexes,
        .is_inline = false,
        .name = if (self.target == .runtime)
            fnid.get(self.types).fmt(self.types).toString(tmp.arena)
        else
            "",
        .linkage = fnid.get(self.types).linkage,
        .optimizations = .{ .opts = opts },
        .builtins = .{},
        .uuid = @splat(0),
    });
}

pub fn emitReachable(types: *Types, gpa: std.mem.Allocator, opts: Machine.OptOptions) void {
    var self: Codegen = undefined;
    self.init(types, .nany(File.Id.root.getScope(types)), .never, gpa);
    defer self.deinit();
    while (types.nextFunc(.runtime, 0)) |fnid| {
        // TODO: we dont want this to reinitialize the bl every time

        self.prepareForFunc(fnid);
        self.emitFunc(fnid) catch continue;
        self.emitToBackend(fnid, types.backend, opts);
    }
}

pub fn typedExprPrec(self: *Codegen, ty: Types.Id, ctx: Ctx, lex: *Lexer, prevPrec: u8) Error!Value {
    const pos = lex.cursor;
    var cx = ctx;
    cx.ty = ty;
    var exp = try self.exprPrec(cx, lex, prevPrec);
    try self.typeCheck(pos, cx, &exp, ty);
    return exp;
}

pub fn typedExpr(self: *Codegen, ty: Types.Id, ctx: Ctx, lex: *Lexer) Error!Value {
    return try self.typedExprPrec(ty, ctx, lex, 254);
}

pub fn expr(self: *Codegen, ctx: Ctx, lex: *Lexer) Error!Value {
    return self.exprPrec(ctx, lex, 254);
}

pub const StringEncodeResutl = union(enum) {
    ok: []u8,
    err: struct { reason: []const u8, pos: u32 },
};

pub fn encodeString(
    literal: []const u8,
    buf: []u8,
) !StringEncodeResutl {
    const SPECIAL_CHARS = "nrt\\'\"0";
    const TO_BYTES = "\n\r\t\\\'\"\x00";

    std.debug.assert(SPECIAL_CHARS.len == TO_BYTES.len);

    var str = std.ArrayList(u8).initBuffer(buf);
    var bytes = std.mem.splitScalar(u8, literal, '\\');

    while (bytes.next()) |chunk| {
        try str.appendSliceBounded(chunk);
        if (bytes.rest().len == 0) break;
        switch (bytes.rest()[0]) {
            '{' => {
                var hex_bytes = bytes.rest();
                var i: usize = 1;
                while (i < hex_bytes.len and hex_bytes[i] != '}') : (i += 2) {
                    if (i + 1 >= hex_bytes.len) {
                        return .{ .err = .{
                            .reason = "incomplete escape sequence",
                            .pos = @intCast(literal.len - bytes.rest().len),
                        } };
                    }
                    const byte_val = std.fmt.parseInt(u8, hex_bytes[i .. i + 2], 16) catch {
                        return .{ .err = .{
                            .reason = "expected hex digit or '}'",
                            .pos = @intCast(literal.len - bytes.rest().len),
                        } };
                    };
                    try str.appendBounded(byte_val);
                }
                bytes.index.? += i + 1;
            },
            else => |b| {
                for (SPECIAL_CHARS, TO_BYTES) |s, sb| {
                    if (s == b) {
                        try str.appendBounded(sb);
                        break;
                    }
                } else return .{ .err = .{
                    .reason = "unknown escape sequence",
                    .pos = @intCast(literal.len - bytes.rest().len),
                } };
                bytes.index.? += 1;
            },
        }
    }

    return .{ .ok = str.items };
}

pub fn prepareMatchValue(self: *Codegen, lex: *Lexer) !Value {
    var pat = self.expr(.{}, lex) catch |err| switch (err) {
        error.Report => {
            try lex.skipExpr();
            return error.Report;
        },
    };

    if (pat.ty.data() == .Union) {
        const tagl = pat.ty.data().Union.get(self.types)
            .getLayout(self.types).tagLayout() orelse {
            return self.report(lex.cursor, "{} is a tagless union", .{pat.ty});
        };
        pat = .value(.nany(tagl.id), self.getUnionTag(lex.cursor, tagl, pat));
    }

    if (pat.ty.data() != .Enum) {
        return self.report(lex.cursor, "{} is not an enum", .{pat.ty});
    }

    return pat;
}

pub fn unitExpr(self: *Codegen, tok: Lexer.Token, ctx: Ctx, lex: *Lexer) UnitError!Value {
    return switch (tok.kind.expand()) {
        .Comment => .voidv,
        .idk => ik: {
            const ty = ctx.ty orelse {
                return self.report(tok.pos, "cant infer the type of the uninitialized value, use @as(<ty>, idk)", .{});
            };

            break :ik switch (ty.category(self.types)) {
                .Impossible => return self.report(tok.pos, "{} is uninhabited, can not be uninitialized", .{ty}),
                .Imaginary => .unit(ty),
                .Scalar => |t| .value(ty, self.bl.addUninit(self.sloc(tok.pos), t)),
                .Stack => .ptr(ty, self.emitLoc(tok.pos, ty, ctx)),
            };
        },
        .null => nl: {
            const ty = ctx.ty orelse {
                return self.report(tok.pos, "cant infer the type of the null literal, use @as(?<ty>, null)", .{});
            };

            if (ty.data() != .Option) {
                return self.report(tok.pos, "this type can not be null", .{});
            }

            switch (ty.category(self.types)) {
                .Impossible => break :nl .unit(ty),
                .Imaginary => break :nl .value(ty, self.bl.addIntImm(self.sloc(tok.pos), .i8, 0)),
                .Scalar, .Stack => {
                    const layout = ty.data().Option.get(self.types).getLayout(self.types);
                    const slot = self.emitLoc(tok.pos, ty, ctx);
                    self.bl.addFieldStore(
                        self.sloc(tok.pos),
                        slot,
                        layout.inner.offset,
                        layout.inner.storage.dataType(),
                        self.bl.addIntImm(self.sloc(tok.pos), layout.inner.storage.dataType(), 0),
                    );
                    break :nl .ptr(ty, slot);
                },
            }
        },
        .die => {
            self.bl.addTrap(self.sloc(tok.pos), 0);
            return error.Unreachable;
        },
        .@"\"" => lit: {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const view = tok.view(lex.source);
            const buf = tmp.arena.alloc(u8, view.len - 2);

            const str = encodeString(view[1 .. view.len - 1], buf) catch
                unreachable;

            const bytes = switch (str) {
                .ok => |o| o,
                .err => |e| {
                    return self.report(
                        tok.pos + 1 + e.pos,
                        "char literal parse error: {}",
                        .{e.reason},
                    );
                },
            };

            break :lit self.emitString(tok.pos, ctx, bytes);
        },
        .@"'" => lit: {
            const view = tok.view(lex.source);
            var char_slot: [1]u8 = undefined;
            const str = encodeString(view[1 .. view.len - 1], &char_slot) catch {
                return self.report(tok.pos, "the char encodes into more then 1 byte", .{});
            };

            const bytes = switch (str) {
                .ok => |o| o,
                .err => |e| {
                    return self.report(
                        tok.pos + 1 + e.pos,
                        "char literal parse error: {}",
                        .{e.reason},
                    );
                },
            };

            if (bytes.len == 0) {
                return self.report(tok.pos, "empty char literal", .{});
            }

            break :lit .value(.u8, self.bl.addIntImm(
                self.sloc(tok.pos),
                .i8,
                bytes[0],
            ));
        },
        .Type => |t| self.tyLit(
            tok.pos,
            @as(Types.Builtin, @enumFromInt(@intFromEnum(t))),
        ),
        .Ident, .@"$" => self.lookupIdent(
            self.scope,
            tok.view(lex.source),
        ) orelse .variable(.void, self.defineVariable(tok)),
        .@"[" => array: {
            if (lex.eatMatch(.@"]")) {
                break :array self.tyLit(tok.pos, self.types.sliceOf(try self.typ(lex)));
            }

            // we defer the error check for recovery
            const len = self.peval(
                tok.pos,
                try self.expr(.{ .ty = .uint }, lex),
                Types.Size,
            );

            _ = try self.expect(lex, .@"]", "expected ']' after array length");

            break :array self.tyLit(
                tok.pos,
                self.types.arrayOf(try self.typ(lex), try len),
            );
        },
        .@"?" => self.tyLit(tok.pos, self.types.optionOf(try self.typ(lex))),
        .@"^" => self.tyLit(tok.pos, self.types.pointerTo(try self.typ(lex))),
        .@"#" => spill: {
            var oper = try self.exprPrec(.{ .ty = ctx.ty }, lex, 1);

            switch (oper.normalized(tok.pos, self)) {
                .empty => break :spill oper,
                .value => |v| {
                    const slot = self.emitLoc(tok.pos, oper.ty, ctx);
                    self.emitArbitraryStore(tok.pos, slot, v, oper.ty.size(self.types));
                    break :spill .ptr(oper.ty, slot);
                },
                .ptr => |p| {
                    if (isUniqueLocal(p)) break :spill oper;

                    const slot = self.emitLoc(tok.pos, oper.ty, ctx);
                    self.bl.addFixedMemCpy(
                        self.sloc(tok.pos),
                        slot,
                        p,
                        oper.ty.size(self.types),
                    );

                    break :spill .ptr(oper.ty, slot);
                },
            }
        },
        .@"&" => ref: {
            if (lex.eatMatch(.@".[")) {
                var elem: ?Types.Id = null;
                if (ctx.ty) |ti| {
                    var t = ti;
                    if (t.data() == .Option) {
                        t = t.data().Option.get(self.types).inner;
                    }

                    if (t.data() == .Slice) {
                        elem = t.data().Slice.get(self.types).elem;
                    }
                }

                const slot = self.bl.addLocal(self.sloc(lex.cursor), 0, std.math.maxInt(u32));

                var iter = lex.list(.@",", .@"]");
                var len: Types.Size = 0;
                while (iter.next()) {
                    if (len != 0) std.debug.assert(elem != null);

                    const loc = self.bl.addFieldOffset(
                        self.sloc(lex.cursor),
                        slot,
                        if (elem) |e| len * e.size(self.types) else 0,
                    );
                    var vl = self.expr(.{ .ty = elem, .loc = loc }, lex) catch |err| switch (err) {
                        error.Report => continue,
                    };
                    if (elem) |e| self.typeCheck(lex.cursor, .{ .loc = loc }, &vl, e) catch {};
                    self.emitGenericStore(lex.cursor, loc, vl);
                    elem = elem orelse vl.ty;

                    len += 1;
                }

                const felem = elem orelse {
                    return self.report(lex.cursor, "cant infer the element type of the slice literal", .{});
                };

                const slot_ty = self.types.arrayOf(felem, len);
                self.bl.resizeLocal(slot, slot_ty.size(self.types), slot_ty.raw());

                const slice_ty = self.types.sliceOf(felem);
                const slice = self.emitLoc(tok.pos, slice_ty, ctx);

                const len_imm = self.bl.addIntImm(self.sloc(tok.pos), .i64, len);
                self.bl.addFieldStore(self.sloc(tok.pos), slice, Types.Slice.len_offset, .i64, len_imm);
                self.bl.addFieldStore(self.sloc(tok.pos), slice, Types.Slice.ptr_offset, .i64, slot);

                return .ptr(slice_ty, slice);
            }

            var oper = try self.exprPrec(.{}, lex, 1);

            const ptr_ty = self.types.pointerTo(oper.ty);

            if (oper.ty.data() == .FuncTy) {
                const vl = try self.peval(lex.cursor, oper, Types.FuncId);
                break :ref .value(ptr_ty, self.bl.addFuncAddr(self.sloc(tok.pos), @intFromEnum(vl)));
            }

            break :ref .value(ptr_ty, try oper.asPtr(tok.pos, self));
        },
        .@"~", .@"-" => neg: {
            var oper = try self.exprPrec(.{ .ty = ctx.ty }, lex, 1);

            if (tok.kind == .@"~" and !oper.ty.isBuiltin(.isInteger)) {
                return self.report(tok.pos, "expected integer, got {}", .{oper.ty});
            }

            if (tok.kind == .@"-" and !oper.ty.isBuiltin(.isFloat) and
                !oper.ty.isBuiltin(.isInteger))
            {
                return self.report(tok.pos, "expected float or integer, got {}", .{oper.ty});
            }

            break :neg .value(oper.ty, self.bl.addUnOp(
                self.sloc(tok.pos),
                if (tok.kind == .@"~") .bnot else .ineg,
                Abi.categorizeBuiltinUnwrapped(oper.ty.data().Builtin),
                oper.load(tok.end, self),
            ));
        },
        .@"!" => not: {
            var oper = try self.typedExprPrec(.bool, .{}, lex, 1);

            break :not .value(.bool, self.bl.addUnOp(
                self.sloc(tok.pos),
                .not,
                .i8,
                oper.load(tok.end, self),
            ));
        },
        ._ => discard: {
            _ = try self.expect(lex, .@"=", "followed by the expression to discard");

            _ = try self.expr(.{ .ty = .void }, lex);

            break :discard .voidv;
        },
        inline .@"union", .@"enum", .@"struct" => |_, t| {
            if (lex.eatMatch(.@"(")) {
                lex.eatUntilClosingDelimeter();
            }

            if (lex.eatMatch(.@"align")) {
                _ = try self.expect(lex, .@"(", "to start the align value");
                lex.eatUntilClosingDelimeter();
            }

            const bra = try self.expect(lex, .@"{", "to open " ++ @tagName(t) ++ " definition");

            const decls = self.scope.data().decls(self.types)
                .lookupScope(tok.pos) orelse {
                return self.report(bra.pos, "malformed " ++ @tagName(t), .{});
            };
            lex.cursor = decls.end;

            const vl = @field(self.types, @tagName(t) ++ "s").push(&self.types.arena, .{
                .scope = self.gatherScope(),
                .captures = .init(self, &self.types.arena),
                .decls = decls,
            });

            return self.tyLit(tok.pos, vl);
        },
        .@"{" => {
            var reached_end = true;

            const scope_frame = self.vars.len;
            const defer_frame = self.defers.items.len;
            defer self.popScope(scope_frame);
            defer {
                if (reached_end) self.emitDefers(defer_frame);
                self.defers.items.len = defer_frame;
            }

            var iter = lex.list(.@";", .@"}");
            while (iter.next()) {
                if (self.branchExpr(lex)) {
                    lex.eatUntilClosingDelimeter();
                    reached_end = false;
                    break;
                }
            }

            if (!reached_end) return error.Unreachable;

            return .voidv;
        },
        .@"defer" => {
            self.defers.append(self.bl.arena(), lex.cursor) catch unreachable;
            lex.skipExprDropErr();

            return .voidv;
        },
        .@"fn" => switch (try self.@"fn"(lex)) {
            .func => |vl| .value(.nany(vl[1]), self.bl.addIntImm(
                self.sloc(tok.pos),
                .i32,
                @intFromEnum(vl[0]),
            )),
            .template => |id| .value(.template, self.bl.addIntImm(
                self.sloc(tok.pos),
                .i32,
                @intFromEnum(id),
            )),
            .func_ty => |id| self.tyLit(tok.pos, id),
        },
        .match => {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const pat = try self.prepareMatchValue(lex);

            var pat_vl = LLValue.init(lex.cursor, .value(pat.ty, pat.load(lex.cursor, self)));
            defer pat_vl.deinit(self);

            const enm = pat.ty.data().Enum.get(self.types).getLayout(self.types);

            _ = try self.expect(lex, .@"{", "to open the match arms");

            var breaker = self.bl.addBlock();

            var seen = tmp.arena.alloc(u32, enm.fields.len);
            @memset(seen, 0);

            var branch_count: usize = 0;
            var else_pos: ?u32 = null;
            var iter = lex.list(.@",", .@"}");
            while (iter.next()) {
                branch_count += 1;
                if (lex.eatMatch(.@"else")) {
                    if (else_pos) |p| {
                        _ = self.report(lex.cursor, "duplicate else arm", .{}) catch {};
                        _ = self.report(p, "...previous else arm is here", .{}) catch {};
                    }

                    _ = try self.expect(lex, .@"=>", "to open a match arm");
                    else_pos = lex.cursor;
                    try lex.skipExpr();
                    continue;
                }

                const pred = try self.typedExpr(pat.ty, .{}, lex);
                const pred_value = try self.peval(lex.cursor, pred, i64);

                _ = try self.expect(lex, .@"=>", "to open a match arm");

                const idx = std.mem.indexOfScalar(i64, enm.fields, pred_value) orelse {
                    self.report(lex.cursor, "corrupted match value ({})", .{pred_value}) catch {};
                    try lex.skipExpr();
                    continue;
                };

                if (seen[idx] != 0) {
                    self.report(lex.cursor, "duplicate match arm", .{}) catch {};
                    self.report(seen[idx], "...previous match arm is here", .{}) catch {};
                }
                seen[idx] = lex.cursor;

                var branch: ?BBuilder.If = null;
                if (branch_count != seen.len) {
                    const pat_vll = pat_vl.load(self);
                    const cond = self.bl.addBinOp(
                        self.sloc(lex.cursor),
                        .eq,
                        pat_vll.data_type,
                        pat_vll,
                        self.bl.addIntImm(self.sloc(lex.cursor), pat_vll.data_type, pred_value),
                    );
                    branch = self.bl.addIfAndBeginThen(self.sloc(lex.cursor), cond);
                }

                if (!self.branchExpr(lex)) breaker.addBreak(&self.bl);

                if (branch) |*b| b.end(&self.bl, b.beginElse(&self.bl));
            }

            if (else_pos) |pos| {
                if (branch_count == enm.fields.len) {
                    _ = self.report(pos, "needless else match arm, all" ++
                        " variants are already handled", .{}) catch {};
                }

                var elex = Lexer.init(lex.source, pos);
                if (!self.branchExpr(&elex)) breaker.addBreak(&self.bl);
            }

            breaker.end(&self.bl);

            if (self.bl.isUnreachable()) return error.Unreachable;

            return .voidv;
        },
        .@"$match" => {
            const pat = try self.prepareMatchValue(lex);

            const pat_value = try self.peval(lex.cursor, pat, i64);

            _ = try self.expect(lex, .@"{", "to open the match arms");

            var iter = lex.list(.@",", .@"}");

            var else_branch: ?u32 = null;

            while (iter.next()) {
                if (lex.eatMatch(.@"else")) {
                    _ = try self.expect(lex, .@"=>", "to start the else branch");
                    else_branch = lex.cursor;
                    try lex.skipExpr();
                    continue;
                }

                const pvl = try self.typedExpr(pat.ty, .{}, lex);
                const pvl_lit = try self.peval(lex.cursor, pvl, i64);

                _ = try self.expect(lex, .@"=>", "to start the branch");
                if (pvl_lit == pat_value) {
                    const unreached = self.branchExpr(lex);
                    lex.eatUntilClosingDelimeter();
                    if (unreached) return error.Unreachable;
                    return .voidv;
                } else {
                    try lex.skipExpr();
                }
            }

            if (else_branch) |pos| {
                var elex = Lexer.init(lex.source, pos);
                if (self.branchExpr(&elex)) return error.Unreachable;
                return .voidv;
            }

            return self.report(tok.pos, "unable to match any pattern for {}" ++
                " (TODO: display enums properly)", .{pat_value});
        },
        .@"$if" => {
            if (self.peval(tok.pos, try self.typedExpr(.bool, .{}, lex), bool) catch false) {
                const unreached = self.branchExpr(lex);

                if (lex.eatMatch(.@"else")) {
                    lex.skipExprDropErr();
                }

                if (unreached) return error.Unreachable;
            } else {
                lex.skipExprDropErr();

                if (lex.eatMatch(.@"else")) {
                    if (self.branchExpr(lex)) return error.Unreachable;
                }
            }

            return .voidv;
        },
        .@"if" => {
            const frame = self.vars.len;

            var cond = self.typedExpr(
                .bool,
                .{ .in_if_or_while = true },
                lex,
            ) catch |err| switch (err) {
                error.Report => self.emitUninitValue(tok.pos, .bool),
            };

            var if_bl = self.bl.addIfAndBeginThen(
                self.sloc(tok.pos),
                cond.load(tok.end, self),
            );

            _ = self.branchExpr(lex);

            self.popScope(frame);

            const tk = if_bl.beginElse(&self.bl);

            if (lex.eatMatch(.@"else")) {
                _ = self.branchExpr(lex);
            }

            if_bl.end(&self.bl, tk);

            if (self.bl.isUnreachable()) return error.Unreachable;

            return .voidv;
        },
        .@"$while", .@"$loop" => {
            var loop = Loop{
                .prev = self.loops,
                .defer_frame = self.defers.items.len,
                .name = try self.eatLabel(lex),
                .state = .{ .cmptime = .{} },
            };
            self.loops = &loop;
            defer self.loops = loop.prev;

            const checkpoint = lex.cursor;
            var end = checkpoint;
            const prev_erred = self.types.errored;

            var fuel: usize = 300;

            while (fuel > 0 and (tok.kind == .@"$loop" or try self.peval(
                tok.pos,
                try self.expr(.{ .ty = .bool }, lex),
                bool,
            ))) : (fuel -= 1) {
                const unreached = self.branchExpr(lex);

                end = lex.cursor;
                lex.cursor = checkpoint;

                if (loop.state.cmptime.kind == .broken and unreached) {
                    break;
                }

                _ = self.loopControl(lex, .@"continue", loop.name) catch {};

                loop.state.cmptime.kind = .falltrough;

                if (prev_erred < self.types.errored) break;
            }

            if (fuel == 0) {
                return self.report(tok.pos, "out of loop fuel", .{});
            }

            if (checkpoint == end) {
                lex.skipExprDropErr();
            } else {
                lex.cursor = end;
            }

            return .voidv;
        },
        .loop => {
            var loop = Loop{
                .prev = self.loops,
                .defer_frame = self.defers.items.len,
                .name = try self.eatLabel(lex),
                .state = .{ .runtime = .{
                    .bl = self.bl.addLoopAndBeginBody(self.sloc(tok.pos)),
                } },
            };
            self.loops = &loop;
            defer self.loops = loop.prev;

            _ = self.branchExpr(lex);

            loop.state.runtime.bl.end(&self.bl);

            if (self.bl.isUnreachable()) {
                return error.Unreachable;
            }

            return .voidv;
        },
        .@"while" => {
            var loop = Loop{
                .prev = self.loops,
                .defer_frame = self.defers.items.len,
                .name = try self.eatLabel(lex),
                .state = .{ .runtime = .{
                    .bl = self.bl.addLoopAndBeginBody(self.sloc(tok.pos)),
                } },
            };
            self.loops = &loop;
            defer self.loops = loop.prev;

            const frame = self.vars.len;

            const cond = try self.typedExpr(.bool, .{ .in_if_or_while = true }, lex);
            var bl = self.bl.addIfAndBeginThen(
                self.sloc(tok.pos),
                cond.load(tok.pos, self),
            );

            _ = self.branchExpr(lex);

            const tk = bl.beginElse(&self.bl);
            loop.state.runtime.bl.addControl(&self.bl, .@"break");
            bl.end(&self.bl, tk);

            self.popScope(frame);

            loop.state.runtime.bl.end(&self.bl);

            if (self.bl.isUnreachable()) {
                return error.Unreachable;
            }

            return .voidv;
        },
        .@"for" => {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const slc = self.sloc(tok.pos);

            const frame = self.vars.len;

            var iters = std.ArrayList(usize).empty;
            var len: ?struct { vl: LLValue, bound: LLValue, idx: usize } = null;
            var length_check_cond: ?LLValue = null;

            while (true) {
                const name = try self.expect(lex, .Ident, "to bind the range decl");
                _ = try self.expect(lex, .@":=", "to start the range definition");

                var vindex: ?usize = null;
                parse_iter: {
                    var value = self.exprPrec(
                        .{},
                        lex,
                        Lexer.Lexeme.@"..".precedence(false),
                    ) catch break :parse_iter;

                    if (lex.eatMatch(.@"..")) {
                        self.typeCheck(lex.cursor, .{}, &value, .uint) catch {};
                        if (lex.peekNext().kind == .@",") {
                            vindex = self.pushVariable(name, value) catch unreachable;
                        } else {
                            var start = LLValue.init(lex.cursor, value);
                            defer start.deinit(self);

                            std.debug.assert(start.value.ty == .uint);

                            var vl = LLValue.init(lex.cursor, self.typedExpr(
                                .uint,
                                .{},
                                lex,
                            ) catch break :parse_iter);

                            const bound = LLValue.init(lex.cursor, .value(
                                .uint,
                                self.bl.addBinOp(slc, .isub, .i64, vl.load(self), start.load(self)),
                            ));

                            if (len) |l| {
                                const cond = self.bl.addBinOp(slc, .ne, .i64, l.bound.load(self), bound.load(self));
                                if (length_check_cond) |*lcc| {
                                    lcc.set(.value(.bool, self.bl.addBinOp(slc, .bor, .i8, lcc.load(self), cond)));
                                } else {
                                    length_check_cond = LLValue.init(tok.pos, .value(.bool, cond));
                                }
                            } else {
                                len = .{ .vl = vl, .bound = bound, .idx = self.vars.len };
                            }

                            vindex = self.pushVariable(name, start.value) catch unreachable;
                        }
                    } else {
                        if (value.ty.data() != .Slice) {
                            self.report(
                                lex.cursor,
                                "{} is not a slice",
                                .{value.ty},
                            ) catch break :parse_iter;
                        }

                        var slen = LLValue.init(tok.pos, .value(.uint, self.bl.addFieldLoad(
                            slc,
                            value.normalized(tok.pos, self).ptr,
                            Types.Slice.len_offset,
                            .i64,
                        )));

                        if (len) |l| {
                            const cond = self.bl.addBinOp(slc, .ne, .i64, l.bound.load(self), slen.load(self));
                            if (length_check_cond) |*lcc| {
                                lcc.set(.value(.bool, self.bl.addBinOp(slc, .bor, .i8, lcc.load(self), cond)));
                            } else {
                                length_check_cond = LLValue.init(tok.pos, .value(.bool, cond));
                            }
                            slen.deinit(self);
                        } else {
                            len = .{
                                .vl = .init(tok.pos, .value(
                                    .uint,
                                    self.bl.addIndexOffset(
                                        slc,
                                        self.bl.addFieldLoad(
                                            slc,
                                            value.normalized(tok.pos, self).ptr,
                                            Types.Slice.ptr_offset,
                                            .i64,
                                        ),
                                        .iadd,
                                        value.ty.data().Slice
                                            .get(self.types).elem.size(self.types),
                                        slen.value.value_.node,
                                    ),
                                )),
                                .bound = slen,
                                .idx = self.vars.len,
                            };
                        }

                        vindex = self.pushVariable(name, .ptr(
                            self.types.pointerTo(value.ty
                                .data().Slice.get(self.types).elem),
                            self.bl.addFieldOffset(
                                slc,
                                value.normalized(tok.pos, self).ptr,
                                Types.Slice.ptr_offset,
                            ),
                        )) catch unreachable;
                    }
                }

                if (vindex) |v| iters.append(tmp.arena.allocator(), v) catch unreachable;

                if (!lex.eatMatch(.@",")) break;
            }

            if (length_check_cond) |*cond| {
                if (self.types.handlers.get(.for_loop_length_mismatch).asOpt()) |fllm| {
                    var handler = self.addHandler(tok.pos, fllm, cond.load(self), tmp.arena);
                    handler.end(self);
                }
                cond.deinit(self);
            }

            var loop = Loop{
                .prev = self.loops,
                .defer_frame = self.defers.items.len,
                .name = try self.eatLabel(lex),
                .state = .{ .runtime = .{
                    .bl = self.bl.addLoopAndBeginBody(slc),
                } },
            };
            self.loops = &loop;
            defer self.loops = loop.prev;

            var ln = len orelse {
                return self.report(tok.pos, "the for loop is missin upper bound", .{});
            };
            ln.bound.deinit(self);
            defer ln.vl.deinit(self);

            const counter_slot = &self.vars.items(.variable)[ln.idx];
            const counter_vl = Value.variable(counter_slot.ty, ln.idx);
            const cond = self.bl.addBinOp(slc, .ult, .i8, counter_vl.load(tok.pos, self), ln.vl.load(self));

            var cond_bl = self.bl.addIfAndBeginThen(slc, cond);

            if (!self.branchExpr(lex)) {
                loop.state.runtime.bl.joinContinues(&self.bl);

                for (iters.items) |vidx| {
                    const slot: *Variable = &self.vars.items(.variable)[vidx];

                    const step = if (slot.ty == .uint)
                        1
                    else
                        slot.ty.data().Pointer.get(self.types).ty.size(self.types);

                    const value = Value.variable(slot.ty, vidx);

                    const step_const = self.bl.addIntImm(slc, .i64, step);
                    const next = self.bl.addBinOp(
                        slc,
                        .iadd,
                        .i64,
                        value.load(tok.pos, self),
                        step_const,
                    );
                    self.assign(tok.pos, value, .value(slot.ty, next)) catch unreachable;
                }
            }

            const tk = cond_bl.beginElse(&self.bl);
            loop.state.runtime.bl.addControl(&self.bl, .@"break");
            cond_bl.end(&self.bl, tk);

            loop.state.runtime.bl.end(&self.bl);

            self.popScope(frame);

            return .voidv;
        },
        .@"break" => try self.loopControl(lex, .@"break", try self.eatLabel(lex)),
        .@"continue" => try self.loopControl(lex, .@"continue", try self.eatLabel(lex)),
        .@"return" => {
            var cursor = self.loops;
            while (cursor) |l| : (cursor = l.prev) {
                switch (l.state) {
                    .runtime => |*r| {
                        r.bl.markBreaking();
                        break;
                    },
                    else => {},
                }
            }

            const cx = Ctx{ .ty = self.ret_ty, .loc = self.ret_ref };

            var ret: Value = if (lex.peekNext().kind.canStartExpression())
                try self.expr(cx, lex)
            else
                .voidv;

            // TODO: copy the return value, if the pointers dont match

            try self.typeCheck(tok.pos, cx, &ret, self.ret_ty);

            if (self.bl.func.signature.returns()) |returns| {
                var buf: [Abi.max_elems]*BNode = undefined;
                if (returns.len == 1) {
                    buf[0] = ret.load(tok.pos, self);
                    buf[0].lockTmp();
                } else if (returns.len == 2) {
                    const ptr = ret.normalized(tok.pos, self).ptr;
                    buf[0] = self.bl.addLoad(self.sloc(tok.pos), ptr, returns[0].Reg);
                    buf[0].lockTmp();
                    buf[1] = self.emitArbitraryLoad(
                        tok.pos,
                        self.bl.addFieldOffset(self.sloc(tok.pos), ptr, 8),
                        returns[1].Reg,
                        ret.ty.size(self.types) - 8,
                    );
                    buf[1].lockTmp();
                } else if (self.ret_ref) |slt| {
                    self.emitGenericStore(tok.pos, slt, ret);
                }

                self.emitDefers(0);

                for (buf[0..returns.len]) |v| v.unlockTmp();

                self.bl.addReturn(buf[0..returns.len]);
            } else {
                return self.report(tok.pos, "`return` can not be used" ++
                    " since `{}` is uninhabited", .{self.ret_ty});
            }

            return error.Unreachable;
        },
        .true => .value(.bool, self.bl.addIntImm(self.sloc(tok.pos), .i8, 1)),
        .false => .value(.bool, self.bl.addIntImm(self.sloc(tok.pos), .i8, 0)),
        .DecInteger, .BinInteger, .OctInteger, .HexInteger => int: {
            const res = std.fmt.parseInt(u64, tok.view(lex.source), 0);
            const val = res catch |err| switch (err) {
                error.Overflow => return self.report(tok.pos, "the integer" ++
                    " value is too large", .{}),
                error.InvalidCharacter => unreachable,
            };

            var ty = ctx.ty orelse .uint;
            if (ty.data() == .Option) ty = ty.data().Option.get(self.types).inner;
            if (!ty.isBuiltin(.isInteger)) ty = .uint;

            break :int .value(ty, self.bl.addIntImm(
                self.sloc(tok.pos),
                Abi.categorizeBuiltinUnwrapped(ty.data().Builtin),
                @bitCast(val),
            ));
        },
        .Float => float: {
            const res = std.fmt.parseFloat(f64, tok.view(lex.source));
            const val = res catch |err| switch (err) {
                error.InvalidCharacter => unreachable,
            };

            var ty = ctx.ty orelse .f32;
            if (!ty.isBuiltin(.isFloat)) ty = .f32;

            break :float .value(ty, self.bl.addIntImm(
                self.sloc(tok.pos),
                Abi.categorizeBuiltinUnwrapped(ty.data().Builtin),
                if (ty == .f64)
                    @bitCast(val)
                else
                    @as(u32, @bitCast(@as(f32, @floatCast(val)))),
            ));
        },
        .@"(" => par: {
            const inner = try self.expr(ctx, lex);
            _ = try self.expect(lex, .@")", "to close the parenthesis");
            break :par inner;
        },
        .@".{" => ctor: {
            const ty = ctx.ty orelse {
                lex.eatUntilClosingDelimeter();
                return self.report(tok.pos, "can't infer the constructor type, use <ty>.{..}", .{});
            };

            break :ctor self.ctor(tok.pos, ctx, ty, lex);
        },
        .@".[" => {
            const ity = ctx.ty orelse {
                lex.eatUntilClosingDelimeter();
                return self.report(tok.pos, "TODO: infer type form the element", .{});
            };

            const ty, const slot = self.emitLocHandleOpt(tok.pos, ity, ctx);

            if (ty.data() != .Array) {
                return self.report(tok.pos, "{} can not be initialized as array", .{ty});
            }

            const arry = ty.data().Array.get(self.types);

            var iter = lex.list(.@",", .@"]");
            var len: Types.Size = 0;
            while (iter.next()) {
                if (len >= arry.len.s) {
                    self.report(lex.cursor, "extra value, array has {} elements", .{arry.len.s}) catch {};
                }

                const loc = self.bl.addFieldOffset(self.sloc(lex.cursor), slot, len * arry.elem.size(self.types));
                const vl = self.typedExpr(arry.elem, .{ .loc = loc }, lex) catch |err| switch (err) {
                    error.Report => continue,
                };
                self.emitGenericStore(lex.cursor, loc, vl);

                len += 1;
            }

            var res = Value.ptr(ity, slot);
            res.normalize(self);
            return res;
        },
        .@".(" => {
            const ty = ctx.ty orelse {
                // TODO: this is gonna cause issues
                const loc = ctx.loc orelse self.bl.addLocal(self.sloc(tok.pos), 0, std.math.maxInt(u32));

                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();

                var offset: Types.Size = 0;
                var alignment: Types.Size = 1;
                var fields = std.ArrayList(Types.Struct.Layout.Field).empty;
                var iter = lex.list(.@",", .@")");

                while (iter.next()) {
                    const value = self.expr(.{ .loc = loc }, lex) catch |err| switch (err) {
                        error.Report => if (iter.recover()) break else continue,
                    };

                    const falign = value.ty.alignment(self.types);
                    alignment = @max(alignment, falign);
                    offset = std.mem.alignForward(Types.Size, offset, falign);

                    fields.append(tmp.arena.allocator(), .{
                        .offset = offset,
                        .ty = value.ty,
                        .default = .invalid,
                    }) catch unreachable;

                    const floc = self.bl.addFieldOffset(self.sloc(lex.cursor), loc, offset);
                    self.emitGenericStore(tok.pos, floc, value);

                    offset += value.ty.size(self.types);
                }

                const size = std.mem.alignForward(Types.Size, offset, alignment);

                const struc = self.types.structs.push(&self.types.arena, .{
                    .scope = .{
                        .file = .root,
                        .name_pos = .tuple,
                        .parent = .init(.{ .Tail = .end }),
                    },
                    .captures = .empty,
                    .decls = &File.Id.root.get(self.types).decls,
                    .layout = .{
                        .spec = .fromByteUnits(size, alignment),
                        .fields = self.types.arena.dupe(Types.Struct.Layout.Field, fields.items),
                    },
                });

                const ty: Types.Id = .nany(struc);

                self.bl.resizeLocal(loc, ty.size(self.types), @intFromEnum(ty));

                return .ptr(.nany(struc), loc);
            };

            return try self.tupl(tok.pos, lex, ty, ctx);
        },
        .Directive => |d| self.directive(d, tok, ctx, lex),
        .@"." => inferred_field: {
            const field = try self.expect(lex, .Ident, "to name a inferred field");

            const ty = ctx.ty orelse
                return self.report(tok.pos, "cant infer the destination type", .{});

            if (lex.eatMatch(.@"(")) {
                const scope = ty.data().downcast(Types.UnorderedScope) orelse
                    return self.report(tok.pos, "expected type with unordered" ++
                        " scope (struct/union/enum)", .{});

                const item = self.lookupIdent(
                    scope.upcast(Types.AnyScope).pack(),
                    field.view(lex.source),
                ) orelse return self.report(field.pos, "{} does not have this declaration", .{ty});

                break :inferred_field self.emitCall(field.end, ctx, null, item, lex);
            } else {
                const scope = ty.data().downcast(Types.UnorderedScope) orelse {
                    return self.report(tok.pos, "{} does not have an unordered scope so it does not support inferred access", .{ty});
                };

                return self.lookupIdentDotted(scope.upcast(Types.AnyScope).pack(), field.view(lex.source)) orelse {
                    return self.report(tok.pos, "cant find the inferred value in {}", .{ty});
                };
            }
        },
        else => return self.report(tok.pos, "unexpected token", .{}),
    };
}

pub fn emitString(self: *Codegen, pos: u32, ctx: Ctx, bytes: []const u8) Value {
    const global = self.types.globals.push(&self.types.arena, .{
        .scope = self.gatherScope(),
        .ty = self.types.arrayOf(.u8, @intCast(bytes.len)),
        .readonly = true,
    });

    self.types.ct_backend.emitData(.{
        .id = @intFromEnum(global),
        .readonly = true,
        .value = .{ .init = bytes },
        .thread_local = false,
        .uuid = @splat(0),
    });

    const ty = self.types.sliceOf(.u8);
    const slot = self.emitLoc(pos, ty, ctx);
    self.bl.addFieldStore(
        self.sloc(pos),
        slot,
        Types.Slice.len_offset,
        .i64,
        self.bl.addIntImm(self.sloc(pos), .i64, @intCast(bytes.len)),
    );
    self.bl.addFieldStore(
        self.sloc(pos),
        slot,
        Types.Slice.ptr_offset,
        .i64,
        self.bl.addGlobalAddr(self.sloc(pos), @intFromEnum(global)),
    );

    return .ptr(ty, slot);
}

pub fn loopControl(self: *Codegen, lex: *Lexer, kind: BBuilder.Loop.Control, label: []const u8) !Value {
    var cursor = self.loops;
    var seen_runtime = false;
    while (cursor) |loop| : (cursor = loop.prev) {
        seen_runtime = seen_runtime or loop.state == .runtime;
        if (std.mem.eql(u8, loop.name, label)) {
            self.emitDefers(loop.defer_frame);
            switch (loop.state) {
                .runtime => |*r| {
                    r.bl.addControl(&self.bl, kind);
                },
                .cmptime => |*c| {
                    if (seen_runtime) {
                        self.report(lex.cursor, "comptime control flow breaks a runtime loop", .{}) catch {};
                    }

                    if (c.kind != .falltrough) {
                        self.report(lex.cursor, "encountered another comptime" ++
                            " control flow, maybe you need to use `$if`", .{}) catch {};
                        self.report(c.pos, "...previous control flow occured here", .{}) catch {};
                    }
                    c.kind = @enumFromInt(@intFromEnum(kind));
                    c.pos = lex.cursor;
                },
            }
            break;
        }
    }

    return error.Unreachable;
}

pub fn eatLabel(self: *Codegen, lex: *Lexer) ![]const u8 {
    return if (lex.eatMatch(.@":"))
        (try self.expect(lex, .Ident, "as a lable name"))
            .view(lex.source)
    else
        "";
}

pub fn directive(
    self: *Codegen,
    d: Lexer.Lexeme.Directive,
    tok: Lexer.Token,
    ctx: Ctx,
    lex: *Lexer,
) !Value {
    _ = try self.expect(lex, .@"(", "to open the directive arguments");

    const iter = lex.list(.@",", .@")");
    const pos = lex.cursor;
    const slc = self.sloc(pos);

    const value: Value = d: switch (d) {
        .Type => {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var call = self.bl.addCall(
                tmp.arena,
                slc,
                .ablecall,
                .{ .sym = comptime_only_fn },
            );

            const generic_return = self.types.builtins.type_union;
            var buf = Abi.Buf{};
            const ret_cata = Abi.ableos.categorize(.type, self.types, &buf);

            const op_cnst = self.bl.addIntImm(slc, .i64, @intFromEnum(ComptimeEca.Type));
            call.pushArg(&self.bl, slc, .{ .Reg = .i64 }, op_cnst, 0);

            _ = try self.passArg(&call, .{ .to_compute = .{ .lex = lex, .inferred = .nany(generic_return) } });

            var bf: [2]*BNode = undefined;
            const bls = call.end(&self.bl, slc, ret_cata, &bf);

            break :d .value(.type, bls[0]);
        },
        .type_name => {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const ty = try self.typ(lex);
            const bytes = ty.fmt(self.types).toString(tmp.arena);

            break :d self.emitString(tok.pos, ctx, bytes);
        },
        .type_info => {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var call = self.bl.addCall(
                tmp.arena,
                slc,
                .ablecall,
                .{ .sym = comptime_only_fn },
            );

            const generic_return = self.types.builtins.type_union;
            var buf = Abi.Buf{};
            const ret_cata = Abi.ableos.categorize(.nany(generic_return), self.types, &buf);

            std.debug.assert(Abi.ableos.isMultivalue(ret_cata));

            // TDOD: we can inline this into the comptime binary, might actually be more efficienato
            const op_cnst = self.bl.addIntImm(slc, .i64, @intFromEnum(ComptimeEca.type_info));
            call.pushArg(&self.bl, slc, .{ .Reg = .i64 }, op_cnst, 0);

            const slot = self.emitLoc(pos, .nany(generic_return), ctx);
            call.pushArg(&self.bl, slc, .{ .Reg = .i64 }, slot, 0);

            const ty = try self.passArg(&call, .{ .to_compute = .{ .lex = lex, .inferred = .type } });
            if (ty != .type) {
                return self.report(pos, "expected type, got {}", .{ty});
            }

            _ = call.end(&self.bl, self.sloc(pos), ret_cata, undefined);

            break :d .ptr(.nany(generic_return), slot);
        },
        .is_comptime => .value(.bool, self.bl.addIntImm(
            slc,
            .i8,
            @intFromBool(self.target == .cmptime),
        )),
        .@"error" => {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var message = std.Io.Writer.Allocating.init(tmp.arena.allocator());

            while (iter.next()) {
                const tk = lex.peekNext();
                if (tk.kind == .@"\"") {
                    lex.cursor = tk.end;
                    const smsg = tk.view(lex.source);
                    message.writer.writeAll(
                        smsg[1 .. smsg.len - 1],
                    ) catch unreachable;
                    continue;
                }

                const vl = self.expr(.{}, lex) catch continue;
                if (vl.ty == .type) {
                    const ty = self.peval(lex.cursor, vl, Types.Id) catch .never;
                    message.writer.print("{f}", .{ty.fmt(self.types)}) catch unreachable;
                }
            }

            return self.report(pos, "{}", .{message.written()});
        },
        .use => {
            _ = lex.slit(.@"\"");

            const use = self.scope.data().decls(self.types)
                .lookupImport(tok.pos) orelse {
                return self.report(tok.pos, "BUG: cannot find imported declaration", .{});
            };

            break :d self.tyLit(tok.pos, use.getScope(self.types));
        },
        .embed => {
            const path = try self.expect(lex, .@"\"", "to declare the relative path");
            var path_str = path.view(lex.source);
            path_str = path_str[1 .. path_str.len - 1];

            self.types.loader.from = self.file;
            self.types.loader.path = self.file.get(self.types).path;
            const embed = self.types.loader.loadEmbed(.{
                .path = path_str,
                .pos = pos,
            }) orelse {
                return self.report(pos, "can't load the embed", .{});
            };

            const storage = self.types.globals.push(&self.types.arena, .{
                .scope = self.gatherScope(),
                .ty = self.types.arrayOf(.u8, @intCast(embed.len)),
                .readonly = true,
            });

            storage.get(self.types).scope.name_pos = .empty;

            self.types.ct_backend.emitData(.{
                .id = @intFromEnum(storage),
                .value = .{ .init = embed },
                .readonly = true,
                .thread_local = false,
                .uuid = @splat(0),
            });

            break :d .ptr(
                storage.get(self.types).ty,
                self.bl.addGlobalAddr(slc, @intFromEnum(storage)),
            );
        },
        .Builtins => self.tyLit(pos, self.types.roots[self.types.files.len - 1]),
        .ReturnType => {
            const func = self.scope.data().findCurrentFunc(self.types) orelse {
                return self.report(lex.cursor, "directive needs to be inside a function", .{});
            };

            break :d self.tyLit(pos, func.get(self.types).ret);
        },
        .Any => self.tyLit(pos, Types.Id.any),
        .TypeOf => {
            const ty = b: {
                var tmp = self.types.tmpCheckpoint();
                defer tmp.deinit();

                var ty_gen: Codegen = undefined;
                ty_gen.init(self.types, self.scope, .never, tmp.allocator());
                ty_gen.vars = self.vars;
                ty_gen.cmptime_values = self.cmptime_values;
                ty_gen.frozen_vars = self.vars.len;
                _ = ty_gen.bl.begin(.systemv, undefined);

                break :b (try ty_gen.expr(.{}, lex)).ty;
            };

            break :d self.tyLit(pos, ty);
        },
        .CurrentScope => self.tyLit(pos, self.scope.data()
            .findCurrentScope(self.types)),
        .RootScope => self.tyLit(pos, hb.frontend.DeclIndex.File.Id
            .root.getScope(self.types)),
        .ChildOf => {
            const oper = try self.typ(lex);
            break :d self.tyLit(pos, oper.child(self.types) orelse
                return self.report(pos, "{} does not have a child, only" ++
                    " pointers, slices, options, and arrays have", .{oper}));
        },
        .float_to_int => {
            const oper = try self.expr(.{}, lex);

            const ret: Types.Id = .int;

            if (!oper.ty.isBuiltin(.isFloat))
                return self.report(pos, "expected float," ++
                    " {} is not", .{oper.ty});

            break :d .value(ret, self.bl.addUnOp(
                slc,
                .fti,
                .i64,
                oper.load(pos, self),
            ));
        },
        .int_to_float => {
            const res = try self.expectDestType(.int_to_float, pos, ctx.ty);

            if (!res.isBuiltin(.isFloat)) {
                return self.report(pos, "expected float dest type, {} is not", .{res});
            }

            const ps = lex.cursor;
            const oper = try self.typedExpr(.int, .{}, lex);

            break :d .value(res, self.bl.addUnOp(
                slc,
                .itf,
                Abi.categorizeBuiltinUnwrapped(res.data().Builtin),
                oper.load(ps, self),
            ));
        },
        .float_cast => {
            const oper = try self.expr(.{}, lex);

            var ret: Types.Id = .f32;
            if (!oper.ty.isBuiltin(.isFloat))
                return self.report(pos, "expected float, {} is on", .{oper.ty});

            if (oper.ty == .f32) ret = .f64;

            break :d .value(ret, self.bl.addUnOp(
                self.sloc(tok.pos),
                .fcst,
                Abi.categorizeBuiltinUnwrapped(ret.data().Builtin),
                oper.load(pos, self),
            ));
        },
        .int_cast => {
            var oper = try self.expr(.{}, lex);

            const ret = try self.expectDestType(.int_cast, pos, ctx.ty);

            if (!ret.isBuiltin(.isInteger)) {
                return self.report(pos, "inferred type must be an integer," ++
                    " {} is not", .{ret});
            }

            if (!oper.ty.isBuiltin(.isInteger)) {
                return self.report(pos, "expeced integer, {} is not", .{oper.ty});
            }

            if (oper.ty.size(self.types) < ret.size(self.types)) {
                break :d .value(ret, self.bl.addUnOp(
                    slc,
                    if (oper.ty.isBuiltin(.isSigned)) .sext else .uext,
                    Abi.categorizeBuiltinUnwrapped(ret.data().Builtin),
                    oper.load(pos, self),
                ));
            }

            if (oper.ty.size(self.types) > ret.size(self.types)) {
                break :d .value(ret, self.bl.addUnOp(
                    slc,
                    .ired,
                    Abi.categorizeBuiltinUnwrapped(ret.data().Builtin),
                    oper.load(pos, self),
                ));
            }

            oper.ty = ret;
            break :d oper;
        },
        .bit_cast => {
            const res = try self.expectDestType(.bit_cast, pos, ctx.ty);

            var oper = try self.expr(.{}, lex);

            if (oper.ty.size(self.types) != res.size(self.types)) {
                return self.report(pos, "can't bitcast from {} to {}," ++
                    " sizes don't match ({} != {})", .{
                    oper.ty,
                    res,
                    oper.ty.size(self.types),
                    res.size(self.types),
                });
            }

            break :d switch (oper.normalized(pos, self)) {
                .empty => .unit(res),
                .value => |v| if (res.isScalar(self.types))
                    if (res.isBuiltin(.isFloat) != oper.ty.isBuiltin(.isFloat))
                        .value(res, self.bl.addCast(
                            slc,
                            self.types.abi.categorizeAssumeReg(res, self.types),
                            v,
                        ))
                    else
                        .value(res, v)
                else
                    .ptr(res, self.bl.addSpill(slc, v, res.raw())),
                .ptr => |p| if (res.isScalar(self.types))
                    .value(res, self.bl.addLoad(
                        slc,
                        p,
                        self.types.abi.categorizeAssumeReg(res, self.types),
                    ))
                else
                    .ptr(res, p),
            };
        },
        .len_of, .align_of, .size_of, .kind_of, .decl_count_of => {
            var res = ctx.ty orelse .uint;
            if (!res.isBuiltin(.isInteger)) res = .uint;

            const ty = try self.typ(lex);

            break :d .value(res, self.bl.addIntImm(
                self.sloc(tok.pos),
                Abi.categorizeBuiltinUnwrapped(res.data().Builtin),
                switch (d) {
                    .size_of => ty.size(self.types),
                    .align_of => ty.alignment(self.types),
                    .len_of => ty.len(self.types),
                    .kind_of => @intFromEnum(ty.data()),
                    .decl_count_of => if (ty.data()
                        .downcast(Types.UnorderedScope)) |v|
                        @intCast(v.decls(self.types).entries.len)
                    else
                        0,
                    else => unreachable,
                },
            ));
        },
        .as => {
            const ty = try self.typ(lex);
            try self.expectNext(iter);
            break :d try self.typedExpr(ty, .{ .loc = ctx.loc }, lex);
        },
        .eval => {
            const vpos = lex.cursor;
            const value = try self.expr(.{}, lex);
            const ct = self.peval(vpos, value, Types.ComptimeValue) catch break :d .never;
            break :d self.ctValueToValue(pos, value.ty, ct);
        },
        .target => {
            const pat = try self.expect(lex, .@"\"", "to define the triple pattern");
            const content = lex.source[pat.pos + 1 .. pat.end - 1];
            const triple = self.types.target;
            const matched = matchTriple(content, triple) catch |err| {
                return self.report(pat.pos, "{}", .{@errorName(err)});
            };
            break :d .value(.bool, self.bl.addIntImm(slc, .i8, @intFromBool(matched)));
        },
        .syscall, .ecall => {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            comptime if (hb.x86_64.X86_64Gen.syscall != hb.hbvm.HbvmGen.eca) unreachable;

            const ret = try self.expectDestType(.syscall, pos, ctx.ty);
            var call = self.bl.addCall(
                tmp.arena,
                self.sloc(pos),
                .systemv,
                .{ .special = hb.x86_64.X86_64Gen.syscall },
            );

            var buf = Abi.Buf{};
            const ret_cata = self.types.abi.categorize(ret, self.types, &buf);

            while (iter.next()) {
                const prev_len = call.abi_params.items.len;
                const ty = self.passArg(&call, .{ .to_compute = .{ .lex = lex } }) catch continue;
                if (call.abi_params.items.len - prev_len != 1 or
                    call.abi_params.items[prev_len] != .Reg)
                {
                    self.report(pos, "{} can not be passed by single register but" ++
                        " syscall/ecall call convention does not allow that", .{ty}) catch {};
                }
            }

            if (self.types.abi.isRetByRef(ret_cata)) {
                return self.report(pos, "{} needs to be passed by stack but" ++
                    " syscall call convention does not allow that", .{ret});
            }

            return try self.endCall(&call, pos, ret_cata, ret, undefined);
        },
        .@"inline" => {
            const fn_arg = try self.expr(.{}, lex);
            return self.emitCall(pos, ctx, null, fn_arg, lex);
        },
        .frame_pointer => .value(.uint, self.bl.addFramePointer(slc, .i64)),
        .has_decl => {
            const ty = try self.typ(lex);
            try self.expectNext(iter);

            const name = try self.expect(lex, .@"\"", "to indicate the decl name");
            var str_name = name.view(lex.source);
            str_name = str_name[1 .. str_name.len - 1];

            const unoscope = ty.data().downcast(Types.UnorderedScope) orelse {
                break :d .value(.bool, self.bl.addIntImm(slc, .i8, 0));
            };

            const scope_file = unoscope.scope(self.types).file.get(self.types).source;
            const has = unoscope.decls(self.types).lookup(scope_file, str_name) != null;

            break :d .value(.bool, self.bl.addIntImm(slc, .i8, @intFromBool(has)));
        },
        .alloc_global => {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var call = self.bl.addCall(
                tmp.arena,
                slc,
                .ablecall,
                .{ .sym = comptime_only_fn },
            );

            const generic_return = self.types.sliceOf(.u8);
            var buf = Abi.Buf{};
            const ret_cata = Abi.ableos.categorize(generic_return, self.types, &buf);

            var slot: *BNode = undefined;
            if (Abi.ableos.isMultivalue(ret_cata)) {
                slot = self.emitLoc(pos, generic_return, ctx);
            }

            if (Abi.ableos.isRetByRef(ret_cata)) {
                unreachable; // TODO
            }

            const op_cnst = self.bl.addIntImm(slc, .i64, @intFromEnum(ComptimeEca.alloc_global));
            call.pushArg(&self.bl, slc, .{ .Reg = .i64 }, op_cnst, 0);

            const ty = try self.passArg(&call, .{ .to_compute = .{ .lex = lex, .inferred = null } });
            if (ty.data() != .Slice) {
                return self.report(pos, "{} is not a slice", .{ty});
            }

            const ty_slot = self.bl.addIntImm(slc, .i64, @intFromEnum(ty.data().Slice.get(self.types).elem));
            call.pushArg(&self.bl, slc, .{ .Reg = .i64 }, ty_slot, 0);

            break :d try self.endCall(&call, slc.index, ret_cata, ty, slot);
        },
        else => {
            lex.eatUntilClosingDelimeter();
            return self.report(tok.pos, "unexpected directive", .{});
        },
    };

    try self.expectEnd(iter);

    return value;
}

pub fn matchTriple(pattern: []const u8, triple: []const u8) !bool {
    // CAUTION: written by LLM

    if (std.mem.eql(u8, pattern, "*")) {
        return error.@"you can replace this with 'true'";
    }

    if (std.mem.endsWith(u8, pattern, "-*")) {
        return error.@"trailing '*' is redundant";
    }

    var matcher = std.mem.splitScalar(u8, pattern, '-');
    var matchee = std.mem.splitScalar(u8, triple, '-');
    var eat_start = false;

    while (matcher.next()) |pat| {
        if (std.mem.eql(u8, pat, "*")) {
            if (eat_start) {
                return error.@"consecutive '*' are redundant";
            }
            if (matchee.next() == null) {
                return false;
            }
            eat_start = true;
        } else if (eat_start) {
            var found = false;
            while (matchee.next()) |v| {
                if (std.mem.eql(u8, v, pat)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                return false;
            }
        } else if (!std.mem.eql(u8, matchee.next() orelse return false, pat)) {
            return false;
        }
    }

    return true;
}

test "sanity match triple" {
    try std.testing.expect(try matchTriple("a-b-c", "a-b-c"));
    try std.testing.expect(try matchTriple("hbvm-ableos", "hbvm-ableos"));
    try std.testing.expect(try matchTriple("*-b-c", "a-b-c"));
    try std.testing.expect(try matchTriple("*-c", "a-b-c"));
    try std.testing.expect(try matchTriple("a", "a-b-c"));
    try std.testing.expect(!try matchTriple("*-a", "a-b-c"));
    try std.testing.expectError(error.@"consecutive '*' are redundant", matchTriple("*-*-a", "a-b-c"));
    try std.testing.expectError(error.@"trailing '*' is redundant", matchTriple("*-b-*", "a-b-c"));
}

pub fn ctValueToValue(self: *Codegen, pos: u32, ty: Types.Id, ct: Types.ComptimeValue) Value {
    return switch (self.ctValueToNorm(pos, ty, ct)) {
        .empty => .unit(ty),
        .value => |v| .value(ty, v),
        .ptr => |p| .ptr(ty, p),
    };
}

pub fn ctValueToNorm(self: *Codegen, pos: u32, ty: Types.Id, ct: Types.ComptimeValue) NormalizedNode {
    if (ty.size(self.types) > @sizeOf(Types.ComptimeValue)) {
        return .{ .ptr = self.bl.addBinOp(
            self.sloc(pos),
            .iadd,
            .i64,
            self.bl.addGlobalAddr(self.sloc(pos), @intFromEnum(ct.spilled.id)),
            self.bl.addIntImm(self.sloc(pos), .i64, ct.spilled.off),
        ) };
    } else {
        const cata = self.types.abi.tryCategorizeReg(ty, self.types) orelse return .empty;
        return .{ .value = self.bl.addIntImm(self.sloc(pos), cata, ct.@"inline") };
    }
}

pub fn accessStructField(self: *Codegen, pos: u32, base: Value, lfield: Types.Struct.Layout.Field) Value {
    var res: Value = switch (lfield.ty.category(self.types)) {
        .Impossible => .unit(lfield.ty),
        .Imaginary => .unit(lfield.ty),
        .Scalar, .Stack => switch (base.normalized(pos, self)) {
            .empty => unreachable,
            .value => |v| if (self.types.abi.tryCategorizeReg(lfield.ty, self.types)) |r|
                .value(
                    lfield.ty,
                    self.bl.addBitFieldLoad(
                        self.sloc(pos),
                        v,
                        lfield.offset,
                        r,
                    ),
                )
            else
                .unit(lfield.ty),
            .ptr => |p| .ptr(
                lfield.ty,
                self.bl.addFieldOffset(self.sloc(pos), p, lfield.offset),
            ),
        },
    };

    res.normalize(self);

    return res;
}

pub const SuffixCtx = struct { Lexer.Token, Lexer.Token, u8, Ctx, *?LLValue, bool };

pub fn suffix(self: *Codegen, sctx: SuffixCtx, lex: *Lexer, res: *LLValue) SuffixError!void {
    const tok, const top, const prevPrec, const ctx, const ass_lhs, const is_ass_op = sctx;

    switch (top.kind) {
        .@"." => {
            const field = try self.expect(lex, .Ident, "to access a field");

            if (res.value.ty == .type) {
                const scope_ty = try self.peval(top.pos, res.value, Types.Id);

                const scope = scope_ty.data().downcast(Types.AnyScope) orelse {
                    return self.report(top.pos, "{} does not support field access", .{scope_ty});
                };

                res.set(self.lookupIdentDotted(scope.pack(), field.view(lex.source)) orelse {
                    return self.report(field.pos, "{} does not have this declaration", .{scope_ty});
                });
            } else if (lex.eatMatch(.@"(")) {
                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();

                var scope = res.value.ty;
                if (res.value.ty.data() == .Pointer) {
                    scope = res.value.ty.data().Pointer.get(self.types).ty;
                }

                const ascope = scope.data().downcast(Types.AnyScope) orelse {
                    lex.eatUntilClosingDelimeter();
                    return self.report(top.pos, "can't dispatch a function on {}", .{scope});
                };

                var field_idx: ?usize = null;
                if (ascope == .Struct) {
                    field_idx = ascope.Struct.get(self.types)
                        .lookupField(self.types, field.view(lex.source));

                    if (field_idx != null and res.value.ty.data() == .Pointer) {
                        res.set(.ptr(
                            res.value.ty.data().Pointer.get(self.types).ty,
                            res.value.load(top.pos, self),
                        ));
                    }
                }

                const value = if (field_idx) |i|
                    self.accessStructField(
                        field.pos,
                        res.value,
                        ascope.Struct.get(self.types).getLayout(self.types).fields[i],
                    )
                else
                    self.lookupIdentDotted(ascope.pack(), field.view(lex.source)) orelse {
                        lex.eatUntilClosingDelimeter();
                        return self.report(top.pos, "{} does not define this", .{scope});
                    };

                res.set(try self.emitCall(field.pos, ctx, if (field_idx != null) null else res, value, lex));
            } else {
                if (res.value.ty.data() == .Pointer) {
                    res.set(.ptr(
                        res.value.ty.data().Pointer.get(self.types).ty,
                        res.value.load(top.pos, self),
                    ));
                }

                switch (res.value.ty.data()) {
                    .Option => return self.report(
                        field.pos,
                        "options must be unwrapped in order to access fields," ++
                            " use <expr>.?.<field> if applicable",
                        .{},
                    ),
                    .Builtin => |b| switch (b) {
                        .never => {
                            return self.silentReport();
                        },
                        else => return self.report(field.pos, "TODO: {}", .{b}),
                    }, // TODO
                    .Pointer => return self.report(
                        field.pos,
                        "double pointer indirection cannot be auto-dereferenced",
                        .{},
                    ),
                    .Array => |a| {
                        if (std.mem.eql(u8, field.view(lex.source), "len")) {
                            res.set(.value(.uint, self.bl.addIntImm(
                                self.sloc(top.pos),
                                .i64,
                                a.get(self.types).len.s,
                            )));
                        } else if (std.mem.eql(u8, field.view(lex.source), "ptr")) {
                            res.set(.value(
                                self.types.pointerTo(a.get(self.types).elem),
                                try res.value.asPtr(top.pos, self),
                            ));
                        } else {
                            return self.report(field.pos, "{} only has `len` field", .{res.value.ty});
                        }
                    },
                    .FuncTy => return self.report(field.pos, "{} doesn't have fields", .{res.value.ty}),
                    .Slice => |s| {
                        const ptr = res.value.normalized(top.pos, self).ptr;
                        if (std.mem.eql(u8, field.view(lex.source), "len")) {
                            res.set(.ptr(
                                .uint,
                                self.bl.addFieldOffset(self.sloc(top.pos), ptr, Types.Slice.len_offset),
                            ));
                        } else if (std.mem.eql(u8, field.view(lex.source), "ptr")) {
                            res.set(.ptr(
                                self.types.pointerTo(s.get(self.types).elem),
                                self.bl.addFieldOffset(self.sloc(top.pos), ptr, Types.Slice.ptr_offset),
                            ));
                        } else {
                            return self.report(field.pos, "{} only has `len` and `ptr` fields", .{res.value.ty});
                        }
                    },
                    .Enum => return self.report(field.pos, "{} is an enum, enums dont have fields", .{res.value.ty}),
                    .Struct => |s| {
                        const index = s.get(self.types).lookupField(
                            self.types,
                            field.view(lex.source),
                        ) orelse {
                            return self.report(field.pos, "undefined field on {}, TODO: list fields", .{res.value.ty});
                        };
                        const lfield = s.get(self.types).getLayout(self.types).fields[index];

                        res.set(self.accessStructField(field.pos, res.value, lfield));
                    },
                    .Union => |u| {
                        const index = u.get(self.types).lookupField(
                            self.types,
                            field.view(lex.source),
                        ) orelse {
                            return self.report(field.pos, "undefined field on {}, TODO: list fields", .{res.value.ty});
                        };
                        const lfield = u.get(self.types).getLayout(self.types).fields[index];

                        res.set(self.accessStructField(
                            field.pos,
                            res.value,
                            .{ .offset = 0, .ty = lfield, .default = .invalid },
                        ));
                    },
                }
            }
        },
        .@".?" => {
            if (res.value.ty.data() != .Option) {
                if (res.value.ty == .never) return self.silentReport();
                return self.report(top.pos, "{} is not optional", .{res.value.ty});
            }

            if (self.types.handlers.get(.null_unwrap).asOpt()) |handler| {
                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();

                const cond = self.emitOptionCheck(top.pos, .@"==", res.value);
                var hbl = self.addHandler(top.pos, handler, cond, tmp.arena);
                hbl.end(self);
            }

            res.set(try self.emitOptionUnwrap(top.pos, res.value));
        },
        .@".*" => {
            if (res.value.ty.data() != .Pointer) {
                if (res.value.ty == .never) return self.silentReport();
                return self.report(top.pos, "{} is not a pointer", .{res.value.ty});
            }

            res.set(.ptr(
                res.value.ty.data().Pointer.get(self.types).ty,
                res.value.load(top.pos, self),
            ));
        },
        .@".(" => {
            const ty = try self.peval(tok.pos, res.value, Types.Id);
            res.set(try self.tupl(top.pos, lex, ty, ctx));
        },
        .@".{" => {
            const ty = try self.peval(tok.pos, res.value, Types.Id);
            res.set(try self.ctor(top.pos, ctx, ty, lex));
        },
        .@"[" => {
            var index: ?LLValue = null;
            defer if (index) |*i| i.deinit(self);
            var end_index: ?LLValue = null;
            defer if (end_index) |*i| i.deinit(self);
            var is_slice = false;

            if (!lex.eatMatch(.@"..")) {
                index = .init(top.pos, try self.typedExprPrec(
                    .uint,
                    .{},
                    lex,
                    Lexer.Lexeme.@"..".precedence(false),
                ));
            } else {
                if (lex.peekNext().kind != .@"]") {
                    end_index = .init(top.pos, try self.typedExpr(
                        .uint,
                        .{},
                        lex,
                    ));
                }
                is_slice = true;
            }

            if (lex.eatMatch(.@"..")) {
                if (lex.peekNext().kind != .@"]") {
                    end_index = .init(top.pos, try self.expr(
                        .{ .ty = .uint },
                        lex,
                    ));
                }
                is_slice = true;
            }

            _ = try self.expect(lex, .@"]", "to close the indexing");

            const can_be_indexed = switch (res.value.ty.data()) {
                .Builtin, .FuncTy, .Enum, .Option, .Union => res.value.ty == .type,
                .Pointer, .Slice, .Array => true,
                .Struct => !is_slice,
            };

            if (!can_be_indexed) {
                return self.report(top.pos, "{} can not be indexed", .{res.value.ty});
            }

            if (is_slice) {
                const Slicable = union(enum(u8)) {
                    Pointer: Types.PointerId = Types.Data.index_start,
                    Slice: Types.SliceId,
                    Array: Types.ArrayId,
                };

                const slc = res.value.ty.data().downcast(Slicable).?;

                var elem = switch (slc) {
                    .Pointer => |p| p.get(self.types).ty,
                    .Slice => |s| s.get(self.types).elem,
                    .Array => |a| a.get(self.types).elem,
                };

                var ptr = switch (slc) {
                    .Pointer => res.load(self),
                    .Slice => self.bl.addFieldLoad(
                        self.sloc(top.pos),
                        res.value.normalized(top.pos, self).ptr,
                        Types.Slice.ptr_offset,
                        .i64,
                    ),
                    .Array => try res.value.asPtr(top.pos, self),
                };

                if (index) |vl| {
                    ptr = self.bl.addIndexOffset(
                        self.sloc(top.pos),
                        ptr,
                        .iadd,
                        elem.size(self.types),
                        vl.load(self),
                    );
                }

                var lock = ptr.lock();
                defer lock.unlock();

                var len = if (end_index) |ei|
                    ei.load(self)
                else switch (slc) {
                    .Pointer => return self.report(
                        top.pos,
                        "pointer slice requires an end index",
                        .{},
                    ),
                    .Slice => self.bl.addFieldLoad(
                        self.sloc(top.pos),
                        res.value.normalized(top.pos, self).ptr,
                        Types.Slice.len_offset,
                        .i64,
                    ),
                    .Array => |a| self.bl.addIntImm(
                        self.sloc(top.pos),
                        .i64,
                        a.get(self.types).len.s,
                    ),
                };

                len.lockTmp();

                if (self.types.handlers.get(.slice_ioob).asOpt()) |ioob_handler| handler: {
                    var tmp = utils.Arena.scrath(null);
                    defer tmp.deinit();

                    const last_idx = end_index orelse index orelse break :handler;

                    var cond = self.bl.addBinOp(
                        self.sloc(top.pos),
                        .ugt,
                        .i64,
                        last_idx.load(self),
                        len,
                    );

                    if (index) |vl| if (end_index) |evl| {
                        cond = self.bl.addBinOp(
                            self.sloc(top.pos),
                            .bor,
                            .i8,
                            cond,
                            self.bl.addBinOp(
                                self.sloc(top.pos),
                                .ule,
                                .i64,
                                vl.load(self),
                                evl.load(self),
                            ),
                        );
                    };

                    var handler = self.addHandler(top.pos, ioob_handler, cond, tmp.arena);
                    handler.pushArg(self, len);
                    handler.pushArg(self, if (index) |i|
                        i.load(self)
                    else
                        self.bl.addIntImm(self.sloc(top.pos), .i64, 0));
                    handler.pushArg(self, if (end_index) |i| i.load(self) else len);
                    handler.end(self);
                }

                len.unlockTmp();

                if (index) |vl| {
                    len = self.bl.addBinOp(
                        self.sloc(top.pos),
                        .isub,
                        .i64,
                        len,
                        vl.load(self),
                    );
                }

                const ty = self.types.sliceOf(elem);
                const slot = self.emitLoc(top.pos, ty, ctx);

                self.bl.addFieldStore(
                    self.sloc(top.pos),
                    slot,
                    Types.Slice.len_offset,
                    .i64,
                    len,
                );
                self.bl.addFieldStore(
                    self.sloc(top.pos),
                    slot,
                    Types.Slice.ptr_offset,
                    .i64,
                    ptr,
                );

                res.set(.ptr(ty, slot));
            } else switch (res.value.ty.data()) {
                .Builtin, .FuncTy, .Enum, .Option, .Union => {
                    std.debug.assert(res.value.ty == .type);

                    const ty = try self.peval(top.pos, res.value, Types.Id);
                    const idx = try self.peval(index.?.pos, index.?.value, i64);

                    const unor = ty.data().downcast(Types.UnorderedScope) orelse {
                        return self.report(
                            top.pos,
                            "{} can not be indexed for declarations",
                            .{ty},
                        );
                    };

                    const decls = unor.decls(self.types);
                    if (idx < 0 or idx >= decls.entries.len) {
                        return self.report(
                            top.pos,
                            "{} only has {} declarations",
                            .{ ty, decls.entries.len },
                        );
                    }

                    const decl_off = decls.entries.get(@intCast(idx)).offset.offset;
                    const decl_name = Lexer.peekStr(unor.scope(self.types)
                        .file.get(self.types).source, decl_off);

                    res.set(self.lookupIdent(
                        unor.upcast(Types.AnyScope).pack(),
                        decl_name,
                    ).?);
                },
                .Pointer => |p| {
                    res.set(.ptr(
                        p.get(self.types).ty,
                        self.bl.addIndexOffset(
                            self.sloc(top.pos),
                            res.load(self),
                            .iadd,
                            p.get(self.types).ty.size(self.types),
                            index.?.load(self),
                        ),
                    ));
                },
                .Slice => |s| {
                    var cpy = res.value;
                    cpy.ty = .uint;
                    const ptr = cpy.load(top.pos, self);

                    if (self.types.handlers.get(.slice_ioob).asOpt()) |ioob| {
                        var tmp = utils.Arena.scrath(null);
                        defer tmp.deinit();

                        const len = self.bl.addFieldLoad(
                            self.sloc(top.pos),
                            res.value.normalized(top.pos, self).ptr,
                            Types.Slice.len_offset,
                            .i64,
                        );
                        const cond = self.bl.addBinOp(
                            self.sloc(top.pos),
                            .uge,
                            .i64,
                            index.?.load(self),
                            len,
                        );
                        var handler = self.addHandler(top.pos, ioob, cond, tmp.arena);
                        handler.pushArg(self, len);
                        handler.pushArg(self, index.?.load(self));
                        handler.pushArg(self, index.?.load(self));
                        handler.end(self);
                    }

                    res.set(.ptr(
                        s.get(self.types).elem,
                        self.bl.addIndexOffset(
                            self.sloc(top.pos),
                            ptr,
                            .iadd,
                            s.get(self.types).elem.size(self.types),
                            index.?.load(self),
                        ),
                    ));
                },
                .Array => |a| ax: {
                    if (a.get(self.types).len.s == 0) {
                        return self.report(top.pos, "can't index empty array", .{});
                    }

                    const elem = a.get(self.types).elem;

                    if (self.types.handlers.get(.slice_ioob).asOpt()) |ioob| {
                        var tmp = utils.Arena.scrath(null);
                        defer tmp.deinit();

                        const len = self.bl.addIntImm(
                            self.sloc(top.pos),
                            .i64,
                            a.get(self.types).len.s,
                        );
                        const cond = self.bl.addBinOp(
                            self.sloc(top.pos),
                            .uge,
                            .i64,
                            index.?.load(self),
                            len,
                        );
                        var handler = self.addHandler(top.pos, ioob, cond, tmp.arena);
                        handler.pushArg(self, len);
                        handler.pushArg(self, index.?.load(self));
                        handler.pushArg(self, index.?.load(self));
                        handler.end(self);
                    }

                    const ptr = switch (res.value.normalized(top.pos, self)) {
                        .empty => self.bl.addUninit(self.sloc(top.pos), .i64),
                        .value => |v| {
                            res.set(.value(elem, self.bl.addBitIndexLoad(
                                self.sloc(top.pos),
                                v,
                                index.?.load(self),
                                self.types.abi.categorizeAssumeReg(elem, self.types),
                            )));
                            break :ax;
                        },
                        .ptr => |p| p,
                    };

                    res.set(.ptr(
                        elem,
                        self.bl.addIndexOffset(
                            self.sloc(top.pos),
                            ptr,
                            .iadd,
                            elem.size(self.types),
                            index.?.load(self),
                        ),
                    ));
                },
                .Struct => |s| {
                    const idx = index orelse return self.report(
                        top.pos,
                        "structs can not be sliced",
                        .{},
                    );
                    index.?.deinitKeep();
                    index = null;

                    const i = try self.peval(top.pos, idx.value, i64);

                    const layout = s.get(self.types).getLayout(self.types);
                    if (i < 0 or i >= layout.fields.len) {
                        return self.report(top.pos, "index out of bounds", .{});
                    }
                    const field = layout.fields[@intCast(i)];

                    res.set(self.accessStructField(top.pos, res.value, field));
                },
            }

            res.normalize(self);
        },
        .@".[" => {
            const elem = self.peval(top.pos, res.value, Types.Id) catch |err| {
                lex.eatUntilClosingDelimeter();
                return err;
            };

            var loc = ctx.loc;
            if (ctx.ty) |t| {
                if (t.data() != .Array) loc = null;
            }

            const slot = loc orelse self.bl.addLocal(self.sloc(top.pos), 0, std.math.maxInt(u32));

            var list = lex.list(.@",", .@"]");
            var offset: Types.Size = 0;
            var i: Types.Size = 0;
            while (list.next()) : (i += 1) {
                const eloc = self.bl.addFieldOffset(self.sloc(top.pos), slot, offset);
                const value = self.typedExpr(elem, .{ .loc = eloc }, lex) catch {
                    if (list.recover()) break else continue;
                };
                self.emitGenericStore(top.pos, eloc, value);

                offset += elem.size(self.types);
            }

            const ty = self.types.arrayOf(elem, i);
            if (loc == null) {
                self.bl.resizeLocal(slot, ty.size(self.types), @intFromEnum(ty));
            }

            res.set(.ptr(ty, slot));
            res.normalize(self);
        },
        .@"(" => {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            res.set(try self.emitCall(top.pos, ctx, null, res.value, lex));
        },
        .@"=" => {
            const value = try self.typedExprPrec(res.value.ty, .{
                .loc = switch (res.value.normalized(tok.pos, self)) {
                    .ptr => |p| p,
                    else => null,
                },
            }, lex, prevPrec);

            try self.assign(top.pos, res.value, value);

            res.set(.voidv);
        },
        .@":", .@":=" => {
            var ty: ?Types.Id = null;
            var eq = top;

            if (top.kind == .@":") {
                ty = self.typ(lex) catch .never;
                eq = try self.expect(lex, .@"=", " to assign a value");
            }

            const index = switch (res.value.node()) {
                .variable => |i| i,
                .value, .ptr, .empty => return self.report(tok.pos, "" ++
                    "can't use this as an identifier (DEBUG: {})", .{res.value.tag}),
            };

            const slot: *Variable = &self.vars.items(.variable)[index];
            if (slot.value != std.math.maxInt(u32)) {
                self.report(top.pos, "can't shadow the existing" ++
                    " declaration", .{}) catch {};
                self.report(slot.meta.pos, "...the existing" ++
                    " declaration", .{}) catch {};
                // NOTE: we dont throw, just shadow it
            }

            self.name = @enumFromInt(slot.meta.pos);

            var value = try self.exprPrec(.{ .ty = ty }, lex, prevPrec);
            if (ty) |t| try self.typeCheck(eq.pos, .{}, &value, t);

            res.set(.voidv);
            if (ctx.in_if_or_while) unwrap: {
                if (value.ty.data() != .Option) {
                    self.report(top.pos, "{} is not optional", .{value.ty}) catch break :unwrap;
                }

                res.set(.value(.bool, self.emitOptionCheck(top.pos, .@"!=", value)));
                value = try self.emitOptionUnwrap(top.pos, value);
            }

            switch (value.normalized(tok.pos, self)) {
                .value, .empty => {},
                .ptr => |p| {
                    if (!isUniqueLocal(p)) {
                        if (value.ty.size(self.types) == 0) {
                            value = .unit(value.ty);
                        } else if (value.ty.isScalar(self.types)) {
                            value = .value(value.ty, value.load(eq.pos, self));
                        } else {
                            const loc = self.bl.addLocal(
                                self.sloc(top.pos),
                                value.ty.size(self.types),
                                @intFromEnum(value.ty),
                            );
                            self.emitGenericStore(eq.pos, loc, value);
                            value = .ptr(value.ty, loc);
                        }
                    }
                },
            }

            // could have been an error
            if (slot.value == std.math.maxInt(u32)) {
                self.declareVariable(eq.pos, index, value) catch {};
            }
        },
        .@"&&" => and_: {
            ass_lhs.* = res.dupe();

            try self.typeCheckLL(.{}, res, .bool);

            var if_bl = self.bl.addIfAndBeginThen(
                self.sloc(top.pos),
                res.load(self),
            );

            var alt = LLValue.init(
                lex.cursor,
                self.exprPrecAllowUnreachable(.{
                    .ty = .bool,
                    .in_if_or_while = ctx.in_if_or_while,
                }, lex, prevPrec) catch |err| switch (err) {
                    error.Unreachable => {
                        if_bl.end(&self.bl, if_bl.beginElse(&self.bl));

                        res.set(.value(.bool, self.bl.addIntImm(
                            self.sloc(top.pos),
                            .i8,
                            0,
                        )));

                        break :and_;
                    },
                    error.Report => self.emitUninitValue(top.pos, .bool),
                },
            );
            defer alt.deinit(self);

            alt.set(.value(.bool, alt.load(self)));

            if_bl.end(&self.bl, if_bl.beginElse(&self.bl));

            res.set(Value.value(.bool, self.bl.addPhi(
                self.sloc(top.pos),
                alt.load(self),
                self.bl.addIntImm(self.sloc(top.pos), .i8, 0),
            )));
        },
        .@"||" => or_: {
            ass_lhs.* = res.dupe();

            if (res.value.ty != .bool and res.value.ty.data() != .Option) {
                return self.report(top.pos, "{} is not a bool nor an optional", .{res.value.ty});
            }

            const is_unwrap = res.value.ty != .bool;
            var res_ty = res.value.ty;
            if (is_unwrap) res_ty = res_ty.data().Option.get(self.types).inner;

            if (res.value.ty.size(self.types) == 0) {
                res.set(try self.exprPrec(.{ .ty = res_ty }, lex, prevPrec));
                break :or_;
            }

            var if_bl = self.bl.addIfAndBeginThen(
                self.sloc(top.pos),
                if (is_unwrap)
                    self.emitOptionCheck(top.pos, .@"!=", res.value)
                else
                    res.load(self),
            );

            var unwrapped = LLValue.init(top.pos, res.value);
            defer unwrapped.deinitKeep();

            if (is_unwrap) {
                unwrapped.set(try self.emitOptionUnwrap(top.pos, unwrapped.value));
                if (res_ty.category(self.types) == .Scalar) {
                    unwrapped.set(.value(unwrapped.value.ty, unwrapped.load(self)));
                }
            }

            const tk = if_bl.beginElse(&self.bl);

            var alt = LLValue.init(
                lex.cursor,
                self.exprPrecAllowUnreachable(
                    .{ .ty = res_ty },
                    lex,
                    prevPrec,
                ) catch |err| switch (err) {
                    error.Unreachable => {
                        if_bl.end(&self.bl, tk);

                        if (is_unwrap) {
                            res.set(unwrapped.value);
                        } else {
                            res.set(.value(.bool, self.bl.addIntImm(
                                self.sloc(top.pos),
                                .i8,
                                0,
                            )));
                        }

                        break :or_;
                    },
                    error.Report => self.emitUninitValue(tok.pos, .bool),
                },
            );
            defer alt.deinit(self);

            if (is_unwrap) b: {
                if (alt.value.ty == res.value.ty) {
                    // we discard the unwrap, should be fine since it has no
                    // side effects
                    unwrapped.set(res.value);
                } else {
                    if (res_ty.isScalar(self.types)) {
                        alt.set(.value(res_ty, alt.load(self)));
                    }
                }

                if_bl.end(&self.bl, tk);

                const rhs_n = alt.value.normalized(top.pos, self);
                const lhs_vl, const rhs_vl = switch (unwrapped.value.normalized(top.pos, self)) {
                    .empty => {
                        std.debug.assert(rhs_n == .empty);
                        break :b;
                    },
                    .value => |v| .{ v, rhs_n.value },
                    .ptr => |p| .{ p, rhs_n.ptr },
                };

                const phi = self.bl.addPhi(self.sloc(top.pos), lhs_vl, rhs_vl);

                res.set(switch (rhs_n) {
                    .empty => unreachable,
                    .value => .value(alt.value.ty, phi),
                    .ptr => .ptr(alt.value.ty, phi),
                });
            } else {
                alt.set(.value(.bool, alt.load(self)));
                if_bl.end(&self.bl, tk);

                res.set(.value(.bool, self.bl.addPhi(
                    self.sloc(top.pos),
                    self.bl.addIntImm(self.sloc(top.pos), .i8, 0),
                    alt.load(self),
                )));
            }
        },
        else => op: {
            ass_lhs.* = res.dupe();

            if ((top.kind == .@"!=" or top.kind == .@"==") and lex.eatMatch(.null)) {
                std.debug.assert(!is_ass_op);

                if (res.value.ty.data() != .Option) {
                    if (res.value.ty == .never) return self.silentReport();
                    return self.report(top.pos, "{} can not be compared with null", .{res.value.ty});
                }

                res.set(.value(.bool, self.emitOptionCheck(
                    top.pos,
                    @enumFromInt(@intFromEnum(top.kind)),
                    res.value,
                )));

                break :op;
            }

            var check_point: ?u32 = lex.cursor;
            if ((top.kind == .@"!=" or top.kind == .@"==") and
                lex.eatMatch(.@"."))
            union_cmp: {
                std.debug.assert(!is_ass_op);

                const name = lex.expect(.Ident) catch break :union_cmp;

                if (res.value.ty.data() != .Union) break :union_cmp;

                const uni = res.value.ty.data().Union.get(self.types);

                const tag_layout = uni.getLayout(self.types).tagLayout() orelse break :union_cmp;

                const cmp_vl_idx = tag_layout.id.get(self.types)
                    .lookupField(self.types, name.view(lex.source)) orelse break :union_cmp;
                const cmp_vl = tag_layout.id.get(self.types)
                    .getLayout(self.types).fields[cmp_vl_idx];

                check_point = null;

                const tag = self.getUnionTag(top.pos, tag_layout, res.value);

                res.set(.value(.bool, self.bl.addBinOp(
                    self.sloc(top.pos),
                    if (top.kind == .@"==") .eq else .ne,
                    .i8,
                    tag,
                    self.bl.addIntImm(self.sloc(top.pos), tag.data_type, cmp_vl),
                )));

                break :op;
            }

            if (check_point) |c| {
                lex.cursor = c;
            }

            const vl = try self.exprPrec(.{ .ty = res.value.ty }, lex, prevPrec);
            var rhs = LLValue.init(lex.cursor, vl);
            defer rhs.deinit(self);

            if (res.value.ty == .never or rhs.value.ty == .never)
                return self.silentReport();

            if (res.value.ty.data() == .Pointer and
                (top.kind == .@"+" or top.kind == .@"-") and
                rhs.value.ty.isBuiltin(.isInteger))
            {
                const elem_ty = res.value.ty.data().Pointer.get(self.types).ty;

                res.set(Value.value(
                    res.value.ty,
                    self.bl.addIndexOffset(
                        self.sloc(top.pos),
                        res.load(self),
                        if (top.kind == .@"+") .iadd else .isub,
                        elem_ty.size(self.types),
                        rhs.load(self),
                    ),
                ));

                break :op;
            }

            if (res.value.ty.data() == .Pointer and
                rhs.value.ty.data() == .Pointer and
                top.kind != .@"-" and !top.kind.isComparison())
            {
                return self.report(top.pos, "pointers can only subtract from" ++
                    " each other, alternatively use @as(int, @bit_cast(expr))", .{});
            }

            var oper_ty = ctx.ty orelse res.value.ty;

            if (is_ass_op) oper_ty = res.value.ty;
            if (top.kind.isComparison()) oper_ty = res.value.ty;
            if (!res.value.ty.canUpcast(oper_ty, self.types)) {
                oper_ty = res.value.ty;
            }

            if (is_ass_op) {
                oper_ty = res.value.ty;
            } else {
                oper_ty = self.binOpUpcast(oper_ty, rhs.value.ty) catch {
                    return self.report(
                        top.pos,
                        "incompatible operands, {} {} {}",
                        .{ oper_ty, top.view(lex.source), rhs.value.ty },
                    );
                };
            }

            try self.typeCheckLL(.{}, res, oper_ty);
            try self.typeCheckLL(.{}, &rhs, oper_ty);

            var result: Types.Id = oper_ty;
            if (res.value.ty.data() == .Pointer) result = .int;
            if (top.kind.isComparison()) result = .bool;

            const op = try self.lexemeToBinOp(top.pos, top.kind, oper_ty);

            res.set(Value.value(result, self.bl.addBinOp(
                self.sloc(top.pos),
                op,
                Abi.categorizeBuiltinUnwrapped(result.data().Builtin),
                res.load(self),
                rhs.load(self),
            )));
            res.peep(self);
        },
    }
}

pub fn getUnionTag(
    self: *Codegen,
    pos: u32,
    tag_layout: Types.Union.Layout.TagLayout,
    res: Value,
) *BNode {
    const cmp_ty =
        Abi.categorizeBuiltinUnwrapped(
            tag_layout.id.get(self.types)
                .getLayout(self.types).backingInteger().data().Builtin,
        );

    const tag_vl = switch (res.normalized(pos, self)) {
        .empty => unreachable,
        .value => |v| self.bl.addBitFieldLoad(
            self.sloc(pos),
            v,
            tag_layout.offset,
            cmp_ty,
        ),
        .ptr => |p| self.bl.addFieldLoad(
            self.sloc(pos),
            p,
            tag_layout.offset,
            cmp_ty,
        ),
    };

    return tag_vl;
}

pub fn isUniqueLocal(ptr: *BNode) bool {
    if (ptr.kind != .Local) return false;

    for (ptr.outputs()) |o| {
        if (o.get().kind == .Scope) return false;
        if (!isOkayOp(o)) return false;
    }

    return true;
}

pub fn isOkayOp(o: BNode.Out) bool {
    if (o.get().kind == .BinOp) {
        for (o.get().outputs()) |oo| {
            if (!isOkayOp(oo)) return false;
        }
        return true;
    }

    if (o.get().kind == .Store and o.pos() == 2) return true;
    if (o.get().kind == .MemCpy and o.pos() == 2) return true;
    if (o.get().kind == .Call) return true;

    return false;
}

pub fn tupl(self: *Codegen, pos: u32, lex: *Lexer, ty: Types.Id, ctx: Ctx) !Value {
    const inner, const loc = self.emitLocHandleOpt(pos, ty, ctx);
    var iter = lex.list(.@",", .@")");
    var i: usize = 0;

    switch (inner.data()) {
        .Builtin, .Pointer, .Slice, .Array, .FuncTy, .Enum, .Option, .Union => {
            return self.report(pos, "cant infer the type of the tuple, use <ty>.(..)", .{});
        },
        .Struct => |s| {
            const layout = s.get(self.types).getLayout(self.types);
            while (iter.next()) : (i += 1) {
                if (layout.fields.len <= i) {
                    defer lex.eatUntilClosingDelimeter();
                    return self.report(lex.cursor, "too many values", .{});
                }

                const floc = self.bl.addFieldOffset(
                    self.sloc(pos),
                    loc,
                    layout.fields[i].offset,
                );
                const value = self.typedExpr(
                    layout.fields[i].ty,
                    .{ .loc = floc },
                    lex,
                ) catch |err| switch (err) {
                    error.Report => if (iter.recover()) break else continue,
                };
                self.emitGenericStore(pos, floc, value);
            }

            if (i < layout.fields.len) {
                return self.report(lex.cursor, "missing {} values", .{layout.fields.len - i});
            }
        },
    }

    var res = Value.ptr(ty, loc);
    res.normalize(self);
    return res;
}

pub fn ctor(self: *Codegen, pos: u32, ctx: Ctx, ty: Types.Id, lex: *Lexer) !Value {
    const inner, const slot = self.emitLocHandleOpt(pos, ty, ctx);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var field_iter = lex.list(.@",", .@"}");

    switch (inner.data()) {
        .Option, .Builtin, .FuncTy, .Pointer, .Array, .Slice, .Enum => return self.report(
            pos,
            "{} can not be initialized this way",
            .{ty},
        ),
        .Union => |u| {
            const uni = u.get(self.types);
            const layout = uni.getLayout(self.types);

            const name = try self.expect(lex, .Ident, "to select the union variant");
            const field_idx = uni.lookupField(self.types, name.view(lex.source)) orelse {
                return self.report(name.pos, "{} does not have this field", .{inner});
            };

            const value = if (lex.eatMatch(.@":"))
                try self.typedExpr(layout.fields[field_idx], .{ .loc = slot }, lex)
            else
                self.lookupIdent(self.scope, name.view(lex.source)) orelse {
                    return self.report(name.pos, "the identifier is not defined", .{});
                };
            self.emitGenericStore(name.pos, slot, value);

            _ = try self.expect(lex, .@"}", "to close union constructor");

            if (layout.tagLayout()) |tl| {
                const tlayout = tl.id.get(self.types).getLayout(self.types);
                const vl = tlayout.fields[field_idx];
                const t = Abi.categorizeBuiltinUnwrapped(tlayout.backingInteger().data().Builtin);
                self.bl.addFieldStore(
                    self.sloc(name.pos),
                    slot,
                    tl.offset,
                    t,
                    self.bl.addIntImm(self.sloc(name.pos), t, vl),
                );
            }
        },
        .Struct => |s| {
            const stru = s.get(self.types);
            const layout = stru.getLayout(self.types);
            var seen = std.DynamicBitSetUnmanaged
                .initEmpty(tmp.arena.allocator(), layout.fields.len) catch unreachable;

            while (field_iter.next()) {
                const field_name = lex.expect(.Ident) catch {
                    self.report(lex.cursor, "expected field name", .{}) catch {};
                    if (field_iter.recover()) break else continue;
                };

                const index = stru.lookupField(
                    self.types,
                    field_name.view(lex.source),
                ) orelse {
                    self.report(
                        lex.cursor,
                        "field does not exits, TODO: list fields",
                        .{},
                    ) catch {};
                    if (field_iter.recover()) break else continue;
                };
                const lfield = layout.fields[index];

                seen.set(index);

                const loc = self.bl.addFieldOffset(
                    self.sloc(field_name.pos),
                    slot,
                    lfield.offset,
                );
                const value = if (lex.eatMatch(.@":"))
                    self.expr(.{ .ty = lfield.ty, .loc = loc }, lex) catch |err| {
                        switch (err) {
                            error.Report => if (field_iter.recover()) break else continue,
                        }
                    }
                else
                    self.lookupIdent(self.scope, field_name.view(lex.source)) orelse {
                        self.report(
                            field_name.pos,
                            "the identifier is not defined",
                            .{},
                        ) catch {};
                        continue;
                    };
                self.emitGenericStore(field_name.end, loc, value);
            }

            errdefer comptime unreachable;

            var iter = seen.iterator(.{ .kind = .unset });
            while (iter.next()) |index| {
                const field = layout.fields[index];

                if (field.default != .invalid) {
                    const loc = self.bl.addFieldOffset(
                        self.sloc(pos),
                        slot,
                        field.offset,
                    );
                    const src = self.bl.addGlobalAddr(
                        self.sloc(pos),
                        @intFromEnum(field.default),
                    );
                    self.bl.addFixedMemCpy(
                        self.sloc(pos),
                        loc,
                        src,
                        field.ty.size(self.types),
                    );
                } else {
                    const field_name = stru.fieldName(self.types, index);
                    self.report(
                        pos,
                        "constructor is missin {} field",
                        .{field_name},
                    ) catch {};
                }
            }
        },
    }

    var res = Value.ptr(ty, slot);
    res.normalize(self);
    return res;
}

pub fn emitOptionUnwrap(self: *Codegen, pos: u32, res: Value) error{Unreachable}!Value {
    const ty = res.ty.data().Option.get(self.types).inner;

    if (res.ty.data().Option.get(self.types).getLayout(self.types).compact) {
        var cpy = res;
        cpy.ty = ty;
        return cpy;
    }

    return switch (res.normalized(pos, self)) {
        .empty => {
            self.bl.addTrap(self.sloc(pos), graph.infinite_loop_trap);
            return error.Unreachable;
        },
        .value => |v| if (self.types.abi.tryCategorizeReg(ty, self.types)) |r|
            .value(ty, self.bl.addUnOp(self.sloc(pos), .ired, r, v))
        else
            .unit(ty),
        .ptr => |p| .ptr(ty, p),
    };
}

pub const OptionCheckOp = enum(u16) {
    @"==" = @intFromEnum(Lexer.Lexeme.@"=="),
    @"!=" = @intFromEnum(Lexer.Lexeme.@"!="),
};

pub fn emitOptionCheck(self: *Codegen, pos: u32, op: OptionCheckOp, lhs: Value) *BNode {
    const opt = lhs.ty.data().Option.get(self.types);
    const layout = opt.getLayout(self.types);

    return switch (lhs.normalized(pos, self)) {
        .empty => self.bl.addIntImm(
            self.sloc(pos),
            .i8,
            @intFromBool(op == .@"=="),
        ),
        .value => |v| self.bl.addBinOp(
            self.sloc(pos),
            if (op == .@"==") .eq else .ne,
            .i8,
            self.bl.addBitFieldLoad(
                self.sloc(pos),
                v,
                layout.inner.offset,
                layout.inner.storage.dataType(),
            ),
            self.bl.addIntImm(
                self.sloc(pos),
                layout.inner.storage.dataType(),
                0,
            ),
        ),
        .ptr => |p| self.bl.addBinOp(
            self.sloc(pos),
            if (op == .@"==") .eq else .ne,
            .i8,
            self.bl.addFieldLoad(
                self.sloc(pos),
                p,
                layout.inner.offset,
                layout.inner.storage.dataType(),
            ),
            self.bl.addIntImm(self.sloc(pos), layout.inner.storage.dataType(), 0),
        ),
    };
}

pub fn exprPrec(self: *Codegen, ctx: Ctx, lex: *Lexer, prevPrec: u8) error{Report}!Value {
    return self.exprPrecAllowUnreachable(ctx, lex, prevPrec) catch |err| switch (err) {
        error.Unreachable => return self.report(lex.cursor, "terminating expression not allowed", .{}),
        error.Report => return error.Report,
    };
}

pub fn branchExpr(self: *Codegen, lex: *Lexer) bool {
    const pos = lex.cursor;
    var value = self.exprAllowUnreachable(.{ .ty = .void }, lex) catch |err| {
        return err == error.Unreachable;
    };
    self.typeCheck(pos, .{}, &value, .void) catch {};
    return false;
}

pub fn exprAllowUnreachable(self: *Codegen, ctx: Ctx, lex: *Lexer) UnreachableErr!Value {
    return self.exprPrecAllowUnreachable(ctx, lex, 254);
}

pub fn exprPrecAllowUnreachable(self: *Codegen, ctx: Ctx, lex: *Lexer, prevPrec: u8) UnreachableErr!Value {
    const tok = lex.next();

    var res: LLValue = .init(tok.pos, self.unitExpr(tok, ctx, lex) catch |err| switch (err) {
        error.SyntaxError => return error.Report,
        error.Unreachable => return error.Unreachable,
        error.Report => .never,
    });
    defer res.deinitKeep();

    while (true) {
        var top = lex.peekNext();

        const prec = top.kind.precedence(ctx.in_if_or_while);
        if (prec >= prevPrec) break;

        var is_ass_op = false;
        if (top.kind.innerOp()) |op| {
            top.kind = op;
            is_ass_op = true;
        }

        lex.cursor = top.end;

        var ass_lhs: ?LLValue = null;

        self.suffix(.{
            tok, top, prec, ctx, &ass_lhs, is_ass_op,
        }, lex, &res) catch |err| switch (err) {
            error.SyntaxError => return error.Report,
            error.Unreachable => return error.Unreachable,
            error.Report => {
                res.set(.never);
            },
        };

        if (ass_lhs) |*lhs| {
            if (is_ass_op) {
                try self.assign(top.pos, lhs.value, res.value);
                res.set(.voidv);
            }
            lhs.deinit(self);
        }
    }

    return res.value;
}

pub fn expectDestType(
    self: *Codegen,
    comptime dir_name: Lexer.Lexeme.Directive,
    pos: u32,
    ty: ?Types.Id,
) !Types.Id {
    return ty orelse return self.report(pos, "cant infer the result type," ++
        " use @as(<ty>, @" ++ @tagName(dir_name) ++ "(...))", .{});
}

pub fn expect(self: *Codegen, lex: *Lexer, comptime to_expect: Lexer.Lexeme, comptime msg: []const u8) error{SyntaxError}!Lexer.Token {
    return lex.expect(to_expect) catch {
        self.report(lex.cursor, "expected '" ++ @tagName(to_expect) ++
            "' " ++ msg, .{}) catch
            return error.SyntaxError;
    };
}

pub fn expectNext(self: *Codegen, iter: anytype) !void {
    if (!iter.next()) return self.report(iter.lexer.cursor, "expected nexti item", .{});
}

pub fn expectEnd(self: *Codegen, iter: anytype) !void {
    if (iter.next()) return self.report(iter.lexer.cursor, "expected list end", .{});
}

pub fn normalizeCaller(self: *Codegen, c: *LLValue, cty: Types.Id) !void {
    var caller_ty = cty;
    var auto_deref = true;
    if (caller_ty.data() == .Pointer) {
        caller_ty = caller_ty.data().Pointer.get(self.types).ty;
        auto_deref = false;
    }

    var auto_ref = true;
    if (c.value.ty.data() == .Pointer) {
        auto_ref = false;
        std.debug.assert(
            caller_ty == c.value.ty.data().Pointer.get(self.types).ty,
        );
    }

    if (auto_deref and !auto_ref) {
        c.set(.ptr(caller_ty, c.load(self)));
    } else if (!auto_deref and auto_ref) {
        c.set(.value(cty, try c.value.asPtr(c.pos, self)));
    }
}

pub fn passArg(
    self: *Codegen,
    call: *BBuilder.Call,
    value: union(enum) {
        computed: struct { value: Value, pos: u32 },
        to_compute: struct { lex: *Lexer, inferred: ?Types.Id = null },
    },
) Error!Types.Id {
    var vl: Value = undefined;

    const pos = switch (value) {
        .computed => |c| c.pos,
        .to_compute => |tc| tc.lex.cursor,
    };

    switch (value) {
        .computed => |v| {
            vl = v.value;
        },
        .to_compute => |tc| b: {
            vl.ty = tc.inferred orelse {
                vl = try self.expr(.{}, tc.lex);
                break :b;
            };
        },
    }

    var bf = Abi.Buf{};
    const splits = self.types.abi.categorize(vl.ty, self.types, &bf) orelse {
        return self.report(
            pos,
            "{} is uninhabited, can not be passed to the call",
            .{vl.ty},
        );
    };

    if (splits.len != 1 or splits[0] != .Stack) {
        switch (value) {
            .computed => {},
            .to_compute => |tc| {
                if (tc.inferred) |t| {
                    vl = try self.typedExpr(t, .{}, tc.lex);
                }
            },
        }

        if (splits.len == 0) {
            return vl.ty;
        }

        if (splits.len == 2) {
            const ptr = vl.normalized(pos, self).ptr;
            const first = self.bl.addLoad(self.sloc(pos), ptr, splits[0].Reg);
            call.pushArg(&self.bl, self.sloc(pos), splits[0], first, 0);
            const second = self.emitArbitraryLoad(
                pos,
                self.bl.addFieldOffset(self.sloc(pos), ptr, splits[0].Reg.size()),
                splits[1].Reg,
                vl.ty.size(self.types) - splits[0].Reg.size(),
            );
            call.pushArg(&self.bl, self.sloc(pos), splits[1], second, 0);
        } else if (splits[0] == .Reg) {
            std.debug.assert(splits.len == 1);
            call.pushArg(&self.bl, self.sloc(pos), splits[0], vl.load(pos, self), 0);
        } else unreachable;
    } else {
        std.debug.assert(splits.len == 1);
        std.debug.assert(splits[0] == .Stack);
        const slot = call.allocArgSlot(&self.bl, self.sloc(pos), splits[0], vl.ty.raw());
        switch (value) {
            .computed => self.emitGenericStore(pos, slot.Stack, vl),
            .to_compute => |tc| {
                if (tc.inferred) |t| {
                    vl = try self.typedExpr(t, .{ .loc = slot.Stack }, tc.lex);
                }
                self.emitGenericStore(pos, slot.Stack, vl);
            },
        }
        call.commitArgSlot(&self.bl, slot);
    }

    return vl.ty;
}

pub fn emitCall(
    self: *Codegen,
    pos: u32,
    ctx: Ctx,
    caller: ?*LLValue,
    res: Value,
    lex: *Lexer,
) !Value {
    if (res.ty == .template) {
        return self.emitTemplateCall(pos, ctx, caller, res, lex);
    } else {
        return self.emitConcreteCall(pos, ctx, caller, res, lex);
    }
}

pub fn emitTemplateCall(
    self: *Codegen,
    pos: u32,
    ctx: Ctx,
    caller: ?*LLValue,
    res: Value,
    lex: *Lexer,
) !Value {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const template_id = self.peval(pos, res, Types.TemplateId) catch |err| {
        lex.eatUntilClosingDelimeter();
        return err;
    };
    const template = template_id.get(self.types);
    const template_file = template.scope.file.get(self.types);

    var call = self.bl.addCall(
        tmp.arena,
        self.sloc(pos),
        self.types.abi.cc,
        .{ .sym = 0 },
    );

    var tp = self.types.tmpCheckpoint();
    defer tp.deinit();

    var template_gen: Codegen = undefined;
    template_gen.init(
        self.types,
        .nany(template_id),
        .never,
        tp.allocator(),
    );
    template_gen.name = template.scope.name_pos;
    _ = template_gen.bl.begin(.systemv, undefined);

    var param_lex = Lexer.init(template_file.source, template.pos);

    var params = std.ArrayList(Types.Func.Param).empty;
    var args = std.ArrayList(Types.Id).empty;

    const arg_iter = lex.list(.@",", .@")");
    const param_iter = param_lex.list(.@",", .@")");

    var caller_vl = caller;
    var errored = false;
    var param_next: bool = undefined;
    var arg_next: bool = undefined;
    while (true) {
        param_next = param_iter.next();
        arg_next = if (caller_vl == null) arg_iter.next() else true;
        if (!param_next or !arg_next) break;

        errdefer lex.eatUntilClosingDelimeter();

        var round_errored = true;
        defer errored = errored or round_errored;
        const ident, const cmptime = param_lex.eatIdent() orelse {
            self.report(param_lex.cursor, "expected argument name", .{}) catch {};
            return error.SyntaxError;
        };

        _ = try self.expect(&param_lex, .@":", "to start an argument type");

        var ty = try template_gen.typ(&param_lex);
        const is_any = ty == .any;

        var ps = lex.cursor;
        var value: Value = if (caller_vl) |vl| b: {
            if (!is_any) self.normalizeCaller(vl, ty) catch {};
            ps = vl.pos;
            break :b vl.value;
        } else if (is_any or cmptime) self.expr(
            .{ .ty = if (is_any) null else ty },
            lex,
        ) catch |err| switch (err) {
            error.Report => {
                if (arg_iter.recover()) break else continue;
            },
        } else .unit(self.passArg(
            &call,
            .{ .to_compute = .{ .lex = lex, .inferred = ty } },
        ) catch continue);

        if (!is_any) self.typeCheck(ps, .{}, &value, ty) catch {};
        ty = if (is_any) value.ty else ty;

        if (cmptime) {
            const index = template_gen.defineVariable(ident);

            const slot: *Variable = &template_gen.vars.items(.variable)[index];
            const is_cmptime = slot.meta.kind == .cmptime;

            std.debug.assert(slot.value == std.math.maxInt(u32));
            std.debug.assert(is_cmptime);

            slot.ty = value.ty;

            const vl = try self.peval(ps, value, Types.ComptimeValue);

            template_gen.cmptime_values.append(template_gen.bl.arena(), vl) catch unreachable;
            slot.value = @intCast(template_gen.cmptime_values.items.len - 1);

            params.append(tmp.arena.allocator(), .{ .value = vl }) catch unreachable;
        } else {
            if (is_any) {
                _ = try template_gen.pushVariable(
                    ident,
                    .ptr(ty, template_gen.bl.addStub(self.sloc(ps), .i64)),
                );
            }

            if (caller_vl != null or is_any) {
                _ = try self.passArg(&call, .{ .computed = .{ .value = value, .pos = ps } });
            }
        }

        args.append(tmp.arena.allocator(), value.ty) catch unreachable;

        template_gen.frozen_vars = template_gen.vars.len;
        round_errored = false;
        caller_vl = null;
    }

    if (param_next) {
        param_lex.eatUntilClosingDelimeter();
    }

    if (arg_next) {
        lex.eatUntilClosingDelimeter();
    }

    _ = try self.expect(&param_lex, .@":", "to start a return type");
    var ret = try template_gen.typ(&param_lex);

    if (ret == .any) {
        ret = ctx.ty orelse
            return self.report(lex.cursor, "can not infer the return type", .{});
    }

    var func_mem = Types.Func{
        .scope = template_gen.gatherScope(),
        .pos = template.pos,
        .params = params.items,
        .args = args.items,
        .captures = .empty,
        .ret = ret,
    };

    var func = &func_mem;
    const slot = self.types.func_index.intern(self.types, func);

    if (!slot.found_existing) {
        slot.key_ptr.* = self.types.funcs.push(&self.types.arena, func_mem);
    }

    func = slot.key_ptr.get(self.types);

    if (!slot.found_existing) {
        std.debug.assert(std.mem.indexOfScalar(Types.Id, args.items, .any) == null);
        func.args = self.types.arena.dupe(Types.Id, args.items);
        func.params = self.types.arena.dupe(Types.Func.Param, func.params);
    }

    call.lateInitSym(@intFromEnum(slot.key_ptr.*));

    var buf = Abi.Buf{};
    const ret_cata = self.types.abi.categorize(ret, self.types, &buf);

    var slt: *BNode = undefined;
    if (self.types.abi.isMultivalue(ret_cata)) {
        slt = self.emitLoc(pos, ret, ctx);
    }

    if (self.types.abi.isRetByRef(ret_cata)) {
        std.debug.assert(self.types.abi.isMultivalue(ret_cata));
        call.prependRefRet(&self.bl, slt);
    }

    return self.endCall(&call, pos, ret_cata, ret, slt);
}

pub fn emitConcreteCall(
    self: *Codegen,
    pos: u32,
    ctx: Ctx,
    caller: ?*LLValue,
    res: Value,
    lex: *Lexer,
) !Value {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const fid: BBuilder.CallId, const func = if (res.ty.data() == .Pointer and
        res.ty.data().Pointer.get(self.types).ty.data() == .FuncTy)
    b: {
        break :b .{
            .{ .fptr = res.load(pos, self) },
            res.ty.data().Pointer.get(self.types).ty.data().FuncTy.get(self.types).*,
        };
    } else b: {
        const fid = self.peval(pos, res, Types.FuncId) catch |err| {
            lex.eatUntilClosingDelimeter();
            return err;
        };

        break :b .{ .{ .sym = @intFromEnum(fid) }, fid.get(self.types).sig() };
    };

    var call = self.bl.addCall(tmp.arena, self.sloc(pos), self.types.abi.cc, fid);

    var buf = Abi.Buf{};
    const ret_cata = self.types.abi.categorize(func.ret, self.types, &buf);

    var slot: *BNode = undefined;
    if (self.types.abi.isMultivalue(ret_cata)) {
        slot = self.emitLoc(pos, func.ret, ctx);
    }

    if (self.types.abi.isRetByRef(ret_cata)) {
        std.debug.assert(self.types.abi.isMultivalue(ret_cata));
        call.pushArg(&self.bl, self.sloc(pos), .{ .Reg = .i64 }, slot, 0);
    }

    var i: usize = 0;
    if (caller) |cl| {
        try self.normalizeCaller(cl, func.args[i]);
        _ = try self.passArg(&call, .{ .computed = .{ .value = cl.value, .pos = cl.pos } });
        i += 1;
    }

    const iter = lex.list(.@",", .@")");
    while (iter.next()) : (i += 1) {
        const ty = if (i < func.args.len) func.args[i] else null;
        if (ty == null) self.report(lex.cursor, "extra argument", .{}) catch {};
        _ = self.passArg(&call, .{ .to_compute = .{ .lex = lex, .inferred = ty } }) catch {};
    }

    if (i < func.args.len) {
        return self.report(
            lex.cursor,
            "{} missing arguments",
            .{func.args.len - i},
        );
    }

    return self.endCall(&call, pos, ret_cata, func.ret, slot);
}

pub fn endCall(
    self: *Codegen,
    call: *BBuilder.Call,
    pos: u32,
    ret_cata: ?[]graph.AbiParam,
    ret: Types.Id,
    slot: *BNode,
) !Value {
    var bf: [2]*BNode = undefined;
    const vls = call.end(&self.bl, self.sloc(pos), ret_cata, &bf);

    const rcta = ret_cata orelse return error.Unreachable;

    if ((Abi{ .cc = call.cc }).isRetByRef(rcta)) {
        std.debug.assert(@intFromPtr(slot) != 0xaaaaaaaaaaaaaaaa);
        return .ptr(ret, slot);
    }

    if (rcta.len == 2) {
        std.debug.assert(@intFromPtr(slot) != 0xaaaaaaaaaaaaaaaa);
        self.bl.addStore(self.sloc(pos), slot, rcta[0].Reg, vls[0]);
        self.emitArbitraryStore(
            pos,
            self.bl.addFieldOffset(self.sloc(pos), slot, 8),
            vls[1],
            ret.size(self.types) - 8,
        );
        return .ptr(ret, slot);
    }

    if (rcta.len == 1) {
        return .value(ret, vls[0]);
    }

    if (rcta.len == 0) {
        return .unit(ret);
    }

    unreachable; // TODO;
}

pub fn silentReport(self: *Codegen) error{Report} {
    self.types.errored += 1;
    return error.Report;
}

pub fn deinitLLList(self: *Codegen, lls: []LLValue) void {
    var iter = std.mem.reverseIterator(lls);
    while (iter.nextPtr()) |ll| {
        ll.deinit(self);
    }
}

pub fn emitArbitraryStore(
    self: *Codegen,
    pos: u32,
    ptr: *BNode,
    value: *BNode,
    size: usize,
) void {
    var storer = value.data_type;
    var offset: Types.Size = 0;
    const slc = self.sloc(pos);

    std.debug.assert(!value.data_type.isFloat()); // TODO

    // TODO: this will be incorrect on ARM

    while (offset < size) {
        while (storer.size() > size - offset) : (storer = storer.halv()) {}

        const shift = self.bl.addIntImm(slc, value.data_type, offset * 8);
        const shi = self.bl.addBinOp(slc, .ushr, value.data_type, value, shift);
        const val = self.bl.addUnOp(slc, .ired, storer, shi);
        self.bl.addFieldStore(slc, ptr, offset, storer, val);

        offset += storer.size();
    }
}

pub fn emitArbitraryLoad(
    self: *Codegen,
    pos: u32,
    ptr: *BNode,
    dt: graph.DataType,
    size: usize,
) *BNode {
    // TODO: this will be incorrect on ARM

    var loader = dt;

    const slc = self.sloc(pos);

    var offset: u64 = 0;
    var value: ?*BNode = null;
    while (offset < size) {
        while (loader.size() > size - offset) : (loader = loader.halv()) {}

        const loaded = self.bl.addFieldLoad(slc, ptr, @intCast(offset), loader);
        const extended = self.bl.addUnOp(slc, .uext, dt, loaded);
        if (value) |v| {
            const shift = self.bl.addIntImm(slc, dt, @intCast(offset * 8));
            const shifted = self.bl.addBinOp(slc, .ishl, dt, extended, shift);
            value = self.bl.addBinOp(slc, .bor, dt, v, shifted);
        } else {
            std.debug.assert(offset == 0);
            value = extended;
        }
        offset += loader.size();
    }
    return value.?;
}

pub fn emitLoc(self: *Codegen, pos: u32, ty: Types.Id, ctx: Ctx) *BNode {
    return (if (ty == ctx.ty) ctx.loc else null) orelse
        self.bl.addLocal(self.sloc(pos), ty.size(self.types), @intFromEnum(ty));
}

pub fn emitLocHandleOpt(self: *Codegen, pos: u32, ty: Types.Id, ctx: Ctx) struct { Types.Id, *BNode } {
    const loc = self.emitLoc(pos, ty, ctx);

    if (ty.data() == .Option) {
        const layout = ty.data().Option.get(self.types).getLayout(self.types);
        if (!layout.compact) {
            self.bl.addFieldStore(
                self.sloc(pos),
                loc,
                layout.inner.offset,
                layout.inner.storage.dataType(),
                self.bl.addIntImm(self.sloc(pos), layout.inner.storage.dataType(), 1),
            );
        }
    }

    return .{
        if (ty.data() == .Option) ty.data().Option.get(self.types).inner else ty,
        loc,
    };
}

pub fn assign(self: *Codegen, pos: u32, dest: Value, src: Value) !void {
    switch (dest.node()) {
        .variable => |i| {
            const slot: *Variable = &self.vars.items(.variable)[i];

            if (slot.value == std.math.maxInt(u32)) {
                return self.report(pos, "can't assign to undeclared variable", .{});
            }

            switch (slot.meta.kind) {
                .empty => {},
                .value => self.bl.setScopeValue(
                    slot.value,
                    src.load(pos, self),
                ),
                .ptr => self.emitGenericStore(
                    pos,
                    self.var_pins.getValue(slot.value),
                    src,
                ),
                .cmptime => {
                    const slt = &self.cmptime_values.items[slot.value];
                    slt.* = try self.peval(pos, src, Types.ComptimeValue);
                },
            }
        },
        .ptr => |p| {
            self.emitGenericStore(pos, p, src);
        },
        .value => {
            return self.report(pos, "can't assign to a value", .{});
        },
        .empty => {},
    }
}

pub fn @"fn"(self: *Codegen, lex: *Lexer) !union(enum) {
    func: struct { Types.FuncId, Types.FuncTyId },
    template: Types.TemplateId,
    func_ty: Types.Id,
} {
    _ = try self.expect(lex, .@"(", "to open the argument list");

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const pos = lex.cursor;

    var args = std.ArrayList(Types.Id).empty;
    var arg_iter = lex.list(.@",", .@")");

    const check_point = lex.cursor;
    const is_fn_ptr = lex.eatIdent() == null or !lex.eatMatch(.@":");
    lex.cursor = check_point;

    while (arg_iter.next()) {
        var cmptime = false;
        if (!is_fn_ptr) {
            _, cmptime = lex.eatIdent() orelse {
                self.report(lex.cursor, "expected argument name", .{}) catch {};
                if (arg_iter.recover()) break else continue;
            };

            _ = try self.expect(lex, .@":", "to start an argument type");
        }

        const tps = lex.cursor;
        const ty = self.typ(lex) catch continue;

        if (cmptime or ty == .any) {
            lex.eatUntilClosingDelimeter();

            _ = try self.expect(lex, .@":", "to start a return type");

            _ = lex.skipExprDropErr();

            if (lex.peekNext().kind == .@"@import") {
                self.report(lex.cursor, "template functions can not be imported", .{}) catch {};
                self.report(tps, "...the function is a template because of this", .{}) catch {};
            }

            _ = lex.skipExprDropErr();

            return .{ .template = self.types.templates.push(
                &self.types.arena,
                Types.Template{
                    .scope = self.gatherScope(),
                    .captures = .init(self, &self.types.arena),
                    .pos = pos,
                },
            ) };
        }

        args.append(tmp.arena.allocator(), ty) catch unreachable;
    }

    std.debug.assert(std.mem.indexOfScalar(Types.Id, args.items, .any) == null);

    _ = try self.expect(lex, .@":", "to start a return type");

    const tps = lex.cursor;
    const ret = try self.typ(lex);

    const fn_ty = self.types.funcTyOf(args.items, ret);

    if (!lex.peekNext().kind.canStartExpression()) {
        return .{ .func_ty = fn_ty };
    }

    var import_name: ?Lexer.Token = null;
    if (lex.eatMatch(.@"@import")) {
        if (ret == .any) {
            self.report(lex.cursor, "template functions can not be imported", .{}) catch {};
            self.report(tps, "...the function is a template because of this", .{}) catch {};
        }

        _ = try self.expect(lex, .@"(", "to start an import declaration");
        import_name = try self.expect(lex, .@"\"", "to denote the import name");
        _ = try self.expect(lex, .@")", "to end an import declaration");
    } else {
        const ps = lex.cursor;
        lex.skipExprDropErr();

        if (is_fn_ptr and args.items.len != 0) {
            return self.report(ps, "signature has nameless arguments" ++
                " so it can not have a body", .{});
        }
    }

    if (ret == .any) {
        return .{ .template = self.types.templates.push(
            &self.types.arena,
            Types.Template{
                .scope = self.gatherScope(),
                .captures = .init(self, &self.types.arena),
                .pos = pos,
            },
        ) };
    }

    var func = Types.Func{
        .scope = self.gatherScope(),
        .params = &.{},
        .captures = .init(self, &self.types.arena),
        .args = self.types.arena.dupe(Types.Id, args.items),
        .ret = ret,
        .pos = pos,
    };

    if (import_name) |in| {
        func.linkage = .imported;
        func.scope.name_pos = @enumFromInt(in.pos);
    }

    const id = self.types.funcs.push(&self.types.arena, func);

    return .{ .func = .{ id, fn_ty.data().FuncTy } };
}

pub fn peval(self: *Codegen, pos: u32, value: Value, comptime T: type) !T {
    const mismatch, const name = switch (T) {
        Types.FuncId => .{ value.ty.data() != .FuncTy, "function" },
        Types.TemplateId => .{ value.ty != .template, "template" },
        Types.Id => .{ value.ty != .type, "type" },
        bool => .{ value.ty != .bool, "bool" },
        else => .{ false, "" },
    };

    if (mismatch) {
        if (value.ty == .never) return self.silentReport();
        return self.report(pos, "expected " ++ name ++ ", got {}", .{value.ty});
    }

    if (T == Types.ComptimeValue) {
        if (value.ty.size(self.types) <= @sizeOf(Types.ComptimeValue)) {
            const res = try self.partialEval(value.load(pos, self));
            return .{ .@"inline" = res.extra(.CInt).value };
        }

        const res = switch (value.normalized(pos, self)) {
            .empty => return self.report(pos, "empty types can not be passed at comptime (TODO)", .{}),
            .value => |v| self.partialEval(v),
            .ptr => |p| self.partialEval(p),
        } catch {
            return self.report(pos, "...the comptime evaluation failed", .{});
        };

        const spill: Types.GlobalId, const offset = d: switch (res.extra2()) {
            .GlobalAddr => |extra| .{ @enumFromInt(extra.id), 0 },
            .BinOp => {
                const base, const offset = res.knownOffset();
                if (base.kind != .GlobalAddr) return self.report(pos, "can't fold the vlaue (debug: {})", .{base.kind});
                break :d .{ @enumFromInt(base.extra(.GlobalAddr).id), offset };
            },
            else => return self.report(pos, "TODO: handle this spill (debug: {})", .{res}),
        };

        if (offset < 0 or offset + value.ty.size(self.types) >
            spill.get(self.types).data.get(self.types).len)
        {
            return self.report(pos, "pointer offset from global is ont of bounds", .{});
        }

        return .{ .spilled = .{ .id = spill, .off = @intCast(offset) } };
    }

    const res = self.partialEval(value.load(pos, self)) catch {
        return self.report(pos, "...the comptime evaluation failed", .{});
    };

    const node_mismatch, const node_name = switch (T) {
        Types.TemplateId,
        Types.FuncId,
        Types.Id,
        i64,
        Types.Size,
        bool,
        => .{ res.kind != .CInt, "constant" },
        else => .{ false, "" },
    };

    if (node_mismatch) {
        return self.report(pos, "comptime type mismatch," ++
            " expected " ++ node_name ++ " but got {}", .{res});
    }

    switch (T) {
        Types.TemplateId => {
            const val = res.extra(.CInt).value;

            if (val < 0 or self.types.templates.meta.len <= val) {
                return self.report(pos, "invalid function id", .{});
            }

            return @enumFromInt(val);
        },
        Types.FuncId => {
            const val = res.extra(.CInt).value;

            if (val < 0 or self.types.funcs.meta.len <= val) {
                return self.report(pos, "invalid function id", .{});
            }

            return @enumFromInt(val);
        },
        Types.Id => return self.validateType(self.sloc(pos), res.extra(.CInt).value),
        i64 => {
            return res.extra(.CInt).value;
        },
        Types.Size => {
            const uint: u64 = @bitCast(res.extra(.CInt).value);

            return std.math.cast(Types.Size, uint) orelse {
                return self.report(pos, "the array size is too large", .{});
            };
        },
        bool => {
            return res.extra(.CInt).value != 0;
        },
        else => @compileError("TODO: " ++ @typeName(T)),
    }
}

pub fn validateType(self: *Codegen, slc: graph.Sloc, value: i64) !Types.Id {
    const val = std.math.cast(u32, value) orelse {
        return self.reportSloc(slc, "the type value is corrupted, (out of range)", .{});
    };

    const ty: Types.Id = @enumFromInt(val);

    const repr = ty.repr();
    const tag = std.meta.intToEnum(
        std.meta.Tag(Types.Data),
        repr.tag,
    ) catch {
        return self.reportSloc(slc, "the type value is corrupted, (invalid tag)", .{});
    };

    switch (tag) {
        .Builtin => _ = std.meta.intToEnum(Types.Builtin, repr.index) catch {
            return self.reportSloc(slc, "the type value is corrupted, (invlaid builtin)", .{});
        },
        inline else => |t| {
            const Payload = std.meta.TagPayload(Types.Data, t);

            const store = @field(self.types, Payload.data.field);

            if (store.meta.len <= repr.index) {
                return self.reportSloc(slc, "the type value is corrupted, (out of bounds)", .{});
            }
        },
    }

    return ty;
}

pub fn partialEval(self: *Codegen, vl: *BNode) error{Report}!*BNode {
    var value = vl;
    switch (value.extra2()) {
        .Stub => return self.reportSloc(value.sloc, "can not access the value, only its type", .{}),
        .GlobalAddr => {
            if (value.isLocked()) return value;
            return try self.partialEvalGlobal(value);
        },
        .CInt => return value,
        .BinOp => {
            value.lockTmp();
            _ = try self.partialEval(value.inputs()[1].?);
            _ = try self.partialEval(value.inputs()[2].?);
            value.unlockTmp();

            value = self.bl.peep(value);

            if (value.kind != .BinOp) return self.partialEval(value);

            const lhs = value.inputs()[1].?;
            const rhs = value.inputs()[2].?;

            if (lhs.kind == .GlobalAddr and rhs.kind == .CInt) {
                return value;
            }

            return self.reportSloc(value.sloc, "cant fold this expression", .{});
        },
        .Load => {
            return self.partialEvalLoad(value, null) catch |err| switch (err) {
                error.Report => return error.Report,
                error.InProgress => unreachable,
            };
        },
        .Local => {
            const allc = value.inputs()[1].?;

            std.debug.assert(allc.outputs().len <= 2);

            const ty = try self.validateType(value.sloc, allc.extra(.LocalAlloc).debug_ty);

            const storage = self.types.globals.push(&self.types.arena, .{
                .scope = self.gatherScope(),
                .ty = ty,
                .readonly = true,
            });

            self.types.ct_backend.emitData(.{
                .id = @intFromEnum(storage),
                .value = .{ .uninit = ty.size(self.types) },
                .readonly = true,
                .thread_local = false,
                .uuid = @splat(0),
            });

            const addr = self.bl.addGlobalAddr(value.sloc, @intFromEnum(storage));
            self.bl.func.subsume(addr, value, .intern);

            return try self.partialEvalGlobal(addr);
        },
        .Phi => {
            return self.reportSloc(value.sloc, "the value depend on the runtime control flow (debug: {})", .{value});
        },
        .Ret => {
            const call_end = value.inputs()[0].?;

            var res = value.lock();
            defer res.unlock();
            try self.partialEvalCall(call_end, &res);
            return res.node;
        },
        .Poison => return self.silentReport(),
        else => return self.reportSloc(
            value.sloc,
            "TODO: handle this: {}",
            .{value},
        ),
    }
}

pub fn partialEvalGlobal(self: *Codegen, addr: *BNode) !*BNode {
    const fns = opaque {
        pub fn handleDep(slf: *Codegen, node: BNode.Out, has_invalid: *bool) bool {
            if (node.get().kind == .Scope) return false;
            const is_interesting = node.get().kind == .Store or (node.get().kind == .Call and
                node.get().extra(.Call).signature.params()[node.pos() - BBuilder.arg_prefix_len] == .Reg) or
                node.get().kind == .Load or node.get().kind == .MemCpy;
            if (!is_interesting) {
                has_invalid.* = true;
                slf.types.reportSloc(node.get().sloc, "TODO: handle this op (debug: {})", .{node});
            }
            return is_interesting;
        }
    };

    const lock = addr.lock();
    defer lock.unlock();

    const storage: Types.GlobalId = @enumFromInt(addr.extra(.GlobalAddr).id);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var interesting_ops = std.ArrayList(BNode.Out).empty;
    var has_invalid = false;
    for (addr.outputs()) |out| {
        if (out.get().kind == .BinOp) {
            for (out.get().outputs()) |o| {
                if (fns.handleDep(self, o, &has_invalid)) {
                    interesting_ops.append(tmp.arena.allocator(), o) catch unreachable;
                }
            }
        } else {
            if (fns.handleDep(self, out, &has_invalid)) {
                interesting_ops.append(tmp.arena.allocator(), out) catch unreachable;
            }
        }
    }

    if (has_invalid) {
        return error.Report;
    }

    std.mem.sortUnstable(BNode.Out, interesting_ops.items, {}, struct {
        fn less(_: void, lhs: BNode.Out, rhs: BNode.Out) bool {
            return lhs.get().id < rhs.get().id;
        }
    }.less);

    var cursor: usize = interesting_ops.items.len;
    var mem_cursor = self.bl.memory() orelse return error.Report;
    while (cursor > 0) {
        const until = interesting_ops.items[cursor - 1].get();
        cursor -= 1;

        if (until.kind == .Load) continue;

        var phi_stack = std.ArrayList(struct {
            node: *BNode,
            is_loop: bool,
            second_round: bool = false,
        }).empty;

        var limita: usize = 10000;

        while (true) : (limita -= 1) {
            var mem_use_count: usize = 0;
            for (mem_cursor.outputs()) |o| {
                if (o.get().kind == .Store or
                    o.get().kind == .Call or
                    o.get().kind == .Phi)
                {
                    mem_use_count += 1;
                }
            }

            if (mem_use_count > 1) {
                // NOTE: we loop since multiple phis can point to the same fork
                while (phi_stack.items.len != 0) : (limita -= 1) {
                    const last = &phi_stack.items[phi_stack.items.len - 1];
                    if (last.is_loop) break;
                    if (last.second_round) {
                        std.debug.assert(last.node == mem_cursor);
                        _ = phi_stack.pop();
                    } else {
                        std.debug.assert(last.node.kind == .Phi);

                        std.mem.swap(*BNode, &mem_cursor, &last.node);
                        mem_cursor = mem_cursor.inputs()[1].?;
                        last.second_round = true;
                        break;
                    }
                }
            }

            const break_out = (mem_cursor == until);

            switch (mem_cursor.kind) {
                .MemCpy, .Store => mem_cursor = mem_cursor.mem(),
                .Mem => {
                    if (mem_cursor.inputs()[0].?.kind == .Start) {
                        break;
                    }
                    std.debug.assert(mem_cursor.inputs()[0].?.kind == .CallEnd);
                    mem_cursor = mem_cursor.inputs()[0].?.inputs()[0].?;
                },
                .Phi => {
                    const is_loop = mem_cursor.cfg0().base.kind == .Loop;
                    if (is_loop and
                        phi_stack.items.len != 0 and
                        phi_stack.items[phi_stack.items.len - 1].node == mem_cursor)
                    {
                        _ = phi_stack.pop().?;
                        mem_cursor = mem_cursor.inputs()[1].?;
                    } else {
                        phi_stack.append(tmp.arena.allocator(), .{
                            .node = mem_cursor,
                            .is_loop = is_loop,
                        }) catch unreachable;
                        mem_cursor = mem_cursor.inputs()[2].?;
                    }
                },
                .Call => mem_cursor = mem_cursor.inputs()[1].?,
                else => utils.panic("{f}", .{mem_cursor}),
            }

            if (break_out) break;
        }

        if (phi_stack.items.len != 0) {
            return self.reportSloc(
                until.sloc,
                "op on a comptime variable depends on runtime control flow (debug: {})",
                .{until},
            );
        }
    }

    var runtime_reads = std.ArrayList(BNode.Out).empty;
    var relocs = std.ArrayList(Machine.DataOptions.Reloc).empty;
    self.types.collectGlobalRelocs(storage, &relocs, tmp.arena, true);

    for (interesting_ops.items) |opp| {
        const op = opp.get();

        const will_be_modified = switch (op.kind) {
            .MemCpy => op.inputs()[3] != addr,
            .Store => op.value().? != addr,
            .Call => true,
            else => false,
        };

        if (will_be_modified and runtime_reads.items.len != 0) {
            const spill = self.createComptimeSpill(storage.get(self.types).ty);
            @memcpy(
                spill.get(self.types).data.get(self.types),
                storage.get(self.types).data.get(self.types),
            );
            const new_addr = self.bl.addGlobalAddr(addr.sloc, @intFromEnum(spill));
            for (runtime_reads.items) |oop| {
                const src, const src_offset = oop.get().inputs()[oop.pos()].?.knownOffset();
                std.debug.assert(src == addr);
                const new_src = self.bl.addFieldOffset(addr.sloc, new_addr, src_offset);
                _ = self.bl.func.setInput(oop.get(), oop.pos(), .intern, new_src);
            }
            runtime_reads.items.len = 0;
        }

        switch (op.extra2()) {
            .Load => _ = self.partialEvalLoad(op, relocs.items) catch |err| switch (err) {
                error.Report => return error.Report,
                error.InProgress => {},
            },
            .MemCpy => {
                if (op.inputs()[3] == addr) {
                    runtime_reads.append(
                        tmp.arena.allocator(),
                        opp,
                    ) catch unreachable;
                    continue;
                }

                const src, const src_offset = (try self.partialEval(op.inputs()[3].?)).knownOffset();
                _, const dst_offset = op.base().knownOffset();
                const len = try self.partialEval(op.inputs()[4].?);

                if (src.kind != .GlobalAddr) return self.reportSloc(src.sloc, "Can't copy form the value (debug: {})", .{src});
                if (len.kind != .CInt) return self.reportSloc(len.sloc, "Can't copy form the value (non constant size) (debug: {})", .{len});

                const src_global: Types.GlobalId = @enumFromInt(src.extra(.GlobalAddr).id);
                const src_mem = src_global.get(self.types).data.get(self.types);
                const dst_mem = storage.get(self.types).data.get(self.types);

                @memcpy(
                    dst_mem[@intCast(dst_offset)..][0..@intCast(len.extra(.CInt).value)],
                    src_mem[@intCast(src_offset)..][0..@intCast(len.extra(.CInt).value)],
                );
            },
            .Store => {
                const add, const offset = op.base().knownOffset();
                if (addr != add) {
                    runtime_reads.append(
                        tmp.arena.allocator(),
                        opp,
                    ) catch unreachable;
                    continue;
                }

                const mem = storage.get(self.types).data.get(self.types);
                const val = self.partialEval(op.value().?) catch continue;

                switch (val.extra2()) {
                    .CInt => |extra| {
                        @memcpy(
                            mem[@intCast(offset)..][0..val.data_type.size()],
                            std.mem.asBytes(extra)[0..val.data_type.size()],
                        );
                    },
                    .GlobalAddr => |extra| {
                        const gid: Types.GlobalId = @enumFromInt(extra.id);
                        @memcpy(
                            mem[@intCast(offset)..][0..8],
                            std.mem.asBytes(&@as(u64, gid.get(self.types).data.sym(self.types).offset)),
                        );
                    },
                    else => self.types.reportSloc(op.sloc, "TODO: handle this store value (debug: {})", .{val}),
                }

                self.bl.func.subsume(op.mem(), op, .intern);
            },
            .Call => {
                try self.partialEvalCall(op.outputs()[0].get(), null);
            },
            else => self.types.reportSloc(op.sloc, "TODO: handle this interesting op (debug: {})", .{op}),
        }
    }

    return addr;
}

pub fn partialEvalLoad(self: *Codegen, op: *BNode, relocs: ?[]Machine.DataOptions.Reloc) !*BNode {
    if (op.isLocked()) return error.InProgress;

    var lock = op.lock();
    defer lock.unlock();

    const src, const src_offset = (try self.partialEval(op.base())).knownOffset();

    switch (src.extra2()) {
        .GlobalAddr => |extra| {
            const storage: Types.GlobalId = @enumFromInt(extra.id);

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var rlocs = std.ArrayList(Machine.DataOptions.Reloc).fromOwnedSlice(relocs orelse &.{});

            if (relocs == null) {
                self.types.collectGlobalRelocs(
                    storage,
                    &rlocs,
                    tmp.arena,
                    false,
                );
            }

            const mem = storage.get(self.types).data.get(self.types);
            var res: *BNode = undefined;
            for (rlocs.items) |reloc| {
                if (reloc.offset == src_offset) {
                    const rel = self.types.collectPointer(
                        op.sloc,
                        reloc.is_func,
                        reloc.offset,
                        0,
                        mem,
                        false,
                    ) catch return error.Report;

                    if (rel.is_func) {
                        res = self.bl.addFuncAddr(op.sloc, rel.target);
                    } else {
                        res = self.bl.addGlobalAddr(op.sloc, rel.target);
                    }

                    break;
                }
            } else {
                var val: i64 = 0;
                @memcpy(
                    std.mem.asBytes(&val)[0..@intCast(op.data_type.size())],
                    mem[@intCast(src_offset)..][0..@intCast(op.data_type.size())],
                );
                res = self.bl.addIntImm(op.sloc, op.data_type, val);
            }

            self.bl.func.subsume(res, op, .intern);

            return res;
        },
        else => return self.reportSloc(op.sloc, "TODO: handle this load source (debug: {})", .{src}),
    }
}

pub fn partialEvalCall(
    self: *Codegen,
    call_end: *BNode,
    res: ?*BNode.Lock,
) !void {
    const call = call_end.inputs()[0].?;

    const until = self.types.func_queue.getPtr(.cmptime).items.len;
    const fnid: Types.FuncId = @enumFromInt(call.extra(.Call).id);

    if (call.extra(.Call).id != comptime_only_fn) {
        fnid.get(self.types).queue(.cmptime, self.types);

        if (self.emitCtFuncs(until, self.types.ct_backend.mach.out.relocs.items.len)) {
            return error.Report;
        }
    }

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const args = tmp.arena.alloc(
        i64,
        call.inputs().len - BBuilder.arg_prefix_len,
    );

    const sig: graph.Signature = call.extra(.Call).signature;
    var cursor: usize = 0;
    const stack_cursor = self.types.vm.regs.getPtr(.stack_addr);

    var stack_size: Types.Size = 0;
    for (sig.params()) |par| {
        if (par == .Stack) {
            stack_size = std.mem.alignForward(
                Types.Size,
                stack_size,
                par.Stack.alignmentBytes(),
            );
            stack_size += par.Stack.size;
        }
    }
    stack_cursor.* -= stack_size;

    stack_size = 0;

    for (call.ordInps()[BBuilder.arg_prefix_len..], sig.params()) |in, par| {
        const inp = in.?;
        switch (par) {
            .Reg => {
                const argvl = try self.partialEval(inp);
                args[cursor] = switch (argvl.extra2()) {
                    .CInt => |extra| extra.value,
                    .GlobalAddr => |extra| @as(Types.GlobalId, @enumFromInt(extra.id))
                        .get(self.types).data.sym(self.types).offset,
                    else => return self.reportSloc(argvl.sloc, "TODO: handle this (debug: {})", .{argvl}),
                };
                cursor += 1;
            },
            .Stack => |s| {
                stack_size = std.mem.alignForward(
                    Types.Size,
                    stack_size,
                    s.alignmentBytes(),
                );
                defer stack_size += s.size;

                // We could be more efficienato by playing with the global offsets
                const local = for (inp.outputs()) |o| {
                    if (o.get().kind == .Local) break o.get();
                } else continue; // uninitialized anyway

                const glob = try self.partialEval(local);
                const inner: Types.GlobalId = @enumFromInt(glob.extra(.GlobalAddr).id);

                const src = inner.get(self.types).data.get(self.types);
                const dst = self.types.ct_backend.mach.out.code.items[stack_cursor.* + stack_size ..][0..src.len];
                @memcpy(dst, src);
            },
        }
    }

    for (args[0..cursor], 0..) |arg, i| {
        self.types.vm.regs.set(.arg(i), @bitCast(arg));
    }

    self.runVm(call.sloc, fnid);

    for (tmp.arena.dupe(BNode.Out, call_end.outputs())) |out| {
        if (out.get().kind == .Ret) {
            const ret = self.bl.addIntImm(
                out.get().sloc,
                out.get().data_type,
                @bitCast(self.types.vm.regs.get(.ret(out.get().extra(.Ret).index))),
            );

            if (res) |r| {
                if (out.get() == r.node) {
                    r.unlock();
                    r.* = ret.lock();
                }
            }

            self.bl.func.subsume(ret, out.get(), .intern);
        }

        if (out.get().kind == .Mem) {
            self.bl.func.subsume(call.inputs()[1].?, out.get(), .intern);
        }
    }

    self.bl.func.subsume(call.inputs()[0].?, call_end, .intern);
}

pub fn createComptimeSpill(self: *Codegen, ty: Types.Id) Types.GlobalId {
    const global = self.types.globals.push(&self.types.arena, .{
        .scope = self.gatherScope(),
        .ty = ty,
        .readonly = true,
    });

    self.types.ct_backend.emitData(.{
        .id = @intFromEnum(global),
        .value = .{ .uninit = ty.size(self.types) },
        .readonly = true,
        .thread_local = false,
        .uuid = @splat(0),
    });

    return global;
}

pub fn reportSloc(self: *Codegen, slc: graph.Sloc, fmt: []const u8, args: anytype) error{Report} {
    @branchHint(.cold);
    self.types.reportSloc(slc, fmt, args);
    return error.Report;
}

pub fn binOpUpcast(self: *Codegen, lhs: Types.Id, rhs: Types.Id) !Types.Id {
    if (lhs == rhs) return lhs;
    if (lhs.canUpcast(rhs, self.types)) return rhs;
    if (rhs.canUpcast(lhs, self.types)) return lhs;
    return error.IncompatibleTypes;
}

pub fn lexemeToBinOp(self: *Codegen, pos: u32, lx: Lexer.Lexeme, ty: Types.Id) !graph.BinOp {
    return (lexemeToBinOpLow(lx, ty) catch
        return self.report(pos, "BUG: lexeme to bin op call" ++
            " with incorrect token", .{})) orelse
        self.report(pos, "the operator not supported for {}", .{ty});
}

pub fn lexemeToBinOpLow(self: Lexer.Lexeme, ty: Types.Id) !?graph.BinOp {
    const unsigned = ty.isBuiltin(.isUnsigned) or ty == .bool or ty == .type or
        ty.data() == .Pointer or ty.data() == .Enum;
    const float = ty.isBuiltin(.isFloat);
    if (!unsigned and !ty.isBuiltin(.isSigned) and !float) return null;
    return switch (self) {
        .@"+" => if (float) .fadd else .iadd,
        .@"-" => if (float) .fsub else .isub,
        .@"*" => if (float) .fmul else .imul,
        .@"/" => if (float) .fdiv else if (unsigned) .udiv else .sdiv,
        .@"%" => if (float) null else if (unsigned) .umod else .smod,

        .@"<<" => if (float) null else .ishl,
        .@">>" => if (unsigned) .ushr else .sshr,
        .@"|" => if (float) null else .bor,
        .@"&" => if (float) null else .band,
        .@"^" => if (float) null else .bxor,

        .@"<" => if (float) .flt else if (unsigned) .ult else .slt,
        .@">" => if (float) .fgt else if (unsigned) .ugt else .sgt,
        .@"<=" => if (float) .fle else if (unsigned) .ule else .sle,
        .@">=" => if (float) .fge else if (unsigned) .uge else .sge,
        .@"==" => .eq,
        .@"!=" => .ne,
        else => error.ShoudNotHappen,
    };
}

pub fn typeCheckLL(
    self: *Codegen,
    ctx: Ctx,
    ll: *LLValue,
    expected: Types.Id,
) error{Report}!void {
    ll.tmpUnlock();
    defer ll.tmpLock();
    return self.typeCheck(ll.pos, ctx, &ll.value, expected);
}

pub fn typeCheck(
    self: *Codegen,
    pos: u32,
    ctx: Ctx,
    got: *Value,
    expected: Types.Id,
) error{Report}!void {
    if (expected == got.ty) return;

    if (expected == .never or got.ty == .never) {
        return self.silentReport();
    }

    if (expected.data() == .Option and expected.data().Option.get(self.types).inner == got.ty) {
        if (expected.data().Option.get(self.types).getLayout(self.types).compact) {
            got.ty = expected;
            return;
        }

        switch (got.ty.category(self.types)) {
            .Impossible => got.* = .unit(expected),
            .Imaginary => got.* = .value(expected, self.bl.addIntImm(self.sloc(pos), .i8, 1)),
            .Scalar, .Stack => {
                _, const slot = self.emitLocHandleOpt(pos, expected, ctx);
                self.emitGenericStore(pos, slot, got.*);
                got.* = .ptr(expected, slot);
            },
        }

        return;
    }

    if (got.ty.canUpcast(expected, self.types)) {
        const sloca = self.sloc(pos);
        const res_dt = Abi.categorizeBuiltinUnwrapped(expected.data().Builtin);

        if (got.ty.data() == .Enum) {
            got.ty = got.ty.data().Enum.get(self.types)
                .getLayout(self.types).backingInteger();
        }

        if (got.ty.isBuiltin(.isSigned) and
            got.ty.size(self.types) < expected.size(self.types))
        {
            const tmp = got.load(pos, self);
            got.* = .value(expected, self.bl.addUnOp(sloca, .sext, res_dt, tmp));
        }

        if ((got.ty.isBuiltin(.isUnsigned) or got.ty == .bool) and
            got.ty.size(self.types) < expected.size(self.types))
        {
            const tmp = got.load(pos, self);
            got.* = .value(expected, self.bl.addUnOp(sloca, .uext, res_dt, tmp));
        }

        if (expected != got.ty) {
            utils.panic("{} {}", .{ got.ty, expected });
        }

        return;
    }

    return self.report(pos, "expected {}, got {} (generic)", .{ expected, got.ty });
}

pub fn defineVariable(self: *Codegen, name: Lexer.Token) usize {
    const file = self.file.get(self.types);
    self.vars.append(self.bl.arena(), .{
        .prefix = file.source[name.pos + @intFromBool(name.kind == .@"$")],
        .variable = .{
            .ty = .void,
            .meta = .{
                .kind = if (name.kind == .@"$") .cmptime else .empty,
                .pos = @intCast(name.pos + @intFromBool(name.kind == .@"$")),
            },
        },
    }) catch unreachable;
    return self.vars.len - 1;
}

pub fn pushVariable(self: *Codegen, name: Lexer.Token, value: Value) !usize {
    const index = self.defineVariable(name);
    try self.declareVariable(name.pos, index, value);
    return index;
}

pub fn declareVariable(self: *Codegen, pos: u32, index: usize, value: Value) error{Report}!void {
    // NOTE: this enforces the order of declarations
    const slot: *Variable = &self.vars.items(.variable)[index];
    const is_cmptime = slot.meta.kind == .cmptime;

    std.debug.assert(slot.value == std.math.maxInt(u32));

    slot.ty = value.ty;

    if (is_cmptime) {
        const vl = try self.peval(pos, value, Types.ComptimeValue);
        self.cmptime_values.append(self.bl.arena(), vl) catch unreachable;
        slot.value = @intCast(self.cmptime_values.items.len - 1);
        return;
    }

    slot.meta.kind = switch (value.tag) {
        .empty => .empty,
        .variable => self.vars.items(.variable)[value.value_.idx].meta.kind,
        .value => .value,
        .ptr => .ptr,
    };
    slot.value = switch (value.normalized(pos, self)) {
        .empty => undefined,
        .value => |v| self.bl.pushScopeValue(v),
        .ptr => |t| self.var_pins.push(&self.bl, t),
    };
}

pub fn popScope(self: *Codegen, scope_marker: usize) void {
    var truncate_vals_by: usize = 0;
    var truncate_slots_by: usize = 0;
    var truncate_cmptime_by: usize = 0;

    const poped_vars = self.vars.items(.variable)[scope_marker..];
    var iter = std.mem.reverseIterator(poped_vars);
    while (@as(?Variable, iter.next())) |vr| {
        if (vr.value == std.math.maxInt(u32)) continue;
        switch (vr.meta.kind) {
            .empty => {},
            .value => truncate_vals_by += 1,
            .ptr => truncate_slots_by += 1,
            .cmptime => truncate_cmptime_by += 1, // TODO
        }
    }

    self.bl.truncateScope(self.bl.scopeSize() -| truncate_vals_by);

    self.var_pins.truncate(&self.bl, self.var_pins.len() -| truncate_slots_by);
    self.cmptime_values.items.len -|= truncate_cmptime_by;

    @memset(poped_vars, undefined);
    self.vars.len = scope_marker;
}

pub fn collectExports(types: *Types, gpa: std.mem.Allocator) !void {
    _ = gpa;
    const root = File.Id.root.get(types);
    const root_scope = File.Id.root.getScope(types);

    errdefer {
        root.decls.log(0, types.loader.diagnostics.?) catch {};
    }

    var tmp = types.tmpCheckpoint();
    defer tmp.deinit();

    var self: Codegen = undefined;
    self.init(types, .nany(root_scope), .never, tmp.allocator());
    _ = self.bl.begin(.systemv, undefined);

    var has_main = false;
    for (types.files) |f| {
        for (f.decls.exports) |epos| {
            var elex = Lexer.init(f.source, epos);
            const kind = elex.next().kind;

            _ = self.expect(
                &elex,
                .@"(",
                "to open the @handler/@erport directive",
            ) catch continue;

            const name_tok = self.expect(
                &elex,
                .@"\"",
                "to declare the @handler/@export name",
            ) catch continue;
            var name = name_tok.view(elex.source);
            name = name[1 .. name.len - 1];

            self.name = @enumFromInt(name_tok.pos);

            const iter = elex.list(.@",", .@")");

            self.expectNext(iter) catch continue;

            switch (kind) {
                .@"@export" => {
                    const value_node = self.expr(.{}, &elex) catch continue;
                    const value = self.peval(elex.cursor, value_node, Types.ComptimeValue) catch continue;

                    has_main = has_main or std.mem.eql(u8, name, "main");

                    if (value_node.ty.data() != .FuncTy) {
                        self.report(
                            elex.cursor,
                            "{} is not a function",
                            .{value_node.ty},
                        ) catch continue;
                    }

                    const func: Types.FuncId = @enumFromInt(value.@"inline");
                    func.get(types).linkage = .exported;
                    func.get(types).queue(.runtime, types);
                },
                .@"@handler" => {
                    const handler = std.meta.stringToEnum(Types.Handler, name) orelse {
                        self.report(
                            name_tok.pos,
                            "handler with this name does not exist, (TODO: list handlers)",
                            .{},
                        ) catch continue;
                    };

                    const handler_slot = types.handlers.getPtr(handler);

                    if (handler_slot.* != .invalid) {
                        self.report(name_tok.pos, "redeclaration of a handler", .{}) catch {};
                        self.report(
                            handler_slot.get(types).pos,
                            "...first handler is declared here",
                            .{},
                        ) catch continue;
                    }

                    const handler_sig = types.handler_signatures.get(handler);

                    const value_node = self.expr(.{
                        .ty = if (handler_sig != .invalid) self.types.optionOf(.nany(handler_sig)) else null,
                    }, &elex) catch continue;
                    const value = self.peval(elex.cursor, value_node, Types.ComptimeValue) catch continue;

                    var sig = value_node.ty;
                    const should_unwrap = sig.data() == .Option;
                    if (should_unwrap) {
                        sig = sig.data().Option.get(self.types).inner;
                    }

                    if (sig.data() != .FuncTy) {
                        self.report(
                            elex.cursor,
                            "{} is not a function nor a option holding a function",
                            .{value_node.ty},
                        ) catch continue;
                    }

                    const val = std.mem.toBytes(value.@"inline");
                    if (should_unwrap and val[4] == 0) continue;

                    if (handler_sig != .invalid) {
                        const supplied = sig.data().FuncTy.get(types);
                        const expected = handler_sig.get(self.types);
                        if (expected.args.len != supplied.args.len) {
                            self.report(
                                name_tok.pos,
                                "the signature expects {} arguments, but got {}",
                                .{ expected.args.len, supplied.args.len },
                            ) catch {};
                            self.report(
                                name_tok.pos,
                                "...the full expected signature is {}",
                                .{types.funcTyOf(expected.args, expected.ret)},
                            ) catch {};
                            self.report(
                                name_tok.pos,
                                "...the actual signature is {}",
                                .{types.funcTyOf(supplied.args, supplied.ret)},
                            ) catch continue;
                        }

                        for (expected.args, supplied.args, 0..) |ea, sa, i| {
                            if (ea != sa) {
                                self.report(
                                    name_tok.pos,
                                    "argument {} mismatch, expected {}, got {}",
                                    .{ i, ea, sa },
                                ) catch continue;
                            }
                        }

                        if (expected.ret != supplied.ret) {
                            self.report(
                                name_tok.pos,
                                "return type mismatch, does not match, expected {}, got {}",
                                .{ expected.ret, supplied.ret },
                            ) catch continue;
                        }
                    }

                    handler_slot.* = @enumFromInt(@as(u32, @bitCast(val[0..4].*)));
                },
                else => unreachable,
            }
        }
    }

    if (!has_main) {
        const main = self.lookupIdent(.nany(root_scope), "main") orelse {
            if (types.loader.diagnostics) |diags| {
                try diags.writeAll(
                    \\...you can define the `main` in the mentioned file (or pass --no-entry):
                    \\
                );

                try highlightCode(
                    \\main := fn(): uint {
                    \\    return 0
                    \\}
                    \\
                , types.loader.colors, diags);
            }

            return error.NoMain;
        };

        const func = try self.peval(0, main, Types.FuncId);

        func.get(types).linkage = .exported;
        func.get(types).queue(.runtime, types);
    }
}

pub const HandlerBuilder = struct {
    if_bl: BBuilder.If,
    call: BBuilder.Call,
    pos: u32,

    pub fn pushArg(self: *HandlerBuilder, gen: *Codegen, value: *BNode) void {
        self.call.pushArg(&gen.bl, gen.sloc(self.pos), .{ .Reg = value.data_type }, value, 0);
    }

    pub fn end(self: *HandlerBuilder, gen: *Codegen) void {
        _ = gen.endCall(&self.call, self.pos, null, .never, undefined) catch {};
        self.if_bl.end(&gen.bl, self.if_bl.beginElse(&gen.bl));
    }
};

pub fn addHandler(self: *Codegen, pos: u32, handler: Types.FuncId, cond: *BNode, scratch: *utils.Arena) HandlerBuilder {
    const if_bl = self.bl.addIfAndBeginThen(self.sloc(pos), cond);

    var handler_call = self.bl.addCall(
        scratch,
        self.sloc(pos),
        self.types.abi.cc,
        .{ .sym = @intFromEnum(handler) },
    );

    const slot = handler_call.allocArgSlot(
        &self.bl,
        self.sloc(pos),
        .{ .Stack = self.types.builtins.source_loc
            .get(self.types).getLayout(self.types).spec },
        Types.Id.nany(self.types.builtins.source_loc).raw(),
    );

    _ = self.emitString(pos, .{ .loc = slot.Stack }, self.file.get(self.types).path);
    const line, const col = self.file.get(self.types).lines.lineCol(pos);

    self.bl.addFieldStore(
        self.sloc(pos),
        slot.Stack,
        16,
        .i32,
        self.bl.addIntImm(self.sloc(pos), .i32, line),
    );
    self.bl.addFieldStore(
        self.sloc(pos),
        slot.Stack,
        20,
        .i32,
        self.bl.addIntImm(self.sloc(pos), .i32, col),
    );

    handler_call.commitArgSlot(&self.bl, slot);

    return .{
        .call = handler_call,
        .if_bl = if_bl,
        .pos = pos,
    };
}

pub fn tyLit(self: *Codegen, pos: u32, vl: anytype) Value {
    const id: Types.Id = if (@TypeOf(vl) != Types.Id) .nany(vl) else vl;
    return .value(.type, self.bl.addIntImm(
        self.sloc(pos),
        .i32,
        @intFromEnum(id),
    ));
}

pub fn typ(self: *Codegen, lex: *Lexer) error{Report}!Types.Id {
    return self.peval(
        lex.cursor,
        try self.exprPrec(.{ .ty = .type }, lex, 1),
        Types.Id,
    );
}

pub fn dbgReport(self: *Codegen, pos: u32, msg: []const u8, args: anytype) void {
    self.types.report(self.file, pos, msg, args);
    self.types.errored -= 1;
}

pub fn report(self: *Codegen, pos: u32, msg: []const u8, args: anytype) error{Report} {
    @branchHint(.cold);

    self.types.report(self.file, pos, msg, args);
    self.types.errored += 1;

    const trace_size = @import("options").report_trace_size;
    if (trace_size != 0) {
        var buf: [trace_size]usize = undefined;
        var st = std.builtin.StackTrace{
            .index = 0,
            .instruction_addresses = &buf,
        };

        std.debug.captureStackTrace(@returnAddress(), &st);
        std.debug.dumpStackTrace(st);
    }

    return error.Report;
}

pub fn reportGeneric(
    path: []const u8,
    source: [:0]const u8,
    types: *Types,
    pos: u32,
    msg: []const u8,
    args: anytype,
) void {
    errdefer unreachable;

    const diags = types.loader.diagnostics orelse return;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const fields = std.meta.fields(@TypeOf(args));
    var argss: [fields.len + 1][]const u8 = undefined;
    inline for (0..fields.len) |i| {
        if (fields[i].type == []const u8) {
            argss[i] = args[i];
        } else if (fields[i].type == Types.Id) {
            argss[i] = args[i].fmt(types).toString(tmp.arena);
        } else if (@typeInfo(fields[i].type) == .pointer and std.meta.Child(fields[i].type) == u8) {
            argss[i] = try std.fmt.allocPrint(tmp.arena.allocator(), "{s}", .{args[i]});
        } else if (std.meta.hasMethod(fields[i].type, "format")) {
            argss[i] = try std.fmt.allocPrint(tmp.arena.allocator(), "{f}", .{args[i]});
        } else {
            argss[i] = try std.fmt.allocPrint(tmp.arena.allocator(), "{}", .{args[i]});
        }
    }
    argss[fields.len] = "";

    reportLow(path, source, pos, msg, &argss, types.loader.colors, diags);
}

pub fn reportLow(
    path: []const u8,
    file: []const u8,
    pos: u32,
    fmt_str: []const u8,
    args: []const []const u8,
    colors: std.io.tty.Config,
    out: *std.Io.Writer,
) void {
    errdefer unreachable;
    const line, const col = lineCol(file, pos);

    try colors.setColor(out, .bright_white);
    try colors.setColor(out, .bold);
    try out.print("{s}:{}:{}: ", .{ path, line, col });
    try colors.setColor(out, .reset);

    var iter = std.mem.splitSequence(u8, fmt_str, "{}");
    var idx: usize = 0;
    while (iter.next()) |chunk| {
        try out.writeAll(chunk);
        try colors.setColor(out, .bold);
        try out.writeAll(args[idx]);
        try colors.setColor(out, .reset);
        idx += 1;
    }

    try out.print("\n{f}\n", .{CodePointer{
        .source = file,
        .index = pos,
        .colors = colors,
    }});
}

pub const CodePointer = struct {
    source: []const u8,
    index: usize,
    colors: std.io.tty.Config,

    pub fn format(slf: *const @This(), writer: *std.Io.Writer) std.Io.Writer.Error!void {
        try pointToCode(slf.source, slf.index, slf.colors, writer);
    }
};

pub fn lineCol(source: []const u8, index: usize) struct { usize, usize } {
    var line: usize = 0;
    var last_nline: isize = -1;
    for (source[0..@min(@as(usize, @intCast(index)), source.len)], 0..) |c, i| if (c == '\n') {
        line += 1;
        last_nline = @intCast(i);
    };
    return .{ line + 1, @intCast(@as(isize, @bitCast(index)) - last_nline) };
}

pub fn highlightCode(
    source: []const u8,
    colors: std.io.tty.Config,
    writer: *std.Io.Writer,
) !void {
    errdefer unreachable;

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var lexer = Lexer.init(try tmp.arena.allocator().dupeZ(u8, source), 0);
    var last: usize = 0;
    var token = lexer.next();
    while (token.kind != .Eof) : (token = lexer.next()) {
        const mods = Class.fromLexeme(token.kind).?;
        for (mods.toTtyColor()) |color| {
            try colors.setColor(writer, color);
        }

        try writer.writeAll(source[last..token.end]);
        last = token.end;

        try colors.setColor(writer, .reset);
    }

    try writer.writeAll(source[last..]);
}

pub fn pointToCode(source: []const u8, index_m: usize, colors: std.io.tty.Config, writer: *std.Io.Writer) std.Io.Writer.Error!void {
    const index = @min(index_m, source.len -| 1); // might be an empty file
    const line_start = if (std.mem.lastIndexOfScalar(u8, source[0..index], '\n')) |l| l + 1 else 0;
    const line_end = if (std.mem.indexOfScalar(u8, source[index..], '\n')) |l| l + index else source.len;
    const the_line = source[line_start..line_end];

    var i: usize = 0;

    var extra_bytes: usize = 0;
    const code_start = for (the_line, 0..) |c, j| {
        if (c == ' ') {
            try writer.writeAll(" ");
            i += 1;
        } else if (c == '\t') {
            try writer.writeAll("    "[0 .. 4 - i % 4]);
            i += 4 - i % 4;
            extra_bytes += 3 - i % 4;
        } else break j;
    } else the_line.len;

    colors.setColor(writer, .white) catch return error.WriteFailed;
    try highlightCode(the_line[code_start..][0 .. the_line.len - code_start], colors, writer);
    try writer.writeAll("\n");

    const col = index - line_start + extra_bytes;
    for (0..col) |_| {
        try writer.writeAll(" ");
    }
    colors.setColor(writer, .green) catch return error.WriteFailed;
    try writer.writeAll("^");
    colors.setColor(writer, .reset) catch return error.WriteFailed;
}

pub const Class = enum(u8) {
    blank,
    comment,
    keyword,
    identifier,
    directive,
    number,
    string,
    op,
    assign,
    paren,
    bracket,
    colon,
    comma,
    dot,
    ctor,

    pub fn toTtyColor(self: Class) []const std.io.tty.Color {
        return switch (self) {
            .blank => unreachable,
            .comment => &.{.dim},
            .keyword => &.{ .bright_white, .bold },
            .identifier => &.{},
            .directive => &.{ .bright_white, .bold },
            .number => &.{.cyan},
            .string => &.{.green},
            .op => &.{.dim},
            .assign => &.{.dim},
            .paren => &.{.dim},
            .bracket => &.{.dim},
            .colon => &.{.dim},
            .comma => &.{.dim},
            .dot => &.{.dim},
            .ctor => &.{.dim},
        };
    }

    pub fn fromLexeme(leme: Lexer.Lexeme) ?Class {
        return switch (leme) {
            inline else => |t| {
                if (comptime @tagName(t)[0] == '@')
                    return .directive;
                if (comptime std.mem.startsWith(u8, @tagName(t), "ty_"))
                    return .identifier;
                if (comptime std.mem.endsWith(u8, @tagName(t), "="))
                    return .assign;
                if (comptime std.ascii.isLower(@tagName(t)[0]) or
                    @tagName(t)[0] == '$')
                    return .keyword;
                if (comptime std.mem.indexOfAny(
                    u8,
                    @tagName(t),
                    "!^*/%+-<>&|.,~?",
                ) != null)
                    return .op;

                comptime unreachable;
            },
            .true,
            .false,
            .BinInteger,
            .OctInteger,
            .DecInteger,
            .HexInteger,
            .Float,
            => .number,
            .@"<=", .@"==", .@">=" => .op,
            .Ident, .@"$", ._ => .identifier,
            .Comment => .comment,
            .@".(", .@".[", .@".{" => .ctor,
            .@"[", .@"]" => .bracket,
            .@"(", .@")", .@"{", .@"}" => .paren,
            .@"\"", .@"`", .@"'" => .string,
            .@":", .@";", .@"#", .@"\\", .@"," => .comma,
            .@"." => .dot,
            .@"unterminated string" => .comment,
            .Eof => null,
        };
    }
};

pub fn runTest(name: []const u8, code: []const u8, gpa: std.mem.Allocator) !void {
    utils.Arena.tryInitScratch(1024 * 1024);

    var scratch = utils.Arena.init(1024 * 1024 * 32);
    var writer = std.fs.File.stderr().writer(&.{});
    const wint = &writer.interface;
    //var writer = std.Io.Writer.Discarding.init(&.{});
    //const wint = &writer.writer;

    errdefer {
        std.fs.cwd().makePath(scratch.print("failed_tests_hbvm/{s}", .{name})) catch {};
    }

    const asts, var kl = try parseExample(&scratch, name, code, wint);

    var target = hb.backend.Machine.SupportedTarget.@"hbvm-ableos";
    //target = hb.backend.Machine.SupportedTarget.@"x86_64-linux";
    //target = hb.backend.Machine.SupportedTarget.@"wasm-freestanding";

    const backend = target.toMachine(&scratch, gpa);
    defer backend.deinit();

    var types = Types.init(asts, &kl.loader, @tagName(target), backend, scratch, gpa);
    defer types.deinit();

    try collectExports(&types, gpa);

    const opt_mode = Machine.OptOptions{
        .mode = .release,
        .error_collector = .{ .data = &types, .collect_ = Types.collectAnalError },
    };

    emitReachable(&types, gpa, opt_mode);

    const exp = Expectations.init(asts[0].source);

    var exe: std.ArrayList(u8) =
        if (types.errored == 0) backend.finalizeBytes(gpa, .{
            .optimizations = opt_mode,
            .builtins = .{},
            .files = types.line_indexes,
        }) else .empty;
    defer exe.deinit(gpa);

    if (exp.should_error) {
        try std.testing.expect(types.errored != 0);
        return;
    }

    try std.testing.expect(types.errored == 0);

    if (std.mem.indexOf(u8, name, "infinite") != null) {
        return;
    }

    const res = if (@import("options").dont_simulate)
        error.SegmentationFault
    else
        backend.run(.{
            .name = name,
            .code = exe.items,
            //.output = &writer.interface,
        });

    errdefer {
        backend.disasm(.{
            .name = name,
            .bin = exe.items,
            .out = wint,
        });
    }

    try exp.assert(res);
}

pub const Expectations = struct {
    return_value: u64 = 0,
    should_error: bool = false,
    times_out: bool = false,
    unreaches: bool = false,

    pub fn init(source: [:0]const u8) Expectations {
        errdefer unreachable;

        var slf: Expectations = .{};

        var lex = Lexer.init(source, 0);

        var tok = lex.next();

        while (tok.kind == .Comment) : (tok = lex.next()) {}

        if (!std.mem.eql(u8, tok.view(source), "expectations")) {
            return slf;
        }

        _ = lex.slit(.@":=");
        _ = lex.slit(.@".{");

        var iter = lex.list(.@",", .@"}");
        while (iter.next()) {
            const fname = lex.slit(.Ident).view(source);
            _ = lex.slit(.@":");
            const value = lex.next().view(source);

            inline for (std.meta.fields(Expectations)) |f| {
                if (std.mem.eql(u8, fname, f.name)) {
                    @field(slf, f.name) = switch (f.type) {
                        u64 => @bitCast(try std.fmt.parseInt(i64, value, 10)),
                        bool => std.mem.eql(u8, value, "true"),
                        else => comptime unreachable,
                    };
                }
            }
        }

        return slf;
    }

    pub fn assert(
        expectations: Expectations,
        res: Machine.RunError!usize,
    ) (error{ TestUnexpectedResult, TestExpectedEqual } ||
        Machine.RunError)!void {
        const ret = res catch |err| switch (err) {
            error.Timeout => {
                try std.testing.expect(expectations.times_out);
                return;
            },
            error.Unreachable => {
                try std.testing.expect(expectations.unreaches);
                return;
            },
            else => |e| return e,
        };

        try std.testing.expect(!expectations.unreaches);
        try std.testing.expect(!expectations.times_out);

        try std.testing.expectEqual(expectations.return_value, ret);
    }
};

const FileRecord = struct {
    path: []const u8,
    source: [:0]const u8,
};

const KnownLoader = struct {
    loader: Loader = .init(@This()),
    files: []const FileRecord,

    pub fn load(self: *@This(), opts: Loader.LoadOptions) ?File.Id {
        return for (self.files, 0..) |fr, i| {
            if (std.mem.eql(u8, fr.path, opts.path)) {
                break @enumFromInt(i);
            }
        } else {
            return null;
        };
    }

    pub fn loadEmbed(
        self: *@This(),
        opts: Loader.LoadOptions,
    ) ?[:0]const u8 {
        return for (self.files) |fr| {
            if (std.mem.eql(u8, fr.path, opts.path)) {
                break fr.source;
            }
        } else {
            return null;
        };
    }
};

pub fn parseExample(
    scratch: *utils.Arena,
    name: []const u8,
    code: []const u8,
    output: ?*std.Io.Writer,
) !struct { []File, KnownLoader } {
    var files = std.ArrayList(FileRecord).empty;

    const signifier = "// in: ";
    var prev_name: []const u8 = name;
    var prev_end: usize = 0;
    while (prev_end < code.len) {
        const next_end =
            if (std.mem.indexOf(u8, code[prev_end..], signifier)) |idx|
                prev_end + idx
            else
                code.len;
        const fr = FileRecord{
            .path = prev_name,
            .source = scratch.dupeZ(
                u8,
                std.mem.trim(u8, code[prev_end..next_end], "\t \n"),
            ),
        };
        try files.append(scratch.allocator(), fr);
        prev_end = next_end + signifier.len;
        if (prev_end < code.len) {
            if (std.mem.indexOf(u8, code[prev_end..], "\n")) |idx| {
                prev_name = code[prev_end..][0..idx];
                prev_end += idx + 1;
            }
        }
    }

    var kl = KnownLoader{ .files = files.items };
    var len: usize = 0;
    const asts = scratch.alloc(File, files.items.len + 1);
    for (files.items, 0..) |fr, i| {
        if (std.mem.endsWith(u8, fr.path, ".hb") or i == 0) {
            kl.loader.path = fr.path;
            kl.loader.from = @enumFromInt(i);
            kl.loader.diagnostics = output;
            kl.loader.colors = .escape_codes;

            asts[len] = .init(fr.source, &kl.loader, scratch);
            len += 1;
        }
    }

    asts[len] = .builtin(scratch);
    len += 1;

    return .{ asts[0..len], kl };
}

pub fn gatherScope(self: *Codegen) Types.Scope {
    return .{
        .file = self.file,
        .parent = self.scope.data().upcast(Types.Parent).pack(),
        .name_pos = self.name,
    };
}
