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
cmptime_values: std.ArrayList(i64) = .empty,
name: Types.Scope.NamePos = .empty,
vars: Scope = .empty,
var_pins: BBuilder.Pins,
ret_ty: Types.Id,
ret_ref: ?*BNode = null,
bl: BBuilder,
target: Types.Target = .runtime,

pub const undeclared_prefix: u8 = 0;

pub const Scope = std.MultiArrayList(VEntry);

pub const Loop = struct {
    prev: ?*Loop,
    state: union(enum) {
        cmptime: struct {
            kind: enum { falltrough, broken, continued } = .falltrough,
            pos: u32 = std.math.maxInt(u32),
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

    pub fn isPinned(self: Value, codegen: *Codegen) bool {
        return switch (self.node()) {
            .variable, .empty => false,
            .value => |v| codegen.bl.isPinned(v),
            .ptr => |p| codegen.bl.isPinned(p),
        };
    }

    pub fn load(self: Value, pos: u32, gen: *Codegen) *BNode {
        return switch (self.normalized(pos, gen)) {
            .empty => unreachable,
            .value => |v| v,
            .ptr => |p| {
                const ty = gen.types.abi
                    .categorizeAssumeReg(self.ty, gen.types);
                return gen.bl.addLoad(gen.sloc(pos), p, ty);
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

    pub fn pin(self: Value, codegen: *Codegen) ?*BNode {
        return switch (self.node()) {
            .variable, .empty => null,
            .value => |v| codegen.bl.pin(v),
            .ptr => |p| codegen.bl.pin(p),
        };
    }

    pub fn unpin(self: *Value, codegen: *Codegen, pn: ?*BNode) void {
        const tmp = self.*;
        self.* = switch (self.node()) {
            .variable, .empty => return std.debug.assert(pn == null),
            .value => .value(tmp.ty, codegen.bl.unpin(pn.?)),
            .ptr => .ptr(tmp.ty, codegen.bl.unpin(pn.?)),
        };
    }

    pub fn unpinKeep(self: *Value, codegen: *Codegen, pn: ?*BNode) void {
        const tmp = self.*;
        self.* = switch (self.node()) {
            .variable, .empty => return std.debug.assert(pn == null),
            .value => .value(tmp.ty, codegen.bl.unpinKeep(pn.?)),
            .ptr => .ptr(tmp.ty, codegen.bl.unpinKeep(pn.?)),
        };
    }

    pub fn sync(self: *Value, pn: ?*BNode) void {
        const tmp = self.*;
        self.* = switch (self.node()) {
            .variable, .empty => return std.debug.assert(pn == null),
            .value => .value(tmp.ty, pn.?.inputs()[0].?),
            .ptr => .ptr(tmp.ty, pn.?.inputs()[0].?),
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

                return switch (slot.meta.kind) {
                    .empty => .empty,
                    .cmptime => {
                        return .{ .value = gen.bl.addIntImm(
                            gen.sloc(pos),
                            Abi.categorizeBuiltinUnwrapped(self.ty.data().Builtin),
                            gen.cmptime_values.items[slot.value],
                        ) };
                    },
                    .value => .{ .value = gen.bl.getScopeValue(slot.value) },
                    .ptr => .{ .ptr = gen.var_pins.getValue(slot.value) },
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

pub const Error = error{ Report, Unreachable };

pub const UnitError = error{SyntaxError} || Error;
pub const SuffixError = error{SyntaxError} || Error;

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

pub fn emitUninitValue(self: *Codegen, pos: u32, ty: Types.Id) Value {
    return switch (self.emitUninit(pos, ty)) {
        .value => .value(ty, self.bl.addUninit(self.sloc(pos), .i64)),
        .ptr => .ptr(ty, self.bl.addUninit(self.sloc(pos), .i64)),
        .empty => .unit(ty),
    };
}

pub fn emitUninit(self: *Codegen, pos: u32, ty: Types.Id) NormalizedNode {
    var buf = Abi.Buf{};

    const slc = self.sloc(pos);

    const spec = self.types.abi.categorize(ty, self.types, &buf) orelse {
        return .empty;
    };

    if (spec.len == 0) return .empty;
    if (spec.len == 1 and spec[0] == .Reg) return .{ .value = self.bl.addUninit(slc, spec[0].Reg) };
    return .{ .ptr = self.bl.addUninit(slc, .i64) };
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

pub fn lookupIdent(
    self: *Codegen,
    scope: Types.AnyScopeRef,
    name: []const u8,
) ?Value {
    const scope_meta = scope.data().scope(self.types);
    const file = scope_meta.file.get(self.types);

    var scope_cursor = scope.data();
    while (true) {
        if (scope_cursor.downcast(Types.UnorderedScope)) |us| {
            if (us.decls(self.types).lookup(file.source, name)) |vl| {
                std.debug.assert(vl.offset == vl.root);

                var global_mem = Types.Global{
                    .scope = .{
                        .parent = scope_cursor.upcast(Types.Parent).pack(),
                        .file = scope_meta.file,
                        .name_pos = @enumFromInt(vl.offset),
                    },
                    .ty = .never,
                    .data = .empty,
                    .readonly = file.isComptime(vl.offset),
                };

                var global = &global_mem;

                const slot = self.types.global_index.intern(self.types, global);

                if (!slot.found_existing) {
                    slot.key_ptr.* = self.types.globals
                        .push(&self.types.arena, global_mem);
                }

                global = self.types.globals.at(slot.key_ptr.*);

                if (!slot.found_existing) {
                    var tmp = self.types.tmp.checkpoint();
                    defer tmp.deinit();

                    var global_gen: Codegen = undefined;
                    global_gen.init(
                        self.types,
                        scope_cursor.pack(),
                        .never,
                        tmp.arena.allocator(),
                    );
                    global_gen.name = @enumFromInt(vl.offset);
                    global_gen.target = .cmptime;

                    var lex = Lexer.init(file.source, vl.offset);

                    _ = lex.slit(.Ident);

                    var ty: ?Types.Id = null;
                    if (lex.eatMatch(.@":")) {
                        ty = self.typ(&lex) catch null;
                        _ = lex.slit(.@"=");
                    } else {
                        _ = lex.slit(.@":=");
                    }

                    global_gen.evalGlobal(&lex, ty, slot.key_ptr.*);
                }

                return .ptr(global.ty, self.bl.addGlobalAddr(
                    self.sloc(vl.offset),
                    @intFromEnum(slot.key_ptr.*),
                ));
            }
        }

        if (scope_cursor.captures(self.types).lookup(file.source, name)) |r| {
            const ty, const value = r;
            std.debug.assert(ty.data() == .Builtin);
            if (value) |vl| {
                return .value(ty, self.bl.addIntImm(
                    .none,
                    Abi.categorizeBuiltinUnwrapped(ty.data().Builtin),
                    vl,
                ));
            } else {
                return .unit(ty);
            }
        }

        scope_cursor = scope_cursor.scope(self.types)
            .parent.data().downcast(Types.AnyScope) orelse break;
    }

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

    return null;
}

pub fn evalGlobal(self: *Codegen, lex: *Lexer, ty: ?Types.Id, global_id: Types.GlobalId) void {
    const token = self.bl
        .begin(.systemv, &.{.{ .Reg = .i64 }}, &.{});
    const global = self.types.globals.at(global_id);
    const pos = lex.cursor;

    const ret_addr = self.bl
        .addParam(self.sloc(lex.cursor), 0, 0);

    const value = self.expr(
        .{ .loc = ret_addr, .ty = ty },
        lex,
    ) catch |err| switch (err) {
        error.Unreachable => self.report(
            lex.cursor,
            "the global variable needs" ++
                " be a reachable expression",
            .{},
        ) catch return,
        error.Report => return,
    };

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

    const previous_reloc_count = self.types.ct_backend.mach.out.relocs.items.len;

    self.emitToBackend(reserved, &self.types.ct_backend.mach, .debug);

    self.types.ct_backend.mach.emitData(.{
        .id = @intFromEnum(global_id),
        .value = .{ .uninit = value.ty.size(self.types) },
        .readonly = global.readonly,
        .thread_local = false,
        .uuid = @splat(0),
    });

    while (self.types.func_queue.getPtr(.cmptime).pop()) |fnid| {
        self.prepareForFunc(fnid);
        self.emitFunc(fnid) catch continue;
        self.emitToBackend(fnid, &self.types.ct_backend.mach, .debug);
    }

    hb.hbvm.object.jitLink(self.types.ct_backend.mach.out, previous_reloc_count);

    const global_sym = self.types.ct_backend.mach.out
        .getGlobalSym(@intFromEnum(global_id));

    global.ty = value.ty;
    global.data = .{
        .pos = global_sym.offset,
        .len = global_sym.size,
    };

    const func_sym = self.types.ct_backend.mach.out
        .getFuncSym(@intFromEnum(reserved));

    const log = 0 == 1;
    var stderr = if (log) std.fs.File.stderr().writer(&.{});
    var vm_ctx = Vm.SafeContext{
        .writer = if (log) &stderr.interface else null,
        .color_cfg = .escape_codes,
        .memory = self.types.ct_backend.mach.out.code.items,
        .code_start = 0,
        .code_end = 0,
    };

    self.types.vm.ip = func_sym.offset;
    self.types.vm.fuel = 1024 * 16;
    // return to hardcoded tx
    self.types.vm.regs.set(.ret_addr, Types.stack_size - 1);
    self.types.vm.regs.set(.arg(0), global.data.pos);

    while (true) switch (self.types.vm.run(&vm_ctx) catch |err| {
        self.report(pos, "the comptime execution failes: {}", .{err}) catch
            return;
    }) {
        .tx => break,
        else => unreachable, // TODO
    };
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

    const args, const returns, const ret_by_ref =
        stypes.abi.computeSignature(
            func.args,
            func.ret,
            stypes,
            tmp.arena,
        ) orelse return;

    const token = self.bl.begin(stypes.abi.cc, args, returns);

    const file = func.scope.file.get(stypes);
    self.file = func.scope.file;

    var i: usize = 0;

    if (ret_by_ref) {
        self.ret_ref = self.bl.addParam(.none, i, 0);
        i += 1;
    }

    var lex = Lexer.init(file.source, func.pos);

    const arg_iter = lex.list(.@",", .@")");
    var param_idx: usize = 0;
    while (arg_iter.next()) {
        const name, const cmptime = lex.eatIdent() orelse unreachable;
        _ = lex.slit(.@":");

        const ty = self.typ(&lex) catch .never;

        if (cmptime) {
            const index = self.defineVariable(name);

            const slot: *Variable = &self.vars.items(.variable)[index];
            const is_cmptime = slot.meta.kind == .cmptime;

            std.debug.assert(slot.value == std.math.maxInt(u32));
            std.debug.assert(is_cmptime);

            slot.ty = func.params[param_idx].ty;

            self.cmptime_values.append(
                self.bl.arena(),
                func.params[param_idx].value,
            ) catch unreachable;
            slot.value = @intCast(self.cmptime_values.items.len - 1);

            param_idx += 1;
        } else {
            var buf = Abi.Buf{};
            const splits = self.types.abi.categorize(ty, self.types, &buf).?;

            if (splits.len == 0) continue;

            const slc = self.sloc(name.pos);

            const value: Value = if (splits.len == 2) b: {
                const stack_slot = self.bl.addLocal(
                    self.sloc(name.pos),
                    ty.size(self.types),
                    @intFromEnum(ty),
                );

                self.bl.addStore(slc, stack_slot, splits[0].Reg, self.bl.addParam(slc, i, 0));
                self.emitArbitraryStore(
                    name.pos,
                    self.bl.addFieldOffset(slc, stack_slot, splits[0].Reg.size()),
                    self.bl.addParam(slc, i + 1, 0),
                    ty.size(self.types) - splits[0].Reg.size(),
                );

                break :b .ptr(ty, stack_slot);
            } else if (splits[0] == .Stack)
                .ptr(ty, self.bl.addParam(slc, i, ty.raw()))
            else
                .value(ty, self.bl.addParam(slc, i, ty.raw()));

            _ = self.pushVariable(name, value) catch unreachable;

            i += splits.len;
        }
    }

    _ = lex.slit(.@":");
    _ = self.typ(&lex) catch .never;

    const ret_pos = lex.cursor;

    var reachable = true;
    _ = self.expr(.{ .ty = .void }, &lex) catch |err| switch (err) {
        error.Report => {},
        error.Unreachable => reachable = false,
    };

    if (reachable) {
        const rets = returns orelse {
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
    opts: Machine.OptOptions.Mode,
) void {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    for (self.bl.func.getSyms().outputs()) |sym| {
        switch (sym.get().extra2()) {
            .GlobalAddr => |extra| {
                if (self.target == .cmptime) continue;

                const global: Types.GlobalId = @enumFromInt(extra.id);
                if (global.get(self.types).runtime_emmited) continue;

                global.get(self.types).runtime_emmited = true;
                backend.emitData(.{
                    .id = @intFromEnum(global),
                    .name = global.get(self.types)
                        .fmt(self.types).toString(tmp.arena),
                    .value = .{ .init = global.get(self.types)
                        .data.get(self.types) },
                    .readonly = global.get(self.types).readonly,
                    .thread_local = false,
                    .uuid = @splat(0),
                });
            },
            inline .Call, .FuncAddr => |extra| {
                const fid: Types.FuncId = @enumFromInt(extra.id);
                fid.get(self.types).queue(self.target, self.types);
            },
            else => utils.panic("{f}", .{sym}),
        }
    }

    backend.emitFunc(&self.bl.func, .{
        .id = @intFromEnum(fnid),
        .files = self.types.line_indexes,
        .is_inline = false,
        .name = if (self.target == .runtime)
            fnid.get(self.types).fmt(self.types).toString(tmp.arena)
        else
            "",
        .linkage = fnid.get(self.types).linkage,
        .optimizations = .{ .opts = .{ .mode = opts } },
        .builtins = .{},
        .uuid = @splat(0),
    });
}

pub fn emitReachable(types: *Types, gpa: std.mem.Allocator, opts: Machine.OptOptions.Mode) void {
    var self: Codegen = undefined;
    while (types.func_queue.getPtr(.runtime).pop()) |fnid| {
        // TODO: we dont want this to reinitialize the bl every time

        self.init(types, .nany(fnid), fnid.get(types).ret, gpa);
        defer self.deinit();

        self.emitFunc(fnid) catch continue;

        self.emitToBackend(fnid, types.backend, opts);

        std.debug.assert(!self.bl.func.keep);
    }
}

pub fn typedExprPrec(self: *Codegen, ty: Types.Id, ctx: Ctx, lex: *Lexer, prevPrec: u8) Error!Value {
    const pos = lex.cursor;
    var exp = try self.exprPrec(.{
        .ty = ty,
        .loc = ctx.loc,
        .in_if_or_while = ctx.in_if_or_while,
    }, lex, prevPrec);
    try self.typeCheck(pos, &exp, ty);
    return exp;
}

pub fn typedExpr(self: *Codegen, ty: Types.Id, ctx: Ctx, lex: *Lexer) Error!Value {
    return try self.typedExprPrec(ty, ctx, lex, 254);
}

pub fn expr(self: *Codegen, ctx: Ctx, lex: *Lexer) Error!Value {
    return self.exprPrec(ctx, lex, 254);
}

pub fn skipBlock(self: *Codegen, lex: *Lexer) !void {
    _ = lex.expect(.@"{") catch {
        return self.report(
            lex.cursor,
            "expected '{' since this expression is getting skipped",
            .{},
        );
    };
    lex.eatUntilClosingDelimeter();
}

const no_address_msg = "the value is not" ++
    " referncable, it has no address, use `#<expr>` to force a sill";

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

pub fn unitExpr(self: *Codegen, tok: Lexer.Token, ctx: Ctx, lex: *Lexer) UnitError!Value {
    return switch (tok.kind.expand()) {
        .Comment => .voidv,
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
        ) orelse .variable(.never, self.defineVariable(tok)),
        .@"^" => self.tyLit(tok.pos, self.types.pointerTo(try self.typ(lex))),
        .@"#" => spill: {
            var oper = try self.exprPrec(.{ .ty = ctx.ty }, lex, 1);

            switch (oper.normalized(tok.pos, self)) {
                .value => |v| {
                    const slot = ctx.loc orelse self.bl.addLocal(
                        self.sloc(tok.pos),
                        oper.ty.size(self.types),
                        @intFromEnum(oper.ty),
                    );

                    self.bl.addStore(self.sloc(tok.pos), slot, v.data_type, v);

                    break :spill .ptr(oper.ty, slot);
                },
                else => break :spill oper,
            }
        },
        .@"&" => ref: {
            var oper = try self.exprPrec(.{}, lex, 1);

            switch (oper.normalized(tok.pos, self)) {
                .value => return self.report(tok.pos, no_address_msg, .{}),
                .ptr => |p| break :ref .value(self.types.pointerTo(oper.ty), p),
                .empty => break :ref oper,
            }
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
            var oper = try self.exprPrec(.{ .ty = .bool }, lex, 1);
            try self.typeCheck(tok.pos, &oper, .bool);

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
        .@"struct" => {
            const bra = try self.expect(lex, .@"{", "to open struct definition");

            const decls = self.scope.data().decls(self.types)
                .lookupScope(tok.pos) orelse {
                return self.report(bra.pos, "malformed struct", .{});
            };
            lex.cursor = decls.end;

            const sru = self.types.structs.push(&self.types.arena, .{
                .scope = self.gatherScope(),
                .captures = .init(self, &self.types.arena),
                .decls = decls,
            });

            return self.tyLit(tok.pos, sru);
        },
        .@"{" => {
            var iter = lex.list(.@";", .@"}");
            var reached_end = false;
            while (iter.next()) {
                if (reached_end) {
                    defer lex.eatUntilClosingDelimeter();
                    self.report(lex.cursor, "code past unreachable" ++
                        " statement, use `if true <stmt>`", .{}) catch {};
                    return error.Unreachable;
                }

                var value = self.expr(.{ .ty = .void }, lex) catch |err| switch (err) {
                    error.Report => continue,
                    error.Unreachable => {
                        reached_end = true;
                        continue;
                    },
                };
                _ = self.typeCheck(lex.cursor, &value, .void) catch {};
            }

            if (reached_end) return error.Unreachable;

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
        },
        .@"$if" => {
            if (try self.peval(tok.pos, try self.expr(.{ .ty = .bool }, lex), bool)) {
                _ = try self.expr(.{ .ty = .void }, lex);

                if (lex.eatMatch(.@"else")) {
                    try self.skipBlock(lex);
                }
            } else {
                try self.skipBlock(lex);

                if (lex.eatMatch(.@"else")) {
                    _ = try self.expr(.{ .ty = .void }, lex);
                }
            }

            return .voidv;
        },
        .@"if" => {
            var cond = try self.expr(.{ .ty = .bool, .in_if_or_while = true }, lex);
            try self.typeCheck(tok.pos, &cond, .bool);

            var if_bl = self.bl.addIfAndBeginThen(
                self.sloc(tok.pos),
                cond.load(tok.end, self),
            );

            var unreachable_count: usize = 0;

            _ = self.expr(.{ .ty = .void }, lex) catch |err| {
                unreachable_count += @intFromBool(err == error.Unreachable);
            };

            const tk = if_bl.beginElse(&self.bl);

            if (lex.eatMatch(.@"else")) {
                _ = self.expr(.{ .ty = .void }, lex) catch |err| {
                    unreachable_count += @intFromBool(err == error.Unreachable);
                };
            }

            if_bl.end(&self.bl, tk);

            if (unreachable_count == 2) return error.Unreachable;

            return .voidv;
        },
        .@"$while" => {
            const checkpoint = lex.cursor;
            var end = checkpoint;

            var loop = Loop{ .prev = self.loops, .state = .{ .cmptime = .{} } };
            self.loops = &loop;
            defer self.loops = loop.prev;

            var fuel: usize = 300;

            while (fuel > 0 and try self.peval(
                tok.pos,
                try self.expr(.{ .ty = .bool }, lex),
                bool,
            )) : (fuel -= 1) {
                _ = self.expr(.{ .ty = .void }, lex) catch |err| switch (err) {
                    error.Unreachable => {},
                    error.Report => return error.Report,
                };

                end = lex.cursor;
                lex.cursor = checkpoint;

                if (loop.state.cmptime.kind == .broken) {
                    break;
                }
            }

            if (fuel == 0) {
                return self.report(tok.pos, "out of loop fuel", .{});
            }

            if (checkpoint == end) {
                _ = lex.expect(.@"{") catch {
                    return self.report(tok.pos, "expected `{`", .{});
                };
                lex.eatUntilClosingDelimeter();
            } else {
                lex.cursor = end;
            }

            return .voidv;
        },
        .@"return" => {
            var ret: Value = if (lex.peekNext().kind.canStartExpression())
                try self.expr(.{ .ty = self.ret_ty, .loc = self.ret_ref }, lex)
            else
                .voidv;

            // TODO: copy the return value, if the pointers dont match

            try self.typeCheck(tok.pos, &ret, self.ret_ty);

            if (self.bl.func.signature.returns()) |returns| {
                var buf: [Abi.max_elems]*BNode = undefined;
                if (returns.len == 1) {
                    buf[0] = ret.load(tok.pos, self);
                } else if (returns.len == 2) {
                    unreachable; // TODO
                } else if (self.ret_ref) |slt| {
                    self.emitGenericStore(tok.pos, slt, ret);
                }

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
        .Directive => |d| b: {
            _ = try self.expect(lex, .@"(", "to open the directive arguments");

            const iter = lex.list(.@",", .@")");
            const pos = lex.cursor;
            const slc = self.sloc(pos);

            const value: Value = d: switch (d) {
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
                    var oper = try self.expr(.{ .ty = .int }, lex);
                    try self.typeCheck(ps, &oper, .int);

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
                                    Abi.categorizeBuiltinUnwrapped(res.data().Builtin),
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
                                Abi.categorizeBuiltinUnwrapped(res.data().Builtin),
                            ))
                        else
                            .ptr(res, p),
                    };
                },
                .as => {
                    const ty = try self.typ(lex);

                    try self.expectNext(iter);

                    const ps = lex.cursor;

                    var value = try self.expr(.{ .ty = ty, .loc = ctx.loc }, lex);
                    try self.typeCheck(ps, &value, ty);

                    break :d value;
                },
                else => {
                    lex.eatUntilClosingDelimeter();
                    return self.report(tok.pos, "unexpected directive", .{});
                },
            };

            try self.expectEnd(iter);

            break :b value;
        },
        else => return self.report(tok.pos, "unexpected token", .{}),
    };
}

pub const SuffixCtx = struct { Lexer.Token, Lexer.Token, u8, Ctx, ?*?LLValue };

pub fn suffix(self: *Codegen, sctx: SuffixCtx, lex: *Lexer, rs: Value) SuffixError!Value {
    const tok, const top, const prevPrec, const ctx, const ass_lhs = sctx;

    var res = rs;

    switch (top.kind) {
        .@"." => {
            const field = try self.expect(lex, .Ident, "to access a field");

            if (lex.eatMatch(.@"(")) {
                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();

                var scope = res.ty;
                if (res.ty.data() == .Pointer) {
                    scope = res.ty.data().Pointer.get(self.types).ty;
                }

                const ascope = scope.data().downcast(Types.AnyScope) orelse {
                    lex.eatUntilClosingDelimeter();
                    return self.report(top.pos, "can not dispatch a function on {}", .{scope});
                };

                const value = self.lookupIdent(ascope.pack(), field.view(lex.source)) orelse {
                    lex.eatUntilClosingDelimeter();
                    return self.report(top.pos, "{} does not define this", .{scope});
                };

                const llres = LLValue.init(tok.pos, res);
                const fnid, const args = try self.resolveFunction(field.pos, llres, value, lex, tmp.arena);

                res = try self.emitCall(
                    ctx,
                    field.end,
                    fnid.get(self.types).sig(),
                    .{ .func = fnid },
                    args,
                );
            } else {
                if (res.ty.data() == .Pointer) {
                    res = .ptr(
                        res.ty.data().Pointer.get(self.types).ty,
                        res.load(top.pos, self),
                    );
                }

                switch (res.ty.data()) {
                    .Builtin => |b| switch (b) {
                        .never => return .never,
                        else => return self.report(field.pos, "TODO: {}", .{b}),
                    }, // TODO
                    .Pointer => return self.report(
                        field.pos,
                        "double pointer indirection cannot be auto-dereferenced",
                        .{},
                    ),
                    .Array, .FuncTy => return self.report(field.pos, "{} doesn't have fields", .{res.ty}),
                    .Struct => |s| {
                        const index = s.get(self.types).lookupField(
                            self.types,
                            field.view(lex.source),
                        ) orelse {
                            return self.report(field.pos, "undefined field on {}, TODO: list fields", .{res.ty});
                        };
                        const lfield = s.get(self.types).getLayout(self.types).fields[index];

                        res = switch (res.normalized(field.pos, self)) {
                            .empty => .unit(lfield.ty),
                            .value => |v| b: {
                                std.debug.assert(lfield.offset == 0);
                                break :b .value(lfield.ty, v);
                            },
                            .ptr => |p| .ptr(
                                lfield.ty,
                                self.bl.addFieldOffset(self.sloc(field.pos), p, lfield.offset),
                            ),
                        };
                    },
                }
            }
        },
        .@".*" => {
            if (res.ty.data() == .Pointer) {
                res = .ptr(
                    res.ty.data().Pointer.get(self.types).ty,
                    res.load(top.pos, self),
                );
            } else {
                return self.report(top.pos, "cant dereference non pointer type", .{});
            }
        },
        .@".{" => {
            errdefer lex.eatUntilClosingDelimeter();

            const ty = try self.peval(tok.pos, res, Types.Id);

            const slot = self.emitLoc(top.pos, ty, ctx);

            switch (ty.data()) {
                .Builtin, .FuncTy, .Pointer, .Array => return self.report(
                    top.pos,
                    "{} can not be initialized this way",
                    .{ty},
                ),
                .Struct => |s| try self.structCtor(top, s, lex, slot),
            }

            res = .ptr(ty, slot);
        },
        .@"[" => index: {
            var base = LLValue.init(tok.pos, res);
            defer base.deinit(self);
            var index: ?LLValue = null;
            defer if (index) |*i| i.deinit(self);
            var end_index: ?LLValue = null;
            defer if (end_index) |*i| i.deinit(self);
            var is_slice = false;

            if (!lex.eatMatch(.@"..")) {
                index = .init(top.pos, try self.exprPrec(
                    .{ .ty = .uint },
                    lex,
                    Lexer.Lexeme.@"..".precedence(false),
                ));
            } else {
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

            if (is_slice) {
                return self.report(lex.cursor, "TODO: slicing", .{});
            }

            _ = try self.expect(lex, .@"]", "to close the indexing");

            switch (base.value.ty.data()) {
                .Builtin, .FuncTy => return self.report(top.pos, "{} can not be indexed", .{base.value.ty}),
                .Pointer => unreachable, // TODO
                .Array => |a| {
                    const ptr = switch (base.value.normalized(top.pos, self)) {
                        .empty => if (a.get(self.types).len.s == 0) {
                            return self.report(top.pos, "can't index empty array", .{});
                        } else {
                            res = .unit(a.get(self.types).elem);
                            break :index;
                        },
                        .value => return self.report(top.pos, no_address_msg, .{}),
                        .ptr => |p| p,
                    };

                    res = .ptr(
                        a.get(self.types).elem,
                        self.bl.addIndexOffset(
                            self.sloc(top.pos),
                            ptr,
                            .iadd,
                            a.get(self.types).elem.size(self.types),
                            index.?.load(self),
                        ),
                    );
                },
                else => unreachable,
            }
        },
        .@".[" => {
            const elem = self.peval(top.pos, res, Types.Id) catch |err| {
                lex.eatUntilClosingDelimeter();
                return err;
            };

            const slot = ctx.loc orelse self.bl.addLocal(self.sloc(top.pos), 0, 0);

            var list = lex.list(.@",", .@"]");
            var offset: Types.Size = 0;
            var i: Types.Size = 0;
            while (list.next()) : (i += 1) {
                const loc = self.bl.addFieldOffset(self.sloc(top.pos), slot, offset);
                const value = self.typedExpr(elem, .{ .loc = loc }, lex) catch {
                    if (list.recover()) break else continue;
                };
                self.emitGenericStore(top.pos, loc, value);

                offset += elem.size(self.types);
            }

            res = .ptr(self.types.arrayOf(elem, i), slot);
        },
        .@"(" => call: {
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const fid, const args =
                self.resolveFunction(top.pos, null, res, lex, tmp.arena) catch {
                    lex.eatUntilClosingDelimeter();
                    res = .never;
                    break :call;
                };
            const func = fid.get(self.types);

            res = self.emitCall(
                ctx,
                top.pos,
                func.sig(),
                .{ .func = fid },
                args,
            ) catch .never;
        },
        .@"=" => {
            var dst = LLValue.init(tok.pos, res);
            defer dst.deinit(self);

            const value = try self.typedExprPrec(dst.value.ty, .{
                .loc = switch (dst.value.normalized(tok.pos, self)) {
                    .ptr => |p| p,
                    else => null,
                },
            }, lex, prevPrec);

            try self.assign(top.pos, dst.value, value);

            res = .voidv;
        },
        .@":", .@":=" => {
            var ty: ?Types.Id = null;
            var eq = top;

            if (top.kind == .@":") {
                ty = self.typ(lex) catch .never;
                eq = try self.expect(lex, .@"=", " to assign a value");
            }

            // NOTE: initialized later
            const loc = self.bl.addLocal(self.sloc(tok.pos), 0, 0);

            var value = try self.exprPrec(.{ .loc = loc, .ty = ty }, lex, prevPrec);
            if (ty) |t| try self.typeCheck(eq.pos, &value, t);

            const index = switch (res.node()) {
                .variable => |i| i,
                .value, .ptr, .empty => return self.report(tok.pos, "" ++
                    "can't use this as an identifier (DEBUG: {})", .{res.tag}),
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

            self.bl.resizeLocal(
                loc,
                value.ty.size(self.types),
                @intFromEnum(value.ty),
            );

            switch (value.normalized(tok.pos, self)) {
                .value, .empty => {},
                .ptr => |p| if (p != loc) {
                    if (value.ty.isScalar(self.types)) {
                        value = .value(value.ty, value.load(eq.pos, self));
                    } else {
                        self.emitGenericStore(eq.pos, loc, value);
                        value = .ptr(value.ty, loc);
                    }
                },
            }

            // could have been an error
            if (slot.value == std.math.maxInt(u32)) {
                self.declareVariable(eq.pos, index, value) catch {};
            }

            res = .voidv;
        },
        .@"&&" => and_: {
            var lhs = LLValue.init(tok.pos, res);
            errdefer lhs.deinit(self);

            try self.typeCheckLL(&lhs, .bool);

            var if_bl = self.bl.addIfAndBeginThen(
                self.sloc(top.pos),
                lhs.load(self),
            );

            var alt = LLValue.init(
                lex.cursor,
                self.exprPrec(.{
                    .ty = .bool,
                    .in_if_or_while = ctx.in_if_or_while,
                }, lex, prevPrec) catch |err| switch (err) {
                    error.Unreachable => {
                        if_bl.end(&self.bl, if_bl.beginElse(&self.bl));

                        res = .value(.bool, self.bl.addIntImm(
                            self.sloc(top.pos),
                            .i8,
                            0,
                        ));

                        break :and_;
                    },
                    error.Report => self.emitUninitValue(top.pos, .bool),
                },
            );
            defer alt.deinit(self);

            alt.set(.value(.bool, alt.load(self)));

            if_bl.end(&self.bl, if_bl.beginElse(&self.bl));

            if (ass_lhs) |al| al.* = lhs;

            res = Value.value(.bool, self.bl.addPhi(
                self.sloc(top.pos),
                alt.load(self),
                self.bl.addIntImm(self.sloc(top.pos), .i8, 0),
            ));
        },
        .@"||" => or_: {
            if (res.ty != .bool) {
                unreachable; // TODO
            }

            var lhs = LLValue.init(tok.pos, res);
            errdefer lhs.deinit(self);

            try self.typeCheckLL(&lhs, .bool);

            var if_bl = self.bl.addIfAndBeginThen(
                self.sloc(top.pos),
                lhs.load(self),
            );

            const tk = if_bl.beginElse(&self.bl);

            var alt = LLValue.init(
                lex.cursor,
                self.exprPrec(.{
                    .ty = .bool,
                }, lex, prevPrec) catch |err| switch (err) {
                    error.Unreachable => {
                        if_bl.end(&self.bl, tk);

                        res = .value(.bool, self.bl.addIntImm(
                            self.sloc(top.pos),
                            .i8,
                            0,
                        ));

                        break :or_;
                    },
                    error.Report => self.emitUninitValue(tok.pos, .bool),
                },
            );
            defer alt.deinit(self);
            alt.set(.value(.bool, alt.load(self)));

            if_bl.end(&self.bl, tk);

            if (ass_lhs) |al| al.* = lhs;

            res = .value(.bool, self.bl.addPhi(
                self.sloc(top.pos),
                self.bl.addIntImm(self.sloc(top.pos), .i8, 0),
                alt.load(self),
            ));
        },
        else => {
            var lhs = LLValue.init(lex.cursor, res);
            errdefer lhs.deinit(self);

            var rhs = LLValue.init(
                lex.cursor,
                try self.exprPrec(.{ .ty = lhs.value.ty }, lex, prevPrec),
            );
            defer rhs.deinit(self);

            var oper_ty = ctx.ty orelse lhs.value.ty;

            if (ass_lhs != null) oper_ty = lhs.value.ty;
            if (top.kind.isComparison()) oper_ty = lhs.value.ty;
            if (!lhs.value.ty.canUpcast(oper_ty, self.types)) {
                oper_ty = lhs.value.ty;
            }

            if (ass_lhs == null) {
                oper_ty = self.binOpUpcast(oper_ty, rhs.value.ty) catch {
                    return self.report(
                        top.pos,
                        "incompatible operands, {} {} {}",
                        .{ oper_ty, top.view(lex.source), rhs.value.ty },
                    );
                };
            } else {
                oper_ty = lhs.value.ty;
            }

            try self.typeCheckLL(&lhs, oper_ty);
            try self.typeCheckLL(&rhs, oper_ty);

            if (lhs.value.ty == .never or rhs.value.ty == .never) return .never;

            var result: Types.Id =
                if (top.kind.isComparison()) .bool else oper_ty;

            const op = try self.lexemeToBinOp(top.pos, top.kind, oper_ty);

            if (ass_lhs) |al| al.* = lhs;

            res = Value.value(result, self.bl.addBinOp(
                self.sloc(top.pos),
                op,
                Abi.categorizeBuiltinUnwrapped(result.data().Builtin),
                lhs.load(self),
                rhs.load(self),
            ));
        },
    }

    return res;
}

pub fn structCtor(
    self: *Codegen,
    top: Lexer.Token,
    s: Types.StructId,
    lex: *Lexer,
    slot: *BNode,
) !void {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const stru = s.get(self.types);
    const layout = stru.getLayout(self.types);

    var seen = std.DynamicBitSetUnmanaged
        .initEmpty(tmp.arena.allocator(), layout.fields.len) catch unreachable;
    var field_iter = lex.list(.@",", .@"}");
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
                    error.Unreachable => return err,
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
                self.sloc(top.pos),
                slot,
                field.offset,
            );
            const src = self.bl.addGlobalAddr(
                self.sloc(top.pos),
                @intFromEnum(field.default),
            );
            self.bl.addFixedMemCpy(
                self.sloc(top.pos),
                loc,
                src,
                field.ty.size(self.types),
            );
        } else {
            const field_name = stru.fieldName(self.types, index);
            self.report(
                top.pos,
                "constructor is missin {} field",
                .{field_name},
            ) catch {};
        }
    }
}

pub fn exprPrec(self: *Codegen, ctx: Ctx, lex: *Lexer, prevPrec: u8) Error!Value {
    const tok = lex.next();

    var res: Value = self.unitExpr(tok, ctx, lex) catch |err| switch (err) {
        error.SyntaxError => return error.Report,
        error.Unreachable => return error.Unreachable,
        error.Report => .never,
    };

    while (true) {
        var top = lex.peekNext();
        var is_ass_op = false;

        if (top.kind.innerOp()) |op| {
            top.kind = op;
            is_ass_op = true;
        }

        const prec = top.kind.precedence(ctx.in_if_or_while);
        if (prec >= prevPrec) break;

        lex.cursor = top.end;

        var ass_lhs: ?LLValue = null;

        // put this into a function and handle the error here
        res = self.suffix(.{
            tok, top, prec, ctx, if (is_ass_op) &ass_lhs else null,
        }, lex, res) catch |err| switch (err) {
            error.SyntaxError => return error.Report,
            error.Unreachable => return error.Unreachable,
            error.Report => .never,
        };

        if (ass_lhs) |*lhs| {
            if (is_ass_op) {
                try self.assign(top.pos, lhs.value, res);
                lhs.deinit(self);
                res = .voidv;
            } else {
                lhs.deinitKeep();
            }
        }
    }

    return res;
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

pub fn expect(self: *Codegen, lex: *Lexer, to_expect: Lexer.Lexeme, comptime msg: []const u8) error{SyntaxError}!Lexer.Token {
    return lex.expect(to_expect) catch {
        self.report(lex.cursor, "expected '=' " ++ msg, .{}) catch
            return error.SyntaxError;
    };
}

pub fn expectNext(self: *Codegen, iter: anytype) !void {
    if (!iter.next()) return self.report(iter.lexer.cursor, "expected nexti item", .{});
}

pub fn expectEnd(self: *Codegen, iter: anytype) !void {
    if (iter.next()) return self.report(iter.lexer.cursor, "expected list end", .{});
}

pub fn resolveFunction(self: *Codegen, pos: u32, caller: ?LLValue, res: Value, lex: *Lexer, scratch: *utils.Arena) !struct { Types.FuncId, []LLValue } {
    if (res.ty == .template) {
        return try self.instantiateTemplate(
            try self.peval(pos, res, Types.TemplateId),
            lex,
            scratch,
        );
    } else {
        // TODO: maybe faactor this out
        const fid = try self.peval(pos, res, Types.FuncId);
        const func = fid.get(self.types);

        var args = scratch.makeArrayList(LLValue, func.args.len);
        errdefer for (args.items) |*v| v.deinit(self);

        var i: usize = 0;
        if (caller) |cl| {
            var c = args.addOneAssumeCapacity();
            c.* = cl;

            var caller_ty = func.args[i];
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
                c.value = .value(func.args[i], switch (c.value.normalized(c.pos, self)) {
                    .empty => self.bl.addUninit(self.sloc(c.pos), .i64),
                    .value => return self.report(c.pos, no_address_msg, .{}),
                    .ptr => |p| p,
                });
            }
        }

        const iter = lex.list(.@",", .@")");
        while (iter.next()) : (i += 1) {
            const ty = if (i < func.args.len) func.args[i] else null;

            const ps = lex.cursor;
            var arg = self.expr(.{ .ty = ty }, lex) catch |err| switch (err) {
                error.Unreachable => return err,
                error.Report => if (iter.recover()) break else continue,
            };

            if (ty) |t| self.typeCheck(ps, &arg, t) catch {};

            var llv = LLValue.init(ps, arg);

            args.appendBounded(llv) catch {
                llv.deinit(self);
                self.report(ps, "extra argment", .{}) catch {};
            };
        }

        if (args.items.len < func.args.len) {
            for (args.items) |*v| v.deinit(self);
            return self.report(
                lex.cursor,
                "{} missing arguments",
                .{func.args.len - args.items.len},
            );
        }

        return .{ fid, args.items };
    }
}

pub fn emitCall(
    self: *Codegen,
    ctx: Ctx,
    pos: u32,
    sig: Types.FuncTy,
    func: union(enum) { func: Types.FuncId, ptr: LLValue },
    args: []LLValue,
) !Value {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const params, const returns, const ret_by_ref = self.types.abi
        .computeSignature(
        sig.args,
        sig.ret,
        self.types,
        tmp.arena,
    ) orelse {
        std.debug.assert(self.types.errored != 0);
        return .never;
    };

    const call_args = self.bl
        .allocCallArgs(tmp.arena, params, returns, switch (func) {
        .func => null,
        .ptr => |p| p.value.load(pos, self),
    });

    var cursor: usize = 0;
    var loc: ?*BNode = null;

    if (ret_by_ref) {
        loc = self.emitLoc(pos, sig.ret, ctx);
        call_args.arg_slots[cursor] = loc.?;
        cursor += 1;
    }

    for (args, sig.args) |*arg, arg_ty| {
        var buf = Abi.Buf{};
        const splits = self.types.abi
            .categorize(arg_ty, self.types, &buf).?;
        if (splits.len == 0) continue;

        if (splits.len == 2) {
            const ptr = arg.value.normalized(arg.pos, self).ptr;
            call_args.arg_slots[cursor] = self.bl.addLoad(self.sloc(arg.pos), ptr, splits[0].Reg);
            call_args.arg_slots[cursor + 1] = self.emitArbitraryLoad(
                arg.pos,
                self.bl.addFieldOffset(self.sloc(arg.pos), ptr, splits[0].Reg.size()),
                splits[1].Reg,
                arg_ty.size(self.types) - splits[0].Reg.size(),
            );
        } else if (splits.len == 1 and splits[0] != .Reg) {
            call_args.arg_slots[cursor] = arg.value.normalized(arg.pos, self).ptr;
        } else {
            call_args.arg_slots[cursor] = arg.value.load(arg.pos, self);
        }
        cursor += splits.len;

        arg.deinitKeep();
    }

    const result = self.bl.addCall(
        self.sloc(pos),
        self.types.abi.cc,
        switch (func) {
            .func => |fid| @intFromEnum(fid),
            .ptr => graph.indirect_call,
        },
        .is_sym,
        call_args,
    ) orelse return error.Unreachable;

    return if (loc) |l|
        .ptr(sig.ret, l)
    else if (result.len == 0)
        .unit(sig.ret)
    else if (result.len == 1)
        .value(sig.ret, result[0])
    else
        unreachable;
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
            const shift = self.bl.addIntImm(slc, .i8, @intCast(offset * 8));
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
    return ctx.loc orelse
        self.bl.addLocal(self.sloc(pos), ty.size(self.types), @intFromEnum(ty));
}

pub fn instantiateTemplate(
    self: *Codegen,
    template_id: Types.TemplateId,
    lex: *Lexer,
    scratch: *utils.Arena,
) !struct { Types.FuncId, []LLValue } {
    const template = template_id.get(self.types);
    const template_file = template.scope.file.get(self.types);

    var tmp = self.types.tmp.checkpoint();
    defer tmp.deinit();

    var template_gen: Codegen = undefined;
    template_gen.init(
        self.types,
        .nany(template_id),
        .never,
        tmp.arena.allocator(),
    );

    var param_lex = Lexer.init(template_file.source, template.pos);

    var args = std.ArrayList(LLValue).empty;
    errdefer for (args.items) |*v| v.deinit(self);

    var params = std.ArrayList(Types.Func.Param).empty;

    const arg_iter = lex.list(.@",", .@")");
    const param_iter = param_lex.list(.@",", .@")");

    var errored = false;
    while (true) {
        const param_next = param_iter.next();
        const arg_next = arg_iter.next();
        if (!param_next or !arg_next) break;

        var round_errored = true;
        defer errored = errored or round_errored;
        const ident, const cmptime = param_lex.eatIdent() orelse {
            self.report(param_lex.cursor, "expected argument name", .{}) catch {};
            if (param_iter.recover()) break else continue;
            if (arg_iter.recover()) break else continue;
        };

        _ = param_lex.expect(.@":") catch {
            self.report(param_lex.cursor, "expected ':'", .{}) catch {};
            if (param_iter.recover()) break else continue;
            if (arg_iter.recover()) break else continue;
        };

        const ty = template_gen.typ(&param_lex) catch {
            if (param_iter.recover()) break else continue;
            if (arg_iter.recover()) break else continue;
        };

        const pos = lex.cursor;
        const value = self.expr(.{ .ty = ty }, lex) catch |err| switch (err) {
            error.Unreachable => return err,
            error.Report => {
                if (arg_iter.recover()) break else continue;
            },
        };

        if (cmptime) {
            const index = template_gen.defineVariable(ident);

            const slot: *Variable = &template_gen.vars.items(.variable)[index];
            const is_cmptime = slot.meta.kind == .cmptime;

            std.debug.assert(slot.value == std.math.maxInt(u32));
            std.debug.assert(is_cmptime);

            slot.ty = value.ty;

            const vl = try self.peval(pos, value, i64);
            template_gen.cmptime_values.append(self.bl.arena(), vl) catch unreachable;
            slot.value = @intCast(template_gen.cmptime_values.items.len - 1);

            params.append(scratch.allocator(), .{
                .ty = ty,
                .value = vl,
            }) catch unreachable;
        } else {
            args.append(scratch.allocator(), .init(pos, value)) catch unreachable;
        }
        round_errored = false;
    }

    _ = param_lex.expect(.@":") catch {
        return template_gen.report(param_lex.cursor, "BUG", .{});
    };
    const ret = try template_gen.typ(&param_lex);

    var func_mem = Types.Func{
        .scope = template_gen.gatherScope(),
        .pos = template.pos,
        .params = params.items,
        .args = &.{},
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
        const arg_tys = self.types.arena.alloc(Types.Id, args.items.len);
        for (args.items, arg_tys) |a, *slt| {
            slt.* = a.value.ty;
        }
        func.args = arg_tys;
        func.params = self.types.arena.dupe(Types.Func.Param, func.params);
    }

    return .{ slot.key_ptr.*, args.items };
}

pub fn assign(self: *Codegen, pos: u32, dest: Value, src: Value) !void {
    switch (dest.node()) {
        .variable => |i| {
            const slot: *Variable = &self.vars.items(.variable)[i];

            switch (slot.meta.kind) {
                .empty => {},
                .value => self.bl.setScopeValue(
                    slot.value,
                    src.load(pos, self),
                ),
                .ptr => unreachable, // TODO
                .cmptime => {
                    const slt = &self.cmptime_values.items[slot.value];
                    slt.* = try self.peval(pos, src, i64);
                },
            }
        },
        .ptr => |p| {
            self.emitGenericStore(pos, p, src);
        },
        .value => {
            self.report(pos, "can't assign to a value", .{}) catch {};
        },
        .empty => {},
    }
}

pub fn @"fn"(self: *Codegen, lex: *Lexer) !union(enum) {
    func: struct { Types.FuncId, Types.FuncTyId },
    template: Types.TemplateId,
} {
    _ = lex.expect(.@"(") catch {
        return self.report(lex.cursor, "expected '(' as a start of" ++
            " argument list", .{});
    };

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var args = std.ArrayList(Types.Id).empty;

    const pos = lex.cursor;

    const arg_iter = lex.list(.@",", .@")");
    while (arg_iter.next()) {
        _, const cmptime = lex.eatIdent() orelse {
            self.report(lex.cursor, "expected argument name", .{}) catch {};
            if (arg_iter.recover()) break else continue;
        };

        if (cmptime) {
            lex.eatUntilClosingDelimeter();

            _ = lex.expect(.@":") catch {
                return self.report(lex.cursor, "expected ':' as a start of" ++
                    " return type", .{});
            };

            const kind = lex.eatUntilSameLevelToken(&.{.@"{"});
            switch (kind) {
                .@"{" => lex.eatUntilClosingDelimeter(),
                else => return self.report(lex.cursor, "invalid function body", .{}),
            }

            return .{ .template = self.types.templates.push(
                &self.types.arena,
                Types.Template{
                    .scope = self.gatherScope(),
                    .captures = .init(self, &self.types.arena),
                    .pos = pos,
                },
            ) };
        }

        _ = lex.expect(.@":") catch {
            return self.report(lex.cursor, "expected ':' as a start of" ++
                " argument type", .{});
        };

        args.append(
            tmp.arena.allocator(),
            self.typ(lex) catch continue,
        ) catch unreachable;
    }

    _ = lex.expect(.@":") catch {
        return self.report(lex.cursor, "expected ':' as a start of" ++
            " return type", .{});
    };

    const ret = self.typ(lex) catch {
        return self.report(lex.cursor, "expected return type", .{});
    };

    const kind = lex.eatUntilSameLevelToken(&.{.@"{"});
    switch (kind) {
        .@"{" => lex.eatUntilClosingDelimeter(),
        else => return self.report(lex.cursor, "invalid function body", .{}),
    }

    const func = Types.Func{
        .scope = self.gatherScope(),
        .params = &.{},
        .captures = .init(self, &self.types.arena),
        .args = self.types.arena.dupe(Types.Id, args.items),
        .ret = ret,
        .pos = pos,
    };

    const id = self.types.funcs.push(&self.types.arena, func);

    var fn_ty_inst = Types.FuncTy{
        .args = func.args,
        .ret = ret,
    };

    const slot = self.types.func_ty_index
        .intern(self.types, &fn_ty_inst);

    if (!slot.found_existing) {
        slot.key_ptr.* = self.types.func_tys.push(
            &self.types.arena,
            fn_ty_inst,
        );
    }

    return .{ .func = .{ id, slot.key_ptr.* } };
}

pub fn peval(self: *Codegen, pos: u32, value: Value, comptime T: type) !T {
    switch (T) {
        Types.FuncId => {
            if (value.ty.data() != .FuncTy) {
                return self.report(pos, "expected function," ++
                    " got {}", .{value.ty});
            }
        },
        Types.TemplateId => {
            if (value.ty != .template) {
                return self.report(pos, "expected template," ++
                    " got {}", .{value.ty});
            }
        },
        Types.Id => {
            if (value.ty != .type) {
                return self.report(pos, "expected type," ++
                    " got {}", .{value.ty});
            }
        },
        bool => {
            if (value.ty != .bool) {
                return self.report(pos, "expected bool," ++
                    " got {}", .{value.ty});
            }
        },
        else => {},
    }

    const res = try self.partialEval(value.load(pos, self));

    switch (T) {
        Types.TemplateId => {
            if (res.kind != .CInt) {
                return self.report(pos, "comptime type mismatch," ++
                    " expected constant but got {}", .{res});
            }

            const val = res.extra(.CInt).value;

            if (val < 0 or self.types.templates.meta.len <= val) {
                return self.report(pos, "invalid function id", .{});
            }

            return @enumFromInt(val);
        },
        Types.FuncId => {
            if (res.kind != .CInt) {
                return self.report(pos, "comptime type mismatch," ++
                    " expected constant but got {}", .{res});
            }

            const val = res.extra(.CInt).value;

            if (val < 0 or self.types.funcs.meta.len <= val) {
                return self.report(pos, "invalid function id", .{});
            }

            return @enumFromInt(val);
        },
        Types.Id => {
            if (res.kind != .CInt) {
                return self.report(pos, "comptime type mismatch," ++
                    " expected constant but got {}", .{res});
            }

            const val = std.math.cast(u32, res.extra(.CInt).value) orelse {
                return self.report(pos, "the type value is corrupted, (out of range)", .{res});
            };

            const ty: Types.Id = @enumFromInt(val);

            const repr = ty.repr();
            const tag = std.meta.intToEnum(
                std.meta.Tag(Types.Data),
                repr.tag,
            ) catch {
                return self.report(pos, "the type value is corrupted, (invalid tag)", .{res});
            };

            switch (tag) {
                .Builtin => _ = std.meta.intToEnum(Types.Builtin, repr.index) catch {
                    return self.report(pos, "the type value is corrupted, (invlaid builtin)", .{res});
                },
                inline else => |t| {
                    const Payload = std.meta.TagPayload(Types.Data, t);

                    const store = @field(self.types, Payload.data.field);

                    if (store.meta.len <= repr.index) {
                        return self.report(pos, "the type value is corrupted, (out of bounds)", .{res});
                    }
                },
            }

            return ty;
        },
        i64 => {
            if (res.kind != .CInt) {
                return self.report(pos, "comptime type mismatch," ++
                    " expected constant but got {}", .{res});
            }

            return res.extra(.CInt).value;
        },
        bool => {
            if (res.kind != .CInt) {
                return self.report(pos, "comptime type mismatch," ++
                    " expected constant but got {}", .{res});
            }

            return res.extra(.CInt).value != 0;
        },
        else => @compileError("TODO: " ++ @typeName(T)),
    }
}

pub fn partialEval(self: *Codegen, value: *BNode) !*BNode {
    switch (value.extra2()) {
        .GlobalAddr, .CInt => return value,
        .Load => {
            const base = try self.partialEval(value.base());

            switch (base.extra2()) {
                .GlobalAddr => |extra| {
                    const gid: Types.GlobalId = @enumFromInt(extra.id);
                    const mem = gid.get(self.types).data.get(self.types);

                    var val: i64 = 0;
                    @memcpy(
                        std.mem.asBytes(&val)[0..@intCast(value.data_type.size())],
                        mem[0..@intCast(value.data_type.size())],
                    );

                    const res = self.bl.addIntImm(.none, value.data_type, val);
                    self.bl.func.subsume(res, value, .intern);
                    return res;
                },
                else => return self.reportSloc(
                    value.sloc,
                    "TODO: handle load fromt this this: {}",
                    .{value},
                ),
            }
        },
        else => return self.reportSloc(
            value.sloc,
            "TODO: handle this: {}",
            .{value},
        ),
    }
}

pub fn reportSloc(self: *Codegen, slc: graph.Sloc, fmt: []const u8, args: anytype) error{Report} {
    @branchHint(.cold);

    self.types.report(@enumFromInt(slc.namespace), slc.index, fmt, args);
    self.types.errored += 1;
    return error.Report;
}

// Long Lived
pub const LLValue = struct {
    value: Value,
    pos: u32,
    prev_id: u16,
    checksum: if (graph.is_debug) ?*BNode else void,

    pub fn init(pos: u32, value: Value) LLValue {
        return .{
            .value = value,
            .pos = pos,
            .prev_id = switch (value.node()) {
                .empty, .variable => 0,
                .value, .ptr => |p| p.lock().prev_id,
            },
            .checksum = if (graph.is_debug) switch (value.node()) {
                .empty, .variable => null,
                .value, .ptr => |p| p,
            },
        };
    }

    pub fn set(self: *LLValue, to: Value) void {
        self.tmpUnlock();
        self.value = to;
        self.tmpLock();
    }

    pub fn tmpUnlock(self: *LLValue) void {
        switch (self.value.node()) {
            .empty, .variable => {},
            .value, .ptr => |p| {
                std.debug.assert(p == self.checksum);
                BNode.Lock.unlock(.{ .prev_id = self.prev_id, .node = p });
            },
        }
    }

    pub fn tmpLock(self: *LLValue) void {
        self.prev_id = switch (self.value.node()) {
            .empty, .variable => 0,
            .value, .ptr => |p| b: {
                self.checksum = p;
                break :b p.lock().prev_id;
            },
        };
    }

    pub fn deinitKeep(self: *LLValue) void {
        self.tmpUnlock();
        self.* = undefined;
    }

    pub fn deinit(self: *LLValue, gen: *Codegen) void {
        switch (self.value.node()) {
            .empty, .variable => {},
            .value, .ptr => |p| {
                std.debug.assert(p == self.checksum);
                BNode.Lock.unlock(.{ .prev_id = self.prev_id, .node = p });
                // NOTE: we make sure we are not locked as locks stack
                if (p.outputs().len == 0 and p.id != self.prev_id) {
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
    const unsigned = ty.isBuiltin(.isUnsigned) or ty == .bool or ty == .type;
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
    ll: *LLValue,
    expected: Types.Id,
) error{Report}!void {
    ll.tmpUnlock();
    defer ll.tmpLock();
    return self.typeCheck(ll.pos, &ll.value, expected);
}

pub fn typeCheck(
    self: *Codegen,
    pos: u32,
    got: *Value,
    expected: Types.Id,
) error{Report}!void {
    if (expected == got.ty) return;

    if (expected == .never or got.ty == .never) {
        return error.Report;
    }

    if (got.ty.canUpcast(expected, self.types)) {
        const sloca = self.sloc(pos);
        const res_dt = Abi.categorizeBuiltinUnwrapped(expected.data().Builtin);

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
            .ty = .never,
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
        const vl = try self.peval(pos, value, i64);
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

    if (!self.bl.isUnreachable()) {
        self.bl.truncateScope(self.bl.scopeSize() - truncate_vals_by);
    }

    self.var_pins.truncate(&self.bl, self.var_pins.len() - truncate_slots_by);
    self.cmptime_values.items.len -= truncate_cmptime_by;

    @memset(poped_vars, undefined);
    self.vars.len = scope_marker;
}

pub fn collectExports(types: *Types, gpa: std.mem.Allocator) !void {
    _ = gpa;
    const root = File.Id.root.get(types);

    errdefer {
        root.decls.log(0, types.loader.diagnostics.?) catch {};
    }

    const decl = root.decls.lookup(root.source, "main") orelse {
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

    std.debug.assert(decl.root == decl.offset); // TODO

    var tmp = types.tmp.checkpoint();
    defer tmp.deinit();

    var self: Codegen = undefined;
    self.init(types, root.root_sope, .never, tmp.arena.allocator());
    self.name = @enumFromInt(decl.offset);

    var lex = Lexer.init(root.source, decl.offset);

    _ = lex.expect(.Ident) catch unreachable; // TODO
    _ = lex.expect(.@":=") catch unreachable; // TODO

    _ = lex.expect(.@"fn") catch {
        return self.report(lex.cursor, "expected function", .{});
    };

    const func = switch (try self.@"fn"(&lex)) {
        .template => return self.report(lex.cursor, "main function cannot be a template", .{}),
        .func => |v| v[0],
    };

    func.get(types).linkage = .exported;

    func.get(types).queue(.runtime, types);
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
        self.exprPrec(
            .{ .ty = .type },
            lex,
            Lexer.Lexeme.@"=".precedence(false) - 1,
        ) catch |err| switch (err) {
            error.Unreachable => {
                return self.report(
                    lex.cursor,
                    "type expression should not be unreachable",
                    .{},
                );
            },
            error.Report => return error.Report,
        },
        Types.Id,
    );
}

pub fn dbgReport(self: *Codegen, pos: u32, msg: []const u8, args: anytype) void {
    self.types.report(self.file, pos, msg, args);
}

pub fn report(self: *Codegen, pos: u32, msg: []const u8, args: anytype) error{Report} {
    @branchHint(.cold);

    self.types.report(self.file, pos, msg, args);
    self.types.errored += 1;
    return error.Report;
}

pub fn reportGeneric(path: []const u8, source: [:0]const u8, types: *Types, pos: u32, msg: []const u8, args: anytype) void {
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

    var scratch = utils.Arena.init(1024 * 1024 * 16);
    var writer = std.fs.File.stderr().writer(&.{});

    const asts, var kl = try parseExample(
        &scratch,
        name,
        code,
        &writer.interface,
    );

    const opt_mode = Machine.OptOptions.Mode.release;

    const backend = hb.backend.Machine.SupportedTarget.@"x86_64-linux"
        .toMachine(&scratch, gpa);
    defer backend.deinit();

    var types = Types.init(asts, &kl.loader, backend, scratch, gpa);
    defer types.deinit();

    try collectExports(&types, gpa);

    emitReachable(&types, gpa, opt_mode);

    const exp = Expectations.init(asts[0].source);

    if (exp.should_error) {
        try std.testing.expect(types.errored != 0);
        return;
    }

    try std.testing.expect(types.errored == 0);

    var exe = backend.finalizeBytes(gpa, .{
        .optimizations = .{ .mode = opt_mode },
        .builtins = .{},
        .files = types.line_indexes,
    });
    defer exe.deinit(gpa);

    const res = backend.run(.{
        .name = name,
        .code = exe.items,
    });

    errdefer {
        backend.disasm(.{
            .name = name,
            .bin = exe.items,
            .out = &writer.interface,
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

    std.debug.print("{s}\n", .{code});

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
    const asts = scratch.alloc(File, files.items.len);
    for (asts, files.items, 0..) |*ast, fr, i| {
        if (std.mem.endsWith(u8, fr.path, ".hb") or i == 0) {
            kl.loader.path = fr.path;
            kl.loader.from = @enumFromInt(i);
            kl.loader.diagnostics = output;
            kl.loader.colors = .escape_codes;

            ast.* = try .init(fr.source, &kl.loader, scratch);
        }
    }

    return .{ asts, kl };
}

pub fn gatherScope(self: *Codegen) Types.Scope {
    return .{
        .file = self.file,
        .parent = self.scope.data().upcast(Types.Parent).pack(),
        .name_pos = self.name,
    };
}
