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
file: File.Id,
scope: Types.AnyScopeRef,
name: Types.Scope.NamePos = .empty,
vars: std.MultiArrayList(VEntry) = .empty,
var_pins: BBuilder.Pins,
ret_ty: Types.Id,
ret_ref: ?*BNode = null,
bl: BBuilder,
target: Types.Target = .runtime,

pub const undeclared_prefix: u8 = 0;

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
        kind: enum(u2) { value, ptr, empty },
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

    pub fn load(self: Value, pos: u32, gen: *Codegen) !*BNode {
        return switch (self.node()) {
            .empty => return error.Report,
            .variable => |idx| vr: {
                const slot: *Variable = &gen.vars.items(.variable)[idx];
                // TODO: this can fail, but do we error?
                if (slot.value == std.math.maxInt(u32)) {
                    return gen.report(
                        pos,
                        "using of uninitialized variable",
                        .{},
                    );
                }
                break :vr switch (slot.meta.kind) {
                    .empty => return error.Report,
                    .value => gen.bl.getScopeValue(slot.value),
                    .ptr => unreachable, // TODO
                };
            }, // TODO
            .value => |v| v,
            .ptr => |p| {
                const ty = gen.types.abi
                    .categorizeAssumeReg(self.ty, gen.types);
                return gen.bl.addLoad(gen.sloc(pos), p, ty);
            },
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

pub const Node = union(enum) {
    empty,
    variable: usize,
    value: *BNode,
    ptr: *BNode,
};

pub const Error = error{ Report, Unreachable };

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
                    .data = .{ .pos = 0, .len = 0 },
                };

                var global = &global_mem;

                const slot = self.types.global_index.intern(self.types, global);

                if (!slot.found_existing) {
                    slot.key_ptr.* = self.types.globals
                        .push(&self.types.arena, global_mem);
                    global = self.types.globals.at(slot.key_ptr.*);

                    var global_gen: Codegen = undefined;
                    global_gen.init(
                        self.types,
                        scope_cursor.pack(),
                        .never,
                        self.types.allocator(),
                    );
                    defer global_gen.deinit();

                    global_gen.evalGlobal(vl.offset, slot.key_ptr.*);
                }

                return .ptr(global.ty, self.bl.addGlobalAddr(
                    self.sloc(vl.offset),
                    @intFromEnum(slot.key_ptr.*),
                ));
            }
        }

        scope_cursor = scope_cursor.scope(self.types)
            .parent.data().downcast(Types.AnyScope) orelse break;
    }

    var cursor: usize = 0;
    while (std.mem.indexOfScalarPos(
        u8,
        self.vars.items(.prefix),
        cursor,
        name[0],
    )) |index| {
        const variable: *Variable = &self.vars.items(.variable)[index];
        if (Lexer.compareIdent(file.source, variable.meta.pos, name)) {
            return .variable(variable.ty, index);
        }

        cursor = index + 1;
    }

    return null;
}

pub fn evalGlobal(self: *Codegen, pos: u32, global_id: Types.GlobalId) void {
    const token = self.bl
        .begin(.systemv, &.{.{ .Reg = .i64 }}, &.{});
    const file = self.file.get(self.types);
    const global = self.types.globals.at(global_id);

    var lex = Lexer.init(file.source, pos);

    _ = lex.slit(.Ident);

    var ty: ?Types.Id = null;
    if (lex.eatMatch(.@":")) {
        ty = self.typ(&lex) catch null;
        _ = lex.slit(.@"=");
    } else {
        _ = lex.slit(.@":=");
    }

    const ret_addr = self.bl
        .addParam(self.sloc(lex.cursor), 0, 0);

    const value = self.expr(
        .{ .loc = ret_addr, .ty = ty },
        &lex,
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
    const reserved = self.types.funcs.push(&self.types.arena, undefined);

    self.types.ct_backend.mach.emitFunc(&self.bl.func, .{
        .id = @intFromEnum(reserved),
        .is_inline = false,
        .name = "",
        .linkage = .local,
        .optimizations = .{ .opts = .{ .mode = .debug } },
        .builtins = .{},
        .uuid = @splat(0),
    });

    self.types.ct_backend.mach.emitData(.{
        .id = @intFromEnum(global_id),
        .value = .{ .uninit = value.ty.size(self.types) },
        .readonly = false,
        .thread_local = false,
        .uuid = @splat(0),
    });

    const global_sym = self.types.ct_backend.mach.out
        .getGlobalSym(@intFromEnum(global_id));

    global.ty = value.ty;
    global.data = .{
        .pos = global_sym.offset,
        .len = global_sym.size,
    };

    const func_sym = self.types.ct_backend.mach.out
        .getFuncSym(@intFromEnum(reserved));

    const log = false;
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
    switch (value.node()) {
        .empty => {},
        .variable => unreachable, // TODO
        .value => |v| self.bl.addStore(self.sloc(pos), dest, v.data_type, v),
        .ptr => unreachable, // TODO
    }
}

pub fn emitReachable(stypes: *Types, gpa: std.mem.Allocator) void {
    var self: Codegen = undefined;
    while (stypes.func_queue.getPtr(.runtime).pop()) |fnid| {
        // TODO: we dont want this to reinitialize the bl every time

        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

        const func = fnid.get(stypes);

        self.init(stypes, .nany(fnid), func.ret, gpa);
        defer self.deinit();

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
        while (arg_iter.next()) : (i += 1) {
            const name = lex.slit(.Ident);
            _ = lex.slit(.@":");

            const ty = self.typ(&lex) catch .never;

            self.pushVariable(name, .value(ty, self.bl.addParam(
                self.sloc(name.pos),
                i,
                ty.raw(),
            )));
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
                    " `{}` is uninhabited", .{func.ret}) catch continue;
            };

            if (rets.len != 0) {
                self.report(ret_pos, "the return value is not empty, but" ++
                    " function implicitly returns", .{}) catch continue;
            }
        }

        self.popScope(0);
        self.bl.end(token);

        for (self.bl.func.getSyms().outputs()) |sym| {
            switch (sym.get().extra2()) {
                .GlobalAddr => |extra| {
                    _ = extra; // autofix
                    for (sym.get().outputs()) |s| {
                        (std.debug).print("{f}\n", .{s});
                    }
                    utils.panic("TODO: {f}", .{sym});
                },
                .FuncAddr => |extra| {
                    _ = extra; // autofix
                    unreachable; // TODO
                },
                .Call => |extra| {
                    const fid: Types.FuncId = @enumFromInt(extra.id);
                    fid.get(self.types).queue(self.target, self.types);
                },
                else => utils.panic("{f}", .{sym}),
            }
        }

        self.types.backend.emitFunc(&self.bl.func, .{
            .id = @intFromEnum(fnid),
            .files = self.types.line_indexes,
            .is_inline = false,
            .name = func.scope.name(self.types),
            .linkage = .exported,
            .optimizations = .{ .opts = .{ .mode = .debug } },
            .builtins = .{},
            .uuid = @splat(0),
        });

        std.debug.assert(!self.bl.func.keep);
    }
}

pub fn expr(self: *Codegen, ctx: Ctx, lex: *Lexer) Error!Value {
    return self.exprPrec(ctx, lex, 254);
}

pub fn exprPrec(self: *Codegen, ctx: Ctx, lex: *Lexer, prevPrec: u8) Error!Value {
    const tok = lex.next();

    var res: Value = switch (tok.kind) {
        .Ident => self.lookupIdent(
            self.scope,
            tok.view(lex.source),
        ) orelse .variable(.never, self.defineVariable(tok)),
        .@"~", .@"-" => neg: {
            var oper = try self.exprPrec(.{ .ty = ctx.ty }, lex, 1);

            break :neg .value(oper.ty, self.bl.addUnOp(
                self.sloc(tok.pos),
                if (tok.kind == .@"~") .bnot else .ineg,
                Abi.categorizeBuiltinUnwrapped(oper.ty.data().Builtin),
                oper.load(tok.end, self) catch return .never,
            ));
        },
        .@"!" => not: {
            var oper = try self.exprPrec(.{ .ty = .bool }, lex, 1);
            try self.typeCheck(tok.pos, &oper, .bool);

            break :not .value(.bool, self.bl.addUnOp(
                self.sloc(tok.pos),
                .not,
                .i8,
                oper.load(tok.end, self) catch return .never,
            ));
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

                _ = self.expr(.{ .ty = .void }, lex) catch |err| switch (err) {
                    error.Report => continue,
                    error.Unreachable => reached_end = true,
                };
            }

            if (reached_end) return error.Unreachable;

            return .voidv;
        },
        .@"fn" => b: {
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
                _ = lex.expect(.Ident) catch {
                    self.report(lex.cursor, "expected argument name", .{}) catch {};
                    if (arg_iter.recover()) break else continue;
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

            const func = Types.Func{
                .scope = .{
                    .parent = self.scope.data().upcast(Types.Parent).pack(),
                    .file = self.file,
                    .name_pos = self.name,
                },
                .params = &.{},
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

            // TODO: maybe we could store it in the value directly
            break :b .value(.nany(slot.key_ptr.*), self.bl.addIntImm(
                self.sloc(tok.pos),
                .i32,
                @intFromEnum(id),
            ));
        },
        .@"if" => {
            var cond = try self.expr(.{ .ty = .bool }, lex);
            self.typeCheck(tok.pos, &cond, .bool) catch {};

            var if_bl = self.bl.addIfAndBeginThen(
                self.sloc(tok.pos),
                cond.load(tok.end, self) catch
                    self.bl.addUninit(self.sloc(tok.end), .i8),
            );

            var unreachable_count: usize = 0;

            _ = self.expr(.{ .ty = .void }, lex) catch |err| {
                unreachable_count += @intFromBool(err == error.Unreachable);
            };

            const tk = if_bl.beginElse(&self.bl);

            _ = self.expr(.{ .ty = .void }, lex) catch |err| {
                unreachable_count += @intFromBool(err == error.Unreachable);
            };

            if_bl.end(&self.bl, tk);

            if (unreachable_count == 2) return error.Unreachable;

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
                    buf[0] = try ret.load(tok.pos, self);
                } else {
                    if (returns.len == 2) unreachable; // TODO
                }

                self.bl.addReturn(buf[0..returns.len]);
            } else {
                return self.report(tok.pos, "`return` can not be used" ++
                    " since `{}` is empty", .{self.ret_ty});
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
                @bitCast(val),
            ));
        },
        .@"(" => par: {
            const inner = try self.expr(ctx, lex);
            _ = lex.expect(.@")") catch {
                return self.report(lex.cursor, "expected ')'", .{});
            };
            break :par inner;
        },
        .@"@float_to_int" => b: {
            const oper = (try self.parseDirectiveArgs(lex, "<float>"))[0];

            const ret: Types.Id = .int;

            if (!oper.value.ty.isBuiltin(.isFloat))
                return self.report(oper.pos, "expected float," ++
                    " {} is not", .{oper.value.ty});

            break :b .value(ret, self.bl.addUnOp(
                self.sloc(tok.pos),
                .fti,
                .i64,
                oper.load(self) catch break :b .never,
            ));
        },
        else => return self.report(tok.pos, "unexpected token", .{}),
    };

    while (true) {
        const top = lex.peekNext();
        const prec = top.kind.precedence(ctx.in_if_or_while);
        if (prec >= prevPrec) break;

        lex.cursor = top.end;

        switch (top.kind) {
            .@"(" => call: {
                const fid = try self.peval(tok.pos, res, Types.FuncId);
                const func = fid.get(self.types);

                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();

                var args = tmp.arena.makeArrayList(ValueAndPos, func.args.len);

                const iter = lex.list(.@",", .@")");
                var i: usize = 0;
                while (iter.next()) : (i += 1) {
                    const ty = if (i < func.args.len) func.args[i] else null;

                    const pos = lex.cursor;
                    var arg = self.expr(.{ .ty = ty }, lex) catch |err| switch (err) {
                        error.Unreachable => return err,
                        error.Report => if (iter.recover()) break else continue,
                    };

                    if (ty) |t| self.typeCheck(pos, &arg, t) catch {};

                    args.appendBounded(.{ .pos = pos, .value = arg }) catch {
                        self.report(pos, "extra arbgment", .{}) catch {};
                    };
                }

                if (args.items.len < func.args.len) {
                    self.report(
                        lex.cursor,
                        "{} missing arguments",
                        .{func.args.len - args.items.len},
                    ) catch break :call;
                }

                const params, const returns, const ret_by_ref = self.types.abi
                    .computeSignature(
                    func.args,
                    func.ret,
                    self.types,
                    tmp.arena,
                ) orelse {
                    std.debug.assert(self.types.errored);
                    break :call;
                };
                std.debug.assert(!ret_by_ref); // TODO

                const call_args = self.bl
                    .allocCallArgs(tmp.arena, params, returns, null);

                var cursor: usize = 0;
                for (args.items) |arg| {
                    var buf = Abi.Buf{};
                    const splits = self.types.abi
                        .categorize(arg.value.ty, self.types, &buf).?;
                    if (splits.len == 0) continue;

                    if (splits.len == 2) unreachable; // TODOa
                    if (splits.len == 1 and splits[0] != .Reg) unreachable; // TODO

                    call_args.arg_slots[cursor] =
                        arg.value.load(arg.pos, self) catch unreachable; // TODO
                    cursor += splits.len;
                }

                const result = self.bl.addCall(
                    self.sloc(top.pos),
                    self.types.abi.cc,
                    @intFromEnum(fid),
                    .is_sym,
                    call_args,
                ) orelse return error.Unreachable;

                if (result.len == 0) res = .voidv;
                if (result.len == 1) res = .value(func.ret, result[0]);
                if (result.len == 2) unreachable;
            },
            .@":", .@":=" => {
                const index = switch (res.node()) {
                    .variable => |i| i,
                    .value, .ptr, .empty => return self.report(top.pos, "" ++
                        "can't use this as an identifier", .{}),
                };

                const slot: *Variable = &self.vars.items(.variable)[index];
                if (slot.value != std.math.maxInt(u32)) {
                    self.report(top.pos, "can't shadow the existing" ++
                        " declaration", .{}) catch {};
                    self.report(slot.meta.pos, "...the existing" ++
                        " declaration", .{}) catch {};
                    // NOTE: we dont throw, just shadow it
                }

                var ty: ?Types.Id = null;
                var eq = top;

                if (top.kind == .@":") {
                    ty = self.typ(lex) catch .never;

                    eq = lex.expect(.@"=") catch {
                        return self.report(lex.cursor, "expected '='", .{});
                    };
                }

                var value = try self.expr(.{ .ty = ty }, lex);
                if (ty) |t| try self.typeCheck(eq.pos, &value, t);

                // could have been an error
                if (slot.value == std.math.maxInt(u32)) {
                    self.declareVariable(index, value);
                }

                res = .voidv;
            },
            else => {
                var pin = res.pin(self);
                errdefer res.unpin(self, pin);

                var rhs = try self.exprPrec(.{ .ty = res.ty }, lex, prec);

                var oper_ty = ctx.ty orelse res.ty;

                if (top.kind.isComparison()) oper_ty = res.ty;
                if (!res.ty.canUpcast(oper_ty, self.types)) oper_ty = res.ty;

                oper_ty = self.binOpUpcast(oper_ty, rhs.ty) catch {
                    return self.report(
                        top.pos,
                        "incompatible operands, {} {} {}",
                        .{ oper_ty, top.view(lex.source), rhs.ty },
                    );
                };

                res.unpinKeep(self, pin);
                pin = rhs.pin(self);

                try self.typeCheck(top.pos, &res, oper_ty);

                rhs.unpinKeep(self, pin);
                pin = res.pin(self);

                try self.typeCheck(top.pos, &rhs, oper_ty);

                if (oper_ty == .never) return .never;

                var result: Types.Id =
                    if (top.kind.isComparison()) .bool else oper_ty;

                const op = try self.lexemeToBinOp(top.pos, top.kind, oper_ty);

                res.unpinKeep(self, pin);

                const bin = Value.value(result, self.bl.addBinOp(
                    self.sloc(top.pos),
                    op,
                    Abi.categorizeBuiltinUnwrapped(result.data().Builtin),
                    res.load(top.pos, self) catch continue,
                    rhs.load(top.pos, self) catch continue,
                ));

                res = bin;
            },
        }
    }

    return res;
}

pub fn peval(self: *Codegen, pos: u32, value: Value, comptime T: type) !T {
    const res = try self.partialEval(try value.load(pos, self));

    switch (T) {
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
    self.types.errored = true;
    return error.Report;
}

pub const ValueAndPos = struct {
    value: Value,
    pos: u32,

    pub fn load(self: ValueAndPos, cg: *Codegen) !*BNode {
        return self.value.load(self.pos, cg);
    }
};

pub fn binOpUpcast(self: *Codegen, lhs: Types.Id, rhs: Types.Id) !Types.Id {
    if (lhs == rhs) return lhs;
    if (lhs.canUpcast(rhs, self.types)) return rhs;
    if (rhs.canUpcast(lhs, self.types)) return lhs;
    return error.IncompatibleTypes;
}

inline fn parseDirectiveArgs(
    cg: *Codegen,
    lex: *Lexer,
    comptime expected: []const u8,
) ![]ValueAndPos {
    const varargs = comptime std.mem.endsWith(u8, expected, "..");
    const min_expected_args = comptime std.mem.count(u8, expected, ",") +
        @intFromBool(expected.len != 0) - @intFromBool(varargs);
    return try parseDirectiveArgsLow(
        cg,
        lex,
        expected,
        min_expected_args,
        varargs,
    );
}

pub fn parseDirectiveArgsLow(
    cg: *Codegen,
    lex: *Lexer,
    expected: []const u8,
    min_expected_args: usize,
    varargs: bool,
) ![]ValueAndPos {
    const scratch = utils.Arena.imm();

    _ = lex.expect(.@"(") catch {
        return cg.report(lex.cursor, "expected '(' as a start of" ++
            " directive argument list", .{});
    };

    var args = scratch.makeArrayList(ValueAndPos, min_expected_args);

    var arg_iter = lex.list(.@",", .@")");
    while (arg_iter.next()) {
        const pos = lex.cursor;
        const value = try cg.expr(.{}, lex);
        args.append(
            scratch.allocator(),
            .{ .value = value, .pos = pos },
        ) catch unreachable;
    }

    if (args.items.len < min_expected_args or
        (!varargs and args.items.len > min_expected_args))
    {
        const range = if (varargs) "at least " else "";
        return cg.report(
            lex.cursor,
            "directive takes {}{} arguments, got {} ({})",
            .{ range, min_expected_args, args.items.len, expected },
        );
    }

    return args.items;
}

pub fn lexemeToBinOp(self: *Codegen, pos: u32, lx: Lexer.Lexeme, ty: Types.Id) !graph.BinOp {
    return (lexemeToBinOpLow(lx, ty) catch
        return self.report(pos, "BUG: lexeme to bin op calles" ++
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

pub fn typeCheck(
    self: *Codegen,
    pos: u32,
    got: *Value,
    expected: Types.Id,
) error{Report}!void {
    if (expected == got.ty) return;

    if (got.ty.canUpcast(expected, self.types)) {
        if (expected == .never or got.ty == .never) {
            return;
        }

        const sloca = self.sloc(pos);
        const res_dt = Abi.categorizeBuiltinUnwrapped(expected.data().Builtin);

        if (got.ty.isBuiltin(.isSigned) and
            got.ty.size(self.types) < expected.size(self.types))
        {
            const tmp = got.load(pos, self) catch return;
            got.* = .value(expected, self.bl.addUnOp(sloca, .sext, res_dt, tmp));
        }

        if ((got.ty.isBuiltin(.isUnsigned) or got.ty == .bool) and
            got.ty.size(self.types) < expected.size(self.types))
        {
            const tmp = got.load(pos, self) catch return;
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
        .prefix = file.source[name.pos],
        .variable = .{
            .ty = .never,
            .meta = .{
                .kind = .empty,
                .pos = @intCast(name.pos),
            },
        },
    }) catch unreachable;
    return self.vars.len - 1;
}

pub fn pushVariable(self: *Codegen, name: Lexer.Token, value: Value) void {
    const index = self.defineVariable(name);
    self.declareVariable(index, value);
}

pub fn declareVariable(self: *Codegen, index: usize, value: Value) void {
    // NOTE: this enforces the order of declarations
    const slot: *Variable = &self.vars.items(.variable)[index];

    std.debug.assert(slot.value == std.math.maxInt(u32));

    slot.ty = value.ty;
    slot.meta.kind = switch (value.tag) {
        .empty => .empty,
        .variable, .value => .value,
        .ptr => .ptr,
    };
    slot.value = switch (value.node()) {
        .empty => undefined,
        .variable => |idx| blk: {
            const other = &self.vars.items(.variable)[idx];
            break :blk switch (other.meta.kind) {
                .empty => undefined,
                .value => self.bl.pushScopeValue(
                    self.bl.getScopeValue(other.value),
                ),
                .ptr => unreachable, // TODO
            };
        }, // TODO
        .value => |v| self.bl.pushScopeValue(v),
        .ptr => |t| self.var_pins.push(&self.bl, t),
    };
}

pub fn popScope(self: *Codegen, scope_marker: usize) void {
    var truncate_vals_by: usize = 0;
    var truncate_slots_by: usize = 0;

    const poped_vars = self.vars.items(.variable)[scope_marker..];
    var iter = std.mem.reverseIterator(poped_vars);
    while (@as(?Variable, iter.next())) |vr| {
        if (vr.value == std.math.maxInt(u32)) continue;
        switch (vr.meta.kind) {
            .empty => {},
            .value => truncate_vals_by += 1,
            .ptr => truncate_slots_by += 1,
        }
    }

    if (!self.bl.isUnreachable()) {
        self.bl.truncateScope(self.bl.scopeSize() - truncate_vals_by);
    }

    self.var_pins.truncate(&self.bl, self.var_pins.len() - truncate_slots_by);

    @memset(poped_vars, undefined);
    self.vars.len = scope_marker;
}

pub fn collectExports(types: *Types) !void {
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

    var self: Codegen = .{
        .types = types,
        .file = .root,
        .name = @enumFromInt(decl.offset),
        .scope = root.root_sope,
        .var_pins = undefined,
        .ret_ty = .never,
        .bl = undefined,
    };

    var lex = Lexer.init(root.source, decl.offset);

    _ = lex.expect(.Ident) catch unreachable; // TODO
    _ = lex.expect(.@":=") catch unreachable; // TODO

    _ = lex.expect(.@"fn") catch {
        return self.report(lex.cursor, "expected function", .{});
    };

    const start = lex.expect(.@"(") catch {
        return self.report(
            lex.cursor,
            "expected '(' as a start of argument list",
            .{},
        );
    };

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var args = std.ArrayList(Types.Id).empty;
    var arg_iter = lex.list(.@",", .@")");
    while (arg_iter.next()) {
        _ = lex.expect(.Ident) catch {
            self.report(lex.cursor, "expected argument name", .{}) catch {};
            if (arg_iter.recover()) break else continue;
        };

        const col = lex.expect(.@":") catch {
            self.report(
                lex.cursor,
                "expected mandatory ':' after name",
                .{},
            ) catch {};
            if (arg_iter.recover()) break else continue;
        };

        const arg_ty = self.typ(&lex) catch {
            self.report(col.end, "failed to parse type", .{}) catch {};
            if (arg_iter.recover()) break else continue;
        };
        try args.append(tmp.arena.allocator(), arg_ty);
    }

    _ = lex.expect(.@":") catch {
        return self.report(
            lex.cursor,
            "expected mandatory ':' after argument list",
            .{},
        );
    };

    const ret = try self.typ(&lex);

    const func = types.funcs.push(
        &types.arena,
        Types.Func{
            .scope = .{
                .parent = root.root_sope.data().upcast(Types.Parent).pack(),
                .file = self.file,
                .name_pos = self.name,
            },
            .args = types.arena.dupe(Types.Id, args.items),
            .ret = ret,
            .pos = start.end,
            .params = &.{},
        },
    );

    func.get(types).queue(.runtime, types);
}

pub fn typ(self: *Codegen, lex: *Lexer) error{Report}!Types.Id {
    const tok = lex.next();
    switch (tok.kind.expand()) {
        .Type => |t| return @enumFromInt(@intFromEnum(t)),
        else => return self.report(tok.pos, "unhandled type syntax", .{}),
    }
}

pub fn report(self: *Codegen, pos: u32, msg: []const u8, args: anytype) error{Report} {
    @branchHint(.cold);

    self.types.report(self.file, pos, msg, args);
    self.types.errored = true;
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

pub fn runTest(name: []const u8, code: []const u8) !void {
    utils.Arena.tryInitScratch(1024 * 1024);

    var scratch = utils.Arena.init(1024 * 1024);
    var writer = std.fs.File.stderr().writer(&.{});
    const gpa = std.testing.allocator;

    const asts, var kl = try parseExample(
        &scratch,
        name,
        code,
        &writer.interface,
    );

    const backend = hb.backend.Machine.SupportedTarget.@"x86_64-linux"
        .toMachine(&scratch, gpa);
    defer backend.deinit();

    var types = Types.init(asts, &kl.loader, backend, scratch, gpa);
    defer types.deinit();

    try collectExports(&types);

    emitReachable(&types, gpa);

    const exp = Expectations.init(asts[0].source);

    if (exp.should_error) {
        try std.testing.expect(types.errored);
        return;
    }

    try std.testing.expect(!types.errored);

    var exe = backend.finalizeBytes(gpa, .{
        .optimizations = .{ .mode = .debug },
        .builtins = .{},
        .files = types.line_indexes,
    });
    defer exe.deinit(gpa);

    const res = backend.run(.{
        .name = "foobar",
        .code = exe.items,
    });

    errdefer {
        backend.disasm(.{
            .name = "foobar",
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
            kl.loader.colors = .no_color;

            ast.* = try .init(fr.source, &kl.loader, scratch);
        }
    }

    return .{ asts, kl };
}
