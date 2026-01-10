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

const print = (std.debug).print;
const Codegen = @This();

types: *Types,
file: File.Id,
func: utils.EntId(Types.Func),
name: Types.Scope.NamePos = .empty,
vars: std.MultiArrayList(VEntry) = .empty,
var_pins: BBuilder.Pins,
ret_ty: Types.Id,
ret_ref: ?*BNode = null,
bl: BBuilder,

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
        kind: enum(u1) { value, ptr },
        pos: u31,
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

    pub fn isPinned(self: Value, codegen: *Codegen) bool {
        return switch (self.node()) {
            .variable => false,
            .value => |v| codegen.bl.isPinned(v),
            .ptr => |p| codegen.bl.isPinned(p),
        };
    }

    pub fn load(self: Value, pos: u32, codegen: *Codegen) *BNode {
        _ = pos; // autofix
        return switch (self.node()) {
            .variable => |idx| vr: {
                const slot: *Variable = &codegen.vars.items(.variable)[idx];
                // TODO: this can fail, but do we error?
                std.debug.assert(slot.value != std.math.maxInt(u32));
                break :vr switch (slot.meta.kind) {
                    .value => codegen.bl.getScopeValue(slot.value),
                    .ptr => unreachable, // TODO
                };
            }, // TODO
            .value => |v| v,
            .ptr => unreachable, // TODO
        };
    }

    pub fn pin(self: Value, codegen: *Codegen) ?*BNode {
        return switch (self.node()) {
            .variable => null,
            .value => |v| codegen.bl.pin(v),
            .ptr => |p| codegen.bl.pin(p),
        };
    }

    pub fn unpin(self: *Value, codegen: *Codegen, pn: ?*BNode) void {
        const tmp = self.*;
        self.* = switch (self.node()) {
            .variable => return std.debug.assert(pn == null),
            .value => .value(tmp.ty, codegen.bl.unpin(pn.?)),
            .ptr => .ptr(tmp.ty, codegen.bl.unpin(pn.?)),
        };
    }

    pub fn unpinKeep(self: *Value, codegen: *Codegen, pn: ?*BNode) void {
        const tmp = self.*;
        self.* = switch (self.node()) {
            .variable => return std.debug.assert(pn == null),
            .value => .value(tmp.ty, codegen.bl.unpinKeep(pn.?)),
            .ptr => .ptr(tmp.ty, codegen.bl.unpinKeep(pn.?)),
        };
    }

    pub fn sync(self: *Value, pn: ?*BNode) void {
        const tmp = self.*;
        self.* = switch (self.node()) {
            .variable => return std.debug.assert(pn == null),
            .value => .value(tmp.ty, pn.?.inputs()[0].?),
            .ptr => .ptr(tmp.ty, pn.?.inputs()[0].?),
        };
    }

    pub fn node(self: Value) Node {
        return switch (self.tag) {
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
        return .{ .ty = ty, .tag = .value, .value_ = undefined };
    }
};

pub const Node = union(enum) {
    variable: usize,
    value: *BNode,
    ptr: *BNode,
};

pub const Error = error{ Report, Unreachable };

pub fn init(slot: *Codegen, types: *Types, func: utils.EntId(Types.Func), gpa: std.mem.Allocator) void {
    slot.bl = .init(gpa);
    slot.* = .{
        .bl = slot.bl,
        .func = func,
        .types = types,
        .file = func.get(types).scope.file,
        .var_pins = slot.bl.addPins(),
        .ret_ty = func.get(types).ret,
    };
}

pub fn deinit(self: *Codegen) void {
    self.bl.deinit();
    self.* = undefined;
}

pub fn sloc(self: *Codegen, pos: u32) graph.Sloc {
    return .{ .namespace = self.file.index(), .index = pos };
}

pub fn lookupIdent(self: *Codegen, scope: Types.Data.Scope, name: []const u8) ?Value {
    const scope_meta = scope.scope(self.types);
    const file = scope_meta.file.get(self.types);

    if (scope.downcast(Types.Data.UnorderedScope)) |us| {
        if (us.decls(self.types).lookup(file.source, name)) |vl| {
            _ = vl; // autofix
            unreachable; // TODO
        }
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

pub fn emitReachable(stypes: *Types, gpa: std.mem.Allocator) void {
    var self: Codegen = undefined;
    while (stypes.func_queue.getPtr(.runtime).pop()) |fnid| {
        // TODO: we dont want this to reinitialize the bl every time
        self.init(stypes, fnid, gpa);
        defer self.deinit();

        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();

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

        self.types.backend.emitFunc(&self.bl.func, .{
            .id = @intFromEnum(self.func),
            .files = self.types.line_indexes,
            .is_inline = false,
            .name = func.scope.name(self.types),
            .linkage = .exported,
            .optimizations = .{ .opts = .{ .mode = .debug } },
            .builtins = .{},
            .uuid = @splat(0),
        });
    }
}

pub fn expr(self: *Codegen, ctx: Ctx, lex: *Lexer) Error!Value {
    return self.exprPrec(ctx, lex, 254);
}

pub fn exprPrec(self: *Codegen, ctx: Ctx, lex: *Lexer, prevPrec: u8) Error!Value {
    const tok = lex.next();

    var res: Value = switch (tok.kind) {
        .Ident => self.lookupIdent(
            .{ .Func = self.func },
            tok.view(lex.source),
        ) orelse .variable(.never, self.defineVariable(tok)),
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

            break :float .value(.f64, self.bl.addIntImm(
                self.sloc(tok.pos),
                .f64,
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
        .@"@float_to_int" => {
            const oper = (try self.parseDirectiveArgs(lex, "<float>"))[0];

            const ret: Types.Id = .int;

            if (!oper.value.ty.isBuiltin(.isFloat))
                return self.report(oper.pos, "expected float," ++
                    " {} is not", .{oper.value.ty});

            return .value(ret, self.bl.addUnOp(
                self.sloc(tok.pos),
                .fti,
                .i64,
                oper.load(self),
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
            .@":" => {
                const index = switch (res.node()) {
                    .variable => |i| i,
                    .value, .ptr => return self.report(top.pos, "" ++
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

                slot.ty = self.typ(lex) catch .never;

                const eq = lex.expect(.@"=") catch {
                    return self.report(lex.cursor, "expected '='", .{});
                };

                var value = try self.exprPrec(
                    .{ .ty = slot.ty },
                    lex,
                    Lexer.Lexeme.@"=".precedence(false),
                );
                try self.typeCheck(eq.pos, &value, slot.ty);

                self.declareVariable(index, value);
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
                        "incompatible operang arguments, {} {} {}",
                        .{ oper_ty, top.view(lex.source), rhs.ty },
                    );
                };

                res.unpinKeep(self, pin);
                pin = rhs.pin(self);

                try self.typeCheck(top.pos, &res, oper_ty);

                rhs.unpinKeep(self, pin);
                pin = res.pin(self);

                try self.typeCheck(top.pos, &rhs, oper_ty);

                var result: Types.Id =
                    if (top.kind.isComparison()) .bool else oper_ty;

                const op = try self.lexemeToBinOp(top.pos, top.kind, res.ty);

                res.unpinKeep(self, pin);

                const bin = Value.value(result, self.bl.addBinOp(
                    self.sloc(top.pos),
                    op,
                    Abi.categorizeBuiltinUnwrapped(result.data().Builtin),
                    res.load(top.pos, self),
                    rhs.load(top.pos, self),
                ));

                res = bin;
            },
        }
    }

    return res;
}

pub const ValueAndPos = struct {
    value: Value,
    pos: u32,

    pub fn load(self: ValueAndPos, cg: *Codegen) *BNode {
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

        if (expected == .never or got.ty == .never) {
            return;
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
                .kind = undefined,
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
    std.debug.assert(index == 0 or
        self.vars.items(.variable)[index - 1].value != std.math.maxInt(u32));
    const slot: *Variable = &self.vars.items(.variable)[index];

    std.debug.assert(slot.value == std.math.maxInt(u32));

    slot.meta.kind = switch (value.tag) {
        .variable, .value => .value,
        .ptr => .ptr,
    };
    slot.value = switch (value.node()) {
        .variable => unreachable, // TODO
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
        switch (vr.meta.kind) {
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
        .var_pins = undefined,
        .func = undefined,
        .ret_ty = root.root_sope,
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

    const func = types.store.add(
        &types.arena,
        Types.Func{
            .scope = .{
                .parent = root.root_sope,
                .file = self.file,
                .name_pos = self.name,
            },
            .args = types.arena.dupe(Types.Id, args.items),
            .ret = ret,
            .pos = start.end,
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
    self.types.report(self.file, pos, msg, args);
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

    var types = Types.init(asts, &kl.loader, backend, scratch);

    try collectExports(&types);

    emitReachable(&types, gpa);

    var exe = backend.finalizeBytes(gpa, .{
        .optimizations = .{ .mode = .debug },
        .builtins = .{},
        .files = types.line_indexes,
    });
    defer exe.deinit(gpa);

    _ = try backend.run(.{
        .name = "foobar",
        .code = exe.items,
    });
}

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
