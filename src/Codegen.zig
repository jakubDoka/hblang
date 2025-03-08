bl: Builder,
types: *Types,
work_list: std.ArrayListUnmanaged(Task),
target: Types.Target,
only_inference: bool = false,
comptime abi: Types.Abi = .ableos,
defers: std.ArrayListUnmanaged(Ast.Id) = undefined,
name: []const u8 = undefined,
parent_scope: Scope = undefined,
ast: *const Ast = undefined,
struct_ret_ptr: ?*Node = undefined,
scope: std.ArrayListUnmanaged(ScopeEntry) = undefined,
loops: std.ArrayListUnmanaged(Loop) = undefined,
ret: Types.Id = undefined,
errored: bool = undefined,

const std = @import("std");
const root = @import("utils.zig");
const graph = @import("graph.zig");
const Ast = @import("Ast.zig");
const Vm = @import("Vm.zig");
const Comptime = @import("Comptime.zig");
const isa = @import("isa.zig");
const Types = @import("Types.zig");
const Builder = @import("Builder.zig");
const Lexer = @import("Lexer.zig");
const Func = Builder.Func;
const Node = Builder.BuildNode;
const DataType = Builder.DataType;
const Codegen = @This();

const Loop = struct {
    defer_base: usize,
    kind: union(enum) {
        Runtime: Builder.Loop,
        Comptime: union(enum) {
            Clean,
            Controlled: Ast.Id,
        },
    },
};

const Task = union(enum) {
    Func: *Types.Func,
    Global: *Types.Global,
};

const ScopeEntry = struct {
    name: Ast.Ident,
    ty: Types.Id,
};

pub fn init(
    gpa: std.mem.Allocator,
    scratch: *root.Arena,
    types: *Types,
    target: Types.Target,
) Codegen {
    return .{
        .types = types,
        .target = target,
        .bl = .init(gpa),
        .work_list = .initBuffer(scratch.alloc(Task, 1024)),
    };
}

pub fn deinit(self: *Codegen) void {
    self.bl.deinit();
    self.* = undefined;
}

pub fn queue(self: *Codegen, task: Task) void {
    switch (task) {
        inline else => |func| {
            if (func.completion.get(self.target) == .compiled) return;
            self.work_list.appendAssumeCapacity(task);
        },
    }
}

pub fn nextTask(self: *Codegen) ?Task {
    while (true) {
        const task = self.work_list.pop() orelse return null;
        switch (task) {
            inline else => |func| {
                if (func.completion.get(self.target) == .compiled) continue;
                func.completion.set(self.target, .compiled);
            },
        }
        return task;
    }
}

pub fn getEntry(self: *Codegen, file: Types.File, name: []const u8) !*Types.Func {
    var tmp = root.Arena.scrath(null);
    defer tmp.deinit();
    _ = self.beginBuilder(tmp.arena, .never, 0, 0);
    defer self.bl.func.reset();

    var entry_vl = try self.lookupScopeItem(.init(0), self.types.getScope(file), name);
    const entry_ty = try self.unwrapTyConst(Ast.Pos.init(0), &entry_vl);

    if (entry_ty.data() != .Func) return error.Never;
    return entry_ty.data().Func;
}

pub fn beginBuilder(
    self: *Codegen,
    scratch: *root.Arena,
    ret: Types.Id,
    param_count: usize,
    return_count: usize,
) struct { Builder.BuildToken, []DataType, []DataType } {
    self.errored = false;
    self.ret = ret;
    const res = self.bl.begin(param_count, return_count);

    self.scope = .initBuffer(scratch.alloc(ScopeEntry, 128));
    self.loops = .initBuffer(scratch.alloc(Loop, 8));
    self.defers = .initBuffer(scratch.alloc(Ast.Id, 32));

    return res;
}

pub fn build(self: *Codegen, func: *Types.Func) !void {
    var tmp = root.Arena.scrath(null);
    defer tmp.deinit();

    self.ast = self.types.getFile(func.key.file);
    const param_count, const return_count, const ret_abi = func.computeAbiSize(self.abi, self.types);
    const token, const params, const returns = self.beginBuilder(tmp.arena, func.ret, param_count, return_count);
    self.parent_scope = .init(.{ .Func = func });
    self.name = "";

    var i: usize = 0;

    if (ret_abi == .ByRef) {
        ret_abi.types(params[0..1]);
        self.struct_ret_ptr = self.bl.addParam(i);
        i += 1;
    } else {
        ret_abi.types(returns);
        self.struct_ret_ptr = null;
    }

    const ast = self.types.getFile(func.key.file);
    const fn_ast = ast.exprs.get(func.key.ast).Fn;

    var ty_idx: usize = 0;
    for (ast.exprs.view(fn_ast.args)) |aarg| {
        const ident = ast.exprs.get(aarg.bindings).Ident;
        if (ident.pos.flag.@"comptime") continue;
        const ty = func.args[ty_idx];
        const abi = self.abi.categorize(ty, self.types);
        abi.types(params[i..]);

        const arg = switch (abi) {
            .ByRef => self.bl.addParam(i),
            .ByValue => self.bl.addSpill(self.bl.addParam(i)),
            .ByValuePair => |p| b: {
                const slot = self.bl.addLocal(ty.size(self.types));
                for (p.offsets(), 0..) |off, j| {
                    const arg = self.bl.addParam(i + j);
                    self.bl.addFieldStore(slot, @intCast(off), arg.data_type, arg);
                }
                break :b slot;
            },
            .Imaginary => self.bl.addLocal(0),
        };
        self.scope.appendAssumeCapacity(.{ .ty = ty, .name = ident.id });
        self.bl.pushScopeValue(arg);
        i += abi.len(false);
        ty_idx += 1;
    }

    var termintes = false;
    _ = self.emit(.{}, ast.exprs.get(func.key.ast).Fn.body) catch |err| switch (err) {
        error.Never => {},
        error.Unreachable => termintes = true,
    };

    if (!termintes and ret_abi != .Imaginary) {
        self.report(fn_ast.body, "function is missing a return value since" ++
            " {} has more then 1 possible value", .{func.ret}) catch {};
    }

    if (self.errored) return error.HasErrors;

    self.bl.end(token);
}

pub const Value = struct {
    id: Mode = .Imaginary,
    ty: Types.Id = .void,

    pub const Mode = union(enum) {
        Imaginary,
        Value: *Node,
        Ptr: *Node,
    };

    inline fn mkv(ty: Types.Id, oid: ?*Node) Value {
        return .{ .ty = ty, .id = if (oid) |id| .{ .Value = id } else .Imaginary };
    }

    inline fn mkp(ty: Types.Id, id: *Node) Value {
        return .{ .ty = ty, .id = .{ .Ptr = id } };
    }
};

pub const Scope = union(enum) {
    Tmp: *Codegen,
    Perm: Types.Id,

    pub fn init(td: Types.Data) Scope {
        return .{ .Perm = .init(td) };
    }

    pub fn parent(self: Scope) Scope {
        return switch (self) {
            .Perm => |p| .{ .Perm = p.parent() },
            .Tmp => |t| t.parent_scope,
        };
    }

    pub fn perm(self: Scope) Types.Id {
        return switch (self) {
            .Perm => |p| p,
            .Tmp => |t| t.parent_scope.perm(),
        };
    }

    pub fn empty(self: Scope) bool {
        return switch (self) {
            .Perm => |p| p == .void,
            .Tmp => false,
        };
    }

    pub fn file(self: Scope) Types.File {
        return switch (self) {
            .Perm => |p| p.file().?,
            .Tmp => |t| t.parent_scope.file(),
        };
    }

    pub fn items(self: Scope, ast: *const Ast) Ast.Slice {
        return switch (self) {
            .Perm => |p| p.items(ast),
            .Tmp => |t| t.parent_scope.items(ast),
        };
    }

    pub fn findCapture(self: Scope, pos: Ast.Pos, id: Ast.Ident) ?Types.Key.Capture {
        return switch (self) {
            .Perm => |p| p.findCapture(id),
            .Tmp => |t| for (t.scope.items, 0..) |se, i| {
                if (se.name == id) {
                    if (se.ty != .type) {
                        return .{ .id = id, .ty = se.ty };
                    }
                    var value = Codegen.Value{ .ty = .type, .id = .{ .Ptr = t.bl.getScopeValue(i) } };
                    break .{ .id = id, .ty = .type, .value = @intFromEnum(t.unwrapTyConst(pos, &value) catch .never) };
                }
            } else null,
        };
    }
};

pub const Ctx = struct {
    ty: ?Types.Id = null,
    loc: ?*Node = null,

    pub fn addLoc(self: Ctx, loc: ?*Node) Ctx {
        var v = self;
        v.loc = loc;
        return v;
    }

    pub fn addTy(self: Ctx, ty: Types.Id) Ctx {
        var v = self;
        v.ty = ty;
        return v;
    }
};

pub fn ensureLoaded(self: *Codegen, value: *Value) void {
    if (value.id == .Ptr) {
        const cata = self.abi.categorize(value.ty, self.types);
        if (cata == .Imaginary) {
            value.id = .Imaginary;
            return;
        }
        value.id = .{ .Value = self.bl.addLoad(value.id.Ptr, cata.ByValue) };
    }
}

pub fn typeCheck(self: *Codegen, expr: anytype, got: *Value, expected: Types.Id) !void {
    if (expected.data() == .Nullable and expected.data().Nullable.inner == got.ty) {
        if (!expected.needsTag(self.types)) {
            got.ty = expected;
            return;
        }
        const abi = self.abi.categorize(got.ty, self.types);
        switch (abi) {
            .Imaginary => {
                got.* = .mkv(expected, self.bl.addIntImm(.i8, 1));
            },
            else => {
                const loc = self.bl.addLocal(expected.size(self.types));
                _ = self.bl.addStore(loc, .i8, self.bl.addIntImm(.i8, 1));
                self.emitGenericStore(self.bl.addFieldOffset(loc, @bitCast(got.ty.alignment(self.types))), got);
                got.* = .mkp(expected, loc);
            },
        }

        return;
    }

    if (got.ty == .never) return;

    if (!got.ty.canUpcast(expected, self.types)) {
        return self.report(expr, "expected {} got {}", .{ expected, got.ty });
    }

    if (got.ty != expected) {
        self.ensureLoaded(got);

        if (got.ty.isSigned() and got.ty.size(self.types) < expected.size(self.types)) {
            got.id.Value = self.bl.addUnOp(.sext, self.abi.categorize(expected, self.types).ByValue, got.id.Value);
        }

        if ((got.ty.isUnsigned() or got.ty == .bool) and got.ty.size(self.types) < expected.size(self.types)) {
            got.id.Value = self.bl.addUnOp(.uext, self.abi.categorize(expected, self.types).ByValue, got.id.Value);
        }

        got.ty = expected;
    }

    return;
}

pub fn report(self: *Codegen, expr: anytype, comptime fmt: []const u8, args: anytype) EmitError {
    self.errored = true;
    self.types.report(self.parent_scope.file(), expr, fmt, args);
    return error.Never;
}

pub fn lexemeToBinOp(self: Lexer.Lexeme, ty: Types.Id) graph.BinOp {
    const unsigned = ty.isUnsigned();
    const float = ty.isFloat();
    return switch (self) {
        .@"+" => if (float) .fadd else .iadd,
        .@"-" => if (float) .fsub else .isub,
        .@"*" => if (float) .fmul else .imul,
        .@"/" => if (float) .fdiv else if (unsigned) .udiv else .sdiv,
        .@"%" => if (unsigned) .umod else .smod,

        .@"<<" => .ishl,
        .@">>" => if (unsigned) .ushr else .sshr,
        .@"|" => .bor,
        .@"&" => .band,
        .@"^" => .bxor,

        .@"<" => if (float) .flt else if (unsigned) .ult else .slt,
        .@">" => if (float) .fgt else if (unsigned) .ugt else .sgt,
        .@"<=" => if (float) .fle else if (unsigned) .ule else .sle,
        .@">=" => if (float) .fge else if (unsigned) .uge else .sge,
        .@"==" => .eq,
        .@"!=" => .ne,
        else => std.debug.panic("{s}", .{@tagName(self)}),
    };
}

fn emitStructFoldOp(self: *Codegen, ty: *Types.Struct, op: Lexer.Lexeme, lhs: *Node, rhs: *Node) ?*Node {
    var fold: ?*Node = null;
    var iter = ty.offsetIter(self.types);
    while (iter.next()) |elem| {
        const lhs_loc = self.bl.addFieldOffset(lhs, @intCast(elem.offset));
        const rhs_loc = self.bl.addFieldOffset(rhs, @intCast(elem.offset));
        const value = if (elem.field.ty.data() == .Struct) b: {
            break :b self.emitStructFoldOp(elem.field.ty.data().Struct, op, lhs_loc, rhs_loc) orelse continue;
        } else b: {
            const dt = self.abi.categorize(elem.field.ty, self.types).ByValue;
            const lhs_val = self.bl.addLoad(lhs_loc, dt);
            const rhs_val = self.bl.addLoad(rhs_loc, dt);
            break :b self.bl.addBinOp(
                lexemeToBinOp(op, elem.field.ty),
                .i8,
                self.bl.addUnOp(.uext, .int, lhs_val),
                self.bl.addUnOp(.uext, .int, rhs_val),
            );
        };
        if (fold) |f| {
            fold = self.bl.addBinOp(if (op == .@"==") .band else .bor, .i8, f, value);
        } else fold = value;
    }
    return fold;
}

fn emitStructOp(self: *Codegen, ty: *Types.Struct, op: Lexer.Lexeme, loc: *Node, lhs: *Node, rhs: *Node) void {
    var iter = ty.offsetIter(self.types);
    while (iter.next()) |elem| {
        const field_loc = self.bl.addFieldOffset(loc, @intCast(elem.offset));
        const lhs_loc = self.bl.addFieldOffset(lhs, @intCast(elem.offset));
        const rhs_loc = self.bl.addFieldOffset(rhs, @intCast(elem.offset));
        if (elem.field.ty.data() == .Struct) {
            self.emitStructOp(elem.field.ty.data().Struct, op, field_loc, lhs_loc, rhs_loc);
        } else {
            const dt = self.abi.categorize(elem.field.ty, self.types).ByValue;
            const lhs_val = self.bl.addLoad(lhs_loc, dt);
            const rhs_val = self.bl.addLoad(rhs_loc, dt);
            const res = self.bl.addBinOp(lexemeToBinOp(op, elem.field.ty), dt, lhs_val, rhs_val);
            _ = self.bl.addStore(field_loc, res.data_type, res);
        }
    }
}

pub fn emitGenericStore(self: *Codegen, loc: *Node, value: *Value) void {
    if (value.id == .Imaginary) return;

    if (self.abi.categorize(value.ty, self.types) == .ByValue) {
        self.ensureLoaded(value);
        _ = self.bl.addStore(loc, self.abi.categorize(value.ty, self.types).ByValue, value.id.Value);
    } else if (value.id.Ptr != loc) {
        _ = self.bl.addFixedMemCpy(loc, value.id.Ptr, value.ty.size(self.types));
    }
}

pub fn resolveAnonTy(self: *Codegen, expr: Ast.Id) !Types.Id {
    return self.types.ct.evalTy("", .{ .Tmp = self }, expr);
}

pub fn resolveTy(self: *Codegen, name: []const u8, expr: Ast.Id) !Types.Id {
    return self.types.ct.evalTy(name, .{ .Tmp = self }, expr);
}

pub fn emitTyped(self: *Codegen, ctx: Ctx, ty: Types.Id, expr: Ast.Id) !Value {
    var value = try self.emit(ctx.addTy(ty), expr);
    try self.typeCheck(expr, &value, ty);
    return value;
}

pub fn emitTyConst(self: *Codegen, ty: Types.Id) Value {
    return .mkv(.type, self.bl.addIntImm(.int, @bitCast(@intFromEnum(ty))));
}

pub fn unwrapTyConst(self: *Codegen, pos: anytype, cnst: *Value) !Types.Id {
    if (cnst.ty != .type) {
        return self.report(pos, "expected type, {} is not", .{cnst.ty});
    }
    self.ensureLoaded(cnst);
    if (cnst.id == .Imaginary) {
        std.debug.dumpCurrentStackTrace(@returnAddress());
        return self.report(pos, "what a fuck {}", .{cnst.ty});
    }
    return @enumFromInt(try self.partialEval(pos, cnst.id.Value));
}

pub const LookupResult = union(enum) { ty: Types.Id, cnst: u64 };

pub fn lookupScopeItem(self: *Codegen, pos: Ast.Pos, bsty: Types.Id, name: []const u8) !Value {
    const other_file = bsty.file() orelse {
        std.debug.dumpCurrentStackTrace(@returnAddress());
        return self.report(pos, "{} does not declare this", .{bsty});
    };
    const ast = self.types.getFile(other_file);
    if (bsty.data() == .Enum) {
        const fields = bsty.data().Enum.getFields(self.types);

        for (fields, 0..) |f, i| {
            if (std.mem.eql(u8, f.name, name))
                if (fields.len <= 1) return .mkv(bsty, null) else {
                    return .mkv(bsty, self.bl.addIntImm(self.abi.categorize(bsty, self.types).ByValue, @bitCast(i)));
                };
        }
    }

    var tmp = root.Arena.scrath(null);
    defer tmp.deinit();

    const decl, const path = ast.findDecl(bsty.items(ast), name, tmp.arena.allocator()) orelse {
        return self.report(pos, "{} does not declare this", .{bsty});
    };

    return self.somethingIdk(name, bsty, ast, decl, path);
}

pub fn somethingIdk(self: *Codegen, name: []const u8, bsty: Types.Id, ast: *const Ast, decl: Ast.Id, path: []Ast.Pos) EmitError!Value {
    const vari = ast.exprs.get(decl).BinOp;
    const ty: ?Types.Id, const value: Ast.Id = switch (vari.op) {
        .@":" => .{
            try self.resolveAnonTy((ast.exprs.getTyped(.BinOp, vari.rhs) orelse
                return self.report(vari.rhs, "TODO: uninitialized variables", .{})).lhs),
            ast.exprs.get(vari.rhs).BinOp.rhs,
        },
        .@":=" => .{ null, vari.rhs },
        else => unreachable,
    };

    const global_ty, const new = self.types.resolveGlobal(bsty, name, value);
    const global = global_ty.data().Global;
    if (new) try self.types.ct.evalGlobal(name, global, ty, value);
    self.queue(.{ .Global = global });

    if (path.len != 0) {
        if (global.ty != .type) return self.report(value, "expected a global holding a type, {} is not", .{global.ty});
        var cur: Types.Id = @enumFromInt(@as(u64, @bitCast(global.data[0..8].*)));
        for (path) |ps| {
            var vl = try self.lookupScopeItem(ps, cur, ast.tokenSrc(ps.index));
            cur = try self.unwrapTyConst(ps, &vl);
        }
        return self.emitTyConst(cur);
    }

    return .mkp(global.ty, self.bl.addGlobalAddr(global.id));
}

pub fn loadIdent(self: *Codegen, pos: Ast.Pos, id: Ast.Ident) !Value {
    const ast = self.ast;
    for (self.scope.items, 0..) |se, i| {
        if (se.name == id) {
            if (se.ty == .never) return error.Never;
            const value = self.bl.getScopeValue(i);
            return .mkp(se.ty, value);
        }
    } else {
        var cursor = self.parent_scope;
        var tmp = root.Arena.scrath(null);
        defer tmp.deinit();
        const decl, const path = while (!cursor.empty()) {
            if (ast.findDecl(cursor.items(ast), id, tmp.arena.allocator())) |v| break v;
            if (cursor.findCapture(pos, id)) |c| {
                return .{ .ty = c.ty, .id = if (c.ty == .type) .{ .Value = self.bl.addIntImm(.int, @bitCast(c.value)) } else b: {
                    if (self.target != .@"comptime") {
                        return self.report(pos, "can't access this value, (yet)", .{});
                    }

                    if (!self.only_inference)
                        return self.report(pos, "can't access non type value (yet) unless" ++
                            " this is a type inference context (inside @TypeOf)", .{});

                    break :b switch (self.abi.categorize(c.ty, self.types)) {
                        .Imaginary => .Imaginary,
                        .ByValue => |v| .{ .Value = self.bl.addIntImm(v, 0) },
                        .ByValuePair, .ByRef => .{ .Ptr = self.bl.addLocal(c.ty.size(self.types)) },
                    };
                } };
            }
            cursor = cursor.parent();
        } else {
            std.debug.dumpCurrentStackTrace(@returnAddress());
            return self.report(pos, "ICE: parser did not catch this", .{});
        };

        return self.somethingIdk(ast.tokenSrc(id.pos()), cursor.perm(), ast, decl, path);
    }
}

pub fn emitCall(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: Ast.Store.TagPayload(.Call)) !Value {
    const ast = self.ast;
    var tmp = root.Arena.scrath(null);
    defer tmp.deinit();

    var typ_res: Value, var caller: ?Value = if (e.called.tag() == .Tag) b: {
        const pos = ast.exprs.get(e.called).Tag;
        const name = ast.tokenSrc(pos.index + 1);
        const ty = ctx.ty orelse {
            return self.report(
                e.called,
                "can infer the implicit access, you can specify the type: <ty>.{s}",
                .{name},
            );
        };

        break :b .{ try self.lookupScopeItem(pos, ty, name), null };
    } else if (e.called.tag() == .Field) b: {
        const field = ast.exprs.get(e.called).Field;
        const name = ast.tokenSrc(field.field.index);
        var value = try self.emit(.{}, field.base);

        if (value.ty == .type) {
            break :b .{ try self.lookupScopeItem(field.field, try self.unwrapTyConst(field.base, &value), name), null };
        }

        const ty = if (value.ty.data() == .Ptr) value.ty.data().Ptr.* else value.ty;
        break :b .{ try self.lookupScopeItem(field.field, ty, name), value };
    } else b: {
        break :b .{ try self.emit(.{}, e.called), null };
    };

    var typ: Types.Id = try self.unwrapTyConst(expr, &typ_res);

    var computed_args: ?[]Value = null;
    const was_template = typ.data() == .Template;
    if (was_template) {
        computed_args, typ = try self.instantiateTemplate(tmp, expr, e, typ);
    }

    if (typ.data() != .Func) {
        return self.report(e.called, "{} is not callable", .{typ});
    }

    const func = typ.data().Func;
    if (self.target != .runtime or func.ret != .type)
        self.queue(.{ .Func = func });

    const passed_args = e.args.len() + @intFromBool(caller != null);
    if (!was_template and passed_args != func.args.len) {
        return self.report(expr, "expected {} arguments, got {}", .{ func.args.len, passed_args });
    }

    const param_count, const return_count, const ret_abi = func.computeAbiSize(self.abi, self.types);
    const args = self.bl.allocCallArgs(tmp.arena, param_count, return_count);

    var i: usize = self.pushReturn(args, ret_abi, func.ret, ctx);

    if (caller) |*value| {
        if (value.ty.data() == .Ptr and func.args[0].data() != .Ptr) {
            self.ensureLoaded(value);
            value.ty = value.ty.data().Ptr.*;
            value.id = .{ .Ptr = value.id.Value };
        }

        if (value.ty.data() != .Ptr and func.args[0].data() == .Ptr) {
            value.ty = self.types.makePtr(value.ty);
            value.id = .{ .Value = value.id.Ptr };
        }

        try self.typeCheck(e.called, value, func.args[0]);

        const abi = self.abi.categorize(value.ty, self.types);
        i += self.pushParam(args, abi, i, value);
    }

    const args_ast = ast.exprs.view(e.args);
    for (func.args[@intFromBool(caller != null)..], 0..) |ty, k| {
        const abi = self.abi.categorize(ty, self.types);
        abi.types(args.params[i..]);
        var value = if (computed_args) |a| a[k] else try self.emitTyped(ctx, ty, args_ast[k]);
        i += self.pushParam(args, abi, i, &value);
    }

    return self.assembleReturn(func.id, args, ctx, func.ret, ret_abi);
}

pub fn instantiateTemplate(
    self: *Codegen,
    tmp: root.Arena.Scratch,
    expr: Ast.Id,
    e: std.meta.TagPayload(Ast.Expr, .Call),
    typ: Types.Id,
) !struct { []Value, Types.Id } {
    const tmpl = typ.data().Template;
    const ast = self.ast;

    var scope = tmpl.*;
    scope.key.scope = typ;
    scope.key.captures = &.{};

    const tmpl_file = self.types.getFile(tmpl.key.file);
    const tmpl_ast = tmpl_file.exprs.getTyped(.Fn, tmpl.key.ast).?;
    const comptime_args = tmpl_file.exprs.view(tmpl_ast.comptime_args);

    const passed_args = e.args.len();
    if (passed_args != tmpl_ast.args.len()) {
        return self.report(expr, "expected {} arguments, got {}", .{ tmpl_ast.args.len(), passed_args });
    }

    const captures = tmp.arena.alloc(Types.Key.Capture, tmpl_ast.args.len());
    const arg_tys = tmp.arena.alloc(Types.Id, tmpl_ast.args.len() - tmpl_ast.comptime_args.len());
    const arg_exprs = tmp.arena.alloc(Value, arg_tys.len);

    var capture_idx: usize = 0;
    var arg_idx: usize = 0;
    for (tmpl_file.exprs.view(tmpl_ast.args), ast.exprs.view(e.args)) |param, arg| {
        const binding = tmpl_file.exprs.get(param.bindings).Ident;
        if (binding.pos.flag.@"comptime") {
            captures[capture_idx] = .{ .id = comptime_args[capture_idx], .ty = .type, .value = @intFromEnum(try self.resolveAnonTy(arg)) };
            capture_idx += 1;
            scope.key.captures = captures[0..capture_idx];
        } else {
            arg_tys[arg_idx] = try self.types.ct.evalTy("", .{ .Perm = .init(.{ .Template = &scope }) }, param.ty);
            if (arg_tys[arg_idx] == .any) {
                arg_exprs[arg_idx] = try self.emit(.{}, arg);
                arg_tys[arg_idx] = arg_exprs[arg_idx].ty;
                captures[capture_idx] = .{ .id = binding.id, .ty = arg_tys[arg_idx] };
                capture_idx += 1;
                scope.key.captures = captures[0..capture_idx];
            } else {
                arg_exprs[arg_idx] = try self.emitTyped(.{}, arg_tys[arg_idx], arg);
            }

            arg_idx += 1;
        }
    }

    const ret = try self.types.ct.evalTy("", .{ .Perm = .init(.{ .Template = &scope }) }, tmpl_ast.ret);

    // TODO: the comptime_args + captures are continuous, we could remove the template from the scope tree in that case
    const slot, const alloc = self.types.intern(.Func, .{
        .scope = typ,
        .file = tmpl.key.file,
        .ast = tmpl.key.ast,
        .name = "",
        .captures = captures[0..capture_idx],
    });

    if (!slot.found_existing) {
        alloc.* = .{
            .id = @intCast(self.types.funcs.items.len),
            .key = alloc.key,
            .args = self.types.arena.dupe(Types.Id, arg_tys),
            .ret = ret,
        };
        self.types.funcs.append(self.types.arena.allocator(), alloc) catch unreachable;
        alloc.key.captures = self.types.arena.dupe(Types.Key.Capture, alloc.key.captures);
    }

    return .{ arg_exprs, slot.key_ptr.* };
}

fn pushReturn(cg: *Codegen, call_args: Builder.CallArgs, ret_abi: Types.Abi.Spec, ret: Types.Id, ctx: Ctx) usize {
    if (ret_abi == .ByRef) {
        ret_abi.types(call_args.params[0..1]);
        call_args.arg_slots[0] = ctx.loc orelse cg.bl.addLocal(ret.size(cg.types));
        return 1;
    } else {
        ret_abi.types(call_args.returns);
        return 0;
    }
}

fn pushParam(cg: *Codegen, call_args: Builder.CallArgs, abi: Types.Abi.Spec, idx: usize, value: *Value) usize {
    abi.types(call_args.params[idx..]);
    switch (abi) {
        .Imaginary => {},
        .ByValue => {
            cg.ensureLoaded(value);
            call_args.arg_slots[idx] = value.id.Value;
        },
        .ByValuePair => |pair| {
            for (pair.types, pair.offsets(), 0..) |t, off, j| {
                call_args.arg_slots[idx + j] =
                    cg.bl.addFieldLoad(value.id.Ptr, @intCast(off), t);
            }
        },
        .ByRef => call_args.arg_slots[idx] = value.id.Ptr,
    }
    return abi.len(false);
}

fn assembleReturn(cg: *Codegen, id: u32, call_args: Builder.CallArgs, ctx: Ctx, ret: Types.Id, ret_abi: Types.Abi.Spec) Value {
    const rets = cg.bl.addCall(id, call_args);
    return switch (ret_abi) {
        .Imaginary => .mkv(ret, null),
        .ByValue => .mkv(ret, rets[0]),
        .ByValuePair => |pair| b: {
            const slot = ctx.loc orelse cg.bl.addLocal(ret.size(cg.types));
            for (pair.types, pair.offsets(), rets) |ty, off, vl| {
                cg.bl.addFieldStore(slot, @intCast(off), ty, vl);
            }
            break :b .mkp(ret, slot);
        },
        .ByRef => .mkp(ret, call_args.arg_slots[0]),
    };
}

fn emitDefers(self: *Codegen, base: usize) void {
    var iter = std.mem.reverseIterator(self.defers.items[base..]);
    while (iter.next()) |e| {
        _ = self.emitTyped(.{}, .void, e) catch {};
    }
}

fn loopControl(self: *Codegen, kind: Builder.Loop.Control, ctrl: Ast.Id) !void {
    if (self.loops.items.len == 0) {
        self.report(ctrl, "{s} outside of the loop", .{@tagName(kind)}) catch {};
        return;
    }

    const loops = &self.loops.items[self.loops.items.len - 1];
    self.emitDefers(loops.defer_base);
    switch (loops.kind) {
        .Runtime => |*l| l.addControl(&self.bl, kind),
        .Comptime => |*l| {
            switch (l.*) {
                .Clean => l.* = .{ .Controlled = ctrl },
                .Controlled => |p| {
                    self.report(ctrl, "reached second $loop control, this means control" ++
                        " flow leading to it is runtime dependant", .{}) catch {};
                    self.report(p, "...previous one reached here", .{}) catch {};
                },
            }
        },
    }

    return error.Unreachable;
}

pub fn emitAutoDeref(self: *Codegen, value: *Value) void {
    if (value.ty.data() == .Ptr) {
        self.ensureLoaded(value);
        value.ty = value.ty.data().Ptr.*;
        value.id = .{ .Ptr = value.id.Value };
    }
}

pub const StringEncodeResutl = union(enum) {
    ok: []const u8,
    err: struct { reason: []const u8, pos: usize },
};

pub fn encodeString(
    literal: []const u8,
    buf: []u8,
) StringEncodeResutl {
    const SPECIAL_CHARS = "nrt\\'\"0";
    const TO_BYTES = "\n\r\t\\\'\"\x00";

    std.debug.assert(SPECIAL_CHARS.len == TO_BYTES.len);

    var str = std.ArrayListUnmanaged(u8).initBuffer(buf);
    var bytes = std.mem.splitScalar(u8, literal, '\\');

    while (bytes.next()) |chunk| {
        str.appendSliceAssumeCapacity(chunk);
        if (bytes.rest().len == 0) break;
        switch (bytes.rest()[0]) {
            '{' => {
                var hex_bytes = bytes.rest();
                var i: usize = 1;
                while (i < hex_bytes.len and hex_bytes[i] != '}') : (i += 2) {
                    if (i + 1 >= hex_bytes.len) {
                        return .{ .err = .{ .reason = "incomplete escape sequence", .pos = literal.len - bytes.rest().len } };
                    }
                    const byte_val = std.fmt.parseInt(u8, hex_bytes[i .. i + 2], 16) catch {
                        return .{ .err = .{ .reason = "expected hex digit or '}'", .pos = literal.len - bytes.rest().len } };
                    };
                    str.appendAssumeCapacity(byte_val);
                }
                bytes.index.? += i + 1;
            },
            else => |b| {
                for (SPECIAL_CHARS, TO_BYTES) |s, sb| {
                    if (s == b) {
                        str.appendAssumeCapacity(sb);
                        break;
                    }
                } else return .{ .err = .{ .reason = "unknown escape sequence", .pos = literal.len - bytes.rest().len } };
                bytes.index.? += 1;
            },
        }
    }

    return .{ .ok = str.items };
}

pub fn partialEval(self: *Codegen, pos: anytype, node: *Builder.BuildNode) !u64 {
    return switch (self.types.ct.partialEval(&self.bl, node)) {
        .Resolved => |r| r,
        .Unsupported => |n| {
            return self.report(pos, "can't evaluate this at compile time (yet), (DEBUG: got stuck on {})", .{n});
        },
    };
}

pub const EmitError = error{ Never, Unreachable };

pub fn emit(self: *Codegen, ctx: Ctx, expr: Ast.Id) EmitError!Value {
    const ast = self.ast;
    switch (ast.exprs.get(expr)) {
        .Comment => return .{},
        .Void => return .{},

        // #VALUES =====================================================================
        .String => |e| {
            const lit = ast.source[e.pos.index + 1 .. e.end - 1];

            const data = switch (encodeString(lit, self.types.arena.alloc(u8, lit.len))) {
                .ok => |dt| dt,
                .err => |err| {
                    var pos = e.pos;
                    pos.index += @intCast(err.pos);
                    return self.report(pos, "{s}", .{err.reason});
                },
            };

            return self.emitStirng(ctx, data, expr);
        },
        .Integer => |e| {
            const ty = ctx.ty orelse .uint;
            if (!ty.isInteger()) {
                return self.report(expr, "{} can not be constructed as integer literal", .{ty});
            }
            const shift: u8 = if (e.base == 10) 0 else 2;
            const parsed = std.fmt.parseInt(u64, ast.tokenSrc(e.pos.index + shift), e.base) catch |err| switch (err) {
                error.InvalidCharacter => unreachable,
                error.Overflow => return self.report(expr, "number does not fit into 64 bits", .{}),
            };
            return .mkv(ty, self.bl.addIntImm(self.abi.categorize(ty, self.types).ByValue, @bitCast(parsed)));
        },
        .Float => |e| {
            const ty = ctx.ty orelse .f32;
            if (!ty.isFloat()) {
                return self.report(expr, "{} can not be constructed as integer literal", .{ty});
            }

            if (ty == .f32) {
                const parsed = std.fmt.parseFloat(f32, ast.tokenSrc(e.index)) catch |err| switch (err) {
                    error.InvalidCharacter => unreachable,
                };
                return .mkv(ty, self.bl.addFlt32Imm(parsed));
            } else {
                const parsed = std.fmt.parseFloat(f64, ast.tokenSrc(e.index)) catch |err| switch (err) {
                    error.InvalidCharacter => unreachable,
                };
                return .mkv(ty, self.bl.addFlt64Imm(parsed));
            }
        },
        .Bool => |e| {
            return .mkv(.bool, self.bl.addIntImm(.i8, @intFromBool(e.value)));
        },
        .Null => {
            const ty: Types.Id = ctx.ty orelse {
                return self.report(expr, "can't infer the type of nullable value, you can speciry a type: @as(?<ty>, null)", .{});
            };

            if (ty.data() != .Nullable) {
                return self.report(expr, "only nullable types can be initialized with null, {} is not", .{ty});
            }

            if (ty.data().Nullable.nieche.offset(self.types)) |spec| {
                switch (self.abi.categorize(ty.data().Nullable.inner, self.types)) {
                    .Imaginary => unreachable,
                    .ByValue => return .mkv(ty, self.bl.addIntImm(spec.kind.abi(), 0)),
                    .ByValuePair, .ByRef => {
                        const loc = ctx.loc orelse self.bl.addLocal(ty.data().Nullable.inner.size(self.types));
                        _ = self.bl.addFieldStore(loc, spec.offset, spec.kind.abi(), self.bl.addIntImm(spec.kind.abi(), 0));
                        return .mkp(ty, loc);
                    },
                }
            } else {
                switch (self.abi.categorize(ty, self.types)) {
                    .Imaginary => unreachable,
                    .ByValue => return .mkv(ty, self.bl.addIntImm(.i8, 0)),
                    .ByValuePair, .ByRef => {
                        const loc = ctx.loc orelse self.bl.addLocal(ty.size(self.types));
                        _ = self.bl.addStore(loc, .i8, self.bl.addIntImm(.i8, 0));
                        return .mkp(ty, loc);
                    },
                }
            }
        },
        .Ident => |e| return self.loadIdent(e.pos, e.id),
        .Idk => {
            const ty: Types.Id = ctx.ty orelse {
                return self.report(expr, "cant infer the type of uninitialized memory," ++
                    " you can specify a type: @as(<ty>, idk)", .{});
            };

            const abi = self.abi.categorize(ty, self.types);
            if (abi == .ByValue) {
                return .mkv(ty, self.bl.addIntImm(abi.ByValue, @bitCast(@as(u64, 0xaaaaaaaaaaaaaaaa))));
            } else {
                const loc = ctx.loc orelse self.bl.addLocal(ty.size(self.types));
                return .mkp(ty, loc);
            }
        },
        .Ctor => |e| {
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            if (e.ty.tag() == .Void and ctx.ty == null) {
                return self.report(expr, "cant infer the type of this constructor, you can specify a type: '<ty>.{{'", .{});
            }

            const oty = ctx.ty orelse try self.resolveAnonTy(e.ty);
            var ty = oty;
            const local = ctx.loc orelse self.bl.addLocal(ty.size(self.types));
            var offset_cursor: usize = 0;

            if (ty.needsTag(self.types)) {
                ty = ty.data().Nullable.inner;
                _ = self.bl.addStore(local, .i8, self.bl.addIntImm(.i8, 1));
                offset_cursor += ty.alignment(self.types);
            }

            switch (ty.data()) {
                .Struct => |struct_ty| {
                    // Existing struct constructor code...
                    const FillSlot = union(enum) {
                        RequiredOffset: usize,
                        Filled: Ast.Id,
                    };

                    const fields = struct_ty.getFields(self.types);
                    const slots = tmp.arena.alloc(FillSlot, fields.len);
                    {
                        var iter = struct_ty.offsetIter(self.types);
                        iter.offset = offset_cursor;
                        for (slots) |*s| {
                            const elem = iter.next().?;
                            s.* = .{ .RequiredOffset = elem.offset };
                        }
                    }

                    for (ast.exprs.view(e.fields)) |field| {
                        const fname = ast.tokenSrc(field.pos.index);
                        const slot, const ftype = for (fields, slots) |tf, *s| {
                            if (std.mem.eql(u8, tf.name, fname)) break .{ s, tf.ty };
                        } else {
                            self.report(field.pos, "{} does not have a field called {s} (TODO: list fields)", .{ ty, fname }) catch continue;
                        };

                        switch (slot.*) {
                            .RequiredOffset => |offset| {
                                const off = self.bl.addFieldOffset(local, @intCast(offset));
                                var value = self.emit(ctx.addTy(ftype).addLoc(off), field.value) catch |err| switch (err) {
                                    error.Never => continue,
                                    error.Unreachable => return err,
                                };
                                try self.typeCheck(field.value, &value, ftype);
                                self.emitGenericStore(off, &value);
                                slot.* = .{ .Filled = field.value };
                            },
                            .Filled => |pos| {
                                self.report(field.pos, "initializing the filed multiple times", .{}) catch {};
                                self.report(pos, "...arleady initialized here", .{}) catch {};
                            },
                        }
                    }

                    for (slots, fields) |s, f| {
                        if (s == .RequiredOffset) {
                            if (f.defalut_value) |value| {
                                // TODO: we will need to optimize constants in the backend
                                self.queue(.{ .Global = value });
                                const off = self.bl.addFieldOffset(local, @intCast(s.RequiredOffset));
                                const glob = self.bl.addGlobalAddr(value.id);
                                self.bl.addFixedMemCpy(off, glob, f.ty.size(self.types));
                            } else {
                                return self.report(expr, "field {s} on struct {} is not initialized", .{ f.name, ty });
                            }
                        }
                    }
                },
                .Union => |union_ty| {
                    if (e.fields.len() != 1) {
                        return self.report(expr, "union constructor must initialize only one field", .{});
                    }

                    const fields = union_ty.getFields(self.types);

                    const field_ast = ast.exprs.view(e.fields)[0];
                    const fname = ast.tokenSrc(field_ast.pos.index);

                    const f = for (fields) |f| {
                        if (std.mem.eql(u8, f.name, fname)) break f;
                    } else {
                        return self.report(field_ast.value, "{} does not have a field called {s} (TODO: list fields)", .{ ty, fname });
                    };

                    offset_cursor = std.mem.alignForward(usize, offset_cursor, f.ty.alignment(self.types));
                    const off = self.bl.addFieldOffset(local, @intCast(offset_cursor));
                    var value = try self.emit(.{ .ty = f.ty, .loc = off }, field_ast.value);
                    try self.typeCheck(field_ast.value, &value, f.ty);
                    self.emitGenericStore(off, &value);
                },
                else => {
                    return self.report(expr, "{} can not be constructed with '.{{..}}'", .{ty});
                },
            }

            return .mkp(oty, local);
        },
        .Tupl => |e| if (e.ty.tag() == .Void and ctx.ty == null) {
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            const local = ctx.loc orelse self.bl.addLocal(0);
            var offset: usize = 0;
            var alignment: usize = 1;
            const tys = tmp.arena.alloc(Types.Id, e.fields.len());

            for (ast.exprs.view(e.fields), tys) |field, *ty| {
                var value = try self.emit(.{}, field);
                ty.* = value.ty;
                offset = std.mem.alignForward(usize, offset, value.ty.alignment(self.types));
                self.emitGenericStore(self.bl.addFieldOffset(local, @bitCast(offset)), &value);
                offset += value.ty.size(self.types);
                alignment = @max(alignment, value.ty.alignment(self.types));
            }
            offset = std.mem.alignForward(usize, offset, alignment);
            if (ctx.loc == null) self.bl.resizeLocal(local, offset);

            return .mkp(self.types.makeTuple(tys), local);
        } else {
            const oty = ctx.ty orelse try self.resolveAnonTy(e.ty);
            var ty = oty;
            const local = ctx.loc orelse self.bl.addLocal(oty.size(self.types));
            var init_offset: usize = 0;

            if (ty.needsTag(self.types)) {
                ty = ty.data().Nullable.inner;
                _ = self.bl.addStore(local, .i8, self.bl.addIntImm(.i8, 1));
                init_offset += ty.alignment(self.types);
            }

            if (ty.data() != .Struct) {
                return self.report(expr, "{} can not be constructed with '.(..)'", .{ty});
            }
            const struct_ty = ty.data().Struct;

            if (e.fields.len() != struct_ty.getFields(self.types).len) {
                return self.report(
                    e.pos,
                    "{} has {} fields, but tuple constructor has {} values",
                    .{ ty, struct_ty.getFields(self.types).len, e.fields.len() },
                );
            }

            var iter = struct_ty.offsetIter(self.types);
            iter.offset = init_offset;
            for (ast.exprs.view(e.fields)) |field| {
                const elem = iter.next().?;
                const ftype = elem.field.ty;
                if (ftype == .never) return error.Never;

                const off = self.bl.addFieldOffset(local, @intCast(elem.offset));
                var value = self.emit(ctx.addTy(ftype).addLoc(off), field) catch |err| switch (err) {
                    error.Never => continue,
                    error.Unreachable => return err,
                };
                try self.typeCheck(field, &value, ftype);
                self.emitGenericStore(off, &value);
            }

            return .mkp(oty, local);
        },
        .Arry => |e| {
            if (e.ty.tag() == .Void and ctx.ty == null) {
                return self.report(expr, "cant infer the type of this constructor, you can specify a type: '<elem-ty>.('", .{});
            }

            const local = ctx.loc orelse self.bl.addLocal(0);
            var start: usize = 0;

            const elem_ty, const res_ty: Types.Id = if (ctx.ty) |ret_ty| b: {
                var ty = ret_ty;
                if (ty.needsTag(self.types)) {
                    ty = ty.data().Nullable.inner;
                    _ = self.bl.addStore(local, .i8, self.bl.addIntImm(.i8, 1));
                    start += 1;
                }

                if (ty.data() != .Slice or ty.data().Slice.len == null) {
                    return self.report(expr, "{} can not bi initialized with array syntax", .{ty});
                }

                if (ty.data().Slice.len != e.fields.len()) {
                    return self.report(expr, "expected array with {} element, got {}", .{ ty.data().Slice.len.?, e.fields.len() });
                }

                break :b .{ ty.data().Slice.elem, ret_ty };
            } else b: {
                const elem_ty = try self.resolveAnonTy(e.ty);
                const array_ty = self.types.makeSlice(e.fields.len(), elem_ty);
                break :b .{ elem_ty, array_ty };
            };

            if (ctx.loc == null) self.bl.resizeLocal(local, res_ty.size(self.types));

            for (ast.exprs.view(e.fields), start..) |elem, i| {
                const off = self.bl.addFieldOffset(local, @intCast(i * elem_ty.size(self.types)));
                var value = self.emitTyped(.{ .loc = off }, elem_ty, elem) catch |err| switch (err) {
                    error.Never => continue,
                    error.Unreachable => return err,
                };
                self.emitGenericStore(off, &value);
            }

            return .mkp(res_ty, local);
        },

        // #OPS ========================================================================
        .SliceTy => |e| {
            const len: ?usize = if (e.len.tag() == .Void) null else @intCast(self.types.ct.evalIntConst(.{ .Tmp = self }, e.len) catch 0);
            const elem = try self.resolveAnonTy(e.elem);
            return self.emitTyConst(self.types.makeSlice(len, elem));
        },
        .UnOp => |e| switch (e.op) {
            .@"^" => return self.emitTyConst(self.types.makePtr(try self.resolveAnonTy(e.oper))),
            .@"?" => return self.emitTyConst(self.types.makeNullable(try self.resolveAnonTy(e.oper))),
            .@"&" => {
                const addrd = try self.emit(.{}, e.oper);
                return .mkv(self.types.makePtr(addrd.ty), switch (addrd.id) {
                    .Imaginary => self.bl.addIntImm(.int, @intCast(addrd.ty.alignment(self.types))),
                    .Value => |v| self.bl.addSpill(v),
                    .Ptr => |p| p,
                });
            },
            inline .@"-", .@"!", .@"~" => |t| {
                var lhs = try self.emit(ctx, e.oper);
                switch (t) {
                    .@"-" => if (!lhs.ty.isInteger() and !lhs.ty.isFloat()) return self.report(expr, "only integers can be negated, {} is not", .{lhs.ty}),
                    .@"!" => if (lhs.ty != .bool) return self.report(expr, "only booleans can be negated, {} is not", .{lhs.ty}),
                    .@"~" => if (!lhs.ty.isInteger()) return self.report(expr, "only integers can invert their bits, {} is not", .{lhs.ty}),
                    else => @compileError("wut"),
                }
                self.ensureLoaded(&lhs);
                if (t == .@"!") lhs.id.Value = self.bl.addUnOp(.uext, .int, lhs.id.Value);
                return .mkv(lhs.ty, self.bl.addUnOp(switch (t) {
                    .@"-" => if (lhs.ty.isFloat()) .fneg else .ineg,
                    .@"!" => .not,
                    .@"~" => .bnot,
                    else => @compileError("wut"),
                }, self.abi.categorize(lhs.ty, self.types).ByValue, lhs.id.Value));
            },
            else => std.debug.panic("{any}\n", .{ast.exprs.get(expr)}),
        },
        .BinOp => |e| switch (e.op) {
            inline .@":=", .@":" => |t| {
                const loc = self.bl.addLocal(0);

                const prev_name = self.name;
                const ident = ast.exprs.getTyped(.Ident, e.lhs) orelse return self.report(expr, "TODO: pattern matching", .{});

                errdefer |err| if (err != error.Unreachable) {
                    self.scope.appendAssumeCapacity(.{ .ty = .never, .name = ident.id });
                    self.bl.pushScopeValue(loc);
                };

                self.name = ast.tokenSrc(ident.id.pos());
                defer self.name = prev_name;

                var value = try if (t == .@":=")
                    self.emit(.{ .loc = loc }, e.rhs)
                else b: {
                    const assign = ast.exprs.getTyped(.BinOp, e.rhs) orelse
                        return @as(EmitError!Value, self.report(e.rhs, "TODO: support this as uninitialized", .{}));
                    if (assign.op != .@"=")
                        return @as(EmitError!Value, self.report(e.lhs, "can't do that binary oprtator here, expected `=`", .{}));
                    const ty = try self.resolveAnonTy(assign.lhs);
                    break :b self.emitTyped(ctx.addLoc(loc), ty, assign.rhs);
                };

                self.bl.resizeLocal(loc, value.ty.size(self.types));
                self.emitGenericStore(loc, &value);

                self.scope.appendAssumeCapacity(.{ .ty = value.ty, .name = ident.id });
                self.bl.pushScopeValue(loc);
                return .{};
            },
            .@"=" => if (e.lhs.tag() == .Wildcard) {
                _ = try self.emit(.{}, e.rhs);
                return .{};
            } else {
                const loc = try self.emit(.{}, e.lhs);

                if (loc.id != .Ptr) {
                    return self.report(e.lhs, "can't assign to this", .{});
                }

                var val = try self.emitTyped(ctx, loc.ty, e.rhs);
                self.emitGenericStore(loc.id.Ptr, &val);
                return .{};
            },
            else => {
                if (e.lhs.tag() == .Null) {
                    return self.report(e.lhs, "null has to be on the right hand side", .{});
                }

                var lhs = try self.emit(if (e.op.isComparison()) .{} else ctx, e.lhs);

                if (e.rhs.tag() == .Null) switch (e.op) {
                    .@"==", .@"!=" => {
                        if (lhs.ty.data() != .Nullable) {
                            return self.report(e.lhs, "only nullable types can be compared with null, {} is not", .{lhs.ty});
                        }

                        const abi = self.abi.categorize(lhs.ty, self.types);
                        var value = switch (abi) {
                            .Imaginary => unreachable,
                            .ByValue => b: {
                                self.ensureLoaded(&lhs);
                                break :b lhs.id.Value;
                            },
                            .ByValuePair, .ByRef => self.bl.addLoad(lhs.id.Ptr, .i8),
                        };

                        value = self.bl.addUnOp(.uext, .int, value);

                        if (e.op == .@"==") {
                            value = self.bl.addBinOp(.eq, .int, value, self.bl.addIntImm(.int, 0));
                        }

                        return .mkv(.bool, value);
                    },
                    else => {
                        return self.report(e.lhs, "only comparing against null is supported", .{});
                    },
                };

                if (!lhs.ty.isBinaryOperand()) {
                    return self.report(e.lhs, "{} can not be used in binary operations", .{lhs.ty});
                }

                var rhs = try self.emit(ctx.addTy(lhs.ty), e.rhs);

                if (!rhs.ty.isBinaryOperand()) {
                    return self.report(e.rhs, "{} can not be used in binary operations", .{rhs.ty});
                }

                if (e.op.isComparison() and lhs.ty.isSigned() != rhs.ty.isSigned())
                    return self.report(e.lhs, "mixed sign comparison ({} {})", .{ lhs.ty, rhs.ty });
                const unified: Types.Id = ctx.ty orelse lhs.ty.binOpUpcast(rhs.ty, self.types) catch |err| {
                    return self.report(expr, "{s} ({} and {})", .{ @errorName(err), lhs.ty, rhs.ty });
                };

                if (!unified.isBinaryOperand()) {
                    return self.report(e.lhs, "{} can not be used in binary operations", .{unified});
                }

                if (lhs.ty.data() == .Struct) if (e.op == .@"==" or e.op == .@"!=") {
                    const value = self.emitStructFoldOp(lhs.ty.data().Struct, e.op, lhs.id.Ptr, rhs.id.Ptr);
                    return .mkv(unified, value orelse self.bl.addIntImm(.i8, 1));
                } else {
                    const loc = ctx.loc orelse self.bl.addLocal(unified.size(self.types));
                    self.emitStructOp(lhs.ty.data().Struct, e.op, loc, lhs.id.Ptr, rhs.id.Ptr);
                    return .mkp(unified, loc);
                } else {
                    const upcast_to: Types.Id = if (e.op.isComparison())
                        if (lhs.ty.isFloat() or lhs.ty.data() == .Ptr) lhs.ty else if (lhs.ty.isSigned()) .int else .uint
                    else
                        unified;
                    const lhs_fail = self.typeCheck(e.lhs, &lhs, upcast_to);
                    try self.typeCheck(e.rhs, &rhs, upcast_to);
                    try lhs_fail;
                    self.ensureLoaded(&lhs);
                    self.ensureLoaded(&rhs);
                    if (e.op == .@"!=" or e.op == .@"==" and lhs.ty == .f32) {
                        lhs.id.Value = self.bl.addUnOp(.uext, .int, lhs.id.Value);
                        rhs.id.Value = self.bl.addUnOp(.uext, .int, rhs.id.Value);
                    }
                    if (lhs.id == .Imaginary) std.debug.print("{}\n{}\n", .{ lhs.ty.fmt(self.types), self.ast.codePointer(self.ast.posOf(expr).index) });
                    return .mkv(unified, self.bl.addBinOp(
                        lexemeToBinOp(e.op, lhs.ty),
                        self.abi.categorize(unified, self.types).ByValue,
                        lhs.id.Value,
                        rhs.id.Value,
                    ));
                }
            },
        },
        .Unwrap => |e| {
            // TODO: better type inference
            var base = try self.emit(.{}, e);

            self.emitAutoDeref(&base);

            if (base.ty.data() != .Nullable) {
                return self.report(e, "only nullable types can be unwrapped, {} is not", .{base.ty});
            }

            const ty = base.ty.data().Nullable.inner;

            if (!base.ty.needsTag(self.types)) return base;

            switch (self.abi.categorize(base.ty, self.types)) {
                .Imaginary => unreachable,
                .ByValue => return .{ .ty = ty },
                .ByRef, .ByValuePair => return .mkp(ty, self.bl.addFieldOffset(base.id.Ptr, @bitCast(ty.alignment(self.types)))),
            }
        },
        .Deref => |e| {
            var base = try self.emit(.{}, e);

            if (base.ty.data() != .Ptr) {
                return self.report(e, "only pointer types can be dereferenced, {} is not", .{base.ty});
            }

            self.ensureLoaded(&base);
            return .mkp(base.ty.data().Ptr.*, base.id.Value);
        },
        .Tag => |e| {
            const ty = ctx.ty orelse {
                return self.report(
                    expr,
                    "cant infer the type of the implicit access, you can specify the type: <ty>.{s}",
                    .{ast.tokenSrc(e.index + 1)},
                );
            };

            return try self.lookupScopeItem(e, ty, ast.tokenSrc(e.index + 1));
        },
        .Field => |e| {
            var base = try self.emit(.{}, e.base);

            self.emitAutoDeref(&base);

            if (base.ty == .type) {
                const bsty = try self.unwrapTyConst(e.base, &base);
                return try self.lookupScopeItem(e.field, bsty, ast.tokenSrc(e.field.index));
            }

            const fname = ast.tokenSrc(e.field.index);

            switch (base.ty.data()) {
                .Struct => |struct_ty| {
                    var iter = struct_ty.offsetIter(self.types);
                    const ftype, const offset = while (iter.next()) |elem| {
                        if (std.mem.eql(u8, fname, elem.field.name)) break .{ elem.field.ty, elem.offset };
                    } else {
                        return self.report(e.field, "no such field on {} (TODO: list fields)", .{base.ty});
                    };

                    return .mkp(ftype, self.bl.addFieldOffset(base.id.Ptr, @intCast(offset)));
                },
                .Union => |union_ty| {
                    const ftype = for (union_ty.getFields(self.types)) |tf| {
                        if (std.mem.eql(u8, fname, tf.name)) break tf.ty;
                    } else {
                        return self.report(e.field, "no such field on {} (TODO: list fields)", .{base.ty});
                    };

                    return .mkp(ftype, self.bl.addFieldOffset(base.id.Ptr, 0));
                },
                .Slice => |slice_ty| {
                    if (std.mem.eql(u8, fname, "len")) {
                        if (slice_ty.len) |l| {
                            return .mkv(.uint, self.bl.addIntImm(.int, @bitCast(l)));
                        } else {
                            return .mkv(.uint, self.bl.addFieldLoad(base.id.Ptr, Types.Slice.len_offset, .int));
                        }
                    } else if (std.mem.eql(u8, fname, "ptr")) {
                        const ptr_ty = self.types.makePtr(slice_ty.elem);
                        if (slice_ty.len == null) {
                            return .mkv(ptr_ty, self.bl.addFieldLoad(base.id.Ptr, Types.Slice.ptr_offset, .int));
                        } else {
                            return .mkv(ptr_ty, base.id.Ptr);
                        }
                    } else {
                        return self.report(e.field, "slices and arrays only support `.ptr` and `.len` field", .{});
                    }
                },
                else => {
                    return self.report(e.field, "field access is only allowed on structs and arrays, {} is not", .{base.ty});
                },
            }
        },
        .Index => |e| if (e.subscript.tag() == .Range) {
            var base = try self.emit(.{}, e.base);

            const range = ast.exprs.get(e.subscript).Range;

            const elem = base.ty.child(self.types) orelse {
                return self.report(e.base, "only pointers, arrays and slices can be sliced, {} is not", .{base.ty});
            };

            var start: Value = if (range.start.tag() == .Void)
                .mkv(.uint, self.bl.addIntImm(.int, 0))
            else
                try self.emitTyped(.{}, .uint, range.start);
            self.ensureLoaded(&start);
            var end: Value = if (range.end.tag() == .Void) switch (base.ty.data()) {
                .Slice => |slice_ty| if (slice_ty.len) |l|
                    .mkv(.uint, self.bl.addIntImm(.int, @bitCast(l)))
                else
                    .mkv(.uint, self.bl.addFieldLoad(base.id.Ptr, Types.Slice.len_offset, .int)),
                else => {
                    return self.report(e.subscript, "unbound range is only allowed on arrays and slices, {} is not", .{base.ty});
                },
            } else try self.emitTyped(.{}, .uint, range.end);
            self.ensureLoaded(&end);

            const res_ty = self.types.makeSlice(null, elem);

            var ptr: Value = switch (base.ty.data()) {
                .Ptr => b: {
                    self.ensureLoaded(&base);
                    break :b base;
                },
                .Slice => |slice_ty| if (slice_ty.len == null)
                    .mkv(self.types.makePtr(elem), self.bl.addFieldLoad(base.id.Ptr, Types.Slice.ptr_offset, .int))
                else
                    .mkv(self.types.makePtr(elem), base.id.Ptr),
                else => {
                    return self.report(expr, "only structs and slices can be indexed, {} is not", .{base.ty});
                },
            };

            ptr.id.Value = self.bl.addIndexOffset(ptr.id.Value, elem.size(self.types), start.id.Value);
            const len = self.bl.addBinOp(.isub, .int, end.id.Value, start.id.Value);

            const loc = ctx.loc orelse self.bl.addLocal(res_ty.size(self.types));
            self.bl.addFieldStore(loc, Types.Slice.ptr_offset, .int, ptr.id.Value);
            self.bl.addFieldStore(loc, Types.Slice.len_offset, .int, len);

            return .mkp(res_ty, loc);
        } else {
            var base = try self.emit(.{}, e.base);

            // TODO: pointers to arrays are kind of an edge case
            self.emitAutoDeref(&base);
            var idx_value = try self.emitTyped(.{}, .uint, e.subscript);
            self.ensureLoaded(&idx_value);
            switch (base.ty.data()) {
                inline .Struct, .Tuple => |struct_ty| {
                    const idx = try self.partialEval(e.subscript, idx_value.id.Value);

                    var iter = struct_ty.offsetIter(self.types);

                    if (idx >= iter.fields.len) {
                        return self.report(e.subscript, "struct has only {} fields, but idnex is {}", .{ iter.fields.len, idx });
                    }

                    var elem: @TypeOf(iter.next().?) = undefined;
                    for (0..idx + 1) |_| elem = iter.next().?;

                    return .mkp(elem.field.ty, self.bl.addFieldOffset(base.id.Ptr, @intCast(elem.offset)));
                },
                .Slice => |slice_ty| {
                    const index_base = if (slice_ty.len == null) self.bl.addLoad(base.id.Ptr, .int) else base.id.Ptr;

                    return .mkp(slice_ty.elem, self.bl.addIndexOffset(index_base, slice_ty.elem.size(self.types), idx_value.id.Value));
                },
                else => {
                    return self.report(expr, "only structs and slices can be indexed, {} is not", .{base.ty});
                },
            }
        },

        // #CONTROL ====================================================================
        .Block => |e| {
            const prev_scope_height = self.scope.items.len;
            defer self.scope.items.len = prev_scope_height;
            defer self.bl.truncateScope(prev_scope_height);

            const defer_scope = self.defers.items.len;
            defer self.defers.items.len = defer_scope;

            for (ast.exprs.view(e.stmts)) |s| {
                _ = self.emitTyped(ctx, .void, s) catch |err| switch (err) {
                    error.Never => {},
                    error.Unreachable => return err,
                };
            }
            self.emitDefers(defer_scope);

            return .{};
        },
        .Defer => |e| {
            self.defers.appendAssumeCapacity(e);
            return .{};
        },
        .If => |e| if (e.pos.flag.@"comptime") {
            var cond = try self.emitTyped(ctx, .bool, e.cond);
            self.ensureLoaded(&cond);
            if (try self.partialEval(e.cond, cond.id.Value) != 0) {
                _ = self.emitTyped(ctx, .void, e.then) catch |err| switch (err) {
                    error.Never => {},
                    error.Unreachable => return err,
                };
            } else {
                _ = self.emitTyped(ctx, .void, e.else_) catch |err| switch (err) {
                    error.Never => {},
                    error.Unreachable => return err,
                };
            }

            return .{};
        } else {
            var cond = try self.emitTyped(ctx, .bool, e.cond);
            self.ensureLoaded(&cond);
            cond.id.Value = self.bl.addUnOp(.uext, .int, cond.id.Value);
            var unreachable_count: usize = 0;
            var if_builder = self.bl.addIfAndBeginThen(cond.id.Value);
            {
                const prev_scope_height = self.scope.items.len;
                defer self.scope.items.len = prev_scope_height;
                defer self.bl.truncateScope(prev_scope_height);
                _ = self.emitTyped(ctx, .void, e.then) catch |err| {
                    unreachable_count += @intFromBool(err == error.Unreachable);
                };
            }
            const end_else = if_builder.beginElse(&self.bl);
            {
                const prev_scope_height = self.scope.items.len;
                defer self.scope.items.len = prev_scope_height;
                defer self.bl.truncateScope(prev_scope_height);
                _ = self.emitTyped(ctx, .void, e.else_) catch |err| {
                    unreachable_count += @intFromBool(err == error.Unreachable);
                };
            }
            if_builder.end(&self.bl, end_else);

            if (unreachable_count == 2) return error.Unreachable;

            return .{};
        },
        .Match => |e| {
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            var value = try self.emit(.{}, e.value);

            if (value.ty.data() != .Enum) return self.report(e.value, "can only match on enums right now, {} is not", .{value.ty});
            const enm = value.ty.data().Enum;

            const fields = enm.getFields(self.types);

            if (fields.len == 0) return error.Unreachable;

            if (e.arms.len() == 0) return self.report(e.pos, "the matched type has non zero possible values, " ++
                "therefore empty match statement is invalid", .{});

            const ArmSlot = union(enum) {
                Unmatched,
                Matched: Ast.Id,
            };

            const Matcher = struct {
                iter_until: usize,
                else_arm: ?Ast.Id = null,
                slots: []ArmSlot,
                ty: Types.Id,

                pub fn decomposeArm(slf: *@This(), cg: *Codegen, i: usize, a: Ast.Id) !?struct { u64, Ast.Id } {
                    const asta = cg.ast;

                    const arm = asta.exprs.getTyped(.BinOp, a) orelse
                        cg.report(a, "expected match arm `<pat> => <body>,`", .{}) catch return null;

                    if (arm.lhs.tag() == .Wildcard or i == slf.iter_until) {
                        if (slf.else_arm) |erm| {
                            if (i == slf.iter_until) {
                                cg.report(erm, "useless esle match arm, all cases are covered", .{}) catch {};
                            } else {
                                cg.report(a, "duplicate else match arm", .{}) catch {};
                                cg.report(erm, "...previouslly matched here", .{}) catch {};
                            }
                        } else {
                            slf.iter_until += 1;
                            slf.else_arm = arm.rhs;
                        }
                        return null;
                    }

                    var match_pat = try cg.emitTyped(.{}, slf.ty, arm.lhs);
                    cg.ensureLoaded(&match_pat);
                    const idx = if (match_pat.id == .Imaginary) 0 else try cg.partialEval(arm.lhs, match_pat.id.Value);

                    switch (slf.slots[idx]) {
                        .Unmatched => slf.slots[idx] = .{ .Matched = a },
                        .Matched => |pos| {
                            cg.report(a, "duplicate match arm", .{}) catch {};
                            cg.report(pos, "...previouslly matched here", .{}) catch {};
                            return null;
                        },
                    }

                    return .{ idx, arm.rhs };
                }
            };

            var matcher = Matcher{
                .iter_until = fields.len - 1,
                .slots = tmp.arena.alloc(ArmSlot, fields.len),
                .ty = value.ty,
            };
            @memset(matcher.slots, .Unmatched);

            self.ensureLoaded(&value);
            if (e.pos.flag.@"comptime") {
                const value_idx = if (value.id == .Imaginary) 0 else try self.partialEval(e.value, value.id.Value);

                var matched_branch: ?Ast.Id = null;
                for (ast.exprs.view(e.arms), 0..) |a, i| {
                    const idx, const body = try matcher.decomposeArm(self, i, a) orelse continue;

                    if (idx == value_idx) {
                        std.debug.assert(matched_branch == null);
                        matched_branch = body;
                    }
                }

                const final_branch = matched_branch orelse matcher.else_arm orelse
                    return self.report(e.pos, "not all branches are covered (TODO: list missing ones)", .{});

                _ = try self.emitTyped(ctx, .void, final_branch);
            } else {
                var if_stack = std.ArrayListUnmanaged(Builder.If).initBuffer(tmp.arena.alloc(Builder.If, e.arms.len() - 1));

                var unreachable_count: usize = 0;
                for (ast.exprs.view(e.arms), 0..) |a, i| {
                    const idx, const body = try matcher.decomposeArm(self, i, a) orelse continue;

                    const cond = self.bl.addBinOp(.eq, .i8, self.bl.addUnOp(.sext, .int, value.id.Value), self.bl.addIntImm(.int, @bitCast(idx)));
                    var if_builder = self.bl.addIfAndBeginThen(cond);
                    _ = self.emitTyped(ctx, .void, body) catch |err| {
                        unreachable_count += @intFromBool(err == error.Unreachable);
                    };
                    _ = if_builder.beginElse(&self.bl);
                    if_stack.appendAssumeCapacity(if_builder);
                }

                const final_else = matcher.else_arm orelse return self.report(e.pos, "not all branches are covered (TODO: list missing ones)", .{});
                _ = self.emitTyped(ctx, .void, final_else) catch |err| {
                    unreachable_count += @intFromBool(err == error.Unreachable);
                };

                var iter = std.mem.reverseIterator(if_stack.items);
                while (iter.nextPtr()) |br| br.end(&self.bl, @enumFromInt(0));

                if (unreachable_count == e.arms.len()) return error.Unreachable;
            }
            return .{};
        },
        .Loop => |e| if (e.pos.flag.@"comptime") {
            self.loops.appendAssumeCapacity(.{
                .defer_base = self.defers.items.len,
                .kind = .{ .Comptime = .Clean },
            });
            const loop = &self.loops.items[self.loops.items.len - 1];
            const default_iters = 200;
            var fuel: usize = default_iters;
            while ((loop.kind.Comptime != .Controlled or loop.kind.Comptime.Controlled.tag() != .Break) and !self.errored) {
                if (fuel == 0) {
                    return self.report(expr, "loop exceeded {} comptime iterations (TODO: add @setComptimeIterLimit(val))", .{default_iters});
                }
                fuel -= 1;
                loop.kind.Comptime = .Clean;
                _ = self.emitTyped(.{}, .void, e.body) catch |err| switch (err) {
                    error.Never => {},
                    error.Unreachable => continue,
                };
                self.loopControl(.@"continue", expr) catch {};
            }
            _ = self.loops.pop().?;
            return .{};
        } else {
            var loop = self.bl.addLoopAndBeginBody();
            self.loops.appendAssumeCapacity(.{
                .defer_base = self.defers.items.len,
                .kind = .{ .Runtime = loop },
            });
            {
                const prev_scope_height = self.scope.items.len;
                defer self.scope.items.len = prev_scope_height;
                defer self.bl.truncateScope(prev_scope_height);
                _ = self.emitTyped(ctx, .void, e.body) catch {};
            }
            loop = self.loops.pop().?.kind.Runtime;
            loop.end(&self.bl);

            if (self.bl.isUnreachable()) return error.Unreachable;

            return .{};
        },
        // TODO: detect conflicting control flow
        .Break => {
            try self.loopControl(.@"break", expr);
            return .{};
        },
        .Continue => {
            try self.loopControl(.@"continue", expr);
            return .{};
        },
        .Call => |e| return self.emitCall(ctx, expr, e),
        .Return => |e| {
            var value = try self.emit(.{ .loc = self.struct_ret_ptr, .ty = self.ret }, e.value);
            try self.typeCheck(expr, &value, self.ret);
            self.emitDefers(0);
            switch (self.abi.categorize(value.ty, self.types)) {
                .Imaginary => self.bl.addReturn(&.{}),
                .ByValue => {
                    self.ensureLoaded(&value);
                    self.bl.addReturn(&.{value.id.Value});
                },
                .ByValuePair => |pair| {
                    var slots: [2]*Node = undefined;
                    for (pair.types, pair.offsets(), &slots) |t, off, *slt| {
                        slt.* = self.bl.addFieldLoad(value.id.Ptr, @intCast(off), t);
                    }
                    self.bl.addReturn(&slots);
                },
                .ByRef => {
                    self.emitGenericStore(self.struct_ret_ptr.?, &value);
                    self.bl.addReturn(&.{});
                },
            }
            return error.Unreachable;
        },
        .Die => {
            self.bl.addTrap(0);
            return error.Unreachable;
        },
        .Buty => |e| return self.emitTyConst(.fromLexeme(e.bt)),
        inline .Struct, .Union, .Enum => |e, t| {
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            const prefix = 3;
            const args = self.bl.allocCallArgs(tmp.arena, prefix + e.captures.len() * 2, 1);
            @memset(args.params, .int);
            @memset(args.returns, .int);

            args.arg_slots[0] = self.bl.addIntImm(.int, @intFromEnum(@field(Comptime.InteruptCode, @tagName(t))));
            args.arg_slots[1] = self.bl.addIntImm(.int, @bitCast(@intFromEnum(self.parent_scope.perm())));
            args.arg_slots[2] = self.bl.addIntImm(.int, @intFromEnum(expr));

            for (ast.exprs.view(e.captures), 0..) |id, slot_idx| {
                var val = try self.loadIdent(.init(id.pos()), id);
                if (val.ty == .type) {
                    self.ensureLoaded(&val);
                    args.arg_slots[prefix + slot_idx * 2 ..][0..2].* =
                        .{ self.emitTyConst(.type).id.Value, val.id.Value };
                } else {
                    args.arg_slots[prefix + slot_idx * 2 ..][0..2].* =
                        .{ self.emitTyConst(val.ty).id.Value, self.bl.addIntImm(.int, 0) };
                }
            }

            const rets = self.bl.addCall(Comptime.eca, args);
            return .mkv(.type, rets[0]);
        },
        .Fn => |e| {
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            const captures = tmp.arena.alloc(Types.Key.Capture, e.captures.len());

            for (ast.exprs.view(e.captures), captures) |id, *slot| {
                var val = try self.loadIdent(.init(id.pos()), id);
                if (val.ty == .type) {
                    slot.* = .{ .id = id, .ty = .type, .value = @intFromEnum(try self.unwrapTyConst(id, &val)) };
                } else {
                    slot.* = .{ .id = id, .ty = val.ty };
                }
            }

            const args = tmp.arena.alloc(Types.Id, e.args.len());
            var has_anytypes = false;
            if (e.comptime_args.len() == 0) {
                for (ast.exprs.view(e.args), args) |argid, *arg| {
                    const ty = argid.ty;
                    arg.* = try self.resolveAnonTy(ty);
                    has_anytypes = has_anytypes or arg.* == .any;
                }
            }

            if (e.comptime_args.len() != 0 or has_anytypes) {
                const slot, const alloc = self.types.intern(.Template, .{
                    .scope = self.parent_scope.perm(),
                    .file = self.parent_scope.file(),
                    .ast = expr,
                    .name = self.name,
                    .captures = captures,
                });
                if (!slot.found_existing) {
                    alloc.key.captures = self.types.arena.dupe(Types.Key.Capture, alloc.key.captures);
                }
                return self.emitTyConst(slot.key_ptr.*);
            } else {
                const slot, const alloc = self.types.intern(.Func, .{
                    .scope = self.parent_scope.perm(),
                    .file = self.parent_scope.file(),
                    .ast = expr,
                    .name = self.name,
                    .captures = captures,
                });
                const id = slot.key_ptr.*;
                errdefer _ = self.types.interner.remove(id);
                if (!slot.found_existing) {
                    if (!has_anytypes) for (ast.exprs.view(e.args), args) |argid, *arg| {
                        const ty = argid.ty;
                        arg.* = try self.resolveAnonTy(ty);
                    };
                    const ret = try self.resolveAnonTy(e.ret);
                    alloc.* = .{
                        .id = @intCast(self.types.funcs.items.len),
                        .key = alloc.key,
                        .args = self.types.arena.dupe(Types.Id, args),
                        .ret = ret,
                    };
                    alloc.key.captures = self.types.arena.dupe(Types.Key.Capture, alloc.key.captures);
                    self.types.funcs.append(self.types.arena.allocator(), alloc) catch unreachable;
                }
                return self.emitTyConst(id);
            }
        },
        .Use => |e| switch (e.pos.flag.use_kind) {
            .use => return self.emitTyConst(self.types.getScope(e.file)),
            .embed => {
                const file = self.types.getFile(e.file);
                const slot, const alloc = self.types.intern(.Global, .{
                    .scope = .void,
                    .file = e.file,
                    .ast = .zeroSized(.Void),
                    .name = file.path,
                    .captures = &.{},
                });
                if (!slot.found_existing) {
                    alloc.* = .{
                        .key = alloc.key,
                        .id = @intCast(self.types.globals.items.len),
                        .data = file.source,
                        .ty = self.types.makeSlice(file.source.len, .u8),
                    };
                    self.types.globals.append(self.types.arena.allocator(), alloc) catch unreachable;
                }
                self.queue(.{ .Global = alloc });
                return .mkp(alloc.ty, self.bl.addGlobalAddr(alloc.id));
            },
        },
        .Directive => |e| return self.emitDirective(ctx, expr, e),
        .Wildcard => return self.report(expr, "wildcard does not make sense here", .{}),
        else => {
            std.debug.panic("{any}\n", .{ast.exprs.get(expr)});
        },
    }
}

fn emitStirng(self: *Codegen, ctx: Ctx, data: []const u8, expr: Ast.Id) Value {
    const global = self.types.resolveGlobal(self.parent_scope.perm(), data, expr)[0].data().Global;
    global.data = data;
    global.ty = self.types.makeSlice(data.len, .u8);
    self.queue(.{ .Global = global });

    const slice_ty = self.types.makeSlice(null, .u8);
    const slice_loc = ctx.loc orelse self.bl.addLocal(slice_ty.size(self.types));
    self.bl.addFieldStore(slice_loc, Types.Slice.ptr_offset, .int, self.bl.addGlobalAddr(global.id));
    self.bl.addFieldStore(slice_loc, Types.Slice.len_offset, .int, self.bl.addIntImm(.int, @bitCast(data.len)));

    return .mkp(slice_ty, slice_loc);
}

fn emitDirective(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: Ast.Store.TagPayload(.Directive)) !Value {
    const ast = self.ast;

    const name = ast.tokenSrc(e.pos.index);
    const args = ast.exprs.view(e.args);

    const utils = enum {
        const mem = std.mem;

        pub fn matchTriple(pattern: []const u8, triple: []const u8) !bool {
            // CAUTION: written by LLM

            if (mem.eql(u8, pattern, "*")) {
                return error.@"you can replace this with 'true'";
            }

            if (mem.endsWith(u8, pattern, "-*")) {
                return error.@"trailing '*' is redundant";
            }

            var matcher = mem.splitScalar(u8, pattern, '-');
            var matchee = mem.splitScalar(u8, triple, '-');
            var eat_start = false;

            while (matcher.next()) |pat| {
                if (mem.eql(u8, pat, "*")) {
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
                        if (mem.eql(u8, v, pat)) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        return false;
                    }
                } else if (!mem.eql(u8, matchee.next() orelse return false, pat)) {
                    return false;
                }
            }

            return true;
        }

        test "sanity match triple" {
            try std.testing.expect(try matchTriple("a-b-c", "a-b-c"));
            try std.testing.expect(try matchTriple("*-b-c", "a-b-c"));
            try std.testing.expect(try matchTriple("*-c", "a-b-c"));
            try std.testing.expect(try matchTriple("a", "a-b-c"));
            try std.testing.expect(!try matchTriple("*-a", "a-b-c"));
            try std.testing.expectError(error.@"consecutive '*' are redundant", matchTriple("*-*-a", "a-b-c"));
            try std.testing.expectError(error.@"trailing '*' is redundant", matchTriple("*-b-*", "a-b-c"));
        }

        fn reportInferrence(cg: *Codegen, exr: anytype, ty: []const u8, dir_name: []const u8) EmitError {
            return cg.report(exr, "type can not be inferred from the context, use `@as(<{s}>, {s}(...))`", .{ ty, dir_name });
        }

        fn assertArgs(cg: *Codegen, exr: anytype, got: []const Ast.Id, comptime expected: []const u8) !void {
            const min_expected_args = comptime std.mem.count(u8, expected, ",") + @intFromBool(expected.len != 0);
            const varargs = comptime std.mem.endsWith(u8, expected, "..");
            if (got.len < min_expected_args or (!varargs and got.len > min_expected_args)) {
                const range = if (varargs) "at least " else "";
                return cg.report(
                    exr,
                    "directive takes {s}{} arguments, got {} (" ++ expected ++ ")",
                    .{ range, min_expected_args, got.len },
                );
            }
        }
    };

    switch (e.kind) {
        .use, .embed => unreachable,
        .CurrentScope => {
            try utils.assertArgs(self, expr, args, "");
            return self.emitTyConst(self.parent_scope.perm());
        },
        .TypeOf => {
            try utils.assertArgs(self, expr, args, "<ty>");
            const ty = try self.types.ct.inferType("", .{ .Tmp = self }, .{}, args[0]);
            return self.emitTyConst(ty);
        },
        .@"inline" => {
            try utils.assertArgs(self, expr, args, "<called>, <args>..");
            return self.emitCall(ctx, expr, .{
                .called = args[0],
                .arg_pos = ast.posOf(args[0]),
                .args = e.args.slice(1, e.args.len()),
            });
        },
        .int_cast => {
            try utils.assertArgs(self, expr, args, "<expr>");

            const ret: Types.Id = ctx.ty orelse {
                return utils.reportInferrence(self, expr, "int-ty", name);
            };

            if (!ret.isInteger()) {
                return self.report(expr, "inferred type must be an integer, {} is not", .{ret});
            }

            var oper = try self.emit(.{}, args[0]);

            if (!oper.ty.isInteger()) {
                return self.report(args[0], "expeced integer, {} is not", .{oper.ty});
            }

            self.ensureLoaded(&oper);

            return .mkv(ret, self.bl.addUnOp(.ired, self.abi.categorize(ret, self.types).ByValue, oper.id.Value));
        },
        .float_cast => {
            try utils.assertArgs(self, expr, args, "<float>");

            var oper = try self.emit(.{}, args[0]);
            self.ensureLoaded(&oper);

            const ret: Types.Id = switch (oper.ty) {
                .f32 => .f64,
                .f64 => .f32,
                else => return self.report(expr, "expected float argument, {} is not", .{oper.ty}),
            };

            return .mkv(ret, self.bl.addUnOp(.fcst, self.abi.categorize(ret, self.types).ByValue, oper.id.Value));
        },
        .int_to_float => {
            try utils.assertArgs(self, expr, args, "<float>");

            const ret: Types.Id = ctx.ty orelse {
                return utils.reportInferrence(self, expr, "float-ty", name);
            };

            if (!ret.isFloat()) return self.report(expr, "expected this to evaluate to float, {} is not", .{ret});

            var oper = try self.emitTyped(.{}, .int, args[0]);
            self.ensureLoaded(&oper);

            return .mkv(ret, self.bl.addUnOp(if (ret == .f32) .itf32 else .itf64, self.abi.categorize(ret, self.types).ByValue, oper.id.Value));
        },
        .float_to_int => {
            try utils.assertArgs(self, expr, args, "<float>");
            const ret: Types.Id = .int;

            var oper = try self.emit(.{}, args[0]);

            if (!oper.ty.isFloat()) return self.report(args[0], "expected float, {} is not", .{oper.ty});

            self.ensureLoaded(&oper);

            return .mkv(ret, self.bl.addUnOp(.fti, .int, oper.id.Value));
        },
        .bit_cast => {
            try utils.assertArgs(self, expr, args, "<expr>");

            const ret: Types.Id = ctx.ty orelse {
                return utils.reportInferrence(self, expr, "ty", name);
            };

            var oper = try self.emit(.{}, args[0]);

            if (oper.ty.size(self.types) != ret.size(self.types)) {
                return self.report(
                    args[0],
                    "cant bitcast from {} to {} because sizes are not equal ({} != {})",
                    .{ oper.ty, ret, oper.ty.size(self.types), ret.size(self.types) },
                );
            }

            const to_abi = self.abi.categorize(ret, self.types);

            if (to_abi != .ByValue) {
                const loc = self.bl.addLocal(ret.size(self.types));
                self.emitGenericStore(loc, &oper);
                return .mkp(ret, loc);
            } else {
                oper.ty = ret;
                self.ensureLoaded(&oper);
                return oper;
            }
        },
        .ChildOf => {
            try utils.assertArgs(self, expr, args, "<ty>");
            const ty = try self.resolveAnonTy(args[0]);
            const child = ty.child(self.types) orelse {
                return self.report(args[0], "directive only work on pointer types and slices, {} is not", .{ty});
            };
            return self.emitTyConst(child);
        },
        .kind_of => {
            try utils.assertArgs(self, expr, args, "<ty>");
            const len = try self.resolveAnonTy(args[0]);
            return .mkv(.uint, self.bl.addIntImm(.int, @intFromEnum(len.data())));
        },
        .len_of => {
            try utils.assertArgs(self, expr, args, "<ty>");
            const ty = try self.resolveAnonTy(args[0]);
            const len = ty.len(self.types) orelse {
                return self.report(args[0], "directive only works on structs and arrays, {} is not", .{ty});
            };
            return .mkv(.uint, self.bl.addIntImm(.int, @bitCast(len)));
        },
        .name_of => {
            try utils.assertArgs(self, expr, args, "<ty>");

            const ty = try self.resolveAnonTy(args[0]);
            const data = std.fmt.allocPrint(self.types.arena.allocator(), "{}", .{ty.fmt(self.types)}) catch unreachable;

            return self.emitStirng(ctx, data, expr);
        },
        .align_of => {
            try utils.assertArgs(self, expr, args, "<ty>");
            const ty = try self.resolveAnonTy(args[0]);
            return .mkv(.uint, self.bl.addIntImm(.int, @bitCast(ty.alignment(self.types))));
        },
        .size_of => {
            try utils.assertArgs(self, expr, args, "<ty>");
            const ty = try self.resolveAnonTy(args[0]);
            return .mkv(.uint, self.bl.addIntImm(.int, @bitCast(ty.size(self.types))));
        },
        .target => {
            try utils.assertArgs(self, expr, args, "<string>");
            const content = ast.exprs.getTyped(.String, args[0]) orelse return self.report(expr, "@target takes a \"string\"", .{});
            const str_content = ast.source[content.pos.index + 1 .. content.end - 1];
            const triple = @tagName(self.abi);
            const matched = utils.matchTriple(str_content, triple) catch |err| {
                return self.report(args[0], "{s}", .{@errorName(err)});
            };
            return .mkv(.bool, self.bl.addIntImm(.i8, @intFromBool(matched)));
        },
        .isComptime => return .mkv(.bool, self.bl.addIntImm(.i8, @intFromBool(self.target == .@"comptime"))),
        .ecall => {
            try utils.assertArgs(self, expr, args, "<expr>..");
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            const ret = ctx.ty orelse {
                return utils.reportInferrence(self, expr, "ty", name);
            };

            const arg_nodes = tmp.arena.alloc(Value, args.len);
            for (args, arg_nodes) |arg, *slot| {
                slot.* = try self.emit(.{}, arg);
            }

            const ret_abi = self.abi.categorize(ret, self.types);
            var param_count: usize = @intFromBool(ret_abi == .ByRef);
            for (arg_nodes) |nod| param_count += self.abi.categorize(nod.ty, self.types).len(false);
            const return_count: usize = ret_abi.len(true);

            const call_args = self.bl.allocCallArgs(tmp.arena, param_count, return_count);

            var i: usize = self.pushReturn(call_args, ret_abi, ret, ctx);

            for (arg_nodes) |*arg| {
                i += self.pushParam(call_args, self.abi.categorize(arg.ty, self.types), i, arg);
            }

            return self.assembleReturn(Comptime.eca, call_args, ctx, ret, ret_abi);
        },
        .as => {
            try utils.assertArgs(self, expr, args, "<ty>, <expr>");
            const ty = try self.resolveAnonTy(args[0]);
            return self.emitTyped(ctx, ty, args[1]);
        },
        .@"error" => {
            try utils.assertArgs(self, expr, args, "<ty/string>..");
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            var msg = std.ArrayList(u8).init(tmp.arena.allocator());
            for (args) |arg| switch (ast.exprs.get(arg)) {
                .String => |s| {
                    msg.appendSlice(ast.source[s.pos.index + 1 .. s.end - 1]) catch unreachable;
                },
                else => {
                    var value = try self.emit(.{}, arg);
                    if (value.ty == .type) {
                        msg.writer().print("{}", .{(try self.unwrapTyConst(arg, &value)).fmt(self.types)}) catch unreachable;
                    } else {
                        return self.report(arg, "only types and strings are supported here, {} is not", .{value.ty});
                    }
                },
            };

            return self.report(expr, "{s}", .{msg.items});
        },
        .Any => return self.emitTyConst(.any),
    }
}
