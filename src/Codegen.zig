bl: Builder,
types: *Types,
work_list: std.ArrayListUnmanaged(Task),
target: Types.Target,
comptime abi: Types.Abi = .ableos,
struct_ret_ptr: ?*Node = undefined,
scope: std.ArrayListUnmanaged(ScopeEntry) = undefined,
loops: std.ArrayListUnmanaged(Builder.Loop) = undefined,
ret: Types.Id = undefined,
errored: bool = undefined,

const std = @import("std");
const root = @import("utils.zig");
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
const panic = std.debug.panic;

const Task = union(enum) {
    Func: *Types.Func,
    Global: *Types.Global,
};

const ScopeEntry = struct {
    name: Ast.Ident,
    ty: Types.Id,
};

pub fn init(
    arena: *root.Arena,
    scratch: *root.Arena,
    types: *Types,
    target: Types.Target,
) Codegen {
    return .{
        .types = types,
        .target = target,
        .bl = .init(arena),
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
        const task = self.work_list.popOrNull() orelse return null;
        switch (task) {
            inline else => |func| {
                if (func.completion.get(self.target) == .compiled) continue;
                func.completion.set(self.target, .compiled);
            },
        }
        return task;
    }
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

    self.scope = .initBuffer(scratch.alloc(ScopeEntry, 1024));
    self.loops = .initBuffer(scratch.alloc(Builder.Loop, 32));

    return res;
}

pub fn build(self: *Codegen, func: *Types.Func) !void {
    var tmp = root.Arena.scrath(self.bl.func.arena);
    defer tmp.deinit();

    const param_count, const return_count, const ret_abi = func.computeAbiSize(self.abi, self.types);
    const token, const params, const returns = self.beginBuilder(tmp.arena, func.ret, param_count, return_count);

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

    var ty_idx: usize = 0;
    for (ast.exprs.view(ast.exprs.get(func.key.ast).Fn.args)) |aarg| {
        const ident = ast.exprs.get(aarg.bindings).Ident;
        if (ident.pos.indented) continue;
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
            .Imaginary => continue,
        };
        self.scope.appendAssumeCapacity(.{ .ty = ty, .name = ident.id });
        self.bl.pushScopeValue(arg);
        i += abi.len(false);
        ty_idx += 1;
    }

    _ = self.emit(.{ .scope = .init(.{ .Func = func }) }, ast.exprs.get(func.key.ast).Fn.body);

    self.bl.end(token);

    if (self.errored) return error.HasErrors;
}

pub const Value = struct {
    id: Mode = .Imaginary,
    ty: Types.Id = .void,

    pub const Mode = union(enum) {
        Imaginary,
        Value: *Node,
        Ptr: *Node,
    };

    pub const never = Value{ .ty = .never };

    inline fn mkv(ty: Types.Id, oid: ?*Node) Value {
        return .{ .ty = ty, .id = if (oid) |id| .{ .Value = id } else .Imaginary };
    }

    inline fn mkp(ty: Types.Id, id: *Node) Value {
        return .{ .ty = ty, .id = .{ .Ptr = id } };
    }
};

pub const Ctx = struct {
    scope: Types.Id,
    ty: ?Types.Id = null,
    loc: ?*Node = null,
    name: []const u8 = &.{},

    pub fn forwardScope(self: Ctx) Ctx {
        return .{ .scope = self.scope };
    }

    pub fn file(self: Ctx) Types.File {
        return self.scope.file();
    }

    pub fn addName(self: Ctx, name: []const u8) Ctx {
        var v = self;
        v.name = name;
        return v;
    }

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

    pub fn stripName(self: Ctx) Ctx {
        var v = self;
        v.name = &.{};
        return v;
    }
};

pub fn ensureLoaded(self: *Codegen, value: *Value) void {
    if (value.id == .Ptr) {
        value.id = .{ .Value = self.bl.addLoad(value.id.Ptr, self.abi.categorize(value.ty, self.types).ByValue) };
    }
}

pub fn typeCheck(self: *Codegen, ctx: Ctx, expr: Ast.Id, got: *Value, expected: Types.Id) bool {
    if (got.ty == .never) return true;

    if (!got.ty.canUpcast(expected, self.types)) {
        self.report(ctx, expr, "expected {} got {}", .{ expected, got.ty });
        got.* = .never;
        return true;
    }

    if (got.ty != expected) {
        if (got.ty.isSigned() and got.ty.size(self.types) < expected.size(self.types)) {
            got.id.Value = self.bl.addUnOp(.sext, self.abi.categorize(expected, self.types).ByValue, got.id.Value);
        }

        if (got.ty.isUnsigned() and got.ty.size(self.types) < expected.size(self.types)) {
            //self.report(expr, "{} {} {}", .{ got.ty, got.id.Value.data_type, expected });
            got.id.Value = self.bl.addUnOp(.uext, self.abi.categorize(expected, self.types).ByValue, got.id.Value);
        }

        got.ty = expected;
    }

    return false;
}

fn codePointer(self: *Codegen, ctx: Ctx, pos: usize) Ast.CodePointer {
    return self.types.getFile(ctx.file()).codePointer(pos);
}

fn report(self: *Codegen, ctx: Ctx, expr: Ast.Id, comptime fmt: []const u8, args: anytype) void {
    self.errored = true;
    const file = self.types.getFile(ctx.scope.file());
    const line, const col = Ast.lineCol(file.source, file.posOf(expr).index);

    self.types.diagnostics.print(
        "{s}:{}:{}: " ++ fmt ++ "\n{}\n",
        .{ file.path, line, col } ++ args ++ .{file.codePointer(file.posOf(expr).index)},
    ) catch unreachable;
}

fn emitStructOp(self: *Codegen, ty: *Types.Struct, op: Lexer.Lexeme, loc: *Node, lhs: *Node, rhs: *Node) void {
    var offset: usize = 0;
    for (ty.getFields(self.types)) |field| {
        offset = std.mem.alignForward(usize, offset, field.ty.alignment(self.types));
        const field_loc = self.bl.addFieldOffset(loc, @intCast(offset));
        const lhs_loc = self.bl.addFieldOffset(lhs, @intCast(offset));
        const rhs_loc = self.bl.addFieldOffset(rhs, @intCast(offset));
        if (field.ty.data() == .Struct) {
            self.emitStructOp(field.ty.data().Struct, op, field_loc, lhs_loc, rhs_loc);
        } else {
            const dt = self.abi.categorize(field.ty, self.types).ByValue;
            const lhs_val = self.bl.addLoad(lhs_loc, dt);
            const rhs_val = self.bl.addLoad(rhs_loc, dt);
            const res = self.bl.addBinOp(op.toBinOp(field.ty), dt, lhs_val, rhs_val);
            _ = self.bl.addStore(field_loc, res.data_type, res);
        }
        offset += field.ty.size(self.types);
    }
}

pub fn emitGenericStore(self: *Codegen, loc: *Node, value: *Value) void {
    if (value.ty == .never) return;

    if (self.abi.categorize(value.ty, self.types) == .ByValue) {
        self.ensureLoaded(value);
        _ = self.bl.addStore(loc, self.abi.categorize(value.ty, self.types).ByValue, value.id.Value);
    } else if (value.id.Ptr != loc) {
        _ = self.bl.addFixedMemCpy(loc, value.id.Ptr, value.ty.size(self.types));
    }
}

pub fn resolveTy(self: *Codegen, ctx: Ctx, expr: Ast.Id) Types.Id {
    return self.types.ct.evalTy(ctx, expr);
}

pub fn emitTyped(self: *Codegen, ctx: Ctx, ty: Types.Id, expr: Ast.Id) Value {
    var value = self.emit(ctx.addTy(ty), expr);
    if (self.typeCheck(ctx, expr, &value, ty)) return .never;
    return value;
}

pub fn emitTyConst(self: *Codegen, ty: Types.Id) Value {
    return .mkv(.type, self.bl.addIntImm(.int, @bitCast(@intFromEnum(ty))));
}

pub fn unwrapTyConst(self: *Codegen, cnst: *Node) Types.Id {
    return @enumFromInt(self.types.ct.partialEval(&self.bl, cnst));
}

pub fn lookupScopeItem(self: *Codegen, bsty: Types.Id, name: []const u8) Types.Id {
    const other_file = bsty.file();
    const other_ast = self.types.getFile(other_file);
    const decl = other_ast.findDecl(bsty.items(), name).?;
    return self.resolveTy(
        .{ .name = name, .scope = bsty },
        other_ast.exprs.get(decl).BinOp.rhs,
    );
}

pub fn loadIdent(self: *Codegen, ctx: Ctx, pos: Ast.Pos, id: Ast.Ident) Value {
    const ast = self.types.getFile(ctx.scope.file());
    for (self.scope.items, 0..) |se, i| {
        if (se.name == id) {
            const value = self.bl.getScopeValue(i);
            return .mkp(se.ty, value);
        }
    } else {
        var cursor = ctx;
        const decl = while (cursor.scope != .void) {
            if (ast.findDecl(cursor.scope.items(), id)) |v| break v;
            if (cursor.scope.findCapture(ast, id)) |c| return self.emitTyConst(c);
            cursor.scope = cursor.scope.parent();
        } else std.debug.panic("\n{}\n", .{ast.codePointer(pos.index)});

        const vari = ast.exprs.get(decl).BinOp;
        const ty: ?Types.Id, const value: Ast.Id = switch (vari.op) {
            .@":" => .{ self.resolveTy(cursor.stripName(), ast.exprs.get(vari.rhs).BinOp.lhs), ast.exprs.get(vari.rhs).BinOp.rhs },
            .@":=" => .{ null, vari.rhs },
            else => unreachable,
        };

        const typ = if (ty) |typ| b: {
            const global = self.types.resolveGlobal(cursor.scope, ast.tokenSrc(id.pos()), value);
            self.types.ct.evalGlobal(global.data().Global, typ, value);
            break :b global;
        } else return self.emitTyConst(self.resolveTy(cursor.addName(ast.tokenSrc(id.pos())), value));
        const global = typ.data().Global;
        self.queue(.{ .Global = global });
        return .mkp(global.ty, self.bl.addGlobalAddr(global.id));
    }
}

pub fn emit(self: *Codegen, ctx: Ctx, expr: Ast.Id) Value {
    const ast = self.types.getFile(ctx.scope.file());
    switch (ast.exprs.get(expr)) {
        .Comment => return .{},
        .Void => return .{},

        // #VALUES =====================================================================
        .Integer => |e| {
            const ty = ctx.ty orelse .uint;
            if (!ty.isInteger()) {
                self.report(ctx, expr, "{} can not be constructed as integer literal", .{ty});
                return .never;
            }
            const parsed = std.fmt.parseInt(i64, ast.tokenSrc(e.index), 10) catch unreachable;
            return .mkv(ty, self.bl.addIntImm(self.abi.categorize(ty, self.types).ByValue, parsed));
        },
        .Bool => |e| {
            return .mkv(.bool, self.bl.addIntImm(.i8, @intFromBool(e.value)));
        },
        .Ident => |e| return self.loadIdent(ctx, e.pos, e.id),
        .Ctor => |e| {
            if (e.ty.tag() == .Void and ctx.ty == null) {
                self.report(ctx, expr, "cant infer the type of this constructor, you can specify a type before the '.{{'", .{});
                return .never;
            }

            const ty = ctx.ty orelse self.resolveTy(ctx, e.ty);
            if (ty.data() != .Struct) {
                self.report(ctx, expr, "{} can not be constructed with '.{{..}}'", .{ty});
                return .never;
            }
            const struct_ty = ty.data().Struct;

            const local = ctx.loc orelse self.bl.addLocal(ty.size(self.types));

            // TODO: diagnostics

            for (ast.exprs.view(e.fields)) |f| {
                const field = ast.exprs.get(f).BinOp;
                const fname = ast.tokenSrc(ast.exprs.get(field.lhs).Tag.index + 1);
                var offset: usize = 0;
                const ftype = for (struct_ty.getFields(self.types)) |tf| {
                    offset = std.mem.alignForward(usize, offset, tf.ty.alignment(self.types));
                    if (std.mem.eql(u8, tf.name, fname)) break tf.ty;
                    offset += tf.ty.size(self.types);
                } else {
                    self.report(ctx, f, "{} does not have a field called {s} (TODO: list fields)", .{ ty, fname });
                    continue;
                };

                const off = self.bl.addFieldOffset(local, @intCast(offset));
                var value = self.emit(ctx.addTy(ftype).addLoc(off), field.rhs);
                if (self.typeCheck(ctx, field.rhs, &value, ftype)) continue;
                self.emitGenericStore(off, &value);
            }

            return .mkp(ty, local);
        },
        .Tupl => |e| {
            if (e.ty.tag() == .Void and ctx.ty == null) {
                self.report(ctx, expr, "cant infer the type of this constructor, you can specify a type before the '.{{'", .{});
                return .never;
            }

            const ty = ctx.ty orelse self.resolveTy(ctx, e.ty);
            if (ty.data() != .Struct) {
                self.report(ctx, expr, "{} can not be constructed with '.{{..}}'", .{ty});
                return .never;
            }
            const struct_ty = ty.data().Struct;

            const local = ctx.loc orelse self.bl.addLocal(ty.size(self.types));

            // TODO: diagnostics

            var offset: usize = 0;
            for (ast.exprs.view(e.fields), struct_ty.getFields(self.types)) |field, sf| {
                const ftype = sf.ty;
                offset = std.mem.alignForward(usize, offset, ftype.alignment(self.types));

                const off = self.bl.addFieldOffset(local, @intCast(offset));
                var value = self.emit(ctx.addTy(ftype).addLoc(off), field);
                if (self.typeCheck(ctx, field, &value, ftype)) continue;
                self.emitGenericStore(off, &value);
                offset += ftype.size(self.types);
            }

            return .mkp(ty, local);
        },
        .Field => |e| {
            var base = self.emit(ctx.forwardScope(), e.base);

            if (base.ty.data() == .Ptr) {
                self.ensureLoaded(&base);
                base.ty = base.ty.data().Ptr.*;
                base.id = .{ .Ptr = base.id.Value };
            }

            if (base.ty == .type) {
                return self.emitTyConst(self.lookupScopeItem(self.unwrapTyConst(base.id.Value), ast.tokenSrc(e.field.index)));
            }

            const struct_ty = base.ty.data().Struct;

            var offset: usize = 0;
            const ftype = for (struct_ty.getFields(self.types)) |tf| {
                offset = std.mem.alignForward(usize, offset, tf.ty.alignment(self.types));
                if (std.mem.eql(u8, ast.tokenSrc(e.field.index), tf.name)) break tf.ty;
                offset += tf.ty.size(self.types);
            } else unreachable;

            return .mkp(ftype, self.bl.addFieldOffset(base.id.Ptr, @intCast(offset)));
        },

        // #OPS ========================================================================
        .UnOp => |e| switch (e.op) {
            .@"^" => return self.emitTyConst(self.types.makePtr(self.resolveTy(ctx, e.oper))),
            .@"&" => {
                const addrd = self.emit(ctx.forwardScope(), e.oper);
                return .mkv(self.types.makePtr(addrd.ty), addrd.id.Ptr);
            },
            .@"*" => {
                // TODO: better type inference
                var oper = self.emit(ctx.forwardScope(), e.oper);
                self.ensureLoaded(&oper);
                const base = oper.ty.data().Ptr.*;
                return .mkp(base, oper.id.Value);
            },
            .@"-" => {
                var lhs = self.emit(ctx, e.oper);
                if (ctx.ty) |ty| if (self.typeCheck(ctx, expr, &lhs, ty)) return .never;
                return .mkv(lhs.ty, self.bl.addUnOp(.neg, self.abi.categorize(lhs.ty, self.types).ByValue, lhs.id.Value));
            },
            else => std.debug.panic("{any}\n", .{ast.exprs.get(expr)}),
        },
        .BinOp => |e| switch (e.op) {
            inline .@":=", .@":" => |t| {
                const loc = self.bl.addLocal(0);

                var value = if (t == .@":=")
                    self.emit(ctx.forwardScope().addLoc(loc), e.rhs)
                else b: {
                    const assign = ast.exprs.get(e.rhs).BinOp;
                    std.debug.assert(assign.op == .@"=");
                    const ty = self.resolveTy(ctx, assign.lhs);
                    break :b self.emitTyped(ctx.addLoc(loc), ty, assign.rhs);
                };

                self.bl.resizeLocal(loc, value.ty.size(self.types));
                self.emitGenericStore(loc, &value);

                self.scope.appendAssumeCapacity(.{ .ty = value.ty, .name = ast.exprs.get(e.lhs).Ident.id });
                self.bl.pushScopeValue(loc);
                return .{};
            },
            .@"=" => if (e.lhs.tag() == .Wildcard) {
                _ = self.emit(ctx.forwardScope(), e.rhs);
                return .{};
            } else {
                const loc = self.emit(ctx.forwardScope(), e.lhs);

                var val = self.emitTyped(ctx, loc.ty, e.rhs);
                self.emitGenericStore(loc.id.Ptr, &val);
                return .{};
            },
            else => {
                var lhs = self.emit(if (e.op.isComparison()) ctx.forwardScope() else ctx, e.lhs);
                var rhs = self.emit(ctx.addTy(lhs.ty), e.rhs);
                if (e.op.isComparison() and lhs.ty.isSigned() != rhs.ty.isSigned())
                    self.report(ctx, e.lhs, "mixed sign comparison ({} {})", .{ lhs.ty, rhs.ty });
                const unified: Types.Id = ctx.ty orelse lhs.ty.binOpUpcast(rhs.ty, self.types) catch |err| {
                    self.report(ctx, expr, "{s} ({} and {})", .{ @errorName(err), lhs.ty, rhs.ty });
                    return .never;
                };

                if (lhs.ty.data() == .Struct) if (e.op.isComparison()) {
                    self.report(ctx, e.lhs, "\n", .{});
                    unreachable;
                } else {
                    const loc = ctx.loc orelse self.bl.addLocal(unified.size(self.types));
                    self.emitStructOp(unified.data().Struct, e.op, loc, lhs.id.Ptr, rhs.id.Ptr);
                    return .mkp(unified, loc);
                } else {
                    const upcast_to: Types.Id = if (e.op.isComparison()) if (lhs.ty.isSigned()) .int else .uint else unified;
                    self.ensureLoaded(&lhs);
                    self.ensureLoaded(&rhs);
                    const lhs_fail = self.typeCheck(ctx, e.lhs, &lhs, upcast_to);
                    const rhs_fail = self.typeCheck(ctx, e.rhs, &rhs, upcast_to);
                    if (lhs_fail or rhs_fail) return .{};
                    return .mkv(unified, self.bl.addBinOp(
                        e.op.toBinOp(lhs.ty),
                        self.abi.categorize(unified, self.types).ByValue,
                        lhs.id.Value,
                        rhs.id.Value,
                    ));
                }
            },
        },

        // #CONTROL ====================================================================
        .Block => |e| {
            const prev_scope_height = self.scope.items.len;
            defer self.scope.items.len = prev_scope_height;
            defer self.bl.truncateScope(prev_scope_height);

            for (ast.exprs.view(e.stmts)) |s| {
                if (self.bl.isUnreachable()) break;
                _ = self.emitTyped(ctx, .void, s);
            }

            return .{};
        },
        .If => |e| {
            var cond = self.emitTyped(ctx, .bool, e.cond);
            self.ensureLoaded(&cond);
            var if_builder = self.bl.addIfAndBeginThen(cond.id.Value);
            _ = self.emitTyped(ctx, .void, e.then);
            const end_else = if_builder.beginElse(&self.bl);
            _ = self.emitTyped(ctx, .void, e.else_);
            if_builder.end(&self.bl, end_else);

            return .{};
        },
        .Loop => |e| {
            var loop = self.bl.addLoopAndBeginBody();
            self.loops.appendAssumeCapacity(loop);
            _ = self.emitTyped(ctx, .void, e.body);
            loop = self.loops.pop();
            loop.end(&self.bl);

            return .{};
        },
        .Break => |_| {
            self.loops.items[self.loops.items.len - 1].addLoopControl(&self.bl, .@"break");
            return .{};
        },
        .Continue => |_| {
            self.loops.items[self.loops.items.len - 1].addLoopControl(&self.bl, .@"continue");
            return .{};
        },
        .Call => |e| {
            var tmp = root.Arena.scrath(self.bl.func.arena);
            defer tmp.deinit();

            var typ: Types.Id, var caller: ?Value = if (e.called.tag() == .Field) b: {
                const field = ast.exprs.get(e.called).Field;
                const value = self.emit(ctx.forwardScope(), field.base);
                if (value.ty == .type) {
                    break :b .{ self.lookupScopeItem(self.unwrapTyConst(value.id.Value), ast.tokenSrc(field.field.index)), null };
                }
                break :b .{ self.lookupScopeItem(value.ty, ast.tokenSrc(field.field.index)), value };
            } else b: {
                break :b .{ self.resolveTy(ctx, e.called), null };
            };

            var computed_args: ?[]Value = null;
            if (typ.data() == .Template) {
                const tmpl = typ.data().Template;

                var scope = tmpl.*;
                const tmpl_file = self.types.getFile(tmpl.key.file);
                const tmpl_ast = tmpl_file.exprs.getTyped(.Fn, tmpl.key.ast).?;

                const captures = tmp.arena.alloc(Types.Id, tmpl_ast.captures.len());
                const arg_tys = tmp.arena.alloc(Types.Id, tmpl_ast.args.len() - tmpl_ast.captures.len());
                const arg_exprs = tmp.arena.alloc(Value, arg_tys.len);

                var capture_idx: usize = 0;
                var arg_idx: usize = 0;
                for (tmpl_file.exprs.view(tmpl_ast.args), ast.exprs.view(e.args)) |param, arg| {
                    if (tmpl_file.exprs.get(param.bindings).Ident.pos.indented) {
                        captures[capture_idx] = self.resolveTy(ctx, arg);

                        std.debug.assert(scope.key.capture_idents.len() == scope.key.captures.len);
                        capture_idx += 1;
                        scope.key.capture_idents = tmpl_ast.captures.slice(0, capture_idx);
                        scope.key.captures = captures[0..capture_idx];
                    } else {
                        // this is in anticipation of the @Any
                        arg_tys[arg_idx] = self.resolveTy(.{ .scope = .init(.{ .Template = &scope }) }, param.ty);
                        arg_exprs[arg_idx] = self.emitTyped(ctx, arg_tys[arg_idx], arg);
                        arg_idx += 1;
                    }
                }

                std.debug.assert(scope.key.capture_idents.len() == scope.key.captures.len);
                const ret = self.resolveTy(.{ .scope = .init(.{ .Template = &scope }) }, tmpl_ast.ret);

                const slot, const alloc = self.types.intern(.Func, .{
                    .scope = tmpl.key.scope,
                    .file = tmpl.key.file,
                    .ast = tmpl.key.ast,
                    .capture_idents = tmpl_ast.captures,
                    .captures = captures,
                });

                if (!slot.found_existing) {
                    alloc.* = .{
                        .id = @intCast(self.types.funcs.items.len),
                        .key = alloc.key,
                        .args = self.types.arena.dupe(Types.Id, arg_tys),
                        .ret = ret,
                        .name = "",
                    };
                    self.types.funcs.append(self.types.arena.allocator(), alloc) catch unreachable;
                    alloc.key.captures = self.types.arena.dupe(Types.Id, alloc.key.captures);
                }

                typ = slot.key_ptr.*;
                computed_args = arg_exprs;
            }

            const func = typ.data().Func;
            self.queue(.{ .Func = func });

            const param_count, const return_count, const ret_abi = func.computeAbiSize(self.abi, self.types);
            const args = self.bl.allocCallArgs(tmp.arena, param_count, return_count);

            var i: usize = 0;
            if (ret_abi == .ByRef) {
                ret_abi.types(args.params[0..1]);
                args.arg_slots[i] = ctx.loc orelse self.bl.addLocal(func.ret.size(self.types));
                i += 1;
            } else {
                ret_abi.types(args.returns[0..return_count]);
            }

            if (caller) |*value| {
                const abi = self.abi.categorize(value.ty, self.types);
                abi.types(args.params[i..]);
                switch (abi) {
                    .Imaginary => {},
                    .ByValue => {
                        self.ensureLoaded(value);
                        args.arg_slots[i] = value.id.Value;
                    },
                    .ByValuePair => |pair| {
                        for (pair.types, pair.offsets(), 0..) |t, off, j| {
                            args.arg_slots[i + j] =
                                self.bl.addFieldLoad(value.id.Ptr, @intCast(off), t);
                        }
                    },
                    .ByRef => args.arg_slots[i] = value.id.Ptr,
                }
                i += abi.len(false);
            }

            const args_ast = ast.exprs.view(e.args);
            for (func.args[@intFromBool(caller != null)..], 0..) |ty, k| {
                const abi = self.abi.categorize(ty, self.types);
                abi.types(args.params[i..]);
                var value = if (computed_args) |a| a[k] else self.emitTyped(ctx, ty, args_ast[k]);
                switch (abi) {
                    .Imaginary => {},
                    .ByValue => {
                        self.ensureLoaded(&value);
                        args.arg_slots[i] = value.id.Value;
                    },
                    .ByValuePair => |pair| {
                        for (pair.types, pair.offsets(), 0..) |t, off, j| {
                            args.arg_slots[i + j] =
                                self.bl.addFieldLoad(value.id.Ptr, @intCast(off), t);
                        }
                    },
                    .ByRef => args.arg_slots[i] = value.id.Ptr,
                }
                i += abi.len(false);
            }

            const rets = self.bl.addCall(func.id, args);

            return switch (ret_abi) {
                .Imaginary => .{},
                .ByValue => .mkv(func.ret, rets[0]),
                .ByValuePair => |pair| b: {
                    const slot = ctx.loc orelse self.bl.addLocal(func.ret.size(self.types));
                    for (pair.types, pair.offsets(), rets) |ty, off, vl| {
                        self.bl.addFieldStore(slot, @intCast(off), ty, vl);
                    }
                    break :b .mkp(func.ret, slot);
                },
                .ByRef => .mkp(func.ret, args.arg_slots[0]),
            };
        },
        .Return => |e| {
            var value = self.emitTyped(ctx.addLoc(self.struct_ret_ptr), self.ret, e.value);
            if (self.typeCheck(ctx, e.value, &value, self.ret)) return .never;
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
            return .{};
        },
        .Buty => |e| return self.emitTyConst(.fromLexeme(e.bt)),
        .Struct => |e| {
            var tmp = root.Arena.scrath(self.bl.func.arena);
            defer tmp.deinit();

            const prefix = 3;
            const args = self.bl.allocCallArgs(tmp.arena, prefix + e.captures.len(), 1);
            @memset(args.params, .int);
            @memset(args.returns, .int);

            args.arg_slots[0] = self.bl.addIntImm(.int, @intFromEnum(Comptime.InteruptCode.Struct));
            args.arg_slots[1] = self.bl.addIntImm(.int, @bitCast(@intFromEnum(ctx.scope)));
            args.arg_slots[2] = self.bl.addIntImm(.int, @as(u32, @bitCast(expr)));

            for (ast.exprs.view(e.captures), args.arg_slots[prefix..]) |id, *slot| {
                var val = self.loadIdent(ctx.forwardScope(), .init(id.pos()), id);
                self.ensureLoaded(&val);
                slot.* = val.id.Value;
            }

            const rets = self.bl.addCall(Comptime.eca, args);
            return .mkv(.type, rets[0]);
        },
        .Fn => |e| if (e.captures.len() != 0) {
            const slot, _ = self.types.intern(.Template, .{
                .scope = ctx.scope,
                .file = ctx.file(),
                .ast = expr,
                .capture_idents = .{},
                .captures = &.{},
            });
            return self.emitTyConst(slot.key_ptr.*);
        } else {
            const slot, const alloc = self.types.intern(.Func, .{
                .scope = ctx.scope,
                .file = ctx.file(),
                .ast = expr,
                .capture_idents = .{},
                .captures = &.{},
            });
            const id = slot.key_ptr.*;
            if (!slot.found_existing) {
                const args = self.types.arena.alloc(Types.Id, e.args.len());
                for (ast.exprs.view(e.args), args) |argid, *arg| {
                    const ty = argid.ty;
                    arg.* = self.resolveTy(ctx.stripName(), ty);
                }
                const ret = self.resolveTy(ctx.stripName(), e.ret);
                alloc.* = .{
                    .id = @intCast(self.types.funcs.items.len),
                    .key = alloc.key,
                    .args = args,
                    .ret = ret,
                    .name = ctx.name,
                };
                self.types.funcs.append(self.types.arena.allocator(), alloc) catch unreachable;
            }
            return self.emitTyConst(id);
        },
        .Use => |e| {
            return self.emitTyConst(self.types.getScope(e.file));
        },
        .Directive => |e| {
            if (std.mem.eql(u8, ast.tokenSrc(e.pos.index), "@CurrentScope")) {
                return self.emitTyConst(ctx.scope);
            } else unreachable;
        },
        else => std.debug.panic("{any}\n", .{ast.exprs.get(expr)}),
    }
}
