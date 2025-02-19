bl: Builder,
types: *Types,
diagnostics: std.io.AnyWriter,
work_list: std.ArrayList(Task),
target: Types.Target,
comptime abi: Types.Abi = .ableos,
struct_ret_ptr: ?*Node = undefined,
scope: std.ArrayList(ScopeEntry) = undefined,
loops: std.ArrayList(*Builder.Loop) = undefined,
file: Types.File = undefined,
ast: Ast = undefined,
fdata: *const Types.FuncData = undefined,
errored: bool = undefined,

const std = @import("std");
const Ast = @import("parser.zig");
const Vm = @import("Vm.zig");
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
    Func: Types.Func,
    Global: Types.Global,
};

const ScopeEntry = struct {
    name: Ast.Ident,
    ty: Types.Id,
};

pub fn init(
    gpa: std.mem.Allocator,
    types: *Types,
    target: Types.Target,
    diagnostics: std.io.AnyWriter,
) Codegen {
    return .{
        .diagnostics = diagnostics,
        .types = types,
        .target = target,
        .bl = .init(gpa),
        .work_list = .init(gpa),
    };
}

pub fn deinit(self: *Codegen) void {
    self.bl.deinit();
    self.work_list.deinit();
    self.* = undefined;
}

pub fn queue(self: *Codegen, task: Task) void {
    switch (task) {
        inline else => |func| {
            const fdata = self.types.get(func);
            if (fdata.completion.get(self.target) == .compiled) return;
            self.work_list.append(task) catch unreachable;
        },
    }
}

pub fn nextTask(self: *Codegen) ?Task {
    while (true) {
        const task = self.work_list.popOrNull() orelse return null;
        switch (task) {
            inline else => |func| {
                const fdata = self.types.get(func);
                if (fdata.completion.get(self.target) == .compiled) continue;
                fdata.completion.set(self.target, .compiled);
            },
        }
        return task;
    }
}

pub inline fn arena(self: *Codegen) std.mem.Allocator {
    return self.bl.func.getTmpArena();
}

pub fn beginBuilder(
    self: *Codegen,
    file: Types.File,
    func: *const Types.FuncData,
    param_count: usize,
    return_count: usize,
) struct { Builder.BuildToken, []DataType, []DataType } {
    self.errored = false;
    self.file = file;
    self.ast = self.types.getFile(file).*;
    self.fdata = func;
    const res = self.bl.begin(param_count, return_count);

    self.scope = .init(self.arena());
    self.loops = .init(self.arena());

    return res;
}

pub fn build(self: *Codegen, file: Types.File, func: Types.Func) !void {
    const fdata: Types.FuncData = self.types.get(func).*;
    const param_count, const return_count, const ret_abi = fdata.computeAbiSize(self.abi);
    const token, const params, const returns = self.beginBuilder(file, &fdata, param_count, return_count);

    var i: usize = 0;

    if (ret_abi == .ByRef) {
        ret_abi.types(params[0..1]);
        self.struct_ret_ptr = self.bl.addParam(i);
        i += 1;
    } else {
        ret_abi.types(returns);
        self.struct_ret_ptr = null;
    }

    for (self.fdata.args, self.getAstSlice(self.getAst(self.fdata.ast).Fn.args)) |ty, aarg| {
        const abi = self.abi.categorize(ty);
        abi.types(params[i..]);

        const arg = switch (abi) {
            .ByRef => self.bl.addParam(i),
            .ByValue => self.bl.addSpill(self.bl.addParam(i)),
            .ByValuePair => |p| b: {
                const slot = self.bl.addLocal(ty.size());
                for (p.offsets(), 0..) |off, j| {
                    const arg = self.bl.addParam(i + j);
                    self.bl.addFieldStore(slot, @intCast(off), arg.data_type, arg);
                }
                break :b slot;
            },
            .Imaginary => continue,
        };
        self.scope.append(.{ .ty = ty, .name = self.getAst(self.getAst(aarg).Arg.bindings).Ident.id }) catch unreachable;
        self.bl.pushScopeValue(arg);
        i += abi.len(false);
    }

    _ = self.emit(.{}, self.getAst(self.fdata.ast).Fn.body);

    self.bl.end(token);

    if (self.errored) return error.HasErrors;
}

inline fn getAst(self: *Codegen, expr: Ast.Id) Ast.Expr {
    return self.ast.exprs.get(expr);
}

inline fn getAstSlice(self: *Codegen, slice: Ast.Slice) []Ast.Id {
    return self.ast.exprs.view(slice);
}

inline fn tokenSrc(self: *Codegen, idx: u32) []const u8 {
    return self.ast.tokenSrc(idx);
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
};

inline fn mkv(ty: Types.Id, oid: ?*Node) Value {
    return .{ .ty = ty, .id = if (oid) |id| .{ .Value = id } else .Imaginary };
}

inline fn mkp(ty: Types.Id, id: *Node) Value {
    return .{ .ty = ty, .id = .{ .Ptr = id } };
}

inline fn mki(ty: Types.Id) Value {
    return .{ .ty = ty };
}

pub const Ctx = struct {
    ty: ?Types.Id = null,
    loc: ?*Node = null,
};

pub fn emitTyped(self: *Codegen, ty: Types.Id, expr: Ast.Id) Value {
    var value = self.emit(.{ .ty = ty }, expr);
    if (self.typeCheck(expr, &value, ty)) return .never;
    return value;
}

pub fn ensureLoaded(self: *Codegen, value: *Value) void {
    if (value.id == .Ptr) {
        value.id = .{ .Value = self.bl.addLoad(value.id.Ptr, self.abi.categorize(value.ty).ByValue) };
    }
}

pub fn typeCheck(self: *Codegen, expr: Ast.Id, got: *Value, expected: Types.Id) bool {
    if (got.ty == .never) return true;

    if (!got.ty.canUpcast(expected)) {
        self.report(expr, "expected {} got {}", .{ expected, got.ty });
        got.* = .never;
        return true;
    }

    if (got.ty != expected) {
        if (got.ty.isSigned() and got.ty.size() < expected.size()) {
            got.id.Value = self.bl.addUnOp(.sext, self.abi.categorize(expected).ByValue, got.id.Value);
        }

        if (got.ty.isUnsigned() and got.ty.size() < expected.size()) {
            //self.report(expr, "{} {} {}", .{ got.ty, got.id.Value.data_type, expected });
            got.id.Value = self.bl.addUnOp(.uext, self.abi.categorize(expected).ByValue, got.id.Value);
        }

        got.ty = expected;
    }

    return false;
}

fn codePointer(self: *Codegen, ast: Ast.Id) Ast.CodePointer {
    return self.types.getFile(self.file).codePointer(self.types.getFile(self.file).posOf(ast).index);
}

fn report(self: *Codegen, expr: Ast.Id, comptime fmt: []const u8, args: anytype) void {
    self.errored = true;
    const file = self.types.getFile(self.file);
    const line, const col = file.lineCol(file.posOf(expr).index);

    self.diagnostics.print(
        "{s}:{}:{}: " ++ fmt ++ "\n{}\n",
        .{ file.path, line, col } ++ args ++ .{file.codePointer(file.posOf(expr).index)},
    ) catch unreachable;
}

fn emitStructOp(self: *Codegen, ty: *const Types.Struct, op: Lexer.Lexeme, loc: *Node, lhs: *Node, rhs: *Node) void {
    var offset: usize = 0;
    for (ty.fields) |field| {
        offset = std.mem.alignForward(usize, offset, field.ty.alignment());
        const field_loc = self.bl.addFieldOffset(loc, @intCast(offset));
        const lhs_loc = self.bl.addFieldOffset(lhs, @intCast(offset));
        const rhs_loc = self.bl.addFieldOffset(rhs, @intCast(offset));
        if (field.ty.data() == .Struct) {
            self.emitStructOp(field.ty.data().Struct, op, field_loc, lhs_loc, rhs_loc);
        } else {
            const dt = self.abi.categorize(field.ty).ByValue;
            const lhs_val = self.bl.addLoad(lhs_loc, dt);
            const rhs_val = self.bl.addLoad(rhs_loc, dt);
            const res = self.bl.addBinOp(op.toBinOp(field.ty), dt, lhs_val, rhs_val);
            _ = self.bl.addStore(field_loc, res.data_type, res);
        }
        offset += field.ty.size();
    }
}

pub fn emitGenericStore(self: *Codegen, loc: *Node, value: *Value) void {
    if (value.ty == .never) return;

    if (self.abi.categorize(value.ty) == .ByValue) {
        self.ensureLoaded(value);
        _ = self.bl.addStore(loc, self.abi.categorize(value.ty).ByValue, value.id.Value);
    } else if (value.id.Ptr != loc) {
        _ = self.bl.addFixedMemCpy(loc, value.id.Ptr, value.ty.size());
    }
}

pub fn emit(self: *Codegen, ctx: Ctx, expr: Ast.Id) Value {
    const file = self.types.getFile(self.file);
    switch (self.getAst(expr)) {
        .Comment => return .{},
        .Void => return .{},

        // #VALUES =====================================================================
        .Integer => |e| {
            const ty = ctx.ty orelse .uint;
            if (!ty.isInteger()) {
                self.report(expr, "{} can not be constructed as integer literal", .{ty});
                return .never;
            }
            const parsed = std.fmt.parseInt(i64, self.tokenSrc(e.index), 10) catch unreachable;
            return mkv(ty, self.bl.addIntImm(self.abi.categorize(ty).ByValue, parsed));
        },
        .Bool => |e| {
            return mkv(.bool, self.bl.addIntImm(.i8, @intFromBool(e.value)));
        },
        .Ident => |e| for (self.scope.items, 0..) |se, i| {
            if (se.name == e.id) {
                const value = self.bl.getScopeValue(i);
                return mkp(se.ty, value);
            }
        } else {
            const decl = self.types.getFile(self.file).findDecl(e.id).?;
            const vari = self.getAst(decl).BinOp;
            const ty: ?Types.Id, const value: Ast.Id = switch (vari.op) {
                .@":" => .{ self.types.resolveTy(.init(self.file), self.getAst(vari.rhs).BinOp.lhs), self.getAst(vari.rhs).BinOp.rhs },
                .@":=" => .{ null, vari.rhs },
                else => unreachable,
            };

            const global = self.types.addGlobal(self.file, self.getAst(vari.lhs).Ident.pos, decl);
            const gdata: *Types.GlobalData = self.types.get(global);

            if (gdata.completion.get(self.target) == .queued) {
                gdata.completion.set(self.target, .staged);

                @import("Comptime.zig").evalGlobal(self, global, ty, value);

                self.queue(.{ .Global = global });
            }

            return mkp(self.types.get(global).ty, self.bl.addGlobalAddr(@intFromEnum(global)));
        },
        .Ctor => |e| {
            if (e.ty.tag() == .Void and ctx.ty == null) {
                self.report(expr, "cant infer the type of this constructor, you can specify a type before the '.{{'", .{});
                return .never;
            }

            const ty = ctx.ty orelse self.types.resolveTy(.init(self.file), e.ty);
            if (ty.data() != .Struct) {
                self.report(expr, "{} can not be constructed with '.{{..}}'", .{ty});
                return .never;
            }
            const struct_ty = ty.data().Struct;

            const struct_file = self.types.getFile(struct_ty.file);
            const local = ctx.loc orelse self.bl.addLocal(ty.size());

            // TODO: diagnostics

            for (self.getAstSlice(e.fields)) |f| {
                const field = self.getAst(f).CtorField;
                var offset: usize = 0;
                const ftype = for (struct_ty.fields) |tf| {
                    offset = std.mem.alignForward(usize, offset, tf.ty.alignment());
                    if (std.mem.eql(u8, file.tokenSrc(field.pos.index), struct_file.tokenSrc(tf.name.index))) break tf.ty;
                    offset += tf.ty.size();
                } else {
                    self.report(f, "{} does not have a field called {s} (TODO: list fields)", .{ ty, file.tokenSrc(field.pos.index) });
                    continue;
                };

                const off = self.bl.addFieldOffset(local, @intCast(offset));
                var value = self.emit(.{ .ty = ftype, .loc = off }, field.value);
                if (self.typeCheck(field.value, &value, ftype)) continue;
                self.emitGenericStore(off, &value);
            }

            return mkp(ty, local);
        },
        .Tupl => |e| {
            if (e.ty.tag() == .Void and ctx.ty == null) {
                self.report(expr, "cant infer the type of this constructor, you can specify a type before the '.{{'", .{});
                return .never;
            }

            const ty = ctx.ty orelse self.types.resolveTy(.init(self.file), e.ty);
            if (ty.data() != .Struct) {
                self.report(expr, "{} can not be constructed with '.{{..}}'", .{ty});
                return .never;
            }
            const struct_ty = ty.data().Struct;

            const local = ctx.loc orelse self.bl.addLocal(ty.size());

            // TODO: diagnostics

            var offset: usize = 0;
            for (self.getAstSlice(e.fields), struct_ty.fields) |field, sf| {
                const ftype = sf.ty;
                offset = std.mem.alignForward(usize, offset, ftype.alignment());

                const off = self.bl.addFieldOffset(local, @intCast(offset));
                var value = self.emit(.{ .ty = ftype, .loc = off }, field);
                if (self.typeCheck(field, &value, ftype)) continue;
                self.emitGenericStore(off, &value);
                offset += ftype.size();
            }

            return mkp(ty, local);
        },
        .Field => |e| {
            var base = self.emit(.{}, e.base);

            if (base.ty.data() == .Ptr) {
                self.ensureLoaded(&base);
                base.ty = base.ty.data().Ptr;
                base.id = .{ .Ptr = base.id.Value };
            }
            const struct_ty = base.ty.data().Struct;
            const struct_file = self.types.getFile(struct_ty.file);

            var offset: usize = 0;
            const ftype = for (struct_ty.fields) |tf| {
                offset = std.mem.alignForward(usize, offset, tf.ty.alignment());
                if (std.mem.eql(u8, file.tokenSrc(e.field.index), struct_file.tokenSrc(tf.name.index))) break tf.ty;
                offset += tf.ty.size();
            } else {
                unreachable;
            };

            return mkp(ftype, self.bl.addFieldOffset(base.id.Ptr, @intCast(offset)));
        },

        // #OPS ========================================================================
        .UnOp => |e| switch (e.op) {
            .@"&" => {
                const addrd = self.emit(.{}, e.oper);
                return mkv(self.types.makePtr(addrd.ty), addrd.id.Ptr);
            },
            .@"*" => {
                // TODO: better type inference
                var oper = self.emit(.{}, e.oper);
                self.ensureLoaded(&oper);
                const base = oper.ty.data().Ptr;
                return mkp(base, oper.id.Value);
            },
            .@"-" => {
                var lhs = self.emit(ctx, e.oper);
                if (ctx.ty) |ty| if (self.typeCheck(expr, &lhs, ty)) return .never;
                return mkv(lhs.ty, self.bl.addUnOp(.neg, self.abi.categorize(lhs.ty).ByValue, lhs.id.Value));
            },
            else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
        },
        .BinOp => |e| switch (e.op) {
            inline .@":=", .@":" => |t| {
                const loc = self.bl.addLocal(0);

                var value = if (t == .@":=")
                    self.emit(.{ .loc = loc }, e.rhs)
                else b: {
                    const assign = self.getAst(e.rhs).BinOp;
                    std.debug.assert(assign.op == .@"=");
                    const ty = self.types.resolveTy(.init(self.file), assign.lhs);
                    var vl = self.emit(.{ .loc = loc, .ty = ty }, assign.rhs);
                    if (self.typeCheck(assign.rhs, &vl, ty)) break :b Value.never;
                    break :b vl;
                };

                self.bl.resizeLocal(loc, value.ty.size());
                self.emitGenericStore(loc, &value);

                self.scope.append(.{ .ty = value.ty, .name = self.getAst(e.lhs).Ident.id }) catch unreachable;
                self.bl.pushScopeValue(loc);
                return .{};
            },
            .@"=" => if (e.lhs.tag() == .Wildcard) {
                _ = self.emit(.{}, e.rhs);
                return .{};
            } else {
                const loc = self.emit(.{}, e.lhs);
                var val = self.emitTyped(loc.ty, e.rhs);
                self.emitGenericStore(loc.id.Ptr, &val);
                return .{};
            },
            else => {
                var lhs = self.emit(if (e.op.isComparison()) .{} else ctx, e.lhs);
                var rhs = self.emit(.{ .ty = lhs.ty }, e.rhs);
                if (e.op.isComparison() and lhs.ty.isSigned() != rhs.ty.isSigned())
                    self.report(e.lhs, "mixed sign comparison ({} {})", .{ lhs.ty, rhs.ty });
                const unified: Types.Id = ctx.ty orelse lhs.ty.binOpUpcast(rhs.ty) catch |err| {
                    self.report(expr, "{s} ({} and {})", .{ @errorName(err), lhs.ty, rhs.ty });
                    return .never;
                };

                if (lhs.ty.data() == .Struct) if (e.op.isComparison()) {
                    self.report(e.lhs, "\n", .{});
                    unreachable;
                } else {
                    const loc = ctx.loc orelse self.bl.addLocal(unified.size());
                    self.emitStructOp(unified.data().Struct, e.op, loc, lhs.id.Ptr, rhs.id.Ptr);
                    return mkp(unified, loc);
                } else {
                    const upcast_to: Types.Id = if (e.op.isComparison()) if (lhs.ty.isSigned()) .int else .uint else unified;
                    self.ensureLoaded(&lhs);
                    self.ensureLoaded(&rhs);
                    const lhs_fail = self.typeCheck(e.lhs, &lhs, upcast_to);
                    const rhs_fail = self.typeCheck(e.rhs, &rhs, upcast_to);
                    if (lhs_fail or rhs_fail) return .{};
                    return mkv(unified, self.bl.addBinOp(
                        e.op.toBinOp(lhs.ty),
                        self.abi.categorize(unified).ByValue,
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

            for (self.getAstSlice(e.stmts)) |s| {
                if (self.bl.isUnreachable()) break;
                _ = self.emitTyped(.void, s);
            }

            return .{};
        },
        .If => |e| {
            var cond = self.emitTyped(.bool, e.cond);
            self.ensureLoaded(&cond);
            var if_builder = self.bl.addIfAndBeginThen(cond.id.Value);
            _ = self.emitTyped(.void, e.then);
            const end_else = if_builder.beginElse(&self.bl);
            _ = self.emitTyped(.void, e.else_);
            if_builder.end(&self.bl, end_else);

            return .{};
        },
        .Loop => |e| {
            var loop = self.bl.addLoopAndBeginBody();
            self.loops.append(&loop) catch unreachable;
            _ = self.emitTyped(.void, e.body);
            _ = self.loops.pop();
            loop.end(&self.bl);

            return .{};
        },
        .Break => |_| {
            self.loops.getLast().addLoopControl(&self.bl, .@"break");
            return .{};
        },
        .Continue => |_| {
            self.loops.getLast().addLoopControl(&self.bl, .@"continue");
            return .{};
        },
        .Call => |e| {
            const func = self.types.resolveFunc(self.file, e.called);
            self.queue(.{ .Func = func });
            const fdata: *Types.FuncData = self.types.get(func);

            const param_count, const return_count, const ret_abi = fdata.computeAbiSize(self.abi);
            const args = self.bl.allocCallArgs(param_count, return_count);

            var i: usize = 0;
            if (ret_abi == .ByRef) {
                ret_abi.types(args.params[0..1]);
                args.arg_slots[i] = ctx.loc orelse self.bl.addLocal(fdata.ret.size());
                i += 1;
            } else {
                ret_abi.types(args.returns[0..return_count]);
            }

            for (self.getAstSlice(e.args), fdata.args) |arg, ty| {
                const abi = self.abi.categorize(ty);
                abi.types(args.params[i..]);
                var value = self.emitTyped(ty, arg);
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

            const rets = self.bl.addCall(@intFromEnum(func), args);

            return switch (ret_abi) {
                .Imaginary => .{},
                .ByValue => mkv(fdata.ret, rets[0]),
                .ByValuePair => |pair| b: {
                    const slot = ctx.loc orelse self.bl.addLocal(fdata.ret.size());
                    for (pair.types, pair.offsets(), rets) |ty, off, vl| {
                        self.bl.addFieldStore(slot, @intCast(off), ty, vl);
                    }
                    break :b mkp(fdata.ret, slot);
                },
                .ByRef => mkp(fdata.ret, args.arg_slots[0]),
            };
        },
        .Return => |e| {
            var value = self.emit(.{ .loc = self.struct_ret_ptr, .ty = self.fdata.ret }, e.value);
            if (self.typeCheck(e.value, &value, self.fdata.ret)) return .never;
            switch (self.abi.categorize(value.ty)) {
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
        else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
    }
}
