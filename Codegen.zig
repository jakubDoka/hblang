bl: Builder,
types: *Types,
diagnostics: std.io.AnyWriter,
comptime abi: Types.Abi = .ableos,
struct_ret_ptr: ?*Node = undefined,
scope: Scope = undefined,
loops: std.ArrayList(*Builder.Loop) = undefined,
file: Types.File = undefined,
ast: Ast = undefined,
fdata: *Types.FuncData = undefined,
errored: bool = undefined,

const std = @import("std");
const Ast = @import("parser.zig");
const Types = @import("Types.zig");
const Builder = @import("Builder.zig");
const Func = Builder.Func;
const Node = Builder.BuildNode;
const DataType = Builder.DataType;
const Codegen = @This();
const panic = std.debug.panic;
const Scope = std.ArrayList(ScopeEntry);

const ScopeEntry = struct {
    ty: Types.Id,
};

const Loop = void;

pub fn init(gpa: std.mem.Allocator, types: *Types, diagnostics: std.io.AnyWriter) Codegen {
    return .{
        .diagnostics = diagnostics,
        .types = types,
        .bl = .init(gpa),
    };
}

pub fn deinit(self: *Codegen) void {
    self.bl.deinit();
    self.* = undefined;
}

pub inline fn arena(self: *Codegen) std.mem.Allocator {
    return self.bl.func.getTmpArena();
}

pub fn build(self: *Codegen, file: Types.File, func: Types.Func) !void {
    self.errored = false;
    self.file = file;
    self.ast = self.types.getFile(file).*;
    self.fdata = self.types.get(func);

    var param_count: usize = 0;
    for (self.fdata.args) |ty| param_count += self.abi.categorize(ty).dataTypes()[0].len;
    const return_count: usize = switch (self.abi.categorize(self.fdata.ret)) {
        .Imaginary => 0,
        .ByValue => 1,
        .ByValuePair => 2,
        .ByRef => b: {
            param_count += 1;
            break :b 0;
        },
    };
    const token, const params, const returns = self.bl.begin(param_count, return_count);

    self.scope = .init(self.arena());
    self.loops = .init(self.arena());

    var i: usize = 0;

    if (self.abi.categorize(self.fdata.ret) == .ByRef) {
        params[i] = .int;
        self.struct_ret_ptr = self.bl.addParam(i);
        i += 1;
    } else {
        @memcpy(returns, self.abi.categorize(self.fdata.ret).dataTypes()[0].slice());
        self.struct_ret_ptr = null;
    }

    for (self.fdata.args) |ty| {
        if (self.abi.categorize(ty) == .ByRef) {
            const arg = self.bl.addParam(i);
            i += 1;
            self.scope.append(.{ .ty = ty }) catch unreachable;
            self.bl.pushScopeValue(arg);
        } else {
            const tys, const offs = self.abi.categorize(ty).dataTypes();
            @memcpy(params[i..][0..tys.len], tys.slice());

            self.scope.append(.{ .ty = ty }) catch unreachable;
            const slot = self.bl.addLocal(ty.size());
            for (offs.slice()) |off| {
                const arg = self.bl.addParam(i);
                self.bl.addFieldStore(slot, @intCast(off), arg);
                i += 1;
            }
            self.bl.pushScopeValue(slot);
        }
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

pub fn emitTyped(self: *Codegen, ty: Types.Id, expr: Ast.Id) Value.Mode {
    var value = self.emit(.{ .ty = ty }, expr);
    self.typeCheck(expr, &value, ty);
    return value.id;
}

pub fn ensureLoaded(self: *Codegen, value: *Value) void {
    if (value.id == .Ptr) {
        value.id = .{ .Value = self.bl.addLoad(value.id.Ptr, self.abi.categorize(value.ty).ByValue) };
    }
}

pub fn typeCheck(self: *Codegen, expr: Ast.Id, got: *Value, expected: Types.Id) void {
    if (!got.ty.canUpcast(expected)) {
        self.report(expr, "expected {} got {}", .{ expected, got.ty });
        return;
    }

    if (got.ty != expected) {
        if (got.ty.isSigned()) {
            got.id.Value = self.bl.addUnOp(.sext, self.abi.categorize(expected).ByValue, got.id.Value);
        }

        if (got.ty.isUnsigned()) {
            got.id.Value = self.bl.addUnOp(.uext, self.abi.categorize(expected).ByValue, got.id.Value);
        }

        got.ty = expected;
    }
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

fn emit(self: *Codegen, ctx: Ctx, expr: Ast.Id) Value {
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
        .Ident => |e| {
            const vari = self.scope.items[e.id.index];
            const value = self.bl.getScopeValue(e.id.index);
            return mkp(vari.ty, value);
        },
        .Ctor => |e| {
            if (e.ty.tag() == .Void and ctx.ty == null) {
                self.report(expr, "cant infer the type of this constructor, you can specify a type before the '.{{'", .{});
                return .never;
            }

            const ty = ctx.ty orelse self.types.resolveTy(self.file, e.ty);
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

                if (self.abi.categorize(value.ty) == .ByValue) {
                    self.ensureLoaded(&value);
                    _ = self.bl.addStore(off, value.id.Value);
                }
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
                if (ctx.ty) |ty| self.typeCheck(expr, &lhs, ty);
                return mkv(lhs.ty, self.bl.addUnOp(.neg, self.abi.categorize(lhs.ty).ByValue, lhs.id.Value));
            },
            else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
        },
        .BinOp => |e| switch (e.op) {
            inline .@":=", .@":" => |t| {
                var value = if (t == .@":=")
                    self.emit(.{}, e.rhs)
                else b: {
                    const assign = self.getAst(e.rhs).BinOp;
                    std.debug.assert(assign.op == .@"=");
                    const ty = self.types.resolveTy(self.file, assign.lhs);
                    var vl = self.emit(.{ .ty = ty }, assign.rhs);
                    self.typeCheck(assign.rhs, &vl, ty);
                    break :b vl;
                };

                const local = if (self.abi.categorize(value.ty) != .ByValue)
                    if (self.bl.isPinned(value.id.Ptr)) b: {
                        const local = self.bl.addLocal(value.ty.size());
                        _ = self.bl.addFixedMemCpy(local, value.id.Ptr, value.ty.size());
                        break :b local;
                    } else b: {
                        break :b value.id.Ptr;
                    }
                else b: {
                    self.ensureLoaded(&value);
                    break :b self.bl.addSpill(value.id.Value);
                };

                self.scope.append(.{ .ty = value.ty }) catch unreachable;
                self.bl.pushScopeValue(local);
                return .{};
            },
            .@"=" => if (e.lhs.tag() == .Wildcard) {
                _ = self.emit(.{}, e.rhs);
                return .{};
            } else {
                const loc = self.emit(.{}, e.lhs);
                var val = Value{ .ty = loc.ty, .id = self.emitTyped(loc.ty, e.rhs) };
                if (self.abi.categorize(loc.ty) == .ByValue) {
                    self.ensureLoaded(&val);
                    _ = self.bl.addStore(loc.id.Ptr, val.id.Value);
                } else {
                    _ = self.bl.addFixedMemCpy(loc.id.Ptr, val.id.Ptr, @intCast(loc.ty.size()));
                }
                return .{};
            },
            else => {
                var lhs = self.emit(if (e.op.isComparison()) .{} else ctx, e.lhs);
                var rhs = self.emit(.{ .ty = lhs.ty }, e.rhs);
                if (e.op.isComparison() and lhs.ty.isSigned() != rhs.ty.isSigned())
                    self.report(e.lhs, "mixed sign comparison ({} {})", .{ lhs.ty, rhs.ty });
                const unified = ctx.ty orelse lhs.ty.binOpUpcast(rhs.ty) catch |err| {
                    self.report(expr, "{s} ({} and {})", .{ @errorName(err), lhs.ty, rhs.ty });
                    return .never;
                };
                const upcast_to: Types.Id = if (e.op.isComparison()) if (lhs.ty.isSigned()) .int else .uint else unified;
                self.ensureLoaded(&lhs);
                self.ensureLoaded(&rhs);
                self.typeCheck(e.lhs, &lhs, upcast_to);
                self.typeCheck(e.rhs, &rhs, upcast_to);
                return mkv(unified, self.bl.addBinOp(e.op.toBinOp(lhs.ty), self.abi.categorize(unified).ByValue, lhs.id.Value, rhs.id.Value));
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
            var cond = Value{ .ty = .bool, .id = self.emitTyped(.bool, e.cond) };
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
            const fdata: *Types.FuncData = self.types.get(func);

            var param_count: usize = 0;
            for (fdata.args) |ty| param_count += self.abi.categorize(ty).dataTypes()[0].len;

            var params: [16]DataType = undefined;
            var i: usize = 0;

            const returns = switch (self.abi.categorize(fdata.ret)) {
                .ByRef => b: {
                    params[i] = .int;
                    param_count += 1;
                    i += 1;
                    break :b self.abi.categorize(.void).dataTypes();
                },
                else => self.abi.categorize(fdata.ret).dataTypes(),
            };

            for (fdata.args) |ty| {
                const tys = self.abi.categorize(ty).dataTypes()[0];
                @memcpy(params[i..][0..tys.len], tys.slice());
                i += tys.len;
            }
            std.debug.assert(param_count == i);

            const args = self.bl.allocCallArgs(params[0..param_count], returns[0].slice());

            i = 0;

            if (self.abi.categorize(fdata.ret) == .ByRef) {
                args.arg_slots[i] = self.bl.addLocal(fdata.ret.size());
                i += 1;
            }

            for (self.getAstSlice(e.args), fdata.args) |arg, ty| {
                var value = Value{ .ty = ty, .id = self.emitTyped(ty, arg) };
                switch (self.abi.categorize(ty)) {
                    .Imaginary => continue,
                    .ByValue => {
                        self.ensureLoaded(&value);
                        args.arg_slots[i] = value.id.Value;
                        i += 1;
                    },
                    .ByValuePair => {
                        const tys, const offs = self.abi.categorize(ty).dataTypes();
                        for (tys.slice(), offs.slice()) |t, off| {
                            args.arg_slots[i] =
                                self.bl.addFieldLoad(value.id.Ptr, @intCast(off), t);
                            i += 1;
                        }
                    },
                    .ByRef => {
                        args.arg_slots[i] = value.id.Ptr;
                        i += 1;
                    },
                }
            }

            const rets = self.bl.addCall(@intFromEnum(func), args);

            return switch (self.abi.categorize(fdata.ret)) {
                .Imaginary => .{},
                .ByValue => mkv(fdata.ret, rets[0]),
                .ByValuePair => b: {
                    const slot = self.bl.addLocal(fdata.ret.size());

                    _, const offs = self.abi.categorize(fdata.ret).dataTypes();
                    for (offs.slice(), rets) |off, vl| {
                        self.bl.addFieldStore(slot, @intCast(off), vl);
                    }

                    break :b mkp(fdata.ret, slot);
                },
                .ByRef => mkp(fdata.ret, args.arg_slots[0]),
            };
        },
        .Return => |e| {
            var value = Value{ .ty = self.fdata.ret, .id = self.emitTyped(self.fdata.ret, e.value) };
            switch (self.abi.categorize(value.ty)) {
                .Imaginary => self.bl.addReturn(&.{}),
                .ByValue => {
                    self.ensureLoaded(&value);
                    self.bl.addReturn(&.{value.id.Value});
                },
                .ByValuePair => {
                    var slots: [2]*Node = undefined;
                    const tys, const offs = self.abi.categorize(value.ty).dataTypes();
                    for (tys.slice(), offs.slice(), &slots) |t, off, *slt| {
                        slt.* = self.bl.addFieldLoad(value.id.Ptr, @intCast(off), t);
                    }
                    self.bl.addReturn(&slots);
                },
                .ByRef => {
                    _ = self.bl.addFixedMemCpy(self.struct_ret_ptr.?, value.id.Ptr, value.ty.size());
                    self.bl.addReturn(&.{});
                },
            }
            return .{};
        },
        else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
    }
}
