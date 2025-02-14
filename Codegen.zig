bl: Builder,
types: *Types,
diagnostics: std.io.AnyWriter,
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
const Node = Builder.Node;
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
    for (self.fdata.args) |ty| param_count += @intFromBool(ty.size() != 0);
    const return_count: usize = @intFromBool(self.fdata.ret.size() != 0);
    const token, const params, const returns = self.bl.begin(param_count, return_count);

    self.scope = .init(self.arena());
    self.loops = .init(self.arena());

    if (returns.len != 0) returns[0] = self.fdata.ret.asDataType();

    var i: usize = 0;
    for (self.fdata.args) |ty| {
        defer i += 1;
        if (ty.size() == 0) continue;
        params[i] = ty.asDataType();

        self.scope.append(.{ .ty = ty }) catch unreachable;
        self.bl.pushScopeValue(self.bl.addSpill(self.bl.addParam(i)));
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
    id: ?*Node = null,
    ty: Types.Id = .void,

    pub const never = Value{ .ty = .never };
};

inline fn mkv(ty: Types.Id, id: ?*Node) Value {
    return .{ .ty = ty, .id = id };
}

pub const Ctx = struct {
    ty: ?Types.Id = null,
};

pub fn emitTyped(self: *Codegen, ty: Types.Id, expr: Ast.Id) ?*Node {
    var value = self.emit(.{ .ty = ty }, expr);
    self.typeCheck(expr, &value, ty);
    return value.id;
}

pub fn typeCheck(self: *Codegen, expr: Ast.Id, got: *Value, expected: Types.Id) void {
    if (!got.ty.canUpcast(expected)) {
        self.report(expr, "expected {} got {}", .{ expected, got.ty });
        return;
    }

    if (got.ty != expected) {
        if (got.ty.isSigned()) {
            got.id = self.bl.addUnOp(.sext, expected.asDataType(), got.id.?);
        }

        if (got.ty.isUnsigned()) {
            got.id = self.bl.addUnOp(.uext, expected.asDataType(), got.id.?);
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
    switch (self.getAst(expr)) {
        .Comment => return .{},
        .Void => return .{},
        .Integer => |e| {
            const ty = ctx.ty orelse .uint;
            const parsed = std.fmt.parseInt(i64, self.tokenSrc(e.index), 10) catch unreachable;
            return mkv(ty, self.bl.addIntConst(ty.asDataType(), parsed));
        },
        .Ident => |e| {
            const vari = self.scope.items[e.id.index];
            const value = self.bl.getScopeValue(e.id.index);
            return mkv(vari.ty, self.bl.addLoad(value, vari.ty.asDataType()));
        },
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
            const cond = self.emitTyped(.bool, e.cond).?;
            var if_builder = self.bl.addIfAndBeginThen(cond);
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
        .UnOp => |e| switch (e.op) {
            .@"&" => {
                const addrd = self.emit(.{}, e.oper);
                return mkv(self.types.makePtr(addrd.ty), addrd.id.?.base());
            },
            .@"*" => {
                const oper = self.emit(.{}, e.oper);
                const base = oper.ty.data().Ptr;
                return mkv(base, self.bl.addLoad(oper.id.?, base.asDataType()));
            },
            .@"-" => {
                var lhs = self.emit(ctx, e.oper);
                if (ctx.ty) |ty| self.typeCheck(expr, &lhs, ty);
                return mkv(lhs.ty, self.bl.addUnOp(.neg, lhs.ty.asDataType(), lhs.id.?));
            },
            else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
        },
        .Break => |_| {
            self.loops.getLast().addLoopControl(&self.bl, .@"break");
            return .{};
        },
        .Continue => |_| {
            self.loops.getLast().addLoopControl(&self.bl, .@"continue");
            return .{};
        },
        .Return => |e| {
            const value = self.emitTyped(self.fdata.ret, e.value);
            self.bl.addReturn(if (value) |v| &.{v} else &.{});
            return .{};
        },
        .BinOp => |e| switch (e.op) {
            .@":=" => {
                const value = self.emit(.{}, e.rhs);
                const local = self.bl.addSpill(value.id.?);
                self.scope.append(.{ .ty = value.ty }) catch unreachable;
                self.bl.pushScopeValue(local);
                return .{};
            },
            .@":" => {
                const assign = self.getAst(e.rhs).BinOp;
                std.debug.assert(assign.op == .@"=");
                const ty = self.types.resolveTy(self.file, assign.lhs);
                const value = self.emitTyped(ty, assign.rhs).?;
                const local = self.bl.addSpill(value);
                self.scope.append(.{ .ty = ty }) catch unreachable;
                self.bl.pushScopeValue(local);
                return .{};
            },
            .@"=" => if (e.lhs.tag() == .Wildcard) {
                _ = self.emit(.{}, e.rhs);
                return .{};
            } else {
                const loc = self.emit(.{}, e.lhs);
                std.debug.assert(loc.id.?.kind == .Load);
                const val = self.emitTyped(loc.ty, e.rhs).?;
                _ = self.bl.addStore(loc.id.?.base(), val);
                return .{};
            },
            else => {
                var lhs = self.emit(ctx, e.lhs);
                var rhs = self.emit(.{ .ty = lhs.ty }, e.rhs);
                if (e.op.isComparison() and lhs.ty.isSigned() != rhs.ty.isSigned())
                    self.report(e.lhs, "mixed sign comparison ({} {})", .{ lhs.ty, rhs.ty });
                const unified = ctx.ty orelse lhs.ty.binOpUpcast(rhs.ty) catch |err| {
                    self.report(expr, "{s} ({} and {})", .{ @errorName(err), lhs.ty, rhs.ty });
                    return .never;
                };
                const upcast_to: Types.Id = if (e.op.isComparison()) if (lhs.ty.isSigned()) .int else .uint else unified;
                self.typeCheck(e.lhs, &lhs, upcast_to);
                self.typeCheck(e.rhs, &rhs, upcast_to);
                return mkv(unified, self.bl.addBinOp(e.op.toBinOp(lhs.ty), unified.asDataType(), lhs.id.?, rhs.id.?));
            },
        },
        .Call => |e| {
            const func = self.types.resolveFunc(self.file, e.called);
            const fdata = self.types.get(func);

            var param_count: usize = 0;
            for (fdata.args) |ty| param_count += @intFromBool(ty.size() != 0);
            const return_count: usize = @intFromBool(fdata.ret.size() != 0);

            var params: [12]DataType = undefined;
            var i: usize = 0;
            for (fdata.args) |ty| {
                if (ty.size() == 0) continue;
                params[i] = ty.asDataType();
                i += 1;
            }
            std.debug.assert(param_count == i);

            var returns: [1]DataType = undefined;
            i = 0;
            for ([_]Types.Id{fdata.ret}) |ty| {
                if (ty.size() == 0) continue;
                returns[i] = ty.asDataType();
                i += 1;
            }
            std.debug.assert(return_count == i);

            const args = self.bl.allocCallArgs(params[0..param_count], returns[0..return_count]);

            i = 0;
            for (self.getAstSlice(e.args), fdata.args) |arg, ty| {
                if (ty.size() == 0) continue;
                args.arg_slots[i] = self.emitTyped(ty, arg).?;
                i += 1;
            }

            const rets = self.bl.addCall(@intFromEnum(func), args);
            std.debug.assert(rets.len < 2);

            return mkv(fdata.ret, if (rets.len > 0) rets[0] else null);
        },
        else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
    }
}
