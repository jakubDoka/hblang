bl: Builder,
types: *Types,
scope: Scope = undefined,
loops: std.ArrayList(*Builder.Loop) = undefined,
file: Types.File = undefined,
ast: Ast = undefined,
fdata: *Types.FuncData = undefined,

const std = @import("std");
const Ast = @import("parser.zig");
const Types = @import("Types.zig");
const Builder = @import("Builder.zig");
const Func = Builder.Func;
const Node = Builder.Node;
const DataType = Builder.DataType;
const Codegen = @This();

const Scope = std.ArrayList(ScopeEntry);

const ScopeEntry = struct {
    ty: Types.Id,
};

const Loop = void;

pub fn init(gpa: std.mem.Allocator, types: *Types) Codegen {
    return .{
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

pub fn build(self: *Codegen, file: Types.File, func: Types.Func) void {
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
        std.debug.assert(ty == .ptr or ty == .uint);
        params[i] = ty.asDataType();

        self.scope.append(.{ .ty = ty }) catch unreachable;
        self.bl.pushScopeValue(self.bl.addSpill(self.bl.addParam(i)));
    }

    _ = self.emit(self.getAst(self.fdata.ast).Fn.body);

    self.bl.end(token);
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

fn emit(self: *Codegen, expr: Ast.Id) ?*Func.Node {
    switch (self.getAst(expr)) {
        .Comment => return null,
        .Void => return null,
        .Integer => |e| {
            const parsed = std.fmt.parseInt(i64, self.tokenSrc(e.index), 10) catch unreachable;
            return self.bl.addIntConst(.int, parsed);
        },
        .Ident => |e| {
            const vari = self.scope.items[e.id.index];
            std.debug.assert(vari.ty == .ptr or vari.ty == .uint);
            const value = self.bl.getScopeValue(e.id.index);
            return self.bl.addLoad(value, vari.ty.asDataType());
        },
        .Block => |e| {
            const prev_scope_height = self.scope.items.len;
            defer self.scope.items.len = prev_scope_height;
            defer self.bl.truncateScope(prev_scope_height);

            for (self.getAstSlice(e.stmts)) |s| {
                if (self.bl.isUnreachable()) break;
                _ = self.emit(s);
            }

            return null;
        },
        .If => |e| {
            const cond = self.emit(e.cond).?;
            var if_builder = self.bl.addIfAndBeginThen(cond);
            _ = self.emit(e.then);
            const end_else = if_builder.beginElse(&self.bl);
            _ = self.emit(e.else_);
            if_builder.end(&self.bl, end_else);

            return null;
        },
        .Loop => |e| {
            var loop = self.bl.addLoopAndBeginBody();
            self.loops.append(&loop) catch unreachable;
            _ = self.emit(e.body);
            _ = self.loops.pop();
            loop.end(&self.bl);

            return null;
        },
        .UnOp => |e| switch (e.op) {
            .@"&" => {
                return self.emit(e.oper).?.base();
            },
            .@"*" => {
                const oper = self.emit(e.oper).?;
                return self.bl.addLoad(oper, .int);
            },
            else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
        },
        .Break => |_| {
            self.loops.getLast().addLoopControl(&self.bl, .@"break");
            return null;
        },
        .Continue => |_| {
            self.loops.getLast().addLoopControl(&self.bl, .@"continue");
            return null;
        },
        .Return => |e| {
            const value = self.emit(e.value);
            self.bl.addReturn(if (value) |v| &.{v} else &.{});
            return null;
        },
        .BinOp => |e| switch (e.op) {
            .@":=" => {
                const value = self.emit(e.rhs).?;
                const local = self.bl.addSpill(value);
                self.scope.append(.{ .ty = .uint }) catch unreachable;
                self.bl.pushScopeValue(local);
                return null;
            },
            .@"=" => {
                const loc = self.emit(e.lhs).?;
                std.debug.assert(loc.kind == .Load);
                const val = self.emit(e.rhs).?;
                _ = self.bl.addStore(loc.base(), val);
                return null;
            },
            else => return self.bl.addBinOp(e.op.toUnsignedBinOp(), self.emit(e.lhs).?, self.emit(e.rhs).?),
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
                std.debug.assert(ty == .ptr or ty == .uint);
                params[i] = .int;
                i += 1;
            }
            std.debug.assert(param_count == i);

            var returns: [1]DataType = undefined;
            i = 0;
            for ([_]Types.Id{fdata.ret}) |ty| {
                if (ty.size() == 0) continue;
                std.debug.assert(ty == .ptr or ty == .uint);
                returns[i] = .int;
                i += 1;
            }
            std.debug.assert(return_count == i);

            const args = self.bl.allocCallArgs(params[0..param_count], returns[0..return_count]);

            i = 0;
            for (self.getAstSlice(e.args), fdata.args) |arg, ty| {
                if (ty.size() == 0) continue;
                args.arg_slots[i] = self.emit(arg).?;
                i += 1;
            }

            const rets = self.bl.addCall(@intFromEnum(func), args);
            std.debug.assert(rets.len < 2);

            return if (rets.len > 0) rets[0] else null;
        },
        else => std.debug.panic("{any}\n", .{self.getAst(expr)}),
    }
}
