bl: Builder,
types: *Types,
work_list: std.ArrayListUnmanaged(Task),
target: Types.Target,
comptime_unreachable: bool = false,
comptime abi: Types.Abi = .ableos,
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

const Loop = union(enum) {
    Runtime: Builder.Loop,
    Comptime: union(enum) {
        Clean,
        Controlled: Ast.Id,
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

    return res;
}

pub fn build(self: *Codegen, func: *Types.Func) !void {
    var tmp = root.Arena.scrath(null);
    defer tmp.deinit();

    const param_count, const return_count, const ret_abi = func.computeAbiSize(self.abi, self.types);
    const token, const params, const returns = self.beginBuilder(tmp.arena, func.ret, param_count, return_count);
    self.ast = self.types.getFile(func.key.file);
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
            .Imaginary => continue,
        };
        self.scope.appendAssumeCapacity(.{ .ty = ty, .name = ident.id });
        self.bl.pushScopeValue(arg);
        i += abi.len(false);
        ty_idx += 1;
    }

    _ = self.emit(.{}, ast.exprs.get(func.key.ast).Fn.body);

    if (!self.bl.isUnreachable() and ret_abi != .Imaginary) {
        self.report(fn_ast.body, "function is missing a return value since" ++
            " {} has more then 1 possible value", .{func.ret});
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

    pub const never = Value{ .ty = .never };

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
            .Perm => |p| p.file(),
            .Tmp => |t| t.parent_scope.file(),
        };
    }

    pub fn items(self: Scope) Ast.Slice {
        return switch (self) {
            .Perm => |p| p.items(),
            .Tmp => |t| t.parent_scope.items(),
        };
    }

    pub fn findCapture(self: Scope, id: Ast.Ident) ?Types.Key.Capture {
        return switch (self) {
            .Perm => |p| p.findCapture(id),
            .Tmp => |t| for (t.scope.items, 0..) |se, i| {
                if (se.name == id) {
                    if (se.ty != .type) {
                        return .{ .id = id, .ty = se.ty };
                    }
                    const value = t.bl.getScopeValue(i);
                    break .{ .id = id, .ty = .type, .value = @intFromEnum(t.unwrapTyConst(t.bl.addLoad(value, .int))) };
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
        if (cata == .Imaginary) return;
        value.id = .{ .Value = self.bl.addLoad(value.id.Ptr, cata.ByValue) };
    }
}

pub fn typeCheck(self: *Codegen, expr: anytype, got: *Value, expected: Types.Id) bool {
    if (got.ty == .never) return true;

    if (expected.data() == .Nullable and expected.data().Nullable.* == got.ty) {
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

        return false;
    }

    if (!got.ty.canUpcast(expected, self.types)) {
        self.report(expr, "expected {} got {}", .{ expected, got.ty });
        got.* = .never;
        return true;
    }

    if (got.ty != expected) {
        self.ensureLoaded(got);

        if (got.ty.isSigned() and got.ty.size(self.types) < expected.size(self.types)) {
            got.id.Value = self.bl.addUnOp(.sext, self.abi.categorize(expected, self.types).ByValue, got.id.Value);
        }

        if (got.ty.isUnsigned() and got.ty.size(self.types) < expected.size(self.types)) {
            //self.report(, "{} {} {}", .{ got.ty, got.id.Value.data_type, expected });
            got.id.Value = self.bl.addUnOp(.uext, self.abi.categorize(expected, self.types).ByValue, got.id.Value);
        }

        got.ty = expected;
    }

    return false;
}

fn report(self: *Codegen, expr: anytype, comptime fmt: []const u8, args: anytype) void {
    self.errored = true;
    const file = self.ast;
    const line, const col = Ast.lineCol(file.source, file.posOf(expr).index);

    const RemapedArgs = comptime b: {
        var tupl = @typeInfo(@TypeOf(args)).@"struct";
        var fields = tupl.fields[0..tupl.fields.len].*;
        for (&fields) |*f| if (f.type == Types.Id) {
            f.type = Types.Id.Fmt;
        };
        tupl.fields = &fields;
        break :b @Type(.{ .@"struct" = tupl });
    };

    var rargs: RemapedArgs = undefined;
    inline for (args, 0..) |v, i| {
        if (@TypeOf(v) == Types.Id) {
            rargs[i] = v.fmt(self.types);
        } else {
            rargs[i] = v;
        }
    }
    self.types.diagnostics.print(
        "{s}:{}:{}: " ++ fmt ++ "\n{}\n",
        .{ file.path, line, col } ++ rargs ++ .{file.codePointer(file.posOf(expr).index)},
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
    if (value.id == .Imaginary) return;

    if (self.abi.categorize(value.ty, self.types) == .ByValue) {
        self.ensureLoaded(value);
        _ = self.bl.addStore(loc, self.abi.categorize(value.ty, self.types).ByValue, value.id.Value);
    } else if (value.id.Ptr != loc) {
        _ = self.bl.addFixedMemCpy(loc, value.id.Ptr, value.ty.size(self.types));
    }
}

pub fn resolveAnonTy(self: *Codegen, expr: Ast.Id) Types.Id {
    return self.types.ct.evalTy("", .{ .Tmp = self }, expr);
}

pub fn resolveTy(self: *Codegen, name: []const u8, expr: Ast.Id) Types.Id {
    return self.types.ct.evalTy(name, .{ .Tmp = self }, expr);
}

pub fn emitTyped(self: *Codegen, ctx: Ctx, ty: Types.Id, expr: Ast.Id) Value {
    var value = self.emit(ctx.addTy(ty), expr);
    if (self.typeCheck(expr, &value, ty)) return .never;
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
    return self.types.ct.evalTy(name, .{ .Perm = bsty }, other_ast.exprs.get(decl).BinOp.rhs);
}

pub fn loadIdent(self: *Codegen, pos: Ast.Pos, id: Ast.Ident) Value {
    const ast = self.ast;
    for (self.scope.items, 0..) |se, i| {
        if (se.name == id) {
            const value = self.bl.getScopeValue(i);
            return .mkp(se.ty, value);
        }
    } else {
        var cursor = self.parent_scope;
        const decl = while (!cursor.empty()) {
            if (ast.findDecl(cursor.items(), id)) |v| break v;
            if (cursor.findCapture(id)) |c| {
                return .{ .ty = c.ty, .id = if (c.ty == .type) .{ .Value = self.bl.addIntImm(.int, @bitCast(c.value)) } else b: {
                    if (self.target != .@"comptime") {
                        self.report(pos, "can't access this value, (yet)", .{});
                        return .never;
                    }
                    break :b .{ .Imaginary = {} };
                } };
            }
            cursor = cursor.parent();
        } else {
            std.debug.panic("\n{}\n", .{ast.codePointer(pos.index)});
        };

        const vari = ast.exprs.get(decl).BinOp;
        const ty: ?Types.Id, const value: Ast.Id = switch (vari.op) {
            .@":" => .{ self.resolveAnonTy(ast.exprs.get(vari.rhs).BinOp.lhs), ast.exprs.get(vari.rhs).BinOp.rhs },
            .@":=" => .{ null, vari.rhs },
            else => unreachable,
        };

        const typ = if (ty) |typ| b: {
            const global = self.types.resolveGlobal(cursor.perm(), ast.tokenSrc(id.pos()), value);
            self.types.ct.evalGlobal(ast.tokenSrc(id.pos()), global.data().Global, typ, value);
            self.queue(.{ .Global = global.data().Global });
            break :b global;
        } else return self.emitTyConst(self.types.ct.evalTy(ast.tokenSrc(id.pos()), cursor, value));
        const global = typ.data().Global;
        return .mkp(global.ty, self.bl.addGlobalAddr(global.id));
    }
}

pub fn instantiateTemplate(
    self: *Codegen,
    tmp: root.Arena.Scratch,
    e: std.meta.TagPayload(Ast.Expr, .Call),
    typ: Types.Id,
) struct { []Value, Types.Id } {
    const ast = self.ast;
    const tmpl = typ.data().Template;

    var scope = tmpl.*;
    scope.key.scope = typ;
    scope.key.captures = &.{};

    const tmpl_file = self.types.getFile(tmpl.key.file);
    const tmpl_ast = tmpl_file.exprs.getTyped(.Fn, tmpl.key.ast).?;
    const comptime_args = ast.exprs.view(tmpl_ast.comptime_args);

    const captures = tmp.arena.alloc(Types.Key.Capture, tmpl_ast.comptime_args.len());
    const arg_tys = tmp.arena.alloc(Types.Id, tmpl_ast.args.len() - captures.len);
    const arg_exprs = tmp.arena.alloc(Value, arg_tys.len);

    var capture_idx: usize = 0;
    var arg_idx: usize = 0;
    for (tmpl_file.exprs.view(tmpl_ast.args), ast.exprs.view(e.args)) |param, arg| {
        if (tmpl_file.exprs.get(param.bindings).Ident.pos.flag.@"comptime") {
            captures[capture_idx] = .{ .id = comptime_args[capture_idx], .ty = .type, .value = @intFromEnum(self.resolveAnonTy(arg)) };

            capture_idx += 1;
            scope.key.captures = captures[0..capture_idx];
        } else {
            // this is in anticipation of the @Any
            arg_tys[arg_idx] = self.types.ct.evalTy("", .{ .Perm = .init(.{ .Template = &scope }) }, param.ty);
            arg_exprs[arg_idx] = self.emitTyped(.{}, arg_tys[arg_idx], arg);
            arg_idx += 1;
        }
    }

    const ret = self.types.ct.evalTy("", .{ .Perm = .init(.{ .Template = &scope }) }, tmpl_ast.ret);

    // TODO: the comptime_args + captures are continuous, we could remove the template from the scope tree in that case
    const slot, const alloc = self.types.intern(.Func, .{
        .scope = typ,
        .file = tmpl.key.file,
        .ast = tmpl.key.ast,
        .name = "",
        .captures = captures,
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
        .Imaginary => .{},
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

fn loopControl(self: *Codegen, kind: Builder.Loop.Control, ctrl: Ast.Id) void {
    switch (self.loops.items[self.loops.items.len - 1]) {
        .Runtime => |*l| l.addLoopControl(&self.bl, kind),
        .Comptime => |*l| {
            self.comptime_unreachable = true;
            switch (l.*) {
                .Clean => l.* = .{ .Controlled = ctrl },
                .Controlled => |p| {
                    self.report(ctrl, "reached second $loop control, this means control" ++
                        " flow leading to it is runtime dependant", .{});
                    self.report(p, "...previous one reached here", .{});
                },
            }
        },
    }
}

pub fn emitAutoDeref(self: *Codegen, value: *Value) void {
    if (value.ty.data() == .Ptr) {
        self.ensureLoaded(value);
        value.ty = value.ty.data().Ptr.*;
        value.id = .{ .Ptr = value.id.Value };
    }
}

pub fn emit(self: *Codegen, ctx: Ctx, expr: Ast.Id) Value {
    const ast = self.ast;
    switch (ast.exprs.get(expr)) {
        .Comment => return .{},
        .Void => return .{},

        // #VALUES =====================================================================
        .Integer => |e| {
            const ty = ctx.ty orelse .uint;
            if (!ty.isInteger()) {
                self.report(expr, "{} can not be constructed as integer literal", .{ty});
                return .never;
            }
            const parsed = std.fmt.parseInt(i64, ast.tokenSrc(e.index), 10) catch unreachable;
            return .mkv(ty, self.bl.addIntImm(self.abi.categorize(ty, self.types).ByValue, parsed));
        },
        .Bool => |e| {
            return .mkv(.bool, self.bl.addIntImm(.i8, @intFromBool(e.value)));
        },
        .Null => {
            const ty: Types.Id = ctx.ty orelse {
                self.report(expr, "can't infer the type of nullable value, you can speciry a type: @as(?<ty>, null)", .{});
                return .never;
            };

            if (ty.data() != .Nullable) {
                self.report(expr, "only nullable types can be initialized with null, {} is not", .{ty});
                return .never;
            }

            switch (self.abi.categorize(ty, self.types)) {
                .Imaginary => unreachable,
                .ByValue => return .mkv(ty, self.bl.addIntImm(.i8, 0)),
                .ByValuePair, .ByRef => {
                    const loc = ctx.loc orelse self.bl.addLocal(ty.size(self.types));
                    _ = self.bl.addStore(loc, .i8, self.bl.addIntImm(.i8, 0));
                    return .mkp(ty, loc);
                },
            }
        },
        .Ident => |e| return self.loadIdent(e.pos, e.id),
        .Idk => {
            const ty: Types.Id = ctx.ty orelse {
                self.report(expr, "cant infer the type of uninitialized memory," ++
                    " you can specify a type: @as(<ty>, idk)", .{});
                return .never;
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
                self.report(expr, "cant infer the type of this constructor, you can specify a type: '<ty>.{{'", .{});
                return .never;
            }

            const oty = ctx.ty orelse self.resolveAnonTy(e.ty);
            var ty = oty;
            const local = ctx.loc orelse self.bl.addLocal(ty.size(self.types));
            var offset_cursor: usize = 0;

            if (ty.data() == .Nullable) {
                ty = ty.data().Nullable.*;
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
                        for (slots, fields) |*s, tf| {
                            offset_cursor = std.mem.alignForward(usize, offset_cursor, tf.ty.alignment(self.types));
                            s.* = .{ .RequiredOffset = offset_cursor };
                            offset_cursor += tf.ty.size(self.types);
                        }
                    }

                    for (ast.exprs.view(e.fields)) |f| {
                        const field = ast.exprs.get(f).BinOp;
                        const fname = ast.tokenSrc(ast.exprs.get(field.lhs).Tag.index + 1);
                        const slot, const ftype = for (fields, slots) |tf, *s| {
                            if (std.mem.eql(u8, tf.name, fname)) break .{ s, tf.ty };
                        } else {
                            self.report(f, "{} does not have a field called {s} (TODO: list fields)", .{ ty, fname });
                            continue;
                        };

                        switch (slot.*) {
                            .RequiredOffset => |offset| {
                                const off = self.bl.addFieldOffset(local, @intCast(offset));
                                var value = self.emit(ctx.addTy(ftype).addLoc(off), field.rhs);
                                if (self.typeCheck(field.rhs, &value, ftype)) continue;
                                self.emitGenericStore(off, &value);
                                slot.* = .{ .Filled = f };
                            },
                            .Filled => |pos| {
                                self.report(f, "initializing the filed multiple times", .{});
                                self.report(pos, "...arleady initialized here", .{});
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
                                self.report(expr, "field {s} on struct {} is not initialized", .{ f.name, ty });
                            }
                        }
                    }
                },
                .Union => |union_ty| {
                    if (e.fields.len() != 1) {
                        self.report(expr, "union constructor must initialize only one field", .{});
                        return .never;
                    }

                    const fields = union_ty.getFields(self.types);

                    const field_ast = ast.exprs.get(ast.exprs.view(e.fields)[0]).BinOp;
                    const fname = ast.tokenSrc(ast.exprs.get(field_ast.lhs).Tag.index + 1);

                    const f = for (fields) |f| {
                        if (std.mem.eql(u8, f.name, fname)) break f;
                    } else {
                        self.report(field_ast.lhs, "{} does not have a field called {s} (TODO: list fields)", .{ ty, fname });
                        return .never;
                    };

                    offset_cursor = std.mem.alignForward(usize, offset_cursor, f.ty.alignment(self.types));
                    const off = self.bl.addFieldOffset(local, @intCast(offset_cursor));
                    var value = self.emit(.{ .ty = f.ty, .loc = off }, field_ast.rhs);
                    if (self.typeCheck(field_ast.rhs, &value, f.ty)) return .never;
                    self.emitGenericStore(off, &value);
                },
                else => {
                    self.report(expr, "{} can not be constructed with '.{{..}}'", .{ty});
                    return .never;
                },
            }

            return .mkp(oty, local);
        },
        .Tupl => |e| {
            if (e.ty.tag() == .Void and ctx.ty == null) {
                self.report(expr, "cant infer the type of this constructor, you can specify a type: '<ty>.('", .{});
                return .never;
            }

            const oty = ctx.ty orelse self.resolveAnonTy(e.ty);
            var ty = oty;
            const local = ctx.loc orelse self.bl.addLocal(oty.size(self.types));
            var offset: usize = 0;

            if (ty.data() == .Nullable) {
                ty = ty.data().Nullable.*;
                _ = self.bl.addStore(local, .i8, self.bl.addIntImm(.i8, 1));
                offset += ty.alignment(self.types);
            }

            if (ty.data() != .Struct) {
                self.report(expr, "{} can not be constructed with '.(..)'", .{ty});
                return .never;
            }
            const struct_ty = ty.data().Struct;

            if (e.fields.len() != struct_ty.getFields(self.types).len) {
                self.report(
                    e.pos,
                    "{} has {} fields, but tuple constructor has {} values",
                    .{ ty, struct_ty.getFields(self.types).len, e.fields.len() },
                );
                return .never;
            }

            for (ast.exprs.view(e.fields), struct_ty.getFields(self.types)) |field, sf| {
                const ftype = sf.ty;
                offset = std.mem.alignForward(usize, offset, ftype.alignment(self.types));

                const off = self.bl.addFieldOffset(local, @intCast(offset));
                var value = self.emit(ctx.addTy(ftype).addLoc(off), field);
                if (self.typeCheck(field, &value, ftype)) continue;
                self.emitGenericStore(off, &value);
                offset += ftype.size(self.types);
            }

            return .mkp(oty, local);
        },
        .Arry => |e| {
            if (e.ty.tag() == .Void and ctx.ty == null) {
                self.report(expr, "cant infer the type of this constructor, you can specify a type: '<elem-ty>.('", .{});
                return .never;
            }

            const local = ctx.loc orelse self.bl.addLocal(0);
            var start: usize = 0;

            const elem_ty, const res_ty: Types.Id = if (ctx.ty) |ret_ty| b: {
                var ty = ret_ty;
                if (ty.data() == .Nullable) {
                    ty = ty.data().Nullable.*;
                    _ = self.bl.addStore(local, .i8, self.bl.addIntImm(.i8, 1));
                    start += 1;
                }

                if (ty.data() != .Slice or ty.data().Slice.len == null) {
                    self.report(expr, "{} can not bi initialized with array syntax", .{ty});
                    return .never;
                }

                if (ty.data().Slice.len != e.fields.len()) {
                    self.report(expr, "expected array with {} element, got {}", .{ ty.data().Slice.len.?, e.fields.len() });
                    return .never;
                }

                break :b .{ ty.data().Slice.elem, ret_ty };
            } else b: {
                const elem_ty = self.resolveAnonTy(e.ty);
                const array_ty = self.types.makeSlice(e.fields.len(), elem_ty);
                break :b .{ elem_ty, array_ty };
            };

            if (ctx.loc == null) self.bl.resizeLocal(local, res_ty.size(self.types));

            for (ast.exprs.view(e.fields), start..) |elem, i| {
                const off = self.bl.addFieldOffset(local, @intCast(i * elem_ty.size(self.types)));
                var value = self.emitTyped(.{ .loc = off }, elem_ty, elem);
                self.emitGenericStore(off, &value);
            }

            return .mkp(res_ty, local);
        },

        // #OPS ========================================================================
        .SliceTy => |e| {
            const len: ?usize = if (e.len.tag() == .Void) null else @intCast(self.types.ct.evalIntConst(.{ .Tmp = self }, e.len));
            const elem = self.resolveAnonTy(e.elem);
            return self.emitTyConst(self.types.makeSlice(len, elem));
        },
        .UnOp => |e| switch (e.op) {
            .@"^" => return self.emitTyConst(self.types.makePtr(self.resolveAnonTy(e.oper))),
            .@"?" => return self.emitTyConst(self.types.makeNullable(self.resolveAnonTy(e.oper))),
            .@"&" => {
                const addrd = self.emit(.{}, e.oper);
                if (addrd.ty == .never) return .never;
                return .mkv(self.types.makePtr(addrd.ty), addrd.id.Ptr);
            },
            .@"-" => {
                var lhs = self.emit(ctx, e.oper);
                if (ctx.ty) |ty| if (self.typeCheck(expr, &lhs, ty)) return .never;
                return .mkv(lhs.ty, self.bl.addUnOp(.neg, self.abi.categorize(lhs.ty, self.types).ByValue, lhs.id.Value));
            },
            else => std.debug.panic("{any}\n", .{ast.exprs.get(expr)}),
        },
        .BinOp => |e| switch (e.op) {
            inline .@":=", .@":" => |t| {
                const loc = self.bl.addLocal(0);

                const prev_name = self.name;
                self.name = ast.tokenSrc(ast.exprs.get(e.lhs).Ident.id.pos());
                defer self.name = prev_name;

                var value = if (t == .@":=")
                    self.emit(.{ .loc = loc }, e.rhs)
                else b: {
                    const assign = ast.exprs.get(e.rhs).BinOp;
                    std.debug.assert(assign.op == .@"=");
                    const ty = self.resolveAnonTy(assign.lhs);
                    break :b self.emitTyped(ctx.addLoc(loc), ty, assign.rhs);
                };

                if (value.ty != .never) {
                    self.bl.resizeLocal(loc, value.ty.size(self.types));
                    self.emitGenericStore(loc, &value);
                }

                self.scope.appendAssumeCapacity(.{ .ty = value.ty, .name = ast.exprs.get(e.lhs).Ident.id });
                self.bl.pushScopeValue(loc);
                return .{};
            },
            .@"=" => if (e.lhs.tag() == .Wildcard) {
                _ = self.emit(.{}, e.rhs);
                return .{};
            } else {
                const loc = self.emit(.{}, e.lhs);
                if (loc.ty == .never) return .{};

                if (loc.id == .Value) {
                    self.report(e.lhs, "can't assign to this", .{});
                    return .{};
                }

                var val = self.emitTyped(ctx, loc.ty, e.rhs);
                self.emitGenericStore(loc.id.Ptr, &val);
                return .{};
            },
            else => {
                if (e.lhs.tag() == .Null) {
                    self.report(e.lhs, "null has to be on the right hand side", .{});
                    return .never;
                }

                var lhs = self.emit(if (e.op.isComparison()) .{} else ctx, e.lhs);

                if (e.rhs.tag() == .Null) switch (e.op) {
                    .@"==", .@"!=" => {
                        if (lhs.ty.data() != .Nullable) {
                            self.report(e.lhs, "only nullable types can be compared with null, {} is not", .{lhs.ty});
                            return .never;
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
                        self.report(e.lhs, "only comparing against null is supported", .{});
                        return .never;
                    },
                };

                if (!lhs.ty.isBinaryOperand()) {
                    self.report(e.lhs, "{} can not be used in binary operations", .{lhs.ty});
                    return .never;
                }

                var rhs = self.emit(ctx.addTy(lhs.ty), e.rhs);
                if (e.op.isComparison() and lhs.ty.isSigned() != rhs.ty.isSigned())
                    self.report(e.lhs, "mixed sign comparison ({} {})", .{ lhs.ty, rhs.ty });
                const unified: Types.Id = ctx.ty orelse lhs.ty.binOpUpcast(rhs.ty, self.types) catch |err| {
                    self.report(expr, "{s} ({} and {})", .{ @errorName(err), lhs.ty, rhs.ty });
                    return .never;
                };

                if (lhs.ty.data() == .Struct) if (e.op.isComparison()) {
                    self.report(e.lhs, "\n", .{});
                    unreachable;
                } else {
                    const loc = ctx.loc orelse self.bl.addLocal(unified.size(self.types));
                    self.emitStructOp(unified.data().Struct, e.op, loc, lhs.id.Ptr, rhs.id.Ptr);
                    return .mkp(unified, loc);
                } else {
                    const upcast_to: Types.Id = if (e.op.isComparison()) if (lhs.ty.isSigned()) .int else .uint else unified;
                    self.ensureLoaded(&lhs);
                    self.ensureLoaded(&rhs);
                    const lhs_fail = self.typeCheck(e.lhs, &lhs, upcast_to);
                    const rhs_fail = self.typeCheck(e.rhs, &rhs, upcast_to);
                    if (lhs_fail or rhs_fail) return .never;
                    return .mkv(unified, self.bl.addBinOp(
                        e.op.toBinOp(lhs.ty),
                        self.abi.categorize(unified, self.types).ByValue,
                        lhs.id.Value,
                        rhs.id.Value,
                    ));
                }
            },
        },
        .Unwrap => |e| {
            // TODO: better type inference
            var base = self.emit(.{}, e);

            if (base.ty == .never) return .never;

            self.emitAutoDeref(&base);

            if (base.ty.data() != .Nullable) {
                self.report(e, "only nullable types can be unwrapped, {} is not", .{base.ty});
                return .never;
            }

            const ty = base.ty.data().Nullable.*;

            switch (self.abi.categorize(base.ty, self.types)) {
                .Imaginary => unreachable,
                .ByValue => return .{ .ty = ty },
                .ByRef, .ByValuePair => return .mkp(ty, self.bl.addFieldOffset(base.id.Ptr, @bitCast(ty.alignment(self.types)))),
            }
        },
        .Deref => |e| {
            var base = self.emit(.{}, e);

            if (base.ty == .never) return .never;

            if (base.ty.data() != .Ptr) {
                self.report(e, "only pointer types can be dereferenced, {} is not", .{base.ty});
                return .never;
            }

            self.ensureLoaded(&base);
            return .mkp(base.ty.data().Ptr.*, base.id.Value);
        },
        .Field => |e| {
            var base = self.emit(.{}, e.base);

            if (base.ty == .never) return .never;

            self.emitAutoDeref(&base);

            if (base.ty == .type) {
                return self.emitTyConst(self.lookupScopeItem(self.unwrapTyConst(base.id.Value), ast.tokenSrc(e.field.index)));
            }

            const fname = ast.tokenSrc(e.field.index);

            switch (base.ty.data()) {
                .Struct => |struct_ty| {
                    var offset: usize = 0;
                    const ftype = for (struct_ty.getFields(self.types)) |tf| {
                        offset = std.mem.alignForward(usize, offset, tf.ty.alignment(self.types));
                        if (std.mem.eql(u8, fname, tf.name)) break tf.ty;
                        offset += tf.ty.size(self.types);
                    } else {
                        self.report(e.field, "no such field on {} (TODO: list fields)", .{base.ty});
                        return .never;
                    };

                    return .mkp(ftype, self.bl.addFieldOffset(base.id.Ptr, @intCast(offset)));
                },
                .Union => |union_ty| {
                    const ftype = for (union_ty.getFields(self.types)) |tf| {
                        if (std.mem.eql(u8, fname, tf.name)) break tf.ty;
                    } else {
                        self.report(e.field, "no such field on {} (TODO: list fields)", .{base.ty});
                        return .never;
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
                        self.report(e.field, "slices and arrays only support `.ptr` and `.len` field", .{});
                        return .never;
                    }
                },
                else => {
                    self.report(e.field, "field access is only allowed on structs and arrays, {} is not", .{base.ty});
                    return .never;
                },
            }
        },
        .Index => |e| if (e.subscript.tag() == .Range) {
            var base = self.emit(.{}, e.base);

            if (base.ty == .never) return .never;
            const range = ast.exprs.get(e.subscript).Range;

            const elem = base.ty.child(self.types) orelse {
                self.report(e.base, "only pointers, arrays and slices can be sliced, {} is not", .{base.ty});
                return .never;
            };

            var start: Value = if (range.start.tag() == .Void)
                .mkv(.uint, self.bl.addIntImm(.int, 0))
            else
                self.emitTyped(.{}, .uint, range.start);
            self.ensureLoaded(&start);
            var end: Value = if (range.end.tag() == .Void) switch (base.ty.data()) {
                .Slice => |slice_ty| if (slice_ty.len) |l|
                    .mkv(.uint, self.bl.addIntImm(.int, @bitCast(l)))
                else
                    .mkv(.uint, self.bl.addFieldLoad(base.id.Ptr, Types.Slice.len_offset, .int)),
                else => {
                    self.report(e.subscript, "unbound range is only allowed on arrays and slices, {} is not", .{base.ty});
                    return .never;
                },
            } else self.emitTyped(.{}, .uint, range.end);
            self.ensureLoaded(&end);

            const res_ty = self.types.makeSlice(null, elem);

            var ptr: Value = switch (base.ty.data()) {
                .Ptr => base,
                .Slice => |slice_ty| if (slice_ty.len == null)
                    .mkv(self.types.makePtr(elem), self.bl.addFieldLoad(base.id.Ptr, Types.Slice.ptr_offset, .int))
                else
                    .mkv(self.types.makePtr(elem), base.id.Ptr),
                else => {
                    self.report(expr, "only structs and slices can be indexed, {} is not", .{base.ty});
                    return .never;
                },
            };

            ptr.id.Value = self.bl.addIndexOffset(ptr.id.Value, elem.size(self.types), start.id.Value);
            const len = self.bl.addBinOp(.isub, .int, end.id.Value, start.id.Value);

            const loc = ctx.loc orelse self.bl.addLocal(res_ty.size(self.types));
            self.bl.addFieldStore(loc, Types.Slice.ptr_offset, .int, ptr.id.Value);
            self.bl.addFieldStore(loc, Types.Slice.len_offset, .int, len);

            return .mkp(res_ty, loc);
        } else {
            var base = self.emit(.{}, e.base);

            if (base.ty == .never) return .never;

            // TODO: pointers to arrays are kind of an edge case
            self.emitAutoDeref(&base);
            switch (base.ty.data()) {
                .Struct => |struct_ty| {
                    var idx_value = self.emitTyped(.{}, .uint, e.subscript);
                    if (idx_value.ty == .never) return .never;
                    self.ensureLoaded(&idx_value);
                    const idx = self.types.ct.partialEval(&self.bl, idx_value.id.Value);

                    const fields = struct_ty.getFields(self.types);

                    if (idx >= fields.len) {
                        self.report(e.subscript, "struct has only {} fields, but idnex is {}", .{ fields.len, idx });
                        return .never;
                    }

                    var offset: usize = 0;
                    for (fields[0..idx], fields[1 .. idx + 1]) |tf, ntf| {
                        offset += tf.ty.size(self.types);
                        offset = std.mem.alignForward(usize, offset, ntf.ty.alignment(self.types));
                    }

                    return .mkp(fields[idx].ty, self.bl.addFieldOffset(base.id.Ptr, @intCast(offset)));
                },
                .Slice => |slice_ty| {
                    var idx = self.emitTyped(.{}, .uint, e.subscript);
                    self.ensureLoaded(&idx);

                    const index_base = if (slice_ty.len == null) self.bl.addLoad(base.id.Ptr, .int) else base.id.Ptr;

                    return .mkp(slice_ty.elem, self.bl.addIndexOffset(index_base, slice_ty.elem.size(self.types), idx.id.Value));
                },
                else => {
                    self.report(expr, "only structs and slices can be indexed, {} is not", .{base.ty});
                    return .never;
                },
            }
        },

        // #CONTROL ====================================================================
        .Block => |e| {
            const prev_scope_height = self.scope.items.len;
            defer self.scope.items.len = prev_scope_height;
            defer self.bl.truncateScope(prev_scope_height);

            for (ast.exprs.view(e.stmts)) |s| {
                if (self.bl.isUnreachable() or self.comptime_unreachable) break;
                _ = self.emitTyped(ctx, .void, s);
            }

            return .{};
        },
        .If => |e| if (e.pos.flag.@"comptime") {
            var cond = self.emitTyped(ctx, .bool, e.cond);
            self.ensureLoaded(&cond);
            if (self.types.ct.partialEval(&self.bl, cond.id.Value) != 0) {
                _ = self.emitTyped(ctx, .void, e.then);
            } else {
                _ = self.emitTyped(ctx, .void, e.else_);
            }

            return .{};
        } else {
            var cond = self.emitTyped(ctx, .bool, e.cond);
            self.ensureLoaded(&cond);
            if (cond.ty == .never) return .{};
            var if_builder = self.bl.addIfAndBeginThen(cond.id.Value);
            _ = self.emitTyped(ctx, .void, e.then);
            const end_else = if_builder.beginElse(&self.bl);
            _ = self.emitTyped(ctx, .void, e.else_);
            if_builder.end(&self.bl, end_else);
            self.comptime_unreachable = false;

            return .{};
        },
        .Loop => |e| if (e.pos.flag.@"comptime") {
            self.loops.appendAssumeCapacity(.{ .Comptime = .Clean });
            const loop = &self.loops.items[self.loops.items.len - 1];
            while ((loop.Comptime != .Controlled or loop.Comptime.Controlled.tag() != .Break) and !self.errored) {
                loop.Comptime = .Clean;
                _ = self.emitTyped(.{}, .void, e.body);
                if (!self.comptime_unreachable) self.loopControl(.@"continue", expr);
                self.comptime_unreachable = false;
            }
            _ = self.loops.pop().?;
            return .{};
        } else {
            var loop = self.bl.addLoopAndBeginBody();
            self.loops.appendAssumeCapacity(.{ .Runtime = loop });
            _ = self.emitTyped(ctx, .void, e.body);
            loop = self.loops.pop().?.Runtime;
            loop.end(&self.bl);

            return .{};
        },
        // TODO: detect conflicting control flow
        .Break => {
            self.loopControl(.@"break", expr);
            return .{};
        },
        .Continue => {
            self.loopControl(.@"continue", expr);
            return .{};
        },
        .Call => |e| {
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            var typ: Types.Id, var caller: ?Value = if (e.called.tag() == .Field) b: {
                const field = ast.exprs.get(e.called).Field;
                const value = self.emit(.{}, field.base);
                if (value.ty == .type) {
                    break :b .{ self.lookupScopeItem(self.unwrapTyConst(value.id.Value), ast.tokenSrc(field.field.index)), null };
                }
                break :b .{ self.lookupScopeItem(value.ty, ast.tokenSrc(field.field.index)), value };
            } else b: {
                break :b .{ self.resolveAnonTy(e.called), null };
            };

            var computed_args: ?[]Value = null;
            const was_template = typ.data() == .Template;
            if (was_template) {
                computed_args, typ = self.instantiateTemplate(tmp, e, typ);
            }

            if (typ == .never) return .never;

            const func = typ.data().Func;
            self.queue(.{ .Func = func });

            const passed_args = e.args.len() + @intFromBool(caller != null);
            if (!was_template and passed_args != func.args.len) {
                self.report(expr, "expected {} arguments, got {}", .{ func.args.len, passed_args });
                return .never;
            }

            const param_count, const return_count, const ret_abi = func.computeAbiSize(self.abi, self.types);
            const args = self.bl.allocCallArgs(tmp.arena, param_count, return_count);

            var i: usize = self.pushReturn(args, ret_abi, func.ret, ctx);

            if (caller) |*value| {
                const abi = self.abi.categorize(value.ty, self.types);
                i += self.pushParam(args, abi, i, value);
            }

            const args_ast = ast.exprs.view(e.args);
            for (func.args[@intFromBool(caller != null)..], 0..) |ty, k| {
                const abi = self.abi.categorize(ty, self.types);
                abi.types(args.params[i..]);
                var value = if (computed_args) |a| a[k] else self.emitTyped(ctx, ty, args_ast[k]);
                if (value.ty == .never) return .never;
                i += self.pushParam(args, abi, i, &value);
            }

            return self.assembleReturn(func.id, args, ctx, func.ret, ret_abi);
        },
        .Return => |e| {
            var value = self.emit(.{ .loc = self.struct_ret_ptr, .ty = self.ret }, e.value);
            if (self.typeCheck(expr, &value, self.ret)) return .never;
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
        inline .Struct, .Union => |e, t| {
            var tmp = root.Arena.scrath(null);
            defer tmp.deinit();

            const prefix = 3;
            const args = self.bl.allocCallArgs(tmp.arena, prefix + e.captures.len() * 2, 1);
            @memset(args.params, .int);
            @memset(args.returns, .int);

            args.arg_slots[0] = self.bl.addIntImm(.int, @intFromEnum(@field(Comptime.InteruptCode, @tagName(t))));
            args.arg_slots[1] = self.bl.addIntImm(.int, @bitCast(@intFromEnum(self.parent_scope.perm())));
            args.arg_slots[2] = self.bl.addIntImm(.int, @as(u32, @bitCast(expr)));

            for (ast.exprs.view(e.captures), 0..) |id, slot_idx| {
                var val = self.loadIdent(.init(id.pos()), id);
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
                var val = self.loadIdent(.init(id.pos()), id);
                if (val.ty == .type) {
                    self.ensureLoaded(&val);
                    slot.* = .{ .id = id, .ty = .type, .value = @intFromEnum(self.unwrapTyConst(val.id.Value)) };
                } else {
                    slot.* = .{ .id = id, .ty = val.ty };
                }
            }

            if (e.comptime_args.len() != 0) {
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
                if (!slot.found_existing) {
                    const args = self.types.arena.alloc(Types.Id, e.args.len());
                    for (ast.exprs.view(e.args), args) |argid, *arg| {
                        const ty = argid.ty;
                        arg.* = self.resolveAnonTy(ty);
                    }
                    const ret = self.resolveAnonTy(e.ret);
                    alloc.* = .{
                        .id = @intCast(self.types.funcs.items.len),
                        .key = alloc.key,
                        .args = args,
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
                        .id = self.types.next_global,
                        .data = file.source,
                        .ty = self.types.makeSlice(file.source.len, .u8),
                    };
                    self.types.next_global += 1;
                }
                self.queue(.{ .Global = alloc });
                return .mkp(alloc.ty, self.bl.addGlobalAddr(alloc.id));
            },
        },
        .Directive => |e| {
            const eql = std.mem.eql;
            const name = ast.tokenSrc(e.pos.index);
            const args = ast.exprs.view(e.args);

            const utils = enum {
                fn reportInferrence(cg: *Codegen, exr: anytype, ty: []const u8, dir_name: []const u8) void {
                    cg.report(exr, "type can not be inferred from the context, use `@as(<{s}>, {s}(...))`", .{ ty, dir_name });
                }

                fn assertArgs(cg: *Codegen, exr: anytype, got: []const Ast.Id, comptime expected: []const u8) bool {
                    const min_expected_args = comptime std.mem.count(u8, expected, ",") + @intFromBool(expected.len != 0);
                    const varargs = comptime std.mem.endsWith(u8, expected, "..");
                    if (got.len < min_expected_args or (!varargs and got.len > min_expected_args)) {
                        const range = if (varargs) "at least " else "";
                        cg.report(
                            exr,
                            "directive takes {s}{} arguments, got {} (" ++ expected ++ ")",
                            .{ range, min_expected_args, got.len },
                        );
                        return true;
                    }
                    return false;
                }
            };

            if (eql(u8, name, "@CurrentScope")) {
                if (utils.assertArgs(self, expr, args, "")) return .never;
                return self.emitTyConst(self.parent_scope.perm());
            } else if (eql(u8, name, "@TypeOf")) {
                if (utils.assertArgs(self, expr, args, "<ty>")) return .never;
                const ty = self.types.ct.jitExpr("", .{ .Tmp = self }, .{}, args[0]).?[1];
                return self.emitTyConst(ty);
            } else if (eql(u8, name, "@int_cast")) {
                if (utils.assertArgs(self, expr, args, "<expr>")) return .never;

                const ret: Types.Id = ctx.ty orelse {
                    utils.reportInferrence(self, expr, "int-ty", name);
                    return .never;
                };

                if (!ret.isInteger()) {
                    self.report(expr, "inferred type must be an integer, {} is not", .{ret});
                    return .never;
                }

                var oper = self.emit(.{}, args[0]);

                if (!oper.ty.isInteger()) {
                    self.report(args[0], "expeced integer, {} is not", .{oper.ty});
                    return .never;
                }

                self.ensureLoaded(&oper);

                return .mkv(ret, self.bl.addUnOp(.ired, self.abi.categorize(ret, self.types).ByValue, oper.id.Value));
            } else if (eql(u8, name, "@bit_cast")) {
                if (utils.assertArgs(self, expr, args, "<expr>")) return .never;

                const ret: Types.Id = ctx.ty orelse {
                    utils.reportInferrence(self, expr, "ty", name);
                    return .never;
                };

                var oper = self.emit(.{}, args[0]);

                if (oper.ty.size(self.types) != ret.size(self.types)) {
                    self.report(
                        args[0],
                        "cant bitcast from {} to {} because sizes are not equal ({} != {})",
                        .{ oper.ty, ret, oper.ty.size(self.types), ret.size(self.types) },
                    );
                    return .never;
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
            } else if (eql(u8, name, "@ChildOf")) {
                if (utils.assertArgs(self, expr, args, "<ty>")) return .never;
                const ty = self.resolveAnonTy(args[0]);
                const child = ty.child(self.types) orelse {
                    self.report(args[0], "directive only work on pointer types and slices, {} is not", .{ty});
                    return .never;
                };
                return self.emitTyConst(child);
            } else if (eql(u8, name, "@kind_of")) {
                if (utils.assertArgs(self, expr, args, "<ty>")) return .never;
                const len = self.resolveAnonTy(args[0]);
                return .mkv(.uint, self.bl.addIntImm(.int, @intFromEnum(len.data())));
            } else if (eql(u8, name, "@len_of")) {
                if (utils.assertArgs(self, expr, args, "<ty>")) return .never;
                const ty = self.resolveAnonTy(args[0]);
                const len = ty.len(self.types) orelse {
                    self.report(args[0], "directive only works on structs and arrays, {} is not", .{ty});
                    return .never;
                };
                return .mkv(.uint, self.bl.addIntImm(.int, @bitCast(len)));
            } else if (eql(u8, name, "@align_of")) {
                if (utils.assertArgs(self, expr, args, "<ty>")) return .never;
                return .mkv(.uint, self.bl.addIntImm(.int, @bitCast(self.resolveAnonTy(args[0]).alignment(self.types))));
            } else if (eql(u8, name, "@size_of")) {
                if (utils.assertArgs(self, expr, args, "<ty>")) return .never;
                return .mkv(.uint, self.bl.addIntImm(.int, @bitCast(self.resolveAnonTy(args[0]).size(self.types))));
            } else if (eql(u8, name, "@ecall")) {
                if (utils.assertArgs(self, expr, args, "<expr>..")) return .never;
                var tmp = root.Arena.scrath(null);
                defer tmp.deinit();

                const ret = ctx.ty orelse {
                    utils.reportInferrence(self, expr, "ty", name);
                    return .never;
                };

                const arg_nodes = tmp.arena.alloc(Value, args.len);
                for (args, arg_nodes) |arg, *slot| {
                    slot.* = self.emit(.{}, arg);
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
            } else if (eql(u8, name, "@as")) {
                if (utils.assertArgs(self, expr, args, "<ty>, <expr>")) return .never;
                const ty = self.resolveAnonTy(args[0]);
                return self.emitTyped(ctx, ty, args[1]);
            } else if (eql(u8, name, "@error")) {
                if (utils.assertArgs(self, expr, args, "<ty/string>..")) return .never;
                var tmp = root.Arena.scrath(null);
                defer tmp.deinit();

                var msg = std.ArrayList(u8).init(tmp.arena.allocator());
                for (args) |arg| switch (ast.exprs.get(arg)) {
                    .String => |s| {
                        msg.appendSlice(ast.source[s.pos.index + 1 .. s.end - 1]) catch unreachable;
                    },
                    else => {
                        var value = self.emit(.{}, arg);
                        if (value.ty == .type) {
                            self.ensureLoaded(&value);
                            msg.writer().print("{}", .{self.unwrapTyConst(value.id.Value).fmt(self.types)}) catch unreachable;
                        } else {
                            unreachable;
                        }
                    },
                };

                self.report(expr, "{s}", .{msg.items});
                return .never;
            } else std.debug.panic("unhandled directive {s}", .{name});
        },
        else => std.debug.panic("{any}\n", .{ast.exprs.get(expr)}),
    }
}
