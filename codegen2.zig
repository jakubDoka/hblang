gpa: std.mem.Allocator,
files: []const Ast,
tmp: struct {
    todo: Alu(Ty) = .{},
    scratch: Alu(Ty) = .{},
    variables: Alu(Value) = .{},
    values: Alu(Instr.Id) = .{},
    loops: Alu(Loop) = .{},
    loop_breaks: Alu(Cfg.Id) = .{},
} = .{},
ctx: struct {
    structs: Alu(Struct) = .{},
    funcs: Alu(Func) = .{},
    allocated: Alu(Ty) = .{},
    computed: Ahmu(Symbol, Ty) = .{},
} = .{},
scope: struct {
    ret: Ty = undefined,
    is_else: bool = false,
    entry: ?Cfg.Id = null,
    returning: ?Cfg.Id = null,
} = .{},
out: struct {
    store: Ir = .{},
    errors: Alu(u8) = .{},
} = .{},

const std = @import("std");
const Alu = std.ArrayListUnmanaged;
const Ahmu = std.AutoHashMapUnmanaged;
const root = @import("root.zig");
const isa = @import("isa.zig");
const codegen = @import("codegen.zig");
const Vm = @import("vm.zig");
const Ast = @import("parser.zig");
const Lexer = @import("lexer.zig");
const HbvmCg = @import("codegen/hbvm.zig");

pub const Ty = codegen.Ty;
pub const Namespace = codegen.Namespace;
pub const Symbol = codegen.Symbol;
pub const Struct = codegen.Struct;
pub const Tuple = codegen.Tuple;
pub const File = codegen.File;
pub const Size = codegen.Size;

pub const testFmt = codegen.testFmt;
pub const runDiff = codegen.runDiff;
pub const buty = codegen.buty;

const Codegen = @This();

pub const Error = error{ Return, LoopControl, NoRet, TooLongTuple } || std.mem.Allocator.Error;

const root_file = 0;

pub const CfgKind = enum {
    Void,
    Decl,
    Call,
    Goto,
    If,
    Ret,
};

pub const Cfg = union(CfgKind) {
    Void,
    Decl: struct {
        value: Instr.Id,
        goto: Id = undefined,
    },
    Call: struct {
        func: Ty,
        args: Instr.Slice,
        goto: Id = undefined,
    },
    Goto: Goto,
    If: struct {
        cond: Instr.Id,
        then: Goto = .{},
        else_: Goto = undefined,
    },
    Ret: Instr.Id,

    pub const Id = root.EnumId(CfgKind);

    pub const Goto = struct {
        to: Id = Id.zeroSized(.Void),
        args: Instr.Slice = undefined,
    };
};

pub const InstrKind = enum {
    Void,
    Arg,
    BlockArg,
    Li64,
    @"+64",
    @"-64",
    @"*64",
    @"/64",
    @"<=64",
    @"==64",
    Call,
};

pub const Instr = union(InstrKind) {
    Void,
    Arg,
    BlockArg: struct {
        block: Cfg.Id,
        index: u32,
    },
    Li64: u64,
    @"+64": BinOp,
    @"-64": BinOp,
    @"*64": BinOp,
    @"/64": BinOp,
    @"<=64": BinOp,
    @"==64": BinOp,
    Call: Cfg.Id,

    pub const Id = root.EnumId(InstrKind);
    pub const Slice = packed struct(u32) {
        base: u25 = 0,
        len: u7 = 0,
    };

    const BinOp = struct { lhs: Id, rhs: Id };
};

pub const Ir = struct {
    instrs: root.TaglessEnumStore(Instr.Id, Instr) = .{},
    instr_rcs: Alu(u16) = .{},
    args: Alu(Instr.Id) = .{},
    cfg: root.TaglessEnumStore(Cfg.Id, Cfg) = .{},
    dom_tree: Alu(Cfg.Id) = .{},
    cfg_rcs: Alu(u16) = .{},

    pub fn view(self: *const Ir, args: Instr.Slice) []const Instr.Id {
        return self.args.items[args.base..][0..args.len];
    }

    fn makeArgs(self: *Ir, len: usize) Instr.Slice {
        return .{ .base = @intCast(self.args.items.len - len), .len = @intCast(len) };
    }

    fn allocSlice(self: *Ir, gpa: std.mem.Allocator, slice: []const Instr.Id) !Instr.Slice {
        const base = self.args.items.len;
        try self.args.appendSlice(gpa, slice);
        return .{ .base = @intCast(base), .len = @intCast(slice.len) };
    }

    pub fn deinit(self: *Ir, gpa: std.mem.Allocator) void {
        inline for (std.meta.fields(Ir)) |field| {
            @field(self, field.name).deinit(gpa);
        }
    }

    pub fn computeDomTree(self: *Ir, gpa: std.mem.Allocator, entry: Cfg.Id) !void {
        try self.computeCfgRcs(gpa, entry);
        try self.dom_tree.resize(gpa, self.cfg.store.items.len);
        for (self.dom_tree.items) |*dom| dom.* = Cfg.Id.compact(.Void, self.cfg_rcs.items.len);
        self.computeDomTreeRec(entry);
    }

    pub fn display(self: *Ir, gpa: std.mem.Allocator, entry: Cfg.Id, out: *std.ArrayList(u8)) !void {
        try self.computeDomTree(gpa, entry);

        var bd = struct {
            out: *std.ArrayList(u8),
            seen: std.ArrayListUnmanaged(Instr.Id) = .{},
            ir: *const Ir,

            pub fn addBlock(s: *@This(), block: Cfg.Id) !void {
                try s.out.writer().print("b{d}:\n", .{block.index});
                switch (s.ir.cfg.get(block)) {
                    .Void => {},
                    .Ret => |r| {
                        try s.displayInstr(r);
                        try s.out.writer().print("\tret v{d}", .{r.index});
                    },
                    .Decl => |d| {
                        try s.displayInstr(d.value);
                        try s.out.writer().print("\tdecl v{d} godo b{d}", .{ d.value.index, d.goto.index });
                    },
                    .Goto => |g| {
                        for (s.ir.view(g.args)) |arg| try s.displayInstr(arg);
                        try s.out.writer().print("\tgoto b{d}", .{g.to.index});
                        for (s.ir.view(g.args)) |arg| try s.out.writer().print(", v{d}", .{arg.index});
                    },
                    .If => |i| {
                        try s.displayInstr(i.cond);
                        try s.out.writer().print(
                            "\tif v{d} b{d} b{d}",
                            .{ i.cond.index, i.then.to.index, i.else_.to.index },
                        );
                    },
                    .Call => |c| {
                        for (s.ir.view(c.args)) |arg| try s.displayInstr(arg);
                        try s.out.writer().print("\tcall :f{d}", .{c.func.index});
                        for (s.ir.view(c.args)) |arg| try s.out.writer().print(", v{d}", .{arg.index});
                    },
                }
                try s.out.appendSlice("\n\n");
            }

            pub fn displayInstr(s: *@This(), instr: Instr.Id) !void {
                if (std.mem.indexOfScalar(u32, @ptrCast(s.seen.items), @bitCast(instr)) != null) return;
                try s.seen.append(s.out.allocator, instr);

                switch (s.ir.instrs.get(instr)) {
                    .Void => {},
                    .Arg => try s.out.writer().print("\tv{d} = arg {d}\n", .{ instr.index, instr.index }),
                    .BlockArg => |b| try s.out.writer().print("\tv{d} = arg b{d} {d}\n", .{ instr.index, b.block.index, b.index }),
                    inline .Li64 => |l, t| try s.out.writer().print(
                        "\tv{d} = {s} {d}\n",
                        .{ instr.index, @tagName(t), l },
                    ),
                    .Call => |c| try s.out.writer().print("\tv{d} = ret b{d}\n", .{ instr.index, c.index }),
                    inline else => |v, t| {
                        try s.displayInstr(v.lhs);
                        try s.displayInstr(v.rhs);
                        try s.out.writer().print(
                            "\tv{d} = {s} v{d}, v{d}\n",
                            .{ instr.index, @tagName(t), v.lhs.index, v.rhs.index },
                        );
                    },
                }
            }
        }{ .out = out, .ir = self };
        defer bd.seen.deinit(out.allocator);
        try self.traverseBlocks(entry, &bd);
    }

    // for child in graph[node]:
    //     if brefs[child] != -1: return
    //     if ref_counts[child] > 1:
    //         cursor = node
    //         while len(graph[brefs[cursor]]) == 1:
    //             cursor = brefs[cursor]
    //         brefs[child] = brefs[cursor]
    //     else: brefs[child] = node
    //     dfs(child)
    pub fn computeDomTreeRec(self: *Ir, id: Cfg.Id) void {
        var buf: [2]Cfg.Id = undefined;
        for (self.nextCfgNodes(id, &buf)) |child| {
            if (self.dom_tree.items[id.index].index != self.cfg_rcs.items.len) return;
            if (self.cfg_rcs.items[id.index] > 1) {
                var cursor = id;
                var tbuf: [2]Cfg.Id = undefined;
                while (self.nextCfgNodes(self.dom_tree.items[cursor.index], &tbuf).len == 1)
                    cursor = self.dom_tree.items[cursor.index];
                self.dom_tree.items[child.index] = self.dom_tree.items[cursor.index];
            } else self.dom_tree.items[child.index] = id;
        }
    }

    pub fn traverseBlocks(self: *Ir, entry: Cfg.Id, ctx: anytype) !void {
        std.debug.assert(self.cfg_rcs.items.len == self.cfg.store.items.len);
        std.debug.assert(self.dom_tree.items.len == self.cfg.store.items.len);
        try self.traverseBlocksRec(entry, ctx);
    }

    // if seen[node]: return
    // seen[node] = True
    // order.append(node)

    // for child in graph[node]:
    //     if dominators[child] != node and ref_counts[child] != 1:
    //         ref_counts[child] -= 1
    //         return
    //     dfs(child)
    fn traverseBlocksRec(self: *Ir, id: Cfg.Id, ctx: anytype) !void {
        try ctx.addBlock(id);
        var buf: [2]Cfg.Id = undefined;
        for (self.nextCfgNodes(id, &buf)) |child| {
            if (self.dom_tree.items[child.index].index != id.index and
                self.cfg_rcs.items[child.index] != 1)
            {
                self.cfg_rcs.items[id.index] -= 1;
                return;
            }
            try self.traverseBlocksRec(child, ctx);
        }
    }

    pub fn computeCfgRcs(self: *Ir, gpa: std.mem.Allocator, entry: Cfg.Id) !void {
        try self.cfg_rcs.resize(gpa, self.cfg.store.items.len);
        @memset(self.cfg_rcs.items, 0);
        self.computeCfgRcsRec(entry);
    }

    fn computeCfgRcsRec(self: *Ir, id: Cfg.Id) void {
        self.cfg_rcs.items[id.index] += 1;
        if (self.cfg_rcs.items[id.index] != 1) return;
        var buf: [2]Cfg.Id = undefined;
        for (self.nextCfgNodes(id, &buf)) |child| self.computeCfgRcsRec(child);
    }

    fn nextCfgNodes(self: *Ir, id: Cfg.Id, buf: *[2]Cfg.Id) []const Cfg.Id {
        return switch (self.cfg.get(id)) {
            .Void, .Ret => &.{},
            inline .Decl, .Call => |v| b: {
                buf[0] = v.goto;
                break :b buf[0..1];
            },
            .Goto => |goto| b: {
                buf[0] = goto.to;
                break :b buf[0..1];
            },
            .If => |ifNode| b: {
                buf.* = .{ ifNode.then.to, ifNode.else_.to };
                break :b buf;
            },
        };
    }
};

pub const Func = struct {
    file: File,
    args: Tuple,
    ret: Ty,
    decl: Ast.Id,
    entry: Cfg.Id = undefined,
    ir: Ir = undefined,
};

const Loop = struct {
    back: Cfg.Id,
    mutates: root.EnumSlice(Ast.Ident),
    break_base: u32,
};

const Value = struct {
    ty: Ty = buty(.void),
    id: Instr.Id = Instr.Id.zeroSized(.Void),
};

pub fn deinit(self: *Codegen) void {
    inline for (std.meta.fields(@TypeOf(self.tmp))) |field| {
        const f = &@field(self.tmp, field.name);
        if (f.items.len > 0) {
            std.debug.panic("temporary lefover in {s}\n", .{field.name});
        }
        f.deinit(self.gpa);
    }

    inline for (std.meta.fields(@TypeOf(self.ctx))) |field| {
        const f = &@field(self.ctx, field.name);
        f.deinit(self.gpa);
    }

    inline for (std.meta.fields(@TypeOf(self.out))) |field| {
        const f = &@field(self.out, field.name);
        f.deinit(self.gpa);
    }
}

pub fn generate(self: *Codegen) !void {
    _ = try self.findOrDeclare(Ast.Pos.init(0), root_file, "main");
    try self.generateFunc(0);
    try self.completeCallGraph();
}

fn completeCallGraph(self: *Codegen) !void {
    while (self.tmp.todo.popOrNull()) |ty| {
        switch (ty.tag()) {
            .func => try self.generateFunc(ty.index),
            else => |v| std.debug.panic("unhandled call graph type: {any}", .{v}),
        }
    }
}

fn generateFunc(self: *Codegen, id: usize) !void {
    var func = &self.ctx.funcs.items[id];
    const ast = self.files[func.file];
    self.scope = .{ .ret = func.ret };
    const decl = ast.exprs.getTyped(.Fn, func.decl).?;

    for (func.args.view(self.ctx.allocated.items), 0..) |arg_ty, i| {
        try self.tmp.variables.append(self.gpa, .{
            .ty = arg_ty,
            .id = Instr.Id.compact(.Arg, @intCast(i)),
        });
    }
    const last_return = try self.catchUnreachable(self.generateExpr(func.file, null, decl.body));
    self.ctx.funcs.items[id].entry = self.scope.entry orelse last_return;
    self.ctx.funcs.items[id].ir = self.out.store;
    self.out.store = .{};
    self.tmp.variables.items.len = 0;
}

fn catchUnreachable(self: *Codegen, res: anytype) Error!Cfg.Id {
    _ = res catch |e| switch (e) {
        error.Return, error.LoopControl => return self.scope.returning.?,
        else => return e,
    };

    return error.NoRet;
}

fn generateExpr(self: *Codegen, file: File, inferred: ?Ty, id: Ast.Id) Error!Value {
    const ast = self.files[file];
    const gi, const ty = switch (ast.exprs.get(id)) {
        .Void, .Comment => return .{},
        .Return => |ret| {
            try self.passControlFlow(try self.out.store.cfg.alloc(
                self.gpa,
                .Ret,
                (try self.generateExpr(file, self.scope.ret, ret.value)).id,
            ));
            return error.Return;
        },
        .Integer => |i| .{ Instr{ .Li64 = std.fmt.parseInt(u64, Lexer.peekStr(ast.source, i.index), 10) catch unreachable }, buty(.int) },
        .Block => |block| {
            for (ast.exprs.view(block.stmts)) |stmt| {
                _ = try self.generateExpr(file, null, stmt);
            }
            return .{};
        },
        .BinOp => |bo| return self.generateBinOp(file, bo, inferred),
        .Call => |call| {
            const called = ast.exprs.getTyped(.Ident, call.called).?;
            const func_id = try self.findOrDeclare(called.pos, file, called.id);
            std.debug.assert(func_id.tag() == .func);
            const func = self.ctx.funcs.items[func_id.index];

            for (ast.exprs.view(call.args), 0..) |arg, i| {
                const arg_ty = func.args.view(self.ctx.allocated.items)[i];
                const value = try self.generateExpr(file, arg_ty, arg);
                try self.tmp.values.append(self.gpa, value.id);
            }
            const base = self.tmp.values.items.len - ast.exprs.view(call.args).len;
            const args = try self.out.store.allocSlice(self.gpa, self.tmp.values.items[base..]);
            self.tmp.values.items.len = base;
            const cid = try self.out.store.cfg.alloc(self.gpa, .Call, .{ .args = args, .func = func_id });
            try self.passControlFlow(cid);
            const icid = try self.out.store.instrs.alloc(self.gpa, .Call, cid);
            return .{ .ty = func.ret, .id = icid };
        },
        .Ident => |i| return self.tmp.variables.items[i.id.index],
        .If => |i| {
            const cond = try self.generateExpr(file, buty(.bool), i.cond);
            const ifNode = try self.out.store.cfg.alloc(self.gpa, .If, .{ .cond = cond.id });
            try self.passControlFlow(ifNode);

            const join = try self.out.store.cfg.alloc(self.gpa, .Goto, .{});
            const thenReachable = try catchIfBranch(self.generateExpr(file, null, i.then));
            if (thenReachable) try self.passControlFlow(join);

            self.scope.returning = ifNode;
            const elseReachable = try catchIfBranch(self.generateExpr(file, null, i.else_));
            if (elseReachable) try self.passControlFlow(join);

            if (!thenReachable and !elseReachable) return error.Return;

            return .{};
        },
        .Loop => |l| {
            for (ast.exprs.view(l.mutates), 0..) |ident, i| {
                try self.out.store.args.append(self.gpa, self.tmp.variables.items[ident.index].id);
                self.tmp.variables.items[ident.index].id = try self.out.store.instrs.alloc(self.gpa, .BlockArg, .{
                    .block = self.out.store.cfg.nextId(.Goto, 1),
                    .index = @intCast(i),
                });
            }
            const back_args = self.out.store.makeArgs(l.mutates.len());

            const back = try self.out.store.cfg.alloc(self.gpa, .Goto, .{ .args = back_args });
            try self.tmp.loops.append(self.gpa, .{
                .back = back,
                .mutates = l.mutates,
                .break_base = @intCast(self.tmp.loop_breaks.items.len),
            });
            _ = try self.passControlFlow(back);

            const loopReachabe = try catchIfBranch(self.generateExpr(file, null, l.body));
            if (loopReachabe)
                try self.passControlFlow(try self.out.store.cfg.alloc(
                    self.gpa,
                    .Goto,
                    .{ .to = self.out.store.cfg.getTyped(.Goto, back).?.to, .args = .{} },
                ));

            const loop = self.tmp.loops.pop();
            const breaks = self.tmp.loop_breaks.items[loop.break_base..];
            self.tmp.loop_breaks.items.len = loop.break_base;
            if (breaks.len != 0) {
                const breaker = try self.out.store.cfg.alloc(self.gpa, .Goto, .{ .args = .{} });
                self.scope.returning = breaker;
                for (breaks) |break_id| {
                    self.out.store.cfg.getTypedPtr(.Goto, break_id).?.to = breaker;
                }
                return .{};
            } else {
                return error.Return;
            }
        },
        .Break => {
            std.debug.assert(self.tmp.loops.items.len != 0);
            const break_block = try self.out.store.cfg.alloc(self.gpa, .Goto, .{ .args = .{} });
            _ = try self.passControlFlow(break_block);
            try self.tmp.loop_breaks.append(self.gpa, break_block);
            return error.LoopControl;
        },
        .Continue => {
            const loop = self.tmp.loops.getLast();
            for (ast.exprs.view(loop.mutates)) |ident| {
                try self.out.store.args.append(self.gpa, self.tmp.variables.items[ident.index].id);
            }
            const back_args = self.out.store.makeArgs(loop.mutates.len());
            _ = try self.passControlFlow(try self.out.store.cfg.alloc(
                self.gpa,
                .Goto,
                .{ .to = self.out.store.cfg.getTyped(.Goto, loop.back).?.to, .args = back_args },
            ));
            return error.LoopControl;
        },
        else => |v| std.debug.panic("unhandled expr: {any}", .{v}),
    };
    return .{ .ty = ty, .id = try self.out.store.instrs.allocDyn(self.gpa, gi) };
}

fn generateBinOp(self: *Codegen, file: File, bo: Ast.Payload(.BinOp), inferred: ?Ty) !Value {
    const ast = self.files[file];
    switch (bo.op) {
        .@":=" => {
            _ = ast.exprs.getTyped(.Ident, bo.lhs).?;
            var value = try self.generateExpr(file, inferred, bo.rhs);
            const cfg = try self.out.store.cfg.alloc(
                self.gpa,
                .Decl,
                .{ .value = value.id },
            );
            try self.passControlFlow(cfg);
            value.id = try self.out.store.instrs.alloc(self.gpa, .Call, cfg);
            try self.tmp.variables.append(self.gpa, value);
            return .{};
        },
        .@"=" => {
            const name = ast.exprs.getTyped(.Ident, bo.lhs).?;
            const value = try self.generateExpr(file, inferred, bo.rhs);
            self.tmp.variables.items[name.id.index] = value;
            return .{};
        },
        inline .@"+=", .@"-=" => |op| {
            const name = ast.exprs.getTyped(.Ident, bo.lhs).?;
            const nop = .{ .lhs = bo.lhs, .op = op.assOp(), .rhs = bo.rhs };
            const value = try self.generateBinOp(file, nop, inferred);
            self.tmp.variables.items[name.id.index] = value;
            return .{};
        },
        inline .@"+", .@"-", .@"*", .@"/", .@"<=", .@"==" => |op| {
            const lhs = try self.generateExpr(file, inferred, bo.lhs);
            const rhs = try self.generateExpr(file, lhs.ty, bo.rhs);
            const body = .{ .lhs = lhs.id, .rhs = rhs.id };
            return .{
                .id = try self.out.store.instrs.allocDyn(
                    self.gpa,
                    @unionInit(Instr, @tagName(op) ++ "64", body),
                ),
                .ty = rhs.ty,
            };
        },
        else => std.debug.panic("unhandled binop: {s}", .{@tagName(bo.op)}),
    }
}

fn catchIfBranch(res: anytype) !bool {
    _ = res catch |e| switch (e) {
        error.Return, error.LoopControl => return false,
        else => return e,
    };

    return true;
}

fn passControlFlow(self: *Codegen, id: Cfg.Id) !void {
    self.scope.entry = self.scope.entry orelse id;
    if (self.scope.returning) |retr| switch (retr.tag()) {
        .If => {
            const p = self.out.store.cfg.getTypedPtr(.If, retr).?;
            if (p.then.to.tag() == .Void) p.then.to = id else p.else_.to = id;
        },
        .Goto => {
            const p = self.out.store.cfg.getTypedPtr(.Goto, retr).?;
            p.to = id;
        },
        inline else => |t| {
            const Payload = std.meta.TagPayload(Cfg, t);
            if (@typeInfo(Payload) != .Struct or !@hasField(Payload, "goto")) std.debug.panic("wat {s}", .{@typeName(Payload)});
            std.debug.assert(!std.meta.eql(retr, id));
            self.out.store.cfg.getTypedPtr(t, retr).?.goto = id;
        },
    };
    self.scope.returning = id;
}

fn findOrDeclare(self: *Codegen, pos: Ast.Pos, file: File, query: anytype) Error!Ty {
    const ast = self.files[file];

    const msg = "Could not find declaration for {s}";
    const decl, const ident = if (@TypeOf(query) == Ast.Ident) b: {
        const decl = ast.decls[query.index];
        const expr = ast.exprs.getTyped(.BinOp, decl.expr).?;
        std.debug.assert(expr.op == .@":=");
        break :b .{ expr.rhs, decl.name };
    } else for (ast.exprs.view(ast.items)) |id| {
        const expr = ast.exprs.getTyped(.BinOp, id) orelse continue;
        std.debug.assert(expr.op == .@":=");
        const name = ast.exprs.getTyped(.Ident, expr.lhs).?;

        if (!switch (@TypeOf(query)) {
            Ast.Pos => query.index == name.id.index,
            else => Ast.cmp(name.pos.index, ast.source, query),
        }) continue;

        break .{ expr.rhs, name.id };
    } else return try self.report(buty(.void), file, pos, msg, .{
        switch (@TypeOf(query)) {
            Ast.Ident => Lexer.peekStr(ast.source, pos.index),
            else => query,
        },
    });

    const sym = Symbol{ .ns = Namespace.init(.file, file), .item = @bitCast(ident) };
    if (self.ctx.computed.get(sym)) |id| return id;

    switch (ast.exprs.get(decl)) {
        .Fn => |f| {
            const func = Func{
                .file = file,
                .decl = decl,
                .args = try self.makeTuple(.Arg, file, f.args),
                .ret = try self.resolveTy(file, f.ret),
            };
            const id = Ty.init(.func, self.ctx.funcs.items.len);
            try self.ctx.funcs.append(self.gpa, func);
            if (@TypeOf(query) == Ast.Ident or !std.mem.eql(u8, query, "main"))
                try self.tmp.todo.append(self.gpa, id);
            try self.ctx.computed.put(self.gpa, sym, id);
            return id;
        },
        .Struct => |s| {
            const stru = Struct{
                .file = file,
                .field_names = s.fields,
                .field_types = try self.makeTuple(.CtorField, file, s.fields),
            };
            const id = Ty.init(.@"struct", self.ctx.structs.items.len);
            try self.ctx.structs.append(self.gpa, stru);
            return id;
        },
        else => |v| std.debug.panic("unhandled declaration: {any}", .{v}),
    }
}

fn makeTuple(self: *Codegen, comptime kind: Ast.Kind, file: File, args: Ast.Slice) !Tuple {
    const ast = self.files[file];
    const arg_exprs = ast.exprs.view(args);
    for (arg_exprs) |id| {
        const arg = ast.exprs.getTyped(kind, id).?;
        const typ = switch (kind) {
            .Arg => arg.ty,
            .CtorField => arg.value,
            else => @compileError("wat"),
        };
        try self.tmp.scratch.append(self.gpa, try self.resolveTy(file, typ));
    }

    var prev_len = self.tmp.scratch.items.len - arg_exprs.len;
    try self.ctx.allocated.appendSlice(self.gpa, self.tmp.scratch.items[prev_len..]);
    self.tmp.scratch.items.len = prev_len;
    prev_len = self.ctx.allocated.items.len - arg_exprs.len;

    const raw_view: *[]const Ty.Repr = @ptrCast(&self.ctx.allocated.items);
    const allocate_types = raw_view.*[prev_len..];
    std.debug.assert(allocate_types.len == ast.exprs.view(args).len);
    const index = std.mem.indexOf(Ty.Repr, raw_view.*, allocate_types) orelse prev_len;
    raw_view.len = @max(prev_len, index + allocate_types.len);
    return try Tuple.init(index, allocate_types.len);
}

fn resolveTy(self: *Codegen, file: File, ty: Ast.Id) !Ty {
    const ast = self.files[file];
    return switch (ast.exprs.get(ty)) {
        .Buty => |b| Ty.init(.builtin, @intFromEnum(b.bt)),
        .UnOp => |u| try self.makePtr(try self.resolveTy(file, u.oper)),
        .Ident => |i| try self.findOrDeclare(i.pos, file, i.id),
        else => |v| std.debug.panic("unhandled type expression: {any}", .{v}),
    };
}

fn makePtr(self: *Codegen, ty: Ty) !Ty {
    if (std.mem.indexOfScalar(u32, @ptrCast(self.ctx.allocated.items), @bitCast(ty))) |idx|
        return Ty.init(.pointer, idx);
    try self.ctx.allocated.append(self.gpa, ty);
    return Ty.init(.pointer, self.ctx.allocated.items.len - 1);
}

pub fn sizeOf(self: *Codegen, ty: Ty) Size {
    return switch (ty.tag()) {
        .builtin => switch (@as(Lexer.Lexeme, @enumFromInt(ty.index))) {
            .void => 0,
            .int => @sizeOf(u64),
            else => std.debug.panic("unhandled builtin type: {s}", .{@tagName(ty.tag())}),
        },
        .pointer => @sizeOf(u64),
        .@"struct" => {
            const stru = self.ctx.structs.items[ty.index];
            var size: Size = 0;
            for (stru.field_types.view(self.ctx.allocated.items)) |fty| {
                size = root.alignTo(size, self.alignOf(fty));
                size += self.sizeOf(fty);
            }
            return size;
        },
        else => |v| std.debug.panic("unhandled type: {s}", .{@tagName(v)}),
    };
}

pub fn alignOf(self: *Codegen, ty: Ty) Size {
    return switch (ty.tag()) {
        .@"struct" => {
            const stru = self.ctx.structs.items[ty.index];
            var alignment: Size = 1;
            for (stru.field_types.view(self.ctx.allocated.items)) |fty| {
                alignment = @max(alignment, self.alignOf(fty));
            }
            return alignment;
        },
        else => self.sizeOf(ty),
    };
}

fn report(self: *Codegen, ph: anytype, file: u32, origin: anytype, comptime fmt: []const u8, args: anytype) !@TypeOf(ph) {
    const pos = self.files[file].posOf(origin);
    const line, const col = self.files[file].lineCol(pos.index);
    try self.out.errors.writer(self.gpa).print(
        "{s}:{d}:{d}: " ++ fmt,
        .{ self.files[file].path, line, col } ++ args,
    );
    return ph;
}

fn runTest(comptime name: []const u8) !void {
    const code = root.findReadmeSnippet(name) catch unreachable;
    try testFmt(name, name ++ ".hb", code);
    try testCodegen(name, code);
}

fn testCodegen(comptime name: []const u8, source: []const u8) !void {
    const gpa = std.testing.allocator;

    var ast = try Ast.init(name ++ ".hb", source, gpa);
    defer ast.deinit(gpa);

    const files = [_]Ast{ast};

    var cg = Codegen{
        .gpa = gpa,
        .files = &files,
    };
    defer cg.deinit();
    try cg.generate();

    var output = std.ArrayList(u8).init(gpa);
    defer output.deinit();

    var code = std.ArrayList(u8).init(gpa);
    defer code.deinit();

    var vm_codegen = HbvmCg{ .gpa = gpa, .cg = &cg, .out = &code };
    defer vm_codegen.deinit();
    try output.writer().print("\nIR\n", .{});
    for (cg.ctx.funcs.items, 0..) |*f, id| {
        try f.ir.display(gpa, f.entry, &output);
        try vm_codegen.generateFunc(id);
    }
    vm_codegen.finalize();

    const stack = try gpa.alloc(u8, 1024 * 1024);
    defer gpa.free(stack);
    var vm = Vm{};
    vm.regs[HbvmCg.Regs.stack_ptr] = @intFromPtr(stack.ptr[stack.len..]);

    const not_terminated, const exec_log = if (cg.out.errors.items.len != 0) b: {
        try output.appendSlice("\nERRORS\n");
        try output.appendSlice(cg.out.errors.items);
        break :b .{ {}, std.ArrayList(u8).init(gpa) };
    } else b: {
        try output.writer().print("\nDISASM\n", .{});
        try isa.disasm(code.items, &output, false);

        var exec_log = std.ArrayList(u8).init(gpa);
        errdefer exec_log.deinit();
        try exec_log.writer().print("EXECUTION\n", .{});
        vm.fuel = 2000;
        vm.ip = @intFromPtr(code.items.ptr);
        vm.log_buffer = &exec_log;
        var ctx = Vm.UnsafeCtx{};
        const ntrm = std.testing.expectEqual(.tx, vm.run(&ctx));

        try output.writer().print("\nREGISTERS\n", .{});
        try output.writer().print("$1: {d}\n", .{vm.regs[1]});

        break :b .{ ntrm, exec_log };
    };
    defer exec_log.deinit();

    const old, const new = .{ "tests/" ++ name ++ ".temp2.old.txt", name ++ ".temp2.new.txt" };

    const update = std.process.getEnvVarOwned(gpa, "PT_UPDATE") catch "";
    defer gpa.free(update);
    if (update.len > 1) {
        try std.fs.cwd().writeFile(.{
            .sub_path = old,
            .data = std.mem.trim(u8, output.items, "\n"),
        });

        not_terminated catch {
            std.debug.print("\n{s}\n", .{exec_log.items});
        };
    } else {
        try std.fs.cwd().writeFile(.{
            .sub_path = new,
            .data = std.mem.trim(u8, output.items, "\n"),
        });
        const err = runDiff(gpa, old, new);
        try std.fs.cwd().deleteFile(new);

        not_terminated catch {
            std.debug.print("\n{s}\n", .{exec_log.items});
            std.debug.print("\n{s}\n", .{output.items});
        };

        err catch {
            std.debug.print("\n{s}\n", .{exec_log.items});
            std.debug.print("\n{s}\n", .{output.items});
        };

        try err;
    }

    try not_terminated;
}

test "main-fn" {
    try runTest("main-fn");
}

test "arithmetic" {
    try runTest("arithmetic");
}

test "functions" {
    try runTest("functions");
}

test "comments" {
    try runTest("comments");
}

test "if-statements" {
    try runTest("if-statements");
}

test "variables" {
    try runTest("variables");
}

test "loops" {
    try runTest("loops");
}
