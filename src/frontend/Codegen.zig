const std = @import("std");

const root = @import("hb");
const graph = root.backend.graph;
const utils = root.utils;
const static_anal = root.backend.static_anal;
const Builder = root.backend.Builder;
const Ast = root.frontend.Ast;
const Arena = utils.Arena;
const Comptime = root.frontend.Comptime;
const Lexer = root.frontend.Lexer;
const Types = root.frontend.Types;
const HbvmGen = root.hbvm.HbvmGen;
const Vm = root.hbvm.Vm;
const TySlice = root.frontend.types.Slice;
const tys = root.frontend.types;
const Expr = Ast.Store.TagPayload;

bl: Builder,
types: *Types,
target: Types.Target,
abi: Types.Abi,
only_inference: bool = false,
partial_eval: bool = false,
name: []const u8 = undefined,
parent_scope: Scope = undefined,
ast: *const Ast = undefined,
struct_ret_ptr: ?*Node = undefined,
scope: std.ArrayListUnmanaged(ScopeEntry) = undefined,
loops: std.ArrayListUnmanaged(Loop) = undefined,
defers: std.ArrayListUnmanaged(Ast.Id) = undefined,
ret: Types.Id = undefined,
errored: bool = undefined,

const Func = graph.Func(Builder);
const Node = Builder.BuildNode;
const DataType = Builder.DataType;
const Codegen = @This();

pub const EmitError = error{ Never, Unreachable };

pub const Sloc = struct {
    file: Types.File,
    pos: Ast.Pos,
};

const Loop = struct {
    id: Ast.Ident,
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
    Func: utils.EntId(root.frontend.types.Func),
    Global: utils.EntId(root.frontend.types.Global),
};

const ScopeEntry = struct {
    name: Ast.Ident,
    ty: Types.Id,
};

pub const Value = struct {
    id: Mode = .Imaginary,
    ty: Types.Id = .void,

    pub const Mode = union(enum) {
        Imaginary,
        Value: *Node,
        Pointer: *Node,
    };

    inline fn mkv(ty: Types.Id, oid: ?*Node) Value {
        return .{ .ty = ty, .id = if (oid) |id| .{ .Value = id } else .Imaginary };
    }

    inline fn mkp(ty: Types.Id, id: *Node) Value {
        return .{ .ty = ty, .id = .{ .Pointer = id } };
    }

    pub fn getValue(value: *Value, sloc: graph.Sloc, self: *Codegen) *Node {
        if (value.id == .Pointer) {
            const cata = self.abiCata(value.ty);

            if (cata.ByValue.size() > value.ty.size(self.types)) {
                var val: ?*Node = null;
                var loader = graph.DataType.i64;
                var offset: u64 = 0;
                while (offset < value.ty.size(self.types)) {
                    while (loader.size() + offset > value.ty.size(self.types)) {
                        loader = @enumFromInt(@intFromEnum(loader) - 1);
                    }

                    const loaded = self.bl.addFieldLoad(sloc, value.id.Pointer, @intCast(offset), loader);
                    const extended = self.bl.addUnOp(sloc, .uext, cata.ByValue, loaded);
                    const shifted = self.bl.addBinOp(sloc, .ishl, cata.ByValue, extended, self.bl.addIntImm(sloc, .i64, @intCast(offset * 8)));
                    val = if (val) |v| self.bl.addBinOp(sloc, .bor, cata.ByValue, v, shifted) else shifted;
                    offset += loader.size();
                }

                value.id = .{ .Value = val.? };
            } else {
                value.id = .{ .Value = self.bl.addLoad(
                    sloc,
                    value.id.Pointer,
                    cata.ByValue,
                ) };
            }
        }
        return value.id.Value;
    }
};

pub const Scope = union(enum) {
    Tmp: *Codegen,
    Perm: Types.Id,

    pub fn init(td: Types.Data) Scope {
        return .{ .Perm = .init(td) };
    }

    pub fn firstType(self: Scope, types: *Types) Types.Id {
        return switch (self) {
            .Perm => |p| p.firstType(types),
            .Tmp => |t| t.parent_scope.firstType(types),
        };
    }

    pub fn parent(self: Scope, types: *Types) Scope {
        return switch (self) {
            .Perm => |p| .{ .Perm = p.parent(types) },
            .Tmp => |t| t.parent_scope,
        };
    }

    pub fn perm(self: Scope, types: *Types) Types.Id {
        return switch (self) {
            .Perm => |p| p.perm(types),
            .Tmp => |t| t.parent_scope.perm(types),
        };
    }

    pub fn empty(self: Scope) bool {
        return switch (self) {
            .Perm => |p| p == .void,
            .Tmp => false,
        };
    }

    pub fn file(self: Scope, types: *Types) Types.File {
        return switch (self) {
            .Perm => |p| p.file(types).?,
            .Tmp => |t| t.parent_scope.file(types),
        };
    }

    pub fn index(self: Scope, types: *Types) ?*Ast.Index {
        return switch (self) {
            .Perm => |p| p.index(types),
            .Tmp => |t| t.parent_scope.index(types),
        };
    }

    pub fn items(self: Scope, ast: *const Ast, types: *Types) Ast.Slice {
        return switch (self) {
            .Perm => |p| p.items(ast, types),
            .Tmp => |t| t.parent_scope.items(ast, types),
        };
    }

    pub fn findCapture(self: Scope, ast: Ast.Pos, id: Ast.Ident, types: *Types, slot: *Types.Scope.Capture) ?*const Types.Scope.Capture {
        return switch (self) {
            .Perm => |p| p.findCapture(id, types),
            .Tmp => |t| for (t.scope.items, 0..) |se, i| {
                if (se.name == id) {
                    var value = Value.mkp(se.ty, t.bl.getPinValue(i));
                    slot.* = .{
                        .ty = se.ty,
                        .id = .fromIdent(id),
                        .value = t.partialEvalLow(t.posOf(ast).index, &value, true) catch 0,
                    };
                    return slot;
                }
            } else null,
        };
    }
};

pub const Ctx = struct {
    loc: ?*Node = null,
    ty: ?Types.Id = null,
    in_if_cond: bool = false,

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

pub fn init(
    scratch: *utils.Arena,
    types: *Types,
    target: Types.Target,
    abi: Types.Abi,
) *Codegen {
    const res = scratch.create(Codegen);
    res.* = .{
        .types = types,
        .abi = abi,
        .target = target,
        .bl = .init(types.pool.allocator()),
    };
    return res;
}

/// returns true when errored
pub fn emitReachable(
    scrath: *utils.Arena,
    types: *Types,
    abi: Types.Abi,
    backend: root.backend.Machine,
    optimizations: root.backend.Machine.OptOptions,
    has_main: bool,
    log_opts: struct {
        colors: std.io.tty.Config = .no_color,
        output: std.io.AnyWriter = std.io.null_writer.any(),
        verbose: bool = false,
    },
) bool {
    errdefer unreachable;

    var root_tmp = utils.Arena.scrath(scrath);
    defer root_tmp.deinit();

    const codegen = Codegen.init(root_tmp.arena, types, .runtime, abi);
    defer codegen.deinit();

    const exports = codegen.collectExports(has_main, root_tmp.arena) catch {
        return true;
    };

    for (exports) |exp| types.queue(.runtime, .init(.{ .Func = exp }));

    var errored = false;
    while (types.nextTask(.runtime, 0)) |func| {
        defer codegen.bl.func.reset();

        const err = codegen.build(func);

        errored = types.retainGlobals(.runtime, backend, scrath) or
            errored;

        err catch |e| switch (e) {
            error.HasErrors => {
                errored = true;
                continue;
            },
            error.Uninhabited => continue,
        };

        var errors = std.ArrayListUnmanaged(static_anal.Error){};

        if (log_opts.verbose) try root.test_utils.header("CODEGEN", log_opts.output, log_opts.colors);

        var tmp = root_tmp.arena.checkpoint();
        defer tmp.deinit();

        const func_data: *root.frontend.types.Func = types.store.get(func);

        var opts = optimizations;
        opts.error_buf = &errors;
        opts.arena = tmp.arena;
        opts.verbose = log_opts.verbose;

        backend.emitFunc(&codegen.bl.func, root.backend.Machine.EmitOptions{
            .id = @intFromEnum(func),
            .name = if (func_data.visibility != .local)
                func_data.key.name
            else
                root.frontend.Types.Id.init(.{ .Func = func })
                    .fmt(types).toString(scrath),
            .is_inline = func_data.is_inline or func_data.key.name.len == 0,
            .linkage = func_data.visibility,
            .special = func_data.special,
            .optimizations = opts,
            .builtins = types.getBuiltins(),
        });

        errored = types.dumpAnalErrors(&errors) or errored;
    }

    return errored;
}

pub fn deinit(self: *Codegen) void {
    self.bl.deinit();
    self.* = undefined;
}

pub inline fn abiCata(self: *Codegen, ty: Types.Id) Types.Abi.Spec {
    return @as(Types.Abi.TmpSpec, self.abi.categorize(ty, self.types)).toPerm(ty, self.types);
}

pub fn collectExports(self: *Codegen, has_main: bool, scrath: *utils.Arena) ![]utils.EntId(root.frontend.types.Func) {
    var tmp = utils.Arena.scrath(scrath);
    defer tmp.deinit();

    var exports_main = false;
    var funcs = std.ArrayListUnmanaged(utils.EntId(root.frontend.types.Func)){};
    for (self.types.files, 0..) |fl, i| {
        self.ast = &fl;
        for (fl.exprs.view(fl.items)) |it| {
            const item: Ast.Id = it;

            if (item.tag() != .Directive) continue;

            const dir = fl.exprs.get(item).Directive;
            if (dir.kind != .@"export" and dir.kind != .handler) continue;

            const args: []const Ast.Id = fl.exprs.view(dir.args);
            try self.assertDirectiveArgs(item, args, "<name>, <func>");

            const name, const func = args[0..2].*;

            if (name.tag() != .String) {
                self.report(name, "non hardcoded strings are not supported (yet)", .{}) catch continue;
            }

            const name_string = fl.exprs.get(name).String;
            const name_str = fl.source[name_string.pos.index + 1 .. name_string.end - 1];

            const scope = self.types.getScope(@enumFromInt(i));
            self.parent_scope = .{ .Perm = scope };
            const ty = try self.types.ct.evalTy(name_str, .{ .Perm = scope }, func);

            if (ty.data() != .Func) {
                if (dir.kind == .handler and ty == .void) continue;

                if (dir.kind == .@"export") {
                    self.report(func, "only function types can be used here", .{}) catch continue;
                } else {
                    self.report(func, "only functions and `void` (usefull for" ++
                        " conditional compilation) can be a handler", .{}) catch continue;
                }
            }

            switch (dir.kind) {
                .handler => {
                    const field = std.meta.stringToEnum(
                        std.meta.FieldEnum(Types.Handlers),
                        name_str,
                    ) orelse {
                        const handlers = comptime b: {
                            var acc: []const u8 = "";
                            for (std.meta.fields(Types.Handlers)) |f| acc = acc ++ ", " ++ f.name;
                            break :b acc[", ".len..];
                        };

                        self.report(name, "invalid handler, only " ++ handlers ++ " are supported", .{}) catch
                            continue;
                    };

                    const field_ptr = switch (field) {
                        inline else => |t| &@field(self.types.handlers, @tagName(t)),
                    };

                    if (field_ptr.* != null) {
                        self.report(name, "redeclaration of a handler," ++
                            " TODO: where is the original?", .{}) catch continue;
                    }

                    const func_data: *tys.Func = self.types.store.get(ty.data().Func);
                    const ast = self.types.getFile(func_data.key.loc.file);
                    const func_ast = ast.exprs.get(func_data.key.loc.ast).Fn;

                    if (self.types.handler_signatures.get(field)) |sig| {
                        if (sig.args.len != func_data.args.len) {
                            self.report(
                                func,
                                "this handler takes function" ++
                                    " with {} arguments, but got {}",
                                .{ sig.args.len, func_data.args.len },
                            ) catch continue;
                        }

                        for (sig.args, func_data.args, ast.exprs.view(func_ast.args)) |expected, got, past| {
                            if (expected != got) {
                                self.report(func, "argument does not match the handler signature," ++
                                    " expected {}, got {}", .{ expected, got }) catch {};
                                self.report(past, "...the argument", .{}) catch continue;
                            }
                        }

                        if (sig.ret != func_data.ret) {
                            self.report(func, "return type does not match the handler signature," ++
                                " expected {}, got {}", .{ sig.ret, func_data.ret }) catch {};
                            self.report(func_ast.ret, "...return type", .{}) catch continue;
                        }
                    }

                    field_ptr.* = ty.data().Func;

                    if (field == .entry and has_main) {
                        self.types.store.get(ty.data().Func).visibility = .exported;
                        self.types.store.get(ty.data().Func).special = .entry;
                        continue;
                    }

                    if (field == .memcpy) {
                        self.types.store.get(ty.data().Func).special = .memcpy;
                    }
                },
                .@"export" => {
                    exports_main = exports_main or std.mem.eql(u8, name_str, "main");

                    self.types.store.get(ty.data().Func).visibility = .exported;
                    self.types.store.get(ty.data().Func).key.name = name_str;
                },
                else => unreachable,
            }

            try funcs.append(tmp.arena.allocator(), ty.data().Func);
        }
    }

    if (has_main and !exports_main and self.types.handlers.entry == null) {
        const entry = self.getEntry(.root, "main") catch {
            try self.types.diagnostics.writeAll(
                \\...you can define the `main` in the mentioned file (or pass --no-entry):
                \\
            );

            try Ast.highlightCode(
                \\main := fn(): uint {
                \\    return 0
                \\}
                \\
            , self.types.colors, self.types.diagnostics);

            return error.Never;
        };

        self.types.store.get(entry).visibility = .exported;
        self.types.store.get(entry).key.name = "main";

        try funcs.append(tmp.arena.allocator(), entry);
    }

    if (self.types.handlers.entry) |entry| {
        try funcs.append(tmp.arena.allocator(), entry);
    }

    return scrath.dupe(utils.EntId(root.frontend.types.Func), funcs.items);
}

pub fn getEntry(self: *Codegen, file: Types.File, name: []const u8) !utils.EntId(root.frontend.types.Func) {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    self.ast = self.types.getFile(file);
    _ = self.beginBuilder(tmp.arena, .never, &.{}, &.{}, .{});
    defer self.bl.func.reset();
    self.parent_scope = .{ .Perm = self.types.getScope(file) };
    self.struct_ret_ptr = null;
    self.name = "";

    var entry_vl = try self.lookupScopeItem(.init(0), self.types.getScope(file), name);
    const entry_ty = try self.unwrapTyConst(Ast.Pos.init(0), &entry_vl);

    if (entry_ty.data() != .Func) return error.Never;
    return entry_ty.data().Func;
}

pub fn beginBuilder(
    self: *Codegen,
    scratch: *utils.Arena,
    ret: Types.Id,
    params: []const graph.AbiParam,
    returns: ?[]const graph.AbiParam,
    caps: struct {
        scope_cap: usize = 0,
        loop_cap: usize = 0,
    },
) Builder.BuildToken {
    self.errored = false;
    self.ret = ret;
    const res = self.bl.begin(self.abi.cc, params, returns);

    self.scope = .initBuffer(scratch.alloc(ScopeEntry, caps.scope_cap));
    self.loops = .initBuffer(scratch.alloc(Loop, caps.loop_cap));
    self.defers = .initBuffer(scratch.alloc(Ast.Id, 32));

    return res;
}

const BuildError = error{ Uninhabited, HasErrors };

pub fn build(self: *Codegen, func_id: utils.EntId(root.frontend.types.Func)) BuildError!void {
    errdefer {
        self.types.store.get(func_id).errored = true;
    }

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var func: *root.frontend.types.Func = self.types.store.get(func_id);

    self.ast = self.types.getFile(func.key.loc.file);
    const ast = self.ast;

    const fn_ast = ast.exprs.getTyped(.Fn, func.key.loc.ast).?;

    if (fn_ast.body.tag() == .Directive and ast.exprs.get(fn_ast.body).Directive.kind == .import) {
        if (self.abi.cc == .ablecall) {
            return self.report(fn_ast.body, "cant use @import() on this target", .{}) catch error.HasErrors;
        }

        const args = ast.exprs.view(ast.exprs.get(fn_ast.body).Directive.args);

        if (args.len != 0) {
            const string = ast.exprs.get(args[0]).String;
            func.key.name = ast.source[string.pos.index + 1 .. string.end - 1];
        }

        func.visibility = .imported;

        return;
    }

    const params, const returns, const ret_abi =
        func.sig().computeAbi(self.abi, self.types, tmp.arena) orelse return error.Uninhabited;
    const token = self.beginBuilder(
        tmp.arena,
        func.ret,
        params,
        returns,
        .{ .scope_cap = fn_ast.peak_vars, .loop_cap = fn_ast.peak_loops },
    );
    self.parent_scope = .init(.{ .Func = func_id });
    self.name = "";

    self.types.checkStack(func.key.loc.file, func.key.loc.ast) catch return error.HasErrors;

    if (func.recursion_lock) {
        self.report(func.key.loc.ast, "the functions types most likely" ++
            " depend on it being evaluated", .{}) catch {};
        return error.HasErrors;
    }
    func.recursion_lock = true;
    defer {
        func = self.types.store.get(func_id);
        func.recursion_lock = false;
    }

    var i: usize = 0;

    if (self.abi.isByRefRet(ret_abi)) {
        self.struct_ret_ptr = self.bl.addParam(.none, i);
        i += 1;
    } else {
        self.struct_ret_ptr = null;
    }

    var ty_idx: usize = 0;
    for (ast.exprs.view(fn_ast.args)) |aarg| {
        const ident = ast.exprs.getTyped(.Ident, aarg.bindings).?;
        if (ident.pos.flag.@"comptime") continue;
        func = self.types.store.get(func_id);
        const ty = func.args[ty_idx];
        const abi = self.abiCata(ty);
        const arg_sloc = self.src(aarg);

        var len: usize = 1;
        const arg = switch (abi) {
            .Impossible => unreachable,
            .ByRef => self.bl.addParam(arg_sloc, i),
            .ByValue => if (params[i] == .Stack)
                self.bl.addParam(arg_sloc, i)
            else
                self.bl.addSpill(arg_sloc, self.bl.addParam(arg_sloc, i)),
            .ByValuePair => |p| if (params[i] == .Stack) b: {
                break :b self.bl.addParam(arg_sloc, i);
            } else b: {
                const slot = self.bl.addLocal(arg_sloc, ty.size(self.types));
                for (p.offsets(), 0..) |off, j| {
                    const arg = self.bl.addParam(arg_sloc, i + j);
                    self.bl.addFieldStore(arg_sloc, slot, @intCast(off), arg.data_type, arg);
                }

                len = 2;
                break :b slot;
            },
            .Imaginary => b: {
                len = 0;
                break :b self.bl.addLocal(self.src(aarg), 0);
            },
        };
        self.scope.appendAssumeCapacity(.{ .ty = ty, .name = ident.id });
        self.bl.pushPin(arg);
        i += len;
        ty_idx += 1;
    }

    var termintes = false;
    func = self.types.store.get(func_id);
    _ = self.emit(.{}, ast.exprs.getTyped(.Fn, func.key.loc.ast).?.body) catch |err| switch (err) {
        error.Never => {},
        error.Unreachable => termintes = true,
    };

    if (ret_abi == .Impossible) {
        const msg = "function returns a {} which has 0 values, ";
        if (!termintes) {
            self.report(fn_ast.body, msg ++ "but end of the body is reachable", .{func.ret}) catch {};
        } else if (self.bl.returns()) {
            self.report(fn_ast.body, msg ++ "but it returns at least once", .{func.ret}) catch {};
        }
    } else if (!termintes and ret_abi != .Imaginary) {
        func = self.types.store.get(func_id);
        self.report(fn_ast.body, "function returns a {}, which has more then" ++
            " 1 value, but end of the function body is reachable", .{func.ret}) catch {};
    }

    if (self.errored) return error.HasErrors;

    self.bl.end(token);
}

pub fn src(self: *Codegen, loc: anytype) graph.Sloc {
    return .{ .namespace = @intFromEnum(self.parent_scope.file(self.types)), .index = self.ast.posOf(loc).index };
}

pub fn listFileds(arena: *utils.Arena, fields: anytype) []const u8 {
    if (fields.len == 0) return "none actually";

    var field_list = std.ArrayList(u8).init(arena.allocator());
    for (fields) |f| field_list.writer().print(", `.{s}`", .{f.name}) catch unreachable;

    return field_list.items[2..];
}

pub fn foo() usize {
    return @frameAddress();
}

pub fn emitParseString(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.String)) !Value {
    const lit = self.ast.source[e.pos.index + 1 .. e.end - 1];

    const data = switch (encodeString(lit, self.types.pool.arena.alloc(u8, lit.len)) catch unreachable) {
        .ok => |dt| dt,
        .err => |err| {
            var pos = e.pos;
            pos.index += @intCast(err.pos);
            return self.report(pos, "{}", .{err.reason});
        },
    };

    return self.emitString(ctx, data, expr);
}

pub fn emitParseQuotes(self: *Codegen, _: Ctx, expr: Ast.Id, e: *Expr(.Quotes)) !Value {
    const lit = self.ast.source[e.pos.index + 1 .. e.end - 1];

    var char: [1]u8 = undefined;

    const data = switch (encodeString(lit, &char) catch {
        return self.report(expr, "the char encodes into more then 1 byte", .{});
    }) {
        .ok => |dt| dt,
        .err => |err| {
            var pos = e.pos;
            pos.index += @intCast(err.pos);
            return self.report(pos, "{}", .{err.reason});
        },
    };

    if (data.len == 0) return self.report(expr, "expected the character to encode to exactly one byte", .{});

    return .mkv(.u8, self.bl.addIntImm(self.src(expr), .i8, data[0]));
}

pub fn emitInteger(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.Integer)) EmitError!Value {
    var ty = ctx.ty orelse .uint;
    if (self.types.store.unwrap(ty.data(), .Nullable)) |n| ty = n.inner;
    if (!ty.isInteger()) ty = .uint;
    const shift: u8 = if (e.base == 10) 0 else 2;
    const num_str = self.ast.tokenSrc(e.pos.index)[shift..];
    const parsed = std.fmt.parseInt(u64, num_str, e.base) catch |err| switch (err) {
        error.InvalidCharacter => return self.report(expr, "invalid integer literal", .{}),
        error.Overflow => return self.report(expr, "number does not fit into 64 bits", .{}),
    };
    return .mkv(ty, self.bl.addIntImm(self.src(expr), self.abiCata(ty).ByValue, @bitCast(parsed)));
}

pub fn emitFloat(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.Float)) EmitError!Value {
    var ty = ctx.ty orelse .f32;
    if (!ty.isFloat()) ty = .f32;

    const content = self.ast.tokenSrc(e.index);
    const sloc = self.src(expr);

    if (ty == .f32) {
        const parsed = std.fmt.parseFloat(f32, content) catch |err| switch (err) {
            error.InvalidCharacter => utils.panic("{s}", .{content}),
        };
        return .mkv(ty, self.bl.addIntImm(sloc, .f32, @as(u32, @bitCast(parsed))));
    } else {
        const parsed = std.fmt.parseFloat(f64, content) catch |err| switch (err) {
            error.InvalidCharacter => utils.panic("{s}", .{content}),
        };
        return .mkv(ty, self.bl.addIntImm(sloc, .f64, @bitCast(parsed)));
    }
}

pub fn emitNull(self: *Codegen, ctx: Ctx, expr: Ast.Id) EmitError!Value {
    const ty: Types.Id = ctx.ty orelse {
        return self.report(expr, "can't infer the type of nullable value," ++
            " you can speciry a type: @as(?<ty>, null)", .{});
    };

    const nullable: *tys.Nullable = self.types.store.unwrap(ty.data(), .Nullable) orelse {
        return self.report(expr, "only nullable types can be initialized with null, {} is not", .{ty});
    };

    const sloc = self.src(expr);

    if (nullable.nieche.offset(self.types)) |spec| {
        switch (self.abiCata(nullable.inner)) {
            .Impossible => unreachable,
            .Imaginary => return .{ .ty = ty },
            .ByValue => return .mkv(ty, self.bl.addIntImm(sloc, spec.kind.abi(), 0)),
            .ByValuePair, .ByRef => {
                const loc = ctx.loc orelse
                    self.bl.addLocal(sloc, nullable.inner.size(self.types));
                const flag_vl = self.bl.addIntImm(sloc, spec.kind.abi(), 0);
                _ = self.bl.addFieldStore(sloc, loc, spec.offset, spec.kind.abi(), flag_vl);
                return .mkp(ty, loc);
            },
        }
    } else {
        switch (self.abiCata(ty)) {
            .Impossible => unreachable,
            .Imaginary => return .{ .ty = ty },
            .ByValue, .ByValuePair, .ByRef => {
                const loc = ctx.loc orelse self.bl.addLocal(sloc, ty.size(self.types));
                _ = self.bl.addStore(sloc, loc, .i8, self.bl.addIntImm(sloc, .i8, 0));
                return .mkp(ty, loc);
            },
        }
    }
}

pub fn emitIdk(self: *Codegen, ctx: Ctx, expr: Ast.Id) EmitError!Value {
    const ty: Types.Id = ctx.ty orelse {
        return self.report(expr, "cant infer the type of uninitialized memory," ++
            " you can specify a type: @as(<ty>, idk)", .{});
    };

    if (ctx.loc) |loc| return .mkp(ty, loc);

    const sloc = self.src(expr);

    return switch (self.abiCata(ty)) {
        .Impossible => return self.report(expr, "can't make an uninitialized" ++
            " {}, its uninhabited", .{ty}) catch error.Unreachable,
        .Imaginary => .{ .ty = ty },
        .ByValue => |t| .mkv(ty, self.bl.addUninit(sloc, t)),
        .ByValuePair, .ByRef => {
            const loc = self.bl.addLocal(sloc, ty.size(self.types));
            return .mkp(ty, loc);
        },
    };
}

pub fn emitCtor(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.Ctor)) EmitError!Value {
    if (e.ty.tag() == .Void and ctx.ty == null) {
        return self.report(expr, "cant infer the type of this constructor," ++
            " you can specify a type: '<ty>.{'", .{});
    }

    const oty = ctx.ty orelse try self.resolveAnonTy(e.ty);
    var ty = oty;
    const local = ctx.loc orelse self.bl.addLocal(self.src(expr), ty.size(self.types));
    var offset_cursor: u64 = 0;

    const sloc = self.src(expr);

    if (ty.needsTag(self.types)) {
        ty = self.types.store.get(ty.data().Nullable).inner;
        _ = self.bl.addStore(sloc, local, .i8, self.bl.addIntImm(sloc, .i8, 1));
        offset_cursor += ty.alignment(self.types);
    } else if (self.types.store.unwrap(ty.data(), .Nullable)) |n| {
        ty = n.inner;
    }

    switch (ty.data()) {
        .Struct => |struct_ty| {
            // Existing struct constructor code...
            const FillSlot = union(enum) {
                RequiredOffset: u64,
                Filled: Ast.Id,
            };

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

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

            for (self.ast.exprs.view(e.fields)) |field| {
                const field_sloc = self.src(field.pos.index);
                const fname = self.ast.tokenSrc(field.pos.index);
                const slot, const ftype = for (fields, slots) |tf, *s| {
                    if (std.mem.eql(u8, tf.name, fname)) break .{ s, tf.ty };
                } else {
                    self.report(
                        field.pos,
                        "{} does not have a field called {}, it has: {}",
                        .{ ty, fname, listFileds(tmp.arena, fields) },
                    ) catch continue;
                };

                switch (slot.*) {
                    .RequiredOffset => |offset| {
                        const off = self.bl.addFieldOffset(field_sloc, local, @intCast(offset));
                        var value = self.emitTyped(ctx.addLoc(off), ftype, field.value) catch |err|
                            switch (err) {
                                error.Never => continue,
                                error.Unreachable => return err,
                            };
                        self.emitGenericStore(field_sloc, off, &value);
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
                        self.types.queue(self.target, .init(.{ .Global = value }));
                        const off = self.bl.addFieldOffset(sloc, local, @intCast(s.RequiredOffset));
                        const glob = self.bl.addGlobalAddr(sloc, @intFromEnum(value));
                        self.bl.addFixedMemCpy(sloc, off, glob, f.ty.size(self.types));
                    } else {
                        return self.report(expr, "field {} on struct {} is not initialized", .{ f.name, ty });
                    }
                }
            }
        },
        .Union => |union_ty| {
            if (e.fields.len() != 1) {
                return self.report(expr, "union constructor must initialize only one field", .{});
            }

            const fields = union_ty.getFields(self.types);

            const field_ast = self.ast.exprs.view(e.fields)[0];
            const fname = self.ast.tokenSrc(field_ast.pos.index);

            const f = for (fields) |f| {
                if (std.mem.eql(u8, f.name, fname)) break f;
            } else {
                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();
                return self.report(
                    field_ast.value,
                    "{} does not have a field called {}, is has: {}",
                    .{ ty, fname, listFileds(tmp.arena, fields) },
                );
            };

            offset_cursor = std.mem.alignForward(u64, offset_cursor, f.ty.alignment(self.types));
            const off = self.bl.addFieldOffset(sloc, local, @intCast(offset_cursor));
            var value = try self.emitTyped(.{ .loc = off }, f.ty, field_ast.value);
            self.emitGenericStore(sloc, off, &value);
        },
        else => {
            return self.report(expr, "{} can not be constructed with '.{..}'", .{ty});
        },
    }

    return .mkp(oty, local);
}

pub fn emitTuple(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.Tupl)) EmitError!Value {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const sloc = self.src(expr);

    if (e.ty.tag() == .Void and ctx.ty == null) {
        const local = ctx.loc orelse self.bl.addLocal(self.src(expr), 0);
        var offset: u64 = 0;
        var alignment: u64 = 1;
        const types = tmp.arena.alloc(Types.Id, e.fields.len());

        for (self.ast.exprs.view(e.fields), types) |field, *ty| {
            const field_sloc = self.src(field);
            var value = try self.emit(.{}, field);
            ty.* = value.ty;
            offset = std.mem.alignForward(u64, offset, value.ty.alignment(self.types));
            self.emitGenericStore(field_sloc, self.bl.addFieldOffset(field_sloc, local, @bitCast(offset)), &value);
            offset += value.ty.size(self.types);
            alignment = @max(alignment, value.ty.alignment(self.types));
        }
        offset = std.mem.alignForward(u64, offset, alignment);
        if (ctx.loc == null) self.bl.resizeLocal(local, offset);

        return .mkp(self.types.makeTuple(types), local);
    } else {
        const oty = ctx.ty orelse try self.resolveAnonTy(e.ty);
        var ty = oty;
        const local = ctx.loc orelse self.bl.addLocal(self.src(expr), oty.size(self.types));
        var init_offset: u64 = 0;

        if (ty.needsTag(self.types)) {
            ty = self.types.store.get(ty.data().Nullable).inner;
            _ = self.bl.addStore(sloc, local, .i8, self.bl.addIntImm(sloc, .i8, 1));
            init_offset += ty.alignment(self.types);
        } else if (self.types.store.unwrap(ty.data(), .Nullable)) |n| {
            ty = n.inner;
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
        for (self.ast.exprs.view(e.fields)) |field| {
            const field_sloc = self.src(field);
            const elem = iter.next().?;
            const ftype = elem.field.ty;
            if (ftype == .never) return error.Never;

            const off = self.bl.addFieldOffset(field_sloc, local, @intCast(elem.offset));
            var value = self.emitTyped(ctx.addLoc(off), ftype, field) catch |err| switch (err) {
                error.Never => continue,
                error.Unreachable => return err,
            };
            self.emitGenericStore(field_sloc, off, &value);
        }

        return .mkp(oty, local);
    }
}

pub fn emitArray(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.Arry)) EmitError!Value {
    if (e.ty.tag() == .Void and ctx.ty == null) {
        return self.report(expr, "cant infer the type of this constructor," ++
            " you can specify a type: '<elem-ty>.('", .{});
    }

    const local = ctx.loc orelse self.bl.addLocal(self.src(expr), 0);
    const sloc = self.src(expr);
    var start: usize = 0;

    const elem_ty, const res_ty: Types.Id = if (ctx.ty) |ret_ty| b: {
        var ty = ret_ty;
        if (ty.needsTag(self.types)) {
            ty = self.types.store.get(ty.data().Nullable).inner;
            _ = self.bl.addStore(sloc, local, .i8, self.bl.addIntImm(sloc, .i8, 1));
            start += 1;
        } else if (self.types.store.unwrap(ty.data(), .Nullable)) |n| {
            ty = n.inner;
        }

        const slice = self.types.store.unwrap(ty.data(), .Slice) orelse {
            return self.report(expr, "{} can not be initialized with array syntax", .{ty});
        };

        if (slice.len != e.fields.len()) if (slice.len) |len| {
            return self.report(expr, "expected array with {} element, got {}", .{ len, e.fields.len() });
        } else {
            return self.report(expr, "expected {}, got array with {} elements", .{ ty, e.fields.len() });
        };

        break :b .{ slice.elem, ret_ty };
    } else b: {
        const elem_ty = try self.resolveAnonTy(e.ty);
        const array_ty = self.types.makeSlice(e.fields.len(), elem_ty);
        break :b .{ elem_ty, array_ty };
    };

    if (ctx.loc == null) self.bl.resizeLocal(local, res_ty.size(self.types));

    for (self.ast.exprs.view(e.fields), start..) |elem, i| {
        const elem_sloc = self.src(elem);
        const off = self.bl.addFieldOffset(elem_sloc, local, @intCast(i * elem_ty.size(self.types)));
        var value = self.emitTyped(.{ .loc = off }, elem_ty, elem) catch |err| switch (err) {
            error.Never => continue,
            error.Unreachable => return err,
        };
        self.emitGenericStore(elem_sloc, off, &value);
    }

    return .mkp(res_ty, local);
}

pub fn emitSliceTy(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.SliceTy)) EmitError!Value {
    const sloc = self.src(expr);
    if (e.len.tag() != .Void) {
        var len = try self.emitTyped(.{}, .uint, e.len);
        var ty = try self.emitTyped(.{}, .type, e.elem);
        return self.emitInternalEca(ctx, .make_array, &.{ len.getValue(sloc, self), ty.getValue(sloc, self) }, .type);
    } else {
        const len: ?usize = null;
        const elem = try self.resolveAnonTy(e.elem);

        const res, const ov = @mulWithOverflow(len orelse 0, elem.size(self.types));
        if (ov != 0 or res > std.math.maxInt(u48)) {
            return self.report(expr, "the array is bigger then most modern virtual memory spaces", .{});
        }

        return self.emitTyConst(self.types.makeSlice(len, elem));
    }
}

pub fn emitUnOp(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.UnOp)) EmitError!Value {
    const sloc = self.src(expr);
    switch (e.op) {
        .@"^" => return self.emitTyConst(self.types.makePtr(try self.resolveAnonTy(e.oper))),
        .@"?" => return self.emitTyConst(self.types.makeNullable(try self.resolveAnonTy(e.oper))),
        .@"&" => {
            if (self.ast.exprs.getTyped(.Arry, e.oper)) |a| {
                if (a.ty.tag() == .Void and a.fields.len() == 0) {
                    const ty = ctx.ty orelse return self.report(expr, "empty slice need to have a known type", .{});
                    const slice = self.types.store.unwrap(ty.data(), .Slice) orelse {
                        return self.report(expr, "{} is not a slice but it was initialized as such", .{ty});
                    };

                    const loc = ctx.loc orelse self.bl.addLocal(self.src(expr), ty.size(self.types));
                    const ptr = self.bl.addIntImm(sloc, .i64, @bitCast(slice.elem.alignment(self.types)));
                    self.bl.addFieldStore(sloc, loc, TySlice.ptr_offset, .i64, ptr);
                    self.bl.addFieldStore(sloc, loc, TySlice.len_offset, .i64, self.bl.addIntImm(sloc, .i64, 0));

                    return .mkp(ty, loc);
                }
            }

            var addrd = try self.emit(.{}, e.oper);

            if (ctx.ty) |fty| function_pointer: {
                const sig: *tys.FnPtr = self.types.store.unwrap(fty.data(), .FnPtr) orelse
                    break :function_pointer;

                const ty = try self.unwrapTyConst(expr, &addrd);
                const func: *tys.Func = self.types.store.unwrap(ty.data(), .Func) orelse
                    break :function_pointer;

                errdefer self.report(
                    e.oper,
                    "...while triing to coerse {} to {}",
                    .{ ty, fty },
                ) catch {};

                for (func.args, sig.args, 0..) |harg, earg, i| {
                    if (harg == earg) continue;
                    return self.report(e.oper, "the argument no. {} does not match, " ++
                        "expected {}, got {}", .{ i, earg, harg });
                }

                if (func.ret != sig.ret) {
                    return self.report(e.oper, "the return type does not match, " ++
                        "expected {}, got {}", .{ sig.ret, func.ret });
                }

                self.types.queue(self.target, ty);
                return .mkv(fty, self.bl.addFuncAddr(sloc, @intFromEnum(ty.data().Func)));
            }

            self.emitSpill(expr, &addrd);
            return addrd;
        },
        inline .@"-", .@"!", .@"~" => |t| {
            var lhs = try self.emit(ctx, e.oper);
            switch (t) {
                .@"-" => if (!lhs.ty.isInteger() and !lhs.ty.isFloat())
                    return self.report(expr, "only integers can be negated, {} is not", .{lhs.ty}),
                .@"!" => if (lhs.ty != .bool)
                    return self.report(expr, "only booleans can be negated, {} is not", .{lhs.ty}),
                .@"~" => if (!lhs.ty.isInteger())
                    return self.report(expr, "only integers can invert their bits, {} is not", .{lhs.ty}),
                else => @compileError("wut"),
            }
            return .mkv(lhs.ty, self.bl.addUnOp(sloc, switch (t) {
                .@"-" => if (lhs.ty.isFloat()) .fneg else .ineg,
                .@"!" => .not,
                .@"~" => .bnot,
                else => @compileError("wut"),
            }, self.abiCata(lhs.ty).ByValue, lhs.getValue(sloc, self)));
        },
        else => return self.report(expr, "cant handle this operation yet", .{}),
    }
}

pub fn emitBinOp(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.BinOp)) EmitError!Value {
    const sloc = self.src(expr);
    switch (e.op) {
        .@"=" => if (e.lhs.tag() == .Wildcard) {
            _ = try self.emit(.{}, e.rhs);
            return .{};
        } else {
            const loc = try self.emit(.{}, e.lhs);

            if (loc.id != .Pointer) {
                return self.report(e.lhs, "can't assign to this", .{});
            }

            var val = try self.emitTyped(ctx.addLoc(loc.id.Pointer), loc.ty, e.rhs);
            self.emitGenericStore(sloc, loc.id.Pointer, &val);
            return .{};
        },
        .@"&&" => {
            const variable = self.bl.addLocal(.none, 1);

            var lhs = try self.emitTyped(.{ .in_if_cond = ctx.in_if_cond }, .bool, e.lhs);
            var builder = self.bl.addIfAndBeginThen(sloc, lhs.getValue(sloc, self));
            {
                var rhs = try self.emitTyped(.{ .loc = variable, .in_if_cond = ctx.in_if_cond }, .i8, e.rhs);
                self.emitGenericStore(sloc, variable, &rhs);
            }
            const token = builder.beginElse(&self.bl);
            {
                self.bl.addStore(sloc, variable, .i8, self.bl.addIntImm(sloc, .i8, 0));
            }
            builder.end(&self.bl, token);

            return .mkp(.bool, variable);
        },
        .@"||" => {
            var lhs = try self.emit(.{ .ty = .bool }, e.lhs);

            if (self.types.store.unwrap(lhs.ty.data(), .Nullable)) |nullable| {
                const inner = nullable.inner;
                const is_compact = lhs.ty.data().Nullable.isCompact(self.types);

                // TODO: this wastes stack, we should fix up the stack
                // allocation once we know this results into unwrapped
                // value
                var variable = self.bl.addLocal(sloc, lhs.ty.size(self.types));
                var cond = try self.checkNull(e.lhs, &lhs, .@"!=");

                var builder = self.bl.addIfAndBeginThen(sloc, cond.getValue(sloc, self));
                {
                    self.emitGenericStore(sloc, variable, &lhs);
                }
                const token = builder.beginElse(&self.bl);
                var res_ty = lhs.ty;
                default_value: {
                    var rhs = self.emit(.{ .loc = variable, .ty = inner }, e.rhs) catch |err| switch (err) {
                        error.Unreachable => {
                            res_ty = inner;
                            if (!is_compact) {
                                variable = self.bl.addFieldOffset(
                                    sloc,
                                    variable,
                                    @intCast(inner.alignment(self.types)),
                                );
                            }
                            break :default_value;
                        },
                        else => return err,
                    };
                    if (rhs.ty != lhs.ty) {
                        try self.typeCheck(e.rhs, &rhs, inner);
                        res_ty = inner;
                        if (!is_compact) {
                            variable = self.bl.addFieldOffset(
                                sloc,
                                variable,
                                @intCast(inner.alignment(self.types)),
                            );
                        }
                    }
                    self.emitGenericStore(sloc, variable, &rhs);
                }
                builder.end(&self.bl, token);

                return .mkp(res_ty, variable);
            } else {
                const variable = self.bl.addLocal(.none, 1);

                try self.typeCheck(e.lhs, &lhs, .bool);

                var builder = self.bl.addIfAndBeginThen(sloc, lhs.getValue(sloc, self));
                {
                    self.bl.addStore(sloc, variable, .i8, self.bl.addIntImm(sloc, .i8, 1));
                }
                const token = builder.beginElse(&self.bl);
                {
                    var rhs = try self.emitTyped(.{ .loc = variable }, .i8, e.rhs);
                    self.emitGenericStore(sloc, variable, &rhs);
                }
                builder.end(&self.bl, token);

                return .mkp(.bool, variable);
            }
        },
        else => {
            if (e.lhs.tag() == .Null) {
                return self.report(e.lhs, "null has to be on the right hand side", .{});
            }

            var lhs = try self.emit(if (e.op.isComparison()) .{} else ctx, e.lhs);

            if (e.rhs.tag() == .Null) switch (e.op) {
                .@"==", .@"!=" => return self.checkNull(e.lhs, &lhs, e.op),
                else => {
                    return self.report(e.lhs, "only comparing against null is supported", .{});
                },
            };

            var rhs = try self.emit(.{ .ty = lhs.ty }, e.rhs);

            switch (lhs.ty.data()) {
                .Struct => |struct_ty| {
                    try self.typeCheck(e.rhs, &rhs, lhs.ty);
                    if (e.op.isComparison()) {
                        if (e.op != .@"==" and e.op != .@"!=")
                            return self.report(expr, "structs only support `!=` and `==`", .{});
                        const value = try self.emitStructFoldOp(expr, struct_ty, e.op, lhs.id.Pointer, rhs.id.Pointer);
                        return .mkv(.bool, value orelse self.bl.addIntImm(sloc, .i8, 1));
                    } else {
                        const loc = ctx.loc orelse self.bl.addLocal(sloc, lhs.ty.size(self.types));
                        try self.emitStructOp(expr, struct_ty, e.op, loc, lhs.id.Pointer, rhs.id.Pointer);
                        return .mkp(lhs.ty, loc);
                    }
                },
                .Builtin => {
                    const binop = try self.lexemeToBinOp(expr, e.op, lhs.ty);
                    const lhs_ty = (if (e.op.isComparison() or
                        (ctx.ty != null and (ctx.ty.?.data() == .Pointer)))
                        null
                    else if (ctx.ty != null and ctx.ty.?.data() == .Nullable)
                        self.types.store.get(ctx.ty.?.data().Nullable).inner
                    else
                        ctx.ty) orelse lhs.ty;
                    const upcast_ty = self.binOpUpcast(lhs_ty, rhs.ty) catch |err|
                        return self.report(expr, "{} ({} and {})", .{ @errorName(err), lhs_ty, rhs.ty });

                    if (lhs.ty.isFloat()) {
                        try self.typeCheck(expr, &rhs, lhs.ty);
                    } else {
                        try self.typeCheck(expr, &lhs, upcast_ty);
                        try self.typeCheck(expr, &rhs, upcast_ty);
                    }

                    const dest_ty = if (e.op.isComparison()) .bool else upcast_ty;
                    return .mkv(dest_ty, self.bl.addBinOp(
                        sloc,
                        binop,
                        self.abiCata(dest_ty).ByValue,
                        lhs.getValue(sloc, self),
                        rhs.getValue(sloc, self),
                    ));
                },
                .Pointer => |ptr_ty| if (rhs.ty.data() == .Pointer) {
                    if (e.op != .@"-" and !e.op.isComparison())
                        return self.report(expr, "two pointers can only be subtracted or compared", .{});

                    const binop = try self.lexemeToBinOp(expr, e.op, lhs.ty);
                    try self.typeCheck(e.rhs, &rhs, lhs.ty);
                    const dest_ty: Types.Id = if (e.op.isComparison()) .bool else .int;

                    return .mkv(dest_ty, self.bl.addBinOp(
                        sloc,
                        binop,
                        self.abiCata(dest_ty).ByValue,
                        lhs.getValue(sloc, self),
                        rhs.getValue(sloc, self),
                    ));
                } else {
                    if (e.op != .@"-" and e.op != .@"+")
                        return self.report(expr, "you can only subtract or add an integer to a pointer", .{});

                    const upcast: Types.Id = if (rhs.ty.isSigned()) .int else .uint;
                    try self.typeCheck(e.rhs, &rhs, upcast);

                    return .mkv(lhs.ty, self.bl.addIndexOffset(
                        sloc,
                        lhs.getValue(sloc, self),
                        if (e.op == .@"-") .isub else .iadd,
                        self.types.store.get(ptr_ty).size(self.types),
                        rhs.getValue(sloc, self),
                    ));
                },
                .Enum => {
                    if (!e.op.isComparison())
                        return self.report(expr, "only comparison operators are allowed for enums", .{});

                    const binop = try self.lexemeToBinOp(expr, e.op, lhs.ty);
                    try self.typeCheck(e.rhs, &rhs, lhs.ty);

                    return .mkv(.bool, self.bl.addBinOp(
                        sloc,
                        binop,
                        self.abiCata(lhs.ty).ByValue,
                        lhs.getValue(sloc, self),
                        rhs.getValue(sloc, self),
                    ));
                },
                else => return self.report(expr, "{} does not support binary operations", .{lhs.ty}),
            }
        },
    }
}

pub fn emitUnwrap(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.Unwrap)) EmitError!Value {
    const pctx = Ctx{ .ty = if (ctx.ty != null and ctx.ty.?.data() == .Nullable)
        self.types.store.get(ctx.ty.?.data().Nullable).inner
    else
        null };
    var base = try self.emit(pctx, e.*);

    try self.unwrapNullable(expr, &base, true);
    return base;
}

pub fn emitParseUnwrap(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.Deref)) EmitError!Value {
    const sloc = self.src(expr);

    const pctx = Ctx{ .ty = if (ctx.ty != null and ctx.ty.?.data() == .Pointer)
        self.types.store.get(ctx.ty.?.data().Pointer).*
    else
        null };
    var base = try self.emit(pctx, e.*);

    const ptr = self.types.store.unwrap(base.ty.data(), .Pointer) orelse {
        return self.report(e, "only pointer types can be dereferenced, {} is not", .{base.ty});
    };

    if (self.abiCata(ptr.*) == .Impossible) {
        return self.report(e, "dereferencing uninhabited type ({}) is not allowed", .{base.ty});
    }

    return .mkp(ptr.*, base.getValue(sloc, self));
}

pub fn emitTag(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.Tag)) EmitError!Value {
    const ty = ctx.ty orelse {
        return self.report(expr, "cant infer the type of the implicit access, " ++
            " you can specify the type: <ty>.{}", .{self.ast.tokenSrc(e.index + 1)});
    };

    return try self.lookupScopeItem(e.*, ty, self.ast.tokenSrc(e.index + 1));
}

pub fn emitField(self: *Codegen, _: Ctx, expr: Ast.Id, e: *Expr(.Field)) EmitError!Value {
    var base = try self.emit(.{}, e.base);

    const sloc = self.src(expr);
    self.emitAutoDeref(sloc, &base);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    if (base.ty == .type) {
        const bsty = try self.unwrapTyConst(e.base, &base);
        return try self.lookupScopeItem(e.field, bsty, self.ast.tokenSrc(e.field.index));
    }

    const fname = self.ast.tokenSrc(e.field.index);

    switch (base.ty.data()) {
        .Struct => |struct_ty| {
            var iter = struct_ty.offsetIter(self.types);
            const ftype, const offset = while (iter.next()) |elem| {
                if (std.mem.eql(u8, fname, elem.field.name))
                    break .{ elem.field.ty, elem.offset };
            } else {
                return self.report(
                    e.field,
                    "no such field on {}, but it has: {}",
                    .{ base.ty, listFileds(tmp.arena, struct_ty.getFields(self.types)) },
                );
            };

            if (ftype == .never) {
                return self.report(e.field, "accessing malformed field" ++
                    " (the type is 'never')", .{});
            }

            return switch (base.id) {
                .Imaginary => .mkv(ftype, null),
                .Value => |v| .mkv(ftype, v),
                .Pointer => |p| .mkp(ftype, self.bl.addFieldOffset(sloc, p, @intCast(offset))),
            };
        },
        .Union => |union_ty| {
            const ftype = for (union_ty.getFields(self.types)) |tf| {
                if (std.mem.eql(u8, fname, tf.name)) break tf.ty;
            } else {
                return self.report(
                    e.field,
                    "no such field on {}, but it has: {}",
                    .{ base.ty, listFileds(tmp.arena, union_ty.getFields(self.types)) },
                );
            };

            if (ftype == .never) {
                return self.report(e.field, "accessing malformed field (the type is 'never')", .{});
            }

            base.ty = ftype;
            return base;
        },
        .Slice => |slice_ty| {
            const slice = self.types.store.get(slice_ty);
            if (std.mem.eql(u8, fname, "len")) {
                if (slice.len) |l| {
                    return .mkv(.uint, self.bl.addIntImm(sloc, .i64, @intCast(l)));
                } else {
                    return .mkp(.uint, self.bl.addFieldOffset(
                        sloc,
                        base.id.Pointer,
                        TySlice.len_offset,
                    ));
                }
            } else if (std.mem.eql(u8, fname, "ptr")) {
                const ptr_ty = self.types.makePtr(slice.elem);
                if (slice.len != null) {
                    return .mkv(ptr_ty, base.id.Pointer);
                } else {
                    return .mkp(ptr_ty, self.bl.addFieldOffset(
                        sloc,
                        base.id.Pointer,
                        TySlice.ptr_offset,
                    ));
                }
            } else {
                return self.report(e.field, "slices and arrays only support" ++
                    " `.ptr` and `.len` field", .{});
            }
        },
        else => {
            return self.report(e.field, "field access is only allowed on" ++
                " structs and arrays, {} is not", .{base.ty});
        },
    }
}

pub fn emitIndex(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.Index)) EmitError!Value {
    const sloc = self.src(expr);

    if (e.subscript.tag() == .Range) {
        var base = try self.emit(.{}, e.base);

        const range = self.ast.exprs.getTyped(.Range, e.subscript).?;

        const elem = base.ty.child(self.types) orelse {
            return self.report(e.base, "only pointers," ++
                " arrays and slices can be sliced, {} is not", .{base.ty});
        };

        var start: Value = if (range.start.tag() == .Void)
            .mkv(.uint, self.bl.addIntImm(sloc, .i64, 0))
        else
            try self.emitTyped(.{}, .uint, range.start);
        var end: Value = if (range.end.tag() == .Void) switch (base.ty.data()) {
            .Slice => |slice_ty| if (self.types.store.get(slice_ty).len) |l|
                .mkv(.uint, self.bl.addIntImm(sloc, .i64, @intCast(l)))
            else
                .mkv(.uint, self.bl.addFieldLoad(sloc, base.id.Pointer, TySlice.len_offset, .i64)),
            else => {
                return self.report(e.subscript, "unbound range is only allowed" ++
                    " on arrays and slices, {} is not", .{base.ty});
            },
        } else try self.emitTyped(.{}, .uint, range.end);

        const res_ty = self.types.makeSlice(null, elem);

        var ptr: Value = switch (base.ty.data()) {
            .Pointer => base,
            .Slice => |slice_ty| if (self.types.store.get(slice_ty).len == null)
                .mkv(
                    self.types.makePtr(elem),
                    self.bl.addFieldLoad(sloc, base.id.Pointer, TySlice.ptr_offset, .i64),
                )
            else
                .mkv(self.types.makePtr(elem), base.id.Pointer),
            else => {
                return self.report(expr, "only structs and slices" ++
                    " can be indexed, {} is not", .{base.ty});
            },
        };

        if (base.ty.data() == .Slice) if (self.types.handlers.slice_ioob) |handler| {
            var len = Value.mkv(.uint, if (self.types.store.get(base.ty.data().Slice).len) |l|
                self.bl.addIntImm(sloc, .i64, @intCast(l))
            else
                self.bl.addFieldLoad(sloc, base.id.Pointer, TySlice.len_offset, .i64));
            const range_check = self.bl.addBinOp(sloc, .ugt, .i8, end.getValue(sloc, self), len.getValue(sloc, self));
            const order_check = self.bl.addBinOp(sloc, .ugt, .i8, start.getValue(sloc, self), end.getValue(sloc, self));
            const check = self.bl.addBinOp(sloc, .bor, .i8, range_check, order_check);
            var arg_values = [_]Value{ undefined, len, start, end };
            self.emitHandlerCall(handler, e.subscript, check, &arg_values);
        };

        ptr.id = .{ .Value = self.bl.addIndexOffset(
            sloc,
            ptr.getValue(sloc, self),
            .iadd,
            elem.size(self.types),
            start.getValue(sloc, self),
        ) };
        const len = self.bl.addBinOp(sloc, .isub, .i64, end.getValue(sloc, self), start.getValue(sloc, self));

        const loc = ctx.loc orelse self.bl.addLocal(self.src(expr), res_ty.size(self.types));
        self.bl.addFieldStore(sloc, loc, TySlice.ptr_offset, .i64, ptr.getValue(sloc, self));
        self.bl.addFieldStore(sloc, loc, TySlice.len_offset, .i64, len);

        return .mkp(res_ty, loc);
    } else {
        var base = try self.emit(.{}, e.base);

        self.emitAutoDeref(sloc, &base);
        var idx_value = try self.emitTyped(.{}, .uint, e.subscript);
        switch (base.ty.data()) {
            inline .Struct, .Tuple => |struct_ty| {
                const idx = try self.partialEval(e.subscript, &idx_value);

                var iter = struct_ty.offsetIter(self.types);

                if (idx >= iter.fields.len) {
                    return self.report(e.subscript, "struct has only {} fields," ++
                        " but idnex is {}", .{ iter.fields.len, idx });
                }

                var elem: @TypeOf(iter.next().?) = undefined;
                for (0..@as(usize, @intCast(idx)) + 1) |_| elem = iter.next().?;

                return switch (base.id) {
                    .Imaginary => .mkv(elem.field.ty, null),
                    .Value => |v| .mkv(elem.field.ty, v),
                    .Pointer => |p| .mkp(
                        elem.field.ty,
                        self.bl.addFieldOffset(sloc, p, @intCast(elem.offset)),
                    ),
                };
            },
            .Slice => |slice_ty| {
                const slice = self.types.store.get(slice_ty);
                const index_base = if (slice.len == null)
                    self.bl.addLoad(sloc, base.id.Pointer, .i64)
                else switch (base.id) {
                    .Imaginary => return self.report(expr, "indexing into an empty array is not allowed", .{}),
                    .Value => self.bl.addSpill(sloc, base.id.Value),
                    .Pointer => base.id.Pointer,
                };

                if (self.types.handlers.slice_ioob) |handler| {
                    var len = Value.mkv(.uint, if (slice.len) |len|
                        self.bl.addIntImm(sloc, .i64, @intCast(len))
                    else
                        self.bl.addFieldLoad(sloc, base.id.Pointer, TySlice.len_offset, .i64));

                    const check = self.bl.addBinOp(sloc, .uge, .i8, idx_value.getValue(sloc, self), len.getValue(sloc, self));
                    var arg_values = [_]Value{ undefined, len, idx_value, idx_value };
                    self.emitHandlerCall(handler, e.subscript, check, &arg_values);
                }

                return .mkp(slice.elem, self.bl.addIndexOffset(
                    sloc,
                    index_base,
                    .iadd,
                    slice.elem.size(self.types),
                    idx_value.getValue(sloc, self),
                ));
            },
            else => {
                return self.report(expr, "only structs and slices" ++
                    " can be indexed, {} is not", .{base.ty});
            },
        }
    }
}

fn emitBlock(self: *Codegen, ctx: Ctx, _: Ast.Id, e: *Expr(.Block)) EmitError!Value {
    const prev_scope_height = self.scope.items.len;
    defer self.scope.items.len = prev_scope_height;
    defer self.bl.truncatePins(prev_scope_height);

    const defer_scope = self.defers.items.len;
    defer self.defers.items.len = defer_scope;

    for (self.ast.exprs.view(e.stmts)) |s| {
        _ = self.emitTyped(ctx, .void, s) catch |err| switch (err) {
            error.Never => {},
            error.Unreachable => return err,
        };
    }
    try self.emitDefers(defer_scope);

    return .{};
}

fn emitIf(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.If)) EmitError!Value {
    const sloc = self.src(expr);
    if (e.pos.flag.@"comptime") {
        var cond = try self.emitTyped(ctx, .bool, e.cond);
        if (try self.partialEval(e.cond, &cond) != 0) {
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
        const prev_scope_height = self.scope.items.len;

        var cond = try self.emitTyped(.{ .in_if_cond = true }, .bool, e.cond);

        var unreachable_count: usize = 0;
        var if_builder = self.bl.addIfAndBeginThen(self.src(expr), cond.getValue(sloc, self));
        unreachable_count += self.emitBranch(e.then);
        // we remove any unwraps int the condition so that else does not
        // have acces to them
        self.scope.items.len = prev_scope_height;
        self.bl.truncatePins(prev_scope_height);

        const end_else = if_builder.beginElse(&self.bl);
        unreachable_count += self.emitBranch(e.else_);
        if_builder.end(&self.bl, end_else);

        if (unreachable_count == 2) return error.Unreachable;

        return .{};
    }
}

fn emitMatch(self: *Codegen, ctx: Ctx, expr: Ast.Id, e: *Expr(.Match)) EmitError!Value {
    const sloc = self.src(expr);
    var value = try self.emit(.{}, e.value);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    _ = self.types.store.unwrap(value.ty.data(), .Enum) orelse {
        return self.report(e.value, "can only match on enums right now," ++
            " {} is not", .{value.ty});
    };

    const fields = value.ty.data().Enum.getFields(self.types);

    if (fields.len == 0) {
        self.bl.addTrap(sloc, 0);
        return error.Unreachable;
    }

    if (e.arms.len() == 0)
        return self.report(e.pos, "the matched type has non zero possible values, " ++
            "therefore empty match statement is invalid", .{});

    const ArmSlot = union(enum) {
        Unmatched,
        Matched: Ast.Id,
    };

    const Matcher = struct {
        iter_until: usize,
        else_arm: ?Ast.Id = null,
        slots: []ArmSlot,
        fields: []const root.frontend.types.Enum.Field,
        ty: Types.Id,

        pub fn missingBranches(
            slf: *@This(),
            arena: *utils.Arena,
            filds: []const root.frontend.types.Enum.Field,
        ) []const u8 {
            var missing_list = std.ArrayList(u8).init(arena.allocator());
            for (slf.slots, filds) |p, f| if (p == .Unmatched) {
                missing_list.writer().print(", `.{s}`", .{f.name}) catch unreachable;
            };
            return missing_list.items[2..];
        }

        pub fn decomposeArm(
            slf: *@This(),
            cg: *Codegen,
            i: usize,
            arm: Ast.MatchArm,
        ) !?struct { usize, Ast.Id } {
            if (arm.pat.tag() == .Wildcard or i == slf.iter_until) {
                if (slf.else_arm) |erm| if (i == slf.iter_until) {
                    cg.report(erm, "useless esle match arm," ++
                        " all cases are covered", .{}) catch {};
                } else {
                    cg.report(arm.body, "duplicate else match arm", .{}) catch {};
                    cg.report(erm, "...previouslly matched here", .{}) catch {};
                } else {
                    slf.iter_until += 1;
                    slf.else_arm = arm.body;
                }
                return null;
            }

            var match_pat = try cg.emitTyped(.{}, slf.ty, arm.pat);
            const arm_value = if (cg.abiCata(match_pat.ty) == .Imaginary)
                0
            else
                try cg.partialEval(arm.pat, &match_pat);

            // do a binary search instead
            //const idx = for (slf.fields, 0..) |field, j| {
            //    if (field.value == arm_value) break j;
            //} else unreachable;

            const idx = std.sort.binarySearch(tys.Enum.Field, slf.fields, arm_value, struct {
                fn lessThenFn(ar: u64, lhs: tys.Enum.Field) std.math.Order {
                    return std.math.order(ar, lhs.value);
                }
            }.lessThenFn).?;

            switch (slf.slots[@intCast(idx)]) {
                .Unmatched => slf.slots[@intCast(idx)] = .{ .Matched = arm.body },
                .Matched => |pos| {
                    cg.report(arm.body, "duplicate match arm", .{}) catch {};
                    cg.report(pos, "...previouslly matched here", .{}) catch {};
                    return null;
                },
            }

            return .{ @intCast(idx), arm.body };
        }
    };

    var matcher = Matcher{
        .iter_until = fields.len - 1,
        .slots = tmp.arena.alloc(ArmSlot, fields.len),
        .fields = fields,
        .ty = value.ty,
    };
    @memset(matcher.slots, .Unmatched);

    if (e.pos.flag.@"comptime") {
        const value_idx = if (self.abiCata(value.ty) == .Imaginary)
            0
        else
            try self.partialEval(e.value, &value);

        var matched_branch: ?Ast.Id = null;
        for (self.ast.exprs.view(e.arms), 0..) |arm, i| {
            const idx, const body = try matcher.decomposeArm(self, i, arm) orelse continue;

            if (idx == value_idx) {
                std.debug.assert(matched_branch == null);
                matched_branch = body;
            }
        }

        const final_branch = matched_branch orelse matcher.else_arm orelse {
            return self.report(
                e.pos,
                "not all branches are covered: {}",
                .{matcher.missingBranches(tmp.arena, fields)},
            );
        };

        _ = try self.emitTyped(ctx, .void, final_branch);
    } else {
        var if_stack = std.ArrayListUnmanaged(Builder.If)
            .initBuffer(tmp.arena.alloc(Builder.If, e.arms.len()));

        var unreachable_count: usize = 0;
        for (self.ast.exprs.view(e.arms), 0..) |arm, i| {
            const arm_sloc = self.src(arm);
            const idx, const body = try matcher.decomposeArm(self, i, arm) orelse {
                continue;
            };

            const vl = self.bl.addUnOp(arm_sloc, .sext, .i64, value.getValue(arm_sloc, self));
            const cond = self.bl.addBinOp(
                arm_sloc,
                .eq,
                .i8,
                vl,
                self.bl.addIntImm(arm_sloc, .i64, @bitCast(matcher.fields[idx].value)),
            );
            var if_builder = self.bl.addIfAndBeginThen(self.src(body), cond);

            unreachable_count += self.emitBranch(body);

            _ = if_builder.beginElse(&self.bl);
            if_stack.appendAssumeCapacity(if_builder);
        }

        const final_else = matcher.else_arm orelse {
            return self.report(
                e.pos,
                "not all branches are covered: {}",
                .{matcher.missingBranches(tmp.arena, fields)},
            );
        };
        unreachable_count += self.emitBranch(final_else);

        var iter = std.mem.reverseIterator(if_stack.items);
        while (iter.nextPtr()) |br| br.end(&self.bl, @enumFromInt(0));

        if (unreachable_count == e.arms.len()) return error.Unreachable;
    }
    return .{};
}

fn emitLoop(self: *Codegen, _: Ctx, expr: Ast.Id, e: *Expr(.Loop)) EmitError!Value {
    if (e.pos.flag.@"comptime") {
        self.loops.appendAssumeCapacity(.{
            .id = if (e.label.tag() != .Void) self.ast.exprs.get(e.label).Ident.id else .invalid,
            .defer_base = self.defers.items.len,
            .kind = .{ .Comptime = .Clean },
        });
        defer _ = self.loops.pop().?;
        const loop = &self.loops.items[self.loops.items.len - 1];
        const default_iters = 300;
        var fuel: usize = default_iters;
        while ((loop.kind.Comptime != .Controlled or
            loop.kind.Comptime.Controlled.tag() != .Break) and !self.errored)
        {
            if (fuel == 0) {
                return self.report(expr, "loop exceeded {} comptime iterations" ++
                    " (TODO: add @setComptimeIterLimit(val))", .{default_iters});
            }
            fuel -= 1;
            loop.kind.Comptime = .Clean;
            if (self.emitBranch(e.body) != 0) {
                if (self.bl.isUnreachable()) return error.Unreachable;
                continue;
            }
            _ = self.loopControl(.@"continue", expr) catch {};
        }
        return .{};
    } else {
        self.loops.appendAssumeCapacity(.{
            .id = if (e.label.tag() != .Void) self.ast.exprs.get(e.label).Ident.id else .invalid,
            .defer_base = self.defers.items.len,
            .kind = .{ .Runtime = self.bl.addLoopAndBeginBody(self.src(expr)) },
        });

        _ = self.emitBranch(e.body);
        var loop: Builder.Loop = self.loops.pop().?.kind.Runtime;
        loop.end(&self.bl);

        if (self.bl.isUnreachable()) {
            return error.Unreachable;
        }

        return .{};
    }
}

pub fn emitFor(self: *Codegen, _: Ctx, expr: Ast.Id, e: *Expr(.For)) !Value {
    if (e.pos.flag.@"comptime") {
        return self.report(expr, "TODO: comptime for loops", .{});
    }

    const sloc = self.src(expr);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const ForIter = union(enum) {
        ClosedRange: struct { idx: Value, end: *Node },
        OpenedRange: struct { idx: Value },
        Slice: struct { base: Value, len: *Node, bound: *Node },
    };

    const iter_data = tmp.arena.alloc(ForIter, e.iters.len());

    for (self.ast.exprs.view(e.iters), iter_data) |iter, *id| {
        if (iter.value.tag() == .Range) {
            const range = self.ast.exprs.get(iter.value).Range;

            var start = try self.emitTyped(.{}, .uint, range.start);
            if (start.id == .Value) start.id = .{
                .Pointer = self.bl.addSpill(self.src(range.start), start.id.Value),
            };

            if (range.end.tag() == .Void) {
                id.* = .{ .OpenedRange = .{ .idx = start } };
            } else {
                var end = try self.emitTyped(.{}, .uint, range.end);
                id.* = .{ .ClosedRange = .{
                    .idx = start,
                    .end = end.getValue(sloc, self),
                } };
            }
        } else {
            const slice = try self.emit(.{}, iter.value);

            if (slice.ty.data() != .Slice) {
                return self.report(iter, "expected a slice", .{});
            }

            const slc: tys.Slice = self.types.store.get(slice.ty.data().Slice).*;

            if (slc.len != null) {
                return self.report(iter, "TODO: arrays", .{});
            } else {
                const base = self.bl.addFieldLoad(sloc, slice.id.Pointer, tys.Slice.ptr_offset, .i64);
                const base_id = self.bl.addSpill(sloc, base);
                const len = self.bl.addFieldLoad(sloc, slice.id.Pointer, tys.Slice.len_offset, .i64);
                const unit = self.bl.addIntImm(sloc, .i64, @intCast(slc.elem.size(self.types)));
                const byte_len = self.bl.addBinOp(sloc, .imul, .i64, len, unit);
                const bound = self.bl.addBinOp(sloc, .iadd, .i64, base, byte_len);
                id.* = .{ .Slice = .{ .base = .mkp(slc.elem, base_id), .len = len, .bound = bound } };
            }
        }
    }

    if (self.types.handlers.for_loop_length_mismatch) |handler| {
        var bounds = tmp.arena.makeArrayList(*Node, iter_data.len);
        for (iter_data) |data| {
            bounds.appendAssumeCapacity(switch (data) {
                .ClosedRange => |r| b: {
                    var start = r.idx;
                    break :b self.bl.addBinOp(sloc, .isub, .i64, r.end, start.getValue(sloc, self));
                },
                .Slice => |s| s.len,
                .OpenedRange => continue,
            });
        }

        if (bounds.items.len == 0) {
            return self.report(expr, "cant determine upper bound of the loop", .{});
        }

        const ref = bounds.items[0];
        var check: ?*Node = null;
        for (bounds.items[1..]) |b| {
            const cmp = self.bl.addBinOp(sloc, .ne, .i8, b, ref);
            check = if (check) |c| self.bl.addBinOp(sloc, .band, .i8, c, cmp) else cmp;
        }

        if (check) |c| {
            var arg: Value = undefined;
            self.emitHandlerCall(handler, expr, c, (&arg)[0..1]);
        }
    }

    const prev_scope_height = self.scope.items.len;
    defer self.scope.items.len = prev_scope_height;
    defer self.bl.truncatePins(prev_scope_height);

    for (self.ast.exprs.view(e.iters), iter_data) |iter, data| {
        if (iter.bindings.tag() != .Ident) {
            return self.report(iter.bindings, "TODO: pattern matching", .{});
        }

        const slot = switch (data) {
            inline .OpenedRange, .ClosedRange => |r| r.idx.id.Pointer,
            inline .Slice => |s| s.base.id.Pointer,
        };

        const ty = switch (data) {
            inline .OpenedRange, .ClosedRange => .uint,
            inline .Slice => |s| self.types.makePtr(s.base.ty),
        };

        self.scope.appendAssumeCapacity(.{
            .ty = ty,
            .name = self.ast.exprs.get(iter.bindings).Ident.id,
        });
        self.bl.pushPin(slot);
    }

    self.loops.appendAssumeCapacity(.{
        .id = if (e.label.tag() != .Void) self.ast.exprs.get(e.label).Ident.id else .invalid,
        .defer_base = self.defers.items.len,
        .kind = .{ .Runtime = self.bl.addLoopAndBeginBody(sloc) },
    });

    const cond = for (iter_data) |data| {
        switch (data) {
            .ClosedRange => |r| {
                var idx = r.idx;
                break self.bl.addBinOp(sloc, .ult, .i8, idx.getValue(sloc, self), r.end);
            },
            .Slice => |s| {
                var base = s.base;
                break self.bl.addBinOp(sloc, .ult, .i8, base.getValue(sloc, self), s.bound);
            },
            .OpenedRange => {},
        }
    } else return self.report(e.pos, "cant determine the termination condition", .{});

    var if_builder = self.bl.addIfAndBeginThen(sloc, cond);
    {
        _ = self.emitBranch(e.body);

        for (iter_data) |data| {
            switch (data) {
                inline .OpenedRange, .ClosedRange => |r| {
                    var idx = r.idx;
                    const off = self.bl.addIntImm(sloc, .i64, 1);
                    const next = self.bl.addBinOp(sloc, .iadd, .i64, idx.getValue(sloc, self), off);
                    self.bl.addStore(sloc, r.idx.id.Pointer, .i64, next);
                },
                .Slice => |s| {
                    var base = s.base;
                    const off = self.bl.addIntImm(sloc, .i64, @intCast(base.ty.size(self.types)));
                    const next = self.bl.addBinOp(sloc, .iadd, .i64, base.getValue(sloc, self), off);
                    self.bl.addStore(sloc, s.base.id.Pointer, .i64, next);
                },
            }
        }
    }
    const end_else = if_builder.beginElse(&self.bl);
    {
        _ = self.loopControl(.@"break", expr) catch {};
    }
    if_builder.end(&self.bl, end_else);

    var loop: Builder.Loop = self.loops.pop().?.kind.Runtime;
    loop.end(&self.bl);

    std.debug.assert(!self.bl.isUnreachable());

    return .{};
}

fn emitReturn(self: *Codegen, _: Ctx, expr: Ast.Id, e: *Expr(.Return)) EmitError!Value {
    // we dont use .emitTyped because the ecpression is different
    const sloc = self.src(expr);
    var value = try self.emit(.{ .loc = self.struct_ret_ptr, .ty = self.ret }, e.value);
    try self.typeCheck(expr, &value, self.ret);
    var slots: [2]*Node = undefined;
    const rets = switch (self.abiCata(value.ty)) {
        .Impossible => return self.report(expr, "can't return uninhabited type", .{}),
        .Imaginary => &.{},
        .ByValue => &.{value.getValue(sloc, self)},
        .ByValuePair => |pair| if (self.abi.isByRefRet(self.abiCata(value.ty))) b: {
            self.emitGenericStore(sloc, self.struct_ret_ptr.?, &value);
            break :b &.{};
        } else b: {
            for (pair.types, pair.offsets(), &slots) |t, off, *slt| {
                slt.* = self.bl.addFieldLoad(sloc, value.id.Pointer, @intCast(off), t);
            }
            break :b &slots;
        },
        .ByRef => b: {
            self.emitGenericStore(sloc, self.struct_ret_ptr.?, &value);
            break :b &.{};
        },
    };

    var iter = std.mem.reverseIterator(self.loops.items);
    while (iter.nextPtr()) |l| {
        if (l.kind == .Runtime) {
            l.kind.Runtime.markBreaking();
            break;
        }
    }
    try self.emitDefers(0);
    self.bl.addReturn(rets);
    return error.Unreachable;
}

fn emitUserType(self: *Codegen, _: Ctx, expr: Ast.Id, e: *Expr(.Type)) !Value {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const sloc = self.src(expr);

    const prefix = 5;
    const params = tmp.arena.alloc(graph.AbiParam, prefix + e.captures.len() * 2);
    @memset(params, .{ .Reg = self.abiCata(.type).ByValue });
    params[0] = .{ .Reg = .i64 };
    params[2] = .{ .Reg = .i64 };
    const returns = [_]graph.AbiParam{.{ .Reg = self.abiCata(.type).ByValue }};

    const args = self.bl.allocCallArgs(tmp.arena, params, &returns, null);

    const code: Comptime.InteruptCode = @enumFromInt(@intFromEnum(e.kind) -
        @intFromEnum(Lexer.Lexeme.@"struct"));

    args.arg_slots[0] = self.bl.addIntImm(sloc, .i64, @intCast(@intFromEnum(code)));
    args.arg_slots[1] = self.emitTyConst(self.parent_scope.perm(self.types)).id.Value;
    args.arg_slots[2] = self.bl.addIntImm(sloc, .i64, @intFromEnum(expr));
    args.arg_slots[3] = self.bl.addIntImm(sloc, .i64, @bitCast(@as(u64, @intFromPtr(self.name.ptr))));
    args.arg_slots[4] = self.bl.addIntImm(sloc, .i64, @bitCast(@as(u64, self.name.len)));

    for (self.ast.exprs.view(e.captures), 0..) |cp, slot_idx| {
        var val = try self.loadIdent(cp.pos, cp.id);
        args.arg_slots[prefix + slot_idx * 2 ..][0..2].* = switch (self.abiCata(val.ty)) {
            .Impossible => unreachable, // TODO: wah
            .Imaginary, .ByRef, .ByValuePair => .{ self.emitTyConst(val.ty).id.Value, self.bl.addIntImm(sloc, .i64, 0) },
            .ByValue => .{ self.emitTyConst(val.ty).id.Value, val.getValue(sloc, self) },
        };
    }

    const rets = self.bl.addCall(sloc, .ablecall, Comptime.eca, args);
    return .mkv(.type, rets.?[0]);
}

fn emitFnPtr(self: *Codegen, _: Ctx, _: Ast.Id, e: *Expr(.FnPtr)) !Value {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const args = tmp.arena.alloc(Types.Id, e.args.len());
    for (args, self.ast.exprs.view(e.args)) |*ty, arg| {
        ty.* = try self.resolveAnonTy(arg);
    }

    return self.emitTyConst(self.types.internPtr(.FnPtr, .{
        .args = args,
        .ret = try self.resolveAnonTy(e.ret),
    }));
}

fn emitFn(self: *Codegen, _: Ctx, expr: Ast.Id, e: *Expr(.Fn)) !Value {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const captures = tmp.arena.alloc(Types.Scope.Capture, e.captures.len());

    for (self.ast.exprs.view(e.captures), captures) |cp, *slot| {
        var val = try self.loadIdent(cp.pos, cp.id);

        slot.* = .{
            .id = .fromIdent(cp.id),
            .ty = val.ty,
            .value = try self.partialEval(cp.id, &val),
        };
    }

    const args = tmp.arena.alloc(Types.Id, e.args.len());
    var has_anytypes = false;
    if (e.comptime_args.len() == 0) {
        for (self.ast.exprs.view(e.args), args) |argid, *arg| {
            const ty = argid.ty;
            arg.* = try self.resolveAnonTy(ty);
            has_anytypes = has_anytypes or arg.* == .any;
            if (has_anytypes) break;
        }
    }

    if (e.comptime_args.len() != 0 or has_anytypes) {
        const slot, const alloc = self.types.intern(.Template, .{
            .loc = .{
                .scope = self.parent_scope.perm(self.types),
                .file = self.parent_scope.file(self.types),
                .ast = expr,
            },
            .name = self.name,
            .captures = captures,
        });
        if (!slot.found_existing) {
            self.types.store.get(alloc).key.captures =
                self.types.pool.arena.dupe(Types.Scope.Capture, self.types.store.get(alloc).key.captures);
        }
        return self.emitTyConst(slot.key_ptr.*);
    } else {
        const slot, const alloc = self.types.intern(.Func, .{
            .loc = .{
                .scope = self.parent_scope.perm(self.types),
                .file = self.parent_scope.file(self.types),
                .ast = expr,
            },
            .name = self.name,
            .captures = captures,
        });
        const id = slot.key_ptr.*;
        errdefer _ = self.types.interner.removeContext(id, .{ .types = self.types });
        if (!slot.found_existing) {
            if (!has_anytypes) for (self.ast.exprs.view(e.args), args) |argid, *arg| {
                const ty = argid.ty;
                arg.* = try self.resolveAnonTy(ty);
            };
            const ret = try self.resolveAnonTy(e.ret);
            self.types.store.get(alloc).* = .{
                .key = self.types.store.get(alloc).key,
                .args = self.types.pool.arena.dupe(Types.Id, args),
                .ret = ret,
            };
            self.types.store.get(alloc).key.captures =
                self.types.pool.arena.dupe(
                    Types.Scope.Capture,
                    self.types.store.get(alloc).key.captures,
                );
        }
        return self.emitTyConst(id);
    }
}

fn emitUse(self: *Codegen, _: Ctx, expr: Ast.Id, e: *Expr(.Use)) EmitError!Value {
    switch (e.pos.flag.use_kind) {
        .use => return self.emitTyConst(self.types.getScope(e.file)),
        .embed => {
            const sloc = self.src(expr);
            const file = self.types.getFile(e.file);
            const slot, const alloc = self.types.intern(.Global, .{
                .loc = .{
                    .scope = .void,
                    .file = e.file,
                    .ast = .zeroSized(.Void),
                },
                .name = file.path,
                .captures = &.{},
            });
            if (!slot.found_existing) {
                self.types.store.get(alloc).* = .{
                    .key = self.types.store.get(alloc).key,
                    .data = self.types.pool.arena.dupe(u8, file.source),
                    .ty = self.types.makeSlice(file.source.len, .u8),
                    .readonly = true,
                };
            }
            self.types.queue(self.target, .init(.{ .Global = alloc }));
            return .mkp(
                self.types.store.get(alloc).ty,
                self.bl.addGlobalAddr(sloc, @intFromEnum(alloc)),
            );
        },
    }
}

pub fn emit(self: *Codegen, ctx: Ctx, expr: Ast.Id) EmitError!Value {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const sloc = self.src(expr);
    const ast = self.ast;
    return switch (ast.exprs.get(expr)) {
        .Comment => .{},
        .Void => .{},

        .String => |e| self.emitParseString(ctx, expr, e),
        .Quotes => |e| self.emitParseQuotes(ctx, expr, e),
        .Integer => |e| self.emitInteger(ctx, expr, e),
        .Float => |e| self.emitFloat(ctx, expr, e),
        .Bool => |e| .mkv(.bool, self.bl.addIntImm(sloc, .i8, @intFromBool(e.value))),
        .Null => self.emitNull(ctx, expr),
        .Ident => |e| self.loadIdent(e.pos, e.id),
        .Idk => self.emitIdk(ctx, expr),
        .Ctor => |e| self.emitCtor(ctx, expr, e),
        .Tupl => |e| self.emitTuple(ctx, expr, e),
        .Arry => |e| self.emitArray(ctx, expr, e),

        .SliceTy => |e| self.emitSliceTy(ctx, expr, e),
        .UnOp => |e| self.emitUnOp(ctx, expr, e),
        .Decl => |e| self.emitDecl(expr, e, ctx.in_if_cond),
        .BinOp => |e| self.emitBinOp(ctx, expr, e),
        .Unwrap => |e| self.emitUnwrap(ctx, expr, e),
        .Deref => |e| self.emitParseUnwrap(ctx, expr, e),
        .Tag => |e| self.emitTag(ctx, expr, e),
        .Field => |e| self.emitField(ctx, expr, e),
        .Index => |e| self.emitIndex(ctx, expr, e),

        .Block => |e| self.emitBlock(ctx, expr, e),
        .Defer => |e| {
            self.defers.appendAssumeCapacity(e.*);
            return .{};
        },
        .If => |e| self.emitIf(ctx, expr, e),
        .Match => |e| self.emitMatch(ctx, expr, e),
        .Loop => |e| self.emitLoop(ctx, expr, e),
        .For => |e| self.emitFor(ctx, expr, e),
        .Break => try self.loopControl(.@"break", expr),
        .Continue => self.loopControl(.@"continue", expr),
        .Call => |e| return self.emitCall(ctx, expr, self.abi.cc, e.*),
        .Return => |e| self.emitReturn(ctx, expr, e),
        .Die => {
            self.bl.addTrap(sloc, 0);
            return error.Unreachable;
        },
        .Buty => |e| return self.emitTyConst(.fromLexeme(e.bt)),
        .Type => |e| self.emitUserType(ctx, expr, e),
        .Fn => |e| self.emitFn(ctx, expr, e),
        .FnPtr => |e| self.emitFnPtr(ctx, expr, e),
        .Use => |e| self.emitUse(ctx, expr, e),
        .Directive => |e| return self.emitDirective(ctx, expr, e),
        .Wildcard => return self.report(expr, "wildcard does not make sense here", .{}),
        .Range => return self.report(expr, "range does not make sense here", .{}),
    };
}

pub fn emitSpill(self: *Codegen, expr: Ast.Id, value: *Value) void {
    value.* = .mkv(self.types.makePtr(value.ty), switch (value.id) {
        .Imaginary => self.bl.addIntImm(self.src(expr), .i64, @intCast(value.ty.alignment(self.types))),
        .Value => |v| self.bl.addSpill(self.src(expr), v),
        .Pointer => |p| p,
    });
}

pub fn emitHandlerCall(self: *Codegen, handler: utils.EntId(tys.Func), expr: Ast.Id, check: *Node, arg_values: []Value) void {
    const func: *tys.Func = self.types.store.get(handler);

    var builder = self.bl.addIfAndBeginThen(self.src(expr), check);

    arg_values[0] = self.emitSrcLoc(expr);

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const params, const returns, const ret_abi =
        func.sig().computeAbi(self.abi, self.types, tmp.arena).?;
    const args = self.bl.allocCallArgs(tmp.arena, params, returns, null);

    var i: usize = self.pushReturn(expr, args, ret_abi, func.ret, .{});

    for (func.args, arg_values) |ty, *value| {
        const abi = self.abiCata(ty);
        i += self.pushParam(.none, args, abi, i, value);
    }

    if (i != params.len) {
        utils.panic("{}", .{.{ i, params.len }});
    }

    _ = self.assembleReturn(
        expr,
        @intFromEnum(handler),
        args,
        .{},
        func.ret,
        ret_abi,
        self.abi.cc,
    ) catch {};

    builder.end(&self.bl, builder.beginElse(&self.bl));
}

pub fn emitSrcLoc(self: *Codegen, expr: Ast.Id) Value {
    const sloc = self.src(expr);
    const src_loc = self.bl.addLocal(sloc, self.types.source_loc.size(self.types));
    _ = self.emitString(.{ .loc = src_loc }, self.types.pool.arena.dupe(u8, self.ast.path), expr);
    const line, const col = Ast.lineCol(self.ast.source, self.ast.posOf(expr).index);
    comptime std.debug.assert(@import("builtin").cpu.arch.endian() == .little);
    const pcked = @as(u64, col) << 32 | @as(u64, line);
    _ = self.bl.addFieldStore(sloc, src_loc, 16, .i64, self.bl.addIntImm(sloc, .i64, @intCast(pcked)));
    return .mkp(self.types.source_loc, src_loc);
}

pub fn unwrapNullable(self: *Codegen, expr: Ast.Id, base: *Value, do_check: bool) !void {
    const sloc = self.src(expr);

    self.emitAutoDeref(sloc, base);

    const nullable = self.types.store.unwrap(base.ty.data(), .Nullable) orelse {
        return self.report(expr, "only nullable types can be unwrapped, {} is not", .{base.ty});
    };

    if (!base.ty.needsTag(self.types)) {
        base.ty = nullable.inner;
        return;
    }

    if (do_check) if (self.types.handlers.null_unwrap) |handler| {
        var check = try self.checkNull(expr, base, .@"==");
        var arg_values = [_]Value{undefined};
        self.emitHandlerCall(handler, expr, check.getValue(sloc, self), &arg_values);
    };

    base.* = switch (self.abiCata(nullable.inner)) {
        .Impossible => return self.report(expr, "option of uninhabited type cna not be unwrapped", .{}),
        .Imaginary => .{ .ty = nullable.inner },
        .ByValue, .ByRef, .ByValuePair => switch (base.id) {
            .Imaginary => unreachable,
            .Value => .mkv(nullable.inner, self.bl.addBinOp(
                sloc,
                .ushr,
                self.abiCata(nullable.inner).ByValue,
                base.id.Value,
                self.bl.addIntImm(sloc, .i8, @intCast(nullable.inner.alignment(self.types) * 8)),
            )),
            .Pointer => .mkp(nullable.inner, self.bl.addFieldOffset(
                sloc,
                base.id.Pointer, // TODO: handle value
                @bitCast(nullable.inner.alignment(self.types)),
            )),
        },
    };
}

pub fn emitDecl(
    self: *Codegen,
    expr: Ast.Id,
    e: *const Expr(.Decl),
    unwrap: bool,
) !Value {
    const sloc = self.src(expr);
    const ast = self.ast;
    const loc = self.bl.addLocal(self.src(expr), 0);

    const prev_name = self.name;
    const ident = ast.exprs.getTyped(.Ident, e.bindings) orelse
        return self.report(expr, "TODO: pattern matching", .{});

    errdefer |err| if (err != error.Unreachable) {
        self.scope.appendAssumeCapacity(.{ .ty = .never, .name = ident.id });
        self.bl.pushPin(loc);
    };

    self.name = ast.tokenSrc(ident.id.pos());
    defer self.name = prev_name;

    var value = try if (e.ty.tag() == .Void)
        self.emit(.{ .loc = loc }, e.value)
    else b: {
        const ty = try self.resolveAnonTy(e.ty);
        break :b self.emitTyped(.{ .loc = loc }, ty, e.value);
    };

    self.bl.resizeLocal(loc, value.ty.size(self.types));

    var out = Value{};
    if (unwrap) {
        out = try self.checkNull(e.value, &value, .@"!=");
        try self.unwrapNullable(e.value, &value, false);
    }

    self.emitGenericStore(sloc, loc, &value);

    self.scope.appendAssumeCapacity(.{ .ty = value.ty, .name = ident.id });
    self.bl.pushPin(loc);

    return out;
}

pub fn checkNull(self: *Codegen, expr: Ast.Id, lhs: *Value, op: Lexer.Lexeme) !Value {
    if (lhs.ty.data() != .Nullable) {
        return self.report(expr, "only nullable types can be compared with null," ++
            " {} is not", .{lhs.ty});
    }

    const sloc = self.src(expr);

    const nul: *tys.Nullable = self.types.store.get(lhs.ty.data().Nullable);

    var value = if (nul.nieche.offset(self.types)) |spec|
        self.bl.addFieldLoad(sloc, lhs.id.Pointer, spec.offset, spec.kind.abi())
    else switch (lhs.id) {
        .Imaginary => unreachable,
        .Value => self.bl.addBinOp(sloc, .band, .i8, lhs.id.Value, self.bl
            .addIntImm(sloc, .i8, 255)),
        .Pointer => self.bl.addLoad(sloc, lhs.id.Pointer, .i8),
    };

    if (op == .@"==") {
        value = self.bl.addBinOp(sloc, .eq, .i8, value, self.bl.addIntImm(sloc, value.data_type, 0));
    }

    return .mkv(.bool, value);
}

pub fn typeCheck(self: *Codegen, expr: Ast.Id, got: *Value, expected: Types.Id) !void {
    const sloc = self.src(expr);

    if (self.types.store.unwrap(expected.data(), .Nullable)) |v| if (v.inner == got.ty) {
        if (!expected.needsTag(self.types)) {
            got.ty = expected;
            return;
        }
        const abi = self.abiCata(got.ty);
        switch (abi) {
            .Imaginary => {
                got.* = .mkv(expected, self.bl.addIntImm(sloc, .i8, 1));
            },
            else => {
                const loc = self.bl.addLocal(self.src(expr), expected.size(self.types));
                _ = self.bl.addStore(sloc, loc, .i8, self.bl.addIntImm(sloc, .i8, 1));
                self.emitGenericStore(
                    sloc,
                    self.bl.addFieldOffset(sloc, loc, @bitCast(got.ty.alignment(self.types))),
                    got,
                );
                got.* = .mkp(expected, loc);
            },
        }

        return;
    };

    if (got.ty == .never) return;

    if (!got.ty.canUpcast(expected, self.types)) {
        return self.report(expr, "expected {} got {}", .{ expected, got.ty });
    }

    if (got.ty != expected) {
        if (got.ty.isSigned() and got.ty.size(self.types) < expected.size(self.types)) {
            got.id = .{ .Value = self.bl.addUnOp(
                sloc,
                .sext,
                self.abiCata(expected).ByValue,
                got.getValue(sloc, self),
            ) };
        }

        if ((got.ty.isUnsigned() or got.ty == .bool) and
            got.ty.size(self.types) < expected.size(self.types))
        {
            got.id = .{ .Value = self.bl.addUnOp(
                sloc,
                .uext,
                self.abiCata(expected).ByValue,
                got.getValue(sloc, self),
            ) };
        }

        if (got.ty.data() == .Enum) {
            const len = got.ty.data().Enum.getFields(self.types).len;
            if (len <= 1) {
                got.id = .{ .Value = self.bl.addIntImm(sloc, self.abiCata(expected).ByValue, 0) };
            } else if (got.ty.size(self.types) < expected.size(self.types)) {
                got.id = .{ .Value = self.bl.addUnOp(
                    sloc,
                    .uext,
                    self.abiCata(expected).ByValue,
                    got.getValue(sloc, self),
                ) };
            }
        }

        got.ty = expected;
    }

    return;
}

pub fn report(self: *Codegen, expr: anytype, fmt: []const u8, args: anytype) EmitError {
    self.errored = true;
    self.types.report(self.parent_scope.file(self.types), expr, fmt, args);
    return error.Never;
}

pub fn lexemeToBinOp(self: *Codegen, pos: anytype, lx: Lexer.Lexeme, ty: Types.Id) !graph.BinOp {
    return lexemeToBinOpLow(lx, ty) orelse self.report(pos, "the operator not supported for {}", .{ty});
}

pub fn lexemeToBinOpLow(self: Lexer.Lexeme, ty: Types.Id) ?graph.BinOp {
    const unsigned = ty.isUnsigned() or ty == .bool or ty.data() == .Pointer or
        ty.data() == .Enum or ty == .type;
    const float = ty.isFloat();
    if (!unsigned and !ty.isSigned() and !float) return null;
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
        else => utils.panic("{s}", .{@tagName(self)}),
    };
}

fn emitInternalEca(
    self: *Codegen,
    ctx: Ctx,
    ic: Comptime.InteruptCode,
    args: []const *Node,
    ret_ty: Types.Id,
) Value {
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var builder = Types.Abi.ableos.builder();

    const params = tmp.arena.alloc(graph.AbiParam, 1 + args.len);

    params[0] = .{ .Reg = .i64 };
    for (args, params[1..]) |a, *ca| ca.* = .{ .Reg = a.data_type };
    const ret_buf = tmp.arena.alloc(graph.AbiParam, Types.Abi.Builder.max_elems);
    const returns = builder.types(ret_buf, true, self.abiCata(ret_ty));
    const c_args = self.bl.allocCallArgs(tmp.arena, params, returns, null);

    c_args.arg_slots[0] = self.bl.addIntImm(.none, .i64, @intCast(@intFromEnum(ic)));
    @memcpy(c_args.arg_slots[1..], args);

    return self.assembleReturn(
        Ast.Id.zeroSized(.Void),
        Comptime.eca,
        c_args,
        ctx,
        ret_ty,
        self.abiCata(ret_ty),
        self.abi.cc,
    ) catch unreachable;
}

fn emitStructFoldOp(
    self: *Codegen,
    pos: anytype,
    ty: utils.EntId(root.frontend.types.Struct),
    op: Lexer.Lexeme,
    lhs: *Node,
    rhs: *Node,
) !?*Node {
    const sloc = self.src(pos);
    var fold: ?*Node = null;
    var iter = ty.offsetIter(self.types);
    while (iter.next()) |elem| {
        const lhs_loc = self.bl.addFieldOffset(sloc, lhs, @intCast(elem.offset));
        const rhs_loc = self.bl.addFieldOffset(sloc, rhs, @intCast(elem.offset));
        const value = if (elem.field.ty.data() == .Struct) b: {
            const stru = elem.field.ty.data().Struct;
            break :b try self.emitStructFoldOp(pos, stru, op, lhs_loc, rhs_loc) orelse continue;
        } else b: {
            if (self.abiCata(elem.field.ty) != .ByValue) {
                return self.report(pos, "cant apply the operator" ++
                    " on field of {}", .{elem.field.ty});
            }
            const dt = self.abiCata(elem.field.ty).ByValue;
            const lhs_val = self.bl.addLoad(sloc, lhs_loc, dt);
            const rhs_val = self.bl.addLoad(sloc, rhs_loc, dt);
            const oper = try self.lexemeToBinOp(pos, op, elem.field.ty);
            break :b self.bl.addBinOp(sloc, oper, .i8, lhs_val, rhs_val);
        };
        if (fold) |f| {
            fold = self.bl.addBinOp(sloc, if (op == .@"==") .band else .bor, .i8, f, value);
        } else fold = value;
    }
    return fold;
}

fn emitStructOp(
    self: *Codegen,
    pos: anytype,
    ty: utils.EntId(root.frontend.types.Struct),
    op: Lexer.Lexeme,
    loc: *Node,
    lhs: *Node,
    rhs: *Node,
) !void {
    const sloc = self.src(pos);
    var iter = ty.offsetIter(self.types);
    while (iter.next()) |elem| {
        const field_loc = self.bl.addFieldOffset(sloc, loc, @intCast(elem.offset));
        const lhs_loc = self.bl.addFieldOffset(sloc, lhs, @intCast(elem.offset));
        const rhs_loc = self.bl.addFieldOffset(sloc, rhs, @intCast(elem.offset));
        if (elem.field.ty.data() == .Struct) {
            const stru = elem.field.ty.data().Struct;
            try self.emitStructOp(pos, stru, op, field_loc, lhs_loc, rhs_loc);
        } else {
            if (self.abiCata(elem.field.ty) != .ByValue) {
                return self.report(pos, "cant apply the operator" ++
                    " on field of {}", .{elem.field.ty});
            }
            const dt = self.abiCata(elem.field.ty).ByValue;
            const lhs_val = self.bl.addLoad(sloc, lhs_loc, dt);
            const rhs_val = self.bl.addLoad(sloc, rhs_loc, dt);
            const oper = try self.lexemeToBinOp(pos, op, elem.field.ty);
            const res = self.bl.addBinOp(sloc, oper, dt, lhs_val, rhs_val);
            _ = self.bl.addStore(sloc, field_loc, res.data_type, res);
        }
    }
}

pub fn emitGenericStore(self: *Codegen, sloc: graph.Sloc, loc: *Node, value: *Value) void {
    if (value.id == .Imaginary) return;
    if (value.id == .Pointer and value.id.Pointer == loc) return;

    const cata = self.abiCata(value.ty);

    if (cata == .ByValue) {
        if (cata.ByValue.size() > value.ty.size(self.types)) {
            var storer = graph.DataType.i64;
            var offset: u64 = 0;
            while (offset < value.ty.size(self.types)) {
                while (storer.size() + offset > value.ty.size(self.types)) {
                    storer = @enumFromInt(@intFromEnum(storer) - 1);
                }

                const shifted = self.bl.addBinOp(
                    sloc,
                    .ushr,
                    cata.ByValue,
                    value.getValue(sloc, self),
                    self.bl.addIntImm(sloc, .i64, @intCast(offset * 8)),
                );
                self.bl.addFieldStore(sloc, loc, @intCast(offset), storer, shifted);
                offset += storer.size();
            }
        } else {
            _ = self.bl.addStore(sloc, loc, cata.ByValue, value.getValue(sloc, self));
        }
    } else {
        _ = self.bl.addFixedMemCpy(sloc, loc, value.id.Pointer, value.ty.size(self.types));
    }
}

pub fn resolveAnonTy(self: *Codegen, expr: Ast.Id) !Types.Id {
    const prev_name = self.name;
    defer self.name = prev_name;
    self.name = "";

    var vl = try self.emitTyped(.{}, .type, expr);
    return self.unwrapTyConst(expr, &vl);
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
    return .mkv(.type, self.bl.addIntImm(
        .none,
        self.abiCata(.type).ByValue,
        @bitCast(@as(u64, @intFromEnum(ty))),
    ));
}

pub fn unwrapTyConst(self: *Codegen, pos: anytype, cnst: *Value) !Types.Id {
    if (cnst.ty != .type) {
        return self.report(pos, "expected type, {} is not", .{cnst.ty});
    }
    return Types.Id.fromRaw(
        @truncate(try self.partialEval(pos, cnst)),
        self.types,
    ) orelse {
        return self.report(pos, "type value of this expression is corrupted", .{});
    };
}

pub const LookupResult = union(enum) { ty: Types.Id, cnst: u64 };

pub fn lookupScopeItem(
    self: *Codegen,
    pos: Ast.Pos,
    bsty: Types.Id,
    name: []const u8,
) !Value {
    const sloc = self.src(pos);

    const other_file = bsty.file(self.types) orelse {
        return self.report(pos, "{} does not declare this", .{bsty});
    };
    const ast = self.types.getFile(other_file);
    if (bsty.data() == .Enum) {
        const fields = bsty.data().Enum.getFields(self.types);

        for (fields) |f| {
            if (std.mem.eql(u8, f.name, name))
                if (fields.len <= 1) return .mkv(bsty, null) else {
                    return .mkv(bsty, self.bl.addIntImm(
                        sloc,
                        self.abiCata(bsty).ByValue,
                        @intCast(f.value),
                    ));
                };
        }
    }

    const decl, const path, _ =
        (bsty.index(self.types) orelse {
            return self.report(pos, "the {} does not have a scope," ++
                " so field access does not make sense", .{bsty});
        }).search(name) orelse {
            return self.report(pos, "{} does not declare this", .{bsty});
        };

    const is_read_only = ast.source[ast.posOf(decl).index] == '$';
    return self.resolveGlobal(name, bsty, ast, decl, path, is_read_only);
}

pub fn resolveGlobalLow(
    self: *Codegen,
    name: []const u8,
    bsty: Types.Id,
    ast: *const Ast,
    decl: Ast.Id,
    readonly: bool,
) EmitError!utils.EntId(tys.Global) {
    const vari = ast.exprs.getTyped(.Decl, decl).?;

    // NOTE: we do this here particularly because the explicit type can contain
    // a cycle
    try self.types.ct.addInProgress(vari.value, bsty);
    defer _ = self.types.ct.in_progress.pop().?;

    const prev_scope = self.parent_scope;
    defer {
        self.parent_scope = prev_scope;
        self.ast = self.types.getFile(prev_scope.file(self.types));
    }
    self.parent_scope = .{ .Perm = bsty };
    self.ast = self.types.getFile(self.parent_scope.file(self.types));

    const ty = if (vari.ty.tag() == .Void) null else try self.resolveAnonTy(vari.ty);

    const global_ty, const new = self.types.resolveGlobal(bsty, name, vari.value, readonly);
    const global_id = global_ty.data().Global;
    if (new) {
        errdefer self.errored = true;
        try self.types.ct.evalGlobal(name, global_id, ty, vari.value);
    }
    self.types.queue(self.target, .init(.{ .Global = global_id }));

    return global_id;
}

pub fn resolveGlobal(
    self: *Codegen,
    name: []const u8,
    bsty: Types.Id,
    ast: *const Ast,
    decl: Ast.Id,
    path: []Ast.Pos,
    readonly: bool,
) EmitError!Value {
    const vari = ast.exprs.getTyped(.Decl, decl).?;
    const global_id = try self.resolveGlobalLow(name, bsty, ast, decl, readonly);

    const global = self.types.store.get(global_id).*;
    if (path.len != 0) {
        if (global.ty != .type)
            return self.report(vari.value, "expected a global holding" ++
                " a type, {} is not", .{global.ty});

        var report_scope = bsty;
        var cur: Types.Id = @enumFromInt(@as(
            Types.IdRepr,
            @bitCast(global.data[0..@sizeOf(Types.Id)].*),
        ));

        for (path, 0..) |ps, i| {
            var vl = try self.lookupScopeItem(ps, cur, ast.tokenSrc(ps.index));

            const prev_scope = self.parent_scope;
            defer self.parent_scope = prev_scope;
            self.parent_scope = .{ .Perm = report_scope };
            report_scope = cur;

            if (i == path.len - 1) {
                return vl;
            } else {
                cur = try self.unwrapTyConst(ps, &vl);
            }
        }
    }

    // TODO: fix the location
    return .mkp(global.ty, self.bl.addGlobalAddr(.none, @intFromEnum(global_id)));
}

pub fn loadIdent(self: *Codegen, expr: Ast.Pos, id: Ast.Ident) !Value {
    const sloc = self.src(expr);
    const ast = self.ast;
    for (self.scope.items, 0..) |se, i| {
        if (se.name == id) {
            if (se.ty == .never) return error.Never;
            const value = self.bl.getPinValue(i);
            return .mkp(se.ty, value);
        }
    } else {
        var cursor = self.parent_scope;
        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();
        var slot: Types.Scope.Capture = undefined;
        const decl, const path, _ = while (!cursor.empty()) {
            if (cursor.index(self.types)) |idx| if (idx.search(id)) |v| break v;
            if (cursor.findCapture(expr, id, self.types, &slot)) |c| {
                return .{ .ty = c.ty, .id = switch (self.abiCata(c.ty)) {
                    .Impossible => return error.Unreachable,
                    .Imaginary => .Imaginary,
                    .ByValue => |v| .{
                        .Value = self.bl.addIntImm(sloc, v, @bitCast(c.value)),
                    },
                    .ByValuePair, .ByRef => b: {
                        self.types.queue(self.target, .init(.{ .Global = @enumFromInt(c.value) }));
                        break :b .{ .Pointer = self.bl.addGlobalAddr(sloc, @intCast(c.value)) };
                    },
                } };
            }
            cursor = cursor.parent(self.types);
        } else {
            self.report(expr, "can not access the identifier", .{}) catch {};
            return self.report(id, "the idnet is declared here", .{});
        };

        return self.resolveGlobal(
            ast.tokenSrc(id.pos()),
            cursor.perm(self.types),
            ast,
            decl,
            path,
            ast.source[ast.posOf(decl).index] == '$',
        );
    }
}

pub fn emitCall(self: *Codegen, ctx: Ctx, expr: Ast.Id, cc: graph.CallConv, e: Expr(.Call)) !Value {
    const sloc = self.src(expr);
    const ast = self.ast;
    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    var typ_res: Value, var caller: ?Value = if (e.called.tag() == .Tag) b: {
        const pos = ast.exprs.getTyped(.Tag, e.called).?;
        const name = ast.tokenSrc(pos.index + 1);
        const ty = ctx.ty orelse {
            return self.report(e.called, "can infer the implicit access," ++
                " you can specify the type: <ty>.{}", .{name});
        };

        break :b .{ try self.lookupScopeItem(pos.*, ty, name), null };
    } else if (e.called.tag() == .Field) b: {
        const field = ast.exprs.getTyped(.Field, e.called).?;
        const name = ast.tokenSrc(field.field.index);
        var value = try self.emit(.{}, field.base);

        if (value.ty == .type) {
            break :b .{ try self.lookupScopeItem(
                field.field,
                try self.unwrapTyConst(field.base, &value),
                name,
            ), null };
        }

        const ty = if (self.types.store.unwrap(value.ty.data(), .Pointer)) |p|
            p.*
        else
            value.ty;
        break :b .{ try self.lookupScopeItem(field.field, ty, name), value };
    } else b: {
        break :b .{ try self.emit(.{}, e.called), null };
    };

    var computed_args: ?[]Value = null;
    var was_template = false;
    const sig, const ptr, const literal_func = if (typ_res.ty == .type) b: {
        var typ = try self.unwrapTyConst(expr, &typ_res);

        was_template = typ.data() == .Template;
        if (was_template) {
            computed_args, typ = try self.instantiateTemplate(&caller, tmp.arena, expr, e, typ);
        }

        const func: *tys.Func = self.types.store.unwrap(typ.data(), .Func) orelse {
            return self.report(e.called, "{} is not callable", .{typ});
        };

        break :b .{ func.sig(), null, typ };
    } else b: {
        const func: *tys.FnPtr = self.types.store.unwrap(typ_res.ty.data(), .FnPtr) orelse {
            return self.report(e.called, "{} is not callable", .{typ_res.ty});
        };

        break :b .{ func.*, typ_res.getValue(sloc, self), null };
    };

    if (literal_func) |typ| {
        const func: root.frontend.types.Func = self.types.store.get(typ.data().Func).*;
        if (self.target != .runtime or func.ret != .type)
            self.types.queue(self.target, .init(.{ .Func = typ.data().Func }));
    }

    const passed_args = e.args.len() + @intFromBool(caller != null);
    if (!was_template and passed_args != sig.args.len) {
        return self.report(expr, "expected {} arguments," ++
            " got {}", .{ sig.args.len, passed_args });
    }

    const params, const returns, const ret_abi =
        sig.computeAbi(self.abi, self.types, tmp.arena) orelse {
            std.debug.assert(computed_args == null);
            const args_ast = ast.exprs.view(e.args);
            for (sig.args[@intFromBool(caller != null)..], 0..) |ty, k| {
                _ = self.emitTyped(.{}, ty, args_ast[k]) catch |err| switch (err) {
                    error.Unreachable => return error.Unreachable,
                    error.Never => {},
                };
            }
            unreachable;
        };
    const args = self.bl.allocCallArgs(tmp.arena, params, returns, ptr);

    var i: usize = self.pushReturn(expr, args, ret_abi, sig.ret, ctx);

    if (caller) |*value| {
        if (value.ty.data() == .Pointer and sig.args[0].data() != .Pointer) {
            value.id = .{ .Pointer = value.getValue(sloc, self) };
            value.ty = self.types.store.get(value.ty.data().Pointer).*;
        }

        if (value.ty.data() != .Pointer and sig.args[0].data() == .Pointer) {
            self.emitSpill(expr, value);
        }

        try self.typeCheck(e.called, value, sig.args[0]);

        const abi = self.abiCata(value.ty);
        i += self.pushParam(sloc, args, abi, i, value);
    }

    const args_ast = ast.exprs.view(e.args);
    for (sig.args[@intFromBool(caller != null)..], 0..) |ty, k| {
        const abi = self.abiCata(ty);
        var value = if (computed_args) |a| a[k] else try self.emitTyped(.{}, ty, args_ast[k]);
        i += self.pushParam(self.src(args_ast[k]), args, abi, i, &value);
    }

    if (i != params.len) {
        utils.panic("{}", .{.{ i, params.len }});
    }

    return self.assembleReturn(
        expr,
        if (literal_func) |ty| @intFromEnum(ty.data().Func) else null,
        args,
        ctx,
        sig.ret,
        ret_abi,
        cc,
    );
}

pub fn instantiateTemplate(
    self: *Codegen,
    caller: *?Value,
    tmp: *utils.Arena,
    expr: Ast.Id,
    e: Expr(.Call),
    typ: Types.Id,
) !struct { []Value, Types.Id } {
    errdefer self.errored = true;

    const tmpl = self.types.store.get(typ.data().Template).*;
    const ast = self.ast;

    const scope = self.types.store.add(self.types.pool.allocator(), tmpl);
    self.types.store.get(scope).temporary = true;
    self.types.store.get(scope).key.loc.scope = typ;
    self.types.store.get(scope).key.captures = &.{};

    const tmpl_file = self.types.getFile(tmpl.key.loc.file);
    const tmpl_ast = tmpl_file.exprs.getTyped(.Fn, tmpl.key.loc.ast).?;
    const comptime_args = tmpl_file.exprs.view(tmpl_ast.comptime_args);

    const passed_args = e.args.len() + @intFromBool(caller.* != null);
    if (passed_args != tmpl_ast.args.len()) {
        return self.report(expr, "expected {} arguments," ++
            " got {}", .{ tmpl_ast.args.len(), passed_args });
    }

    const captures = tmp.alloc(Types.Scope.Capture, tmpl_ast.args.len());
    const arg_tys = tmp.alloc(Types.Id, tmpl_ast.args.len() - tmpl_ast.comptime_args.len());
    const arg_exprs = tmp.alloc(Value, arg_tys.len);

    var capture_idx: usize = 0;
    var comptime_idx: usize = 0;
    var arg_idx: usize = 0;
    var arg_expr_idx: usize = 0;
    var expr_idx: usize = 0;
    var caller_slot: ?*Value = if (caller.*) |*c| c else null;

    const template_scope: Scope = .{ .Perm = .init(.{ .Template = scope }) };

    for (tmpl_file.exprs.view(tmpl_ast.args)) |param| {
        const arg: union(enum) { Value: *Value, Expr: Ast.Id } =
            if (caller_slot) |c|
                .{ .Value = c }
            else
                .{ .Expr = ast.exprs.view(e.args)[expr_idx] };

        const binding = tmpl_file.exprs.getTyped(.Ident, param.bindings).?;
        if (binding.pos.flag.@"comptime") {
            const ty = try self.types.ct.evalTy("", template_scope, param.ty);
            captures[capture_idx] = .{
                .id = .fromIdent(comptime_args[comptime_idx]),
                .ty = ty,
                .value = if (ty == .type)
                    @intFromEnum(switch (arg) {
                        .Value => |v| try self.unwrapTyConst(expr, v),
                        .Expr => |ex| try self.resolveAnonTy(ex),
                    })
                else switch (arg) {
                    .Value => |v| try self.partialEval(expr, v),
                    .Expr => |ar| b: {
                        var val = try self.emitTyped(.{}, ty, ar);
                        break :b try self.partialEval(ar, &val);
                    },
                },
            };
            capture_idx += 1;
            comptime_idx += 1;
            self.types.store.get(scope).key.captures = captures[0..capture_idx];
        } else {
            arg_tys[arg_idx] = try self.types.ct.evalTy("", template_scope, param.ty);
            if (arg_tys[arg_idx] == .any) {
                arg_tys[arg_idx] = switch (arg) {
                    .Value => |v| v.ty,
                    .Expr => |ar| b: {
                        arg_exprs[arg_expr_idx] = try self.emit(.{}, ar);
                        break :b arg_exprs[arg_expr_idx].ty;
                    },
                };
                captures[capture_idx] = .{ .id = .fromIdent(binding.id), .ty = arg_tys[arg_idx] };
                captures[capture_idx].id.from_any = true;
                capture_idx += 1;
                self.types.store.get(scope).key.captures = captures[0..capture_idx];
            } else if (arg == .Expr) {
                arg_exprs[arg_expr_idx] =
                    try self.emitTyped(.{}, arg_tys[arg_idx], arg.Expr);
            }

            arg_expr_idx += @intFromBool(caller_slot == null);
            arg_idx += 1;
        }

        expr_idx += @intFromBool(caller_slot == null);
        caller_slot = null;
    }

    const ret = try self.types.ct.evalTy("", template_scope, tmpl_ast.ret);

    const slot, const alloc = self.types.intern(.Func, .{
        .loc = .{
            .scope = typ,
            .file = tmpl.key.loc.file,
            .ast = tmpl.key.loc.ast,
        },
        .name = "-",
        .captures = captures[0..capture_idx],
    });

    if (!slot.found_existing) {
        const alc = self.types.store.get(alloc);
        alc.* = .{
            .key = alc.key,
            .args = self.types.pool.arena.dupe(Types.Id, arg_tys),
            .ret = ret,
        };
        alc.key.captures =
            self.types.pool.arena.dupe(Types.Scope.Capture, alc.key.captures);
        alc.is_inline = tmpl.is_inline;
    }

    return .{ arg_exprs, slot.key_ptr.* };
}

fn pushReturn(
    self: *Codegen,
    pos: anytype,
    call_args: Builder.CallArgs,
    ret_abi: Types.Abi.Spec,
    ret: Types.Id,
    ctx: Ctx,
) usize {
    if (self.abi.isByRefRet(ret_abi)) {
        call_args.arg_slots[0] = ctx.loc orelse
            self.bl.addLocal(self.src(pos), ret.size(self.types));
        return 1;
    } else {
        return 0;
    }
}

fn pushParam(
    self: *Codegen,
    sloc: graph.Sloc,
    call_args: Builder.CallArgs,
    abi: Types.Abi.Spec,
    idx: usize,
    value: *Value,
) usize {
    var len: usize = 1;
    switch (abi) {
        .Impossible => unreachable,
        .Imaginary => {
            len = 0;
        },
        .ByValue => {
            if (call_args.params[idx] == .Stack) {
                call_args.arg_slots[idx] = self.bl.addSpill(.none, value.getValue(sloc, self));
            } else {
                call_args.arg_slots[idx] = value.getValue(sloc, self);
            }
        },
        .ByValuePair => |pair| {
            if (call_args.params[idx] == .Stack) {
                call_args.arg_slots[idx] = value.id.Pointer;
            } else {
                for (pair.types, pair.offsets(), 0..) |t, off, j| {
                    call_args.arg_slots[idx + j] =
                        self.bl.addFieldLoad(sloc, value.id.Pointer, @intCast(off), t);
                }
                len = 2;
            }
        },
        .ByRef => call_args.arg_slots[idx] = value.id.Pointer,
    }
    return len;
}

fn assembleReturn(
    self: *Codegen,
    expr: anytype,
    id: ?u32,
    call_args: Builder.CallArgs,
    ctx: Ctx,
    ret: Types.Id,
    ret_abi: Types.Abi.Spec,
    cc: graph.CallConv,
) !Value {
    const sloc = self.src(expr);
    const rets = self.bl.addCall(sloc, cc, id orelse graph.indirect_call, call_args);
    return switch (ret_abi) {
        .Impossible => return error.Unreachable,
        .Imaginary => .mkv(ret, null),
        .ByValue => .mkv(ret, rets.?[0]),
        .ByValuePair => |pair| if (self.abi.isByRefRet(ret_abi)) b: {
            break :b .mkp(ret, call_args.arg_slots[0]);
        } else b: {
            const slot = ctx.loc orelse self.bl.addLocal(sloc, ret.size(self.types));
            for (pair.types, pair.offsets(), rets.?) |ty, off, vl| {
                self.bl.addFieldStore(sloc, slot, @intCast(off), ty, vl);
            }
            break :b .mkp(ret, slot);
        },
        .ByRef => .mkp(ret, call_args.arg_slots[0]),
    };
}

fn emitDefers(self: *Codegen, base: usize) !void {
    var iter = std.mem.reverseIterator(self.defers.items[base..]);
    while (iter.next()) |e| {
        _ = try self.emitTyped(.{}, .void, e);
    }
}

fn loopControl(self: *Codegen, kind: Builder.Loop.Control, ctrl: Ast.Id) !Value {
    if (self.loops.items.len == 0) {
        return self.report(ctrl, "{} outside of the loop", .{@tagName(kind)});
    }

    const label = switch (self.ast.exprs.get(ctrl)) {
        .Break => |b| b.label,
        .Continue => |b| b.label,
        .Loop => |b| b.label,
        .For => |b| b.label,
        else => unreachable,
    };

    const id = if (label.tag() != .Void) self.ast.exprs.get(label).Ident.id else .invalid;

    var cursor = std.mem.reverseIterator(self.loops.items);
    const loop = while (cursor.nextPtr()) |p| {
        if (p.id == id) break p;
    } else {
        if (label.tag() == .Void) {
            return self.report(ctrl, "break is missing a explicit label", .{});
        } else {
            return self.report(ctrl, "the label did not refer to a loop", .{});
        }
    };
    try self.emitDefers(loop.defer_base);
    switch (loop.kind) {
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

pub fn emitAutoDeref(self: *Codegen, sloc: graph.Sloc, value: *Value) void {
    if (value.ty.data() == .Pointer) {
        value.id = .{ .Pointer = value.getValue(sloc, self) };
        value.ty = self.types.store.get(value.ty.data().Pointer).*;
    }
}

pub const StringEncodeResutl = union(enum) {
    ok: []u8,
    err: struct { reason: []const u8, pos: usize },
};

pub fn encodeString(
    literal: []const u8,
    buf: []u8,
) !StringEncodeResutl {
    const SPECIAL_CHARS = "nrt\\'\"0";
    const TO_BYTES = "\n\r\t\\\'\"\x00";

    std.debug.assert(SPECIAL_CHARS.len == TO_BYTES.len);

    var alc = std.heap.FixedBufferAllocator.init(buf);
    var str = std.ArrayListUnmanaged(u8).initBuffer(buf);
    var bytes = std.mem.splitScalar(u8, literal, '\\');

    while (bytes.next()) |chunk| {
        try str.appendSlice(alc.allocator(), chunk);
        if (bytes.rest().len == 0) break;
        switch (bytes.rest()[0]) {
            '{' => {
                var hex_bytes = bytes.rest();
                var i: usize = 1;
                while (i < hex_bytes.len and hex_bytes[i] != '}') : (i += 2) {
                    if (i + 1 >= hex_bytes.len) {
                        return .{ .err = .{
                            .reason = "incomplete escape sequence",
                            .pos = literal.len - bytes.rest().len,
                        } };
                    }
                    const byte_val = std.fmt.parseInt(u8, hex_bytes[i .. i + 2], 16) catch {
                        return .{ .err = .{
                            .reason = "expected hex digit or '}'",
                            .pos = literal.len - bytes.rest().len,
                        } };
                    };
                    try str.append(alc.allocator(), byte_val);
                }
                bytes.index.? += i + 1;
            },
            else => |b| {
                for (SPECIAL_CHARS, TO_BYTES) |s, sb| {
                    if (s == b) {
                        try str.append(alc.allocator(), sb);
                        break;
                    }
                } else return .{ .err = .{
                    .reason = "unknown escape sequence",
                    .pos = literal.len - bytes.rest().len,
                } };
                bytes.index.? += 1;
            },
        }
    }

    return .{ .ok = str.items };
}

pub fn partialEvalLow(self: *Codegen, pos: u32, value: *Value, can_recover: bool) !u64 {
    const file = self.parent_scope.file(self.types);
    return switch (self.types.ct.partialEval(
        file,
        self.parent_scope.perm(self.types),
        pos,
        &self.bl,
        switch (self.abiCata(value.ty)) {
            .Impossible, .Imaginary => return 0,
            .ByValue => value.getValue(.none, self),
            .ByValuePair, .ByRef => value.id.Pointer,
        },
        value.ty,
    )) {
        .Resolved => |r| r,
        .Arbitrary => |a| @intFromEnum(a),
        .Unsupported => |n| {
            if (can_recover) {
                return 0;
            }
            return self.report(pos, "can't evaluate this at compile time (yet)," ++
                " (DEBUG: got stuck on {})", .{n});
        },
    };
}

pub fn posOf(self: *Codegen, pos: anytype) Ast.Pos {
    return self.types.posOf(self.parent_scope.file(self.types), pos);
}

pub fn partialEval(self: *Codegen, pos: anytype, value: *Value) !u64 {
    return self.partialEvalLow(self.posOf(pos).index, value, false);
}

pub fn binOpUpcast(self: *Codegen, lhs: Types.Id, rhs: Types.Id) !Types.Id {
    if (lhs == rhs) return lhs;
    if (lhs.canUpcast(rhs, self.types)) return rhs;
    if (rhs.canUpcast(lhs, self.types)) return lhs;
    return error.@"incompatible types";
}

pub fn emitBranch(self: *Codegen, block: Ast.Id) usize {
    const prev_scope_height = self.scope.items.len;
    defer self.scope.items.len = prev_scope_height;
    defer self.bl.truncatePins(prev_scope_height);

    const prev_defer_height = self.defers.items.len;
    defer self.defers.items.len = prev_defer_height;

    _ = self.emitTyped(.{}, .void, block) catch |err|
        return @intFromBool(err == error.Unreachable);

    self.emitDefers(prev_defer_height) catch |err|
        return @intFromBool(err == error.Unreachable);

    return 0;
}

fn emitString(self: *Codegen, ctx: Ctx, data: []u8, expr: Ast.Id) Value {
    const sloc = self.src(expr);
    const global = self.types.addUniqueGlobal(self.parent_scope.perm(self.types));
    self.types.store.get(global).key.name = data;
    self.types.store.get(global).data = data;
    self.types.store.get(global).ty = self.types.makeSlice(data.len, .u8);
    self.types.queue(self.target, .init(.{ .Global = global }));

    const slice_ty = self.types.string;
    const slice_loc = ctx.loc orelse
        self.bl.addLocal(self.src(expr), slice_ty.size(self.types));
    self.bl.addFieldStore(
        sloc,
        slice_loc,
        TySlice.ptr_offset,
        .i64,
        self.bl.addGlobalAddr(sloc, @intFromEnum(global)),
    );
    self.bl.addFieldStore(
        sloc,
        slice_loc,
        TySlice.len_offset,
        .i64,
        self.bl.addIntImm(sloc, .i64, @intCast(data.len)),
    );

    return .mkp(slice_ty, slice_loc);
}

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
    try std.testing.expect(try matchTriple("hbvm-ableos", "hbvm-ableos"));
    try std.testing.expect(try matchTriple("*-b-c", "a-b-c"));
    try std.testing.expect(try matchTriple("*-c", "a-b-c"));
    try std.testing.expect(try matchTriple("a", "a-b-c"));
    try std.testing.expect(!try matchTriple("*-a", "a-b-c"));
    try std.testing.expectError(error.@"consecutive '*' are redundant", matchTriple("*-*-a", "a-b-c"));
    try std.testing.expectError(error.@"trailing '*' is redundant", matchTriple("*-b-*", "a-b-c"));
}

fn reportInferrence(
    cg: *Codegen,
    exr: anytype,
    ty: []const u8,
    dir_name: []const u8,
) EmitError {
    return cg.report(exr, "type can not be inferred from the context," ++
        " use `@as(<{}>, {}(...))`", .{ ty, dir_name });
}

inline fn assertDirectiveArgs(
    cg: *Codegen,
    exr: anytype,
    got: []const Ast.Id,
    comptime expected: []const u8,
) !void {
    const varargs = comptime std.mem.endsWith(u8, expected, "..");
    const min_expected_args = comptime std.mem.count(u8, expected, ",") +
        @intFromBool(expected.len != 0) - @intFromBool(varargs);
    try assertDirectiveArgsLow(cg, exr, got, expected, min_expected_args, varargs);
}

fn assertDirectiveArgsLow(
    cg: *Codegen,
    exr: Ast.Id,
    got: []const Ast.Id,
    expected: []const u8,
    min_expected_args: usize,
    varargs: bool,
) !void {
    if (got.len < min_expected_args or (!varargs and got.len > min_expected_args)) {
        const range = if (varargs) "at least " else "";
        return cg.report(
            exr,
            "directive takes {}{} arguments, got {} ({})",
            .{ range, min_expected_args, got.len, expected },
        );
    }
}

fn emitComptimeDirectiveEca(self: *Codegen, ctx: Ctx, expr: Ast.Id, code: Comptime.InteruptCode, ret_ty: Types.Id) !Value {
    var vl = try self.emitTyped(.{}, .type, expr);

    return self.emitInternalEca(ctx, code, &.{
        self.bl.addIntImm(.none, .i64, @bitCast(self.src(expr))),
        vl.getValue(self.src(expr), self),
    }, ret_ty);
}

fn emitDirective(
    self: *Codegen,
    ctx: Ctx,
    expr: Ast.Id,
    e: *const Expr(.Directive),
) !Value {
    const sloc = self.src(expr);
    const ast = self.ast;

    const name = ast.tokenSrc(e.pos.index);
    const args = ast.exprs.view(e.args);

    switch (e.kind) {
        .use, .embed => unreachable,
        .CurrentScope => {
            try assertDirectiveArgs(self, expr, args, "");
            return self.emitTyConst(self.parent_scope.firstType(self.types));
        },
        .RootScope => {
            try assertDirectiveArgs(self, expr, args, "");
            return self.emitTyConst(self.types.file_scopes[0]);
        },
        .TypeOf => {
            try assertDirectiveArgs(self, expr, args, "<ty>");
            const ty = try self.types.ct.inferType("", .{ .Tmp = self }, .{}, args[0]);
            return self.emitTyConst(ty);
        },
        .@"inline" => {
            try assertDirectiveArgs(self, expr, args, "<called>, <args>..");
            return self.emitCall(ctx, expr, .@"inline", .{
                .called = args[0],
                .arg_pos = ast.posOf(args[0]),
                .args = e.args.slice(1, e.args.len()),
            });
        },
        .int_cast => {
            try assertDirectiveArgs(self, expr, args, "<expr>");

            const ret: Types.Id = ctx.ty orelse {
                return reportInferrence(self, expr, "int-ty", name);
            };

            if (!ret.isInteger()) {
                return self.report(expr, "inferred type must be an integer," ++
                    " {} is not", .{ret});
            }

            var oper = try self.emit(.{}, args[0]);

            if (!oper.ty.isInteger()) {
                return self.report(args[0], "expeced integer, {} is not", .{oper.ty});
            }

            return .mkv(ret, self.bl.addUnOp(
                sloc,
                .ired,
                self.abiCata(ret).ByValue,
                oper.getValue(sloc, self),
            ));
        },
        .float_cast => {
            try assertDirectiveArgs(self, expr, args, "<float>");

            var oper = try self.emit(.{}, args[0]);

            const ret: Types.Id = switch (oper.ty) {
                .f32 => .f64,
                .f64 => .f32,
                else => return self.report(expr, "expected float argument," ++
                    " {} is not", .{oper.ty}),
            };

            return .mkv(ret, self.bl.addUnOp(
                sloc,
                .fcst,
                self.abiCata(ret).ByValue,
                oper.getValue(sloc, self),
            ));
        },
        .int_to_float => {
            try assertDirectiveArgs(self, expr, args, "<float>");

            const ret: Types.Id = ctx.ty orelse {
                return reportInferrence(self, expr, "float-ty", name);
            };

            if (!ret.isFloat())
                return self.report(expr, "expected this to evaluate to float," ++
                    " {} is not", .{ret});

            var oper = try self.emitTyped(.{}, .int, args[0]);

            return .mkv(ret, self.bl.addUnOp(
                sloc,
                .itf,
                self.abiCata(ret).ByValue,
                oper.getValue(sloc, self),
            ));
        },
        .float_to_int => {
            try assertDirectiveArgs(self, expr, args, "<float>");
            const ret: Types.Id = .int;

            var oper = try self.emit(.{}, args[0]);

            if (!oper.ty.isFloat())
                return self.report(args[0], "expected float, {} is not", .{oper.ty});

            return .mkv(ret, self.bl.addUnOp(sloc, .fti, .i64, oper.getValue(sloc, self)));
        },
        .bit_cast => {
            try assertDirectiveArgs(self, expr, args, "<expr>");

            const ret: Types.Id = ctx.ty orelse {
                return reportInferrence(self, expr, "ty", name);
            };

            var oper = try self.emit(.{}, args[0]);

            if (oper.ty.size(self.types) != ret.size(self.types)) {
                return self.report(
                    args[0],
                    "cant bitcast from {} to {} because sizes are not equal ({} != {})",
                    .{ oper.ty, ret, oper.ty.size(self.types), ret.size(self.types) },
                );
            }

            const to_abi = self.abiCata(ret);

            if (to_abi != .ByValue) {
                const loc = self.bl.addLocal(sloc, ret.size(self.types));
                self.emitGenericStore(sloc, loc, &oper);
                return .mkp(ret, loc);
            } else {
                if ((oper.ty.isInteger() and ret.isFloat()) or
                    (oper.ty.isFloat() and ret.isInteger()))
                {
                    oper.id.Value = self.bl.addCast(sloc, to_abi.ByValue, oper.id.Value);
                }
                oper.ty = ret;
                return oper;
            }
        },
        .ChildOf => {
            try assertDirectiveArgs(self, expr, args, "<ty>");
            if (self.target == .@"comptime") {
                return self.emitComptimeDirectiveEca(ctx, args[0], .ChildOf, .type);
            }

            const ty = try self.resolveAnonTy(args[0]);
            const child = ty.child(self.types) orelse {
                return self.report(args[0], "directive only work on pointer" ++
                    " types and slices, {} is not", .{ty});
            };
            return self.emitTyConst(child);
        },
        .kind_of => {
            try assertDirectiveArgs(self, expr, args, "<ty>");
            if (self.target == .@"comptime") {
                return self.emitComptimeDirectiveEca(ctx, args[0], .kind_of, .i8);
            }

            const len = try self.resolveAnonTy(args[0]);
            return .mkv(.u8, self.bl.addIntImm(sloc, .i8, @intFromEnum(len.data())));
        },
        .len_of => {
            try assertDirectiveArgs(self, expr, args, "<ty>");

            if (self.target == .@"comptime") {
                return self.emitComptimeDirectiveEca(ctx, args[0], .len_of, .uint);
            }

            const ty = try self.resolveAnonTy(args[0]);
            const len = ty.len(self.types) orelse {
                return self.report(args[0], "directive only works on structs" ++
                    " and arrays, {} is not", .{ty});
            };
            return .mkv(.uint, self.bl.addIntImm(sloc, .i64, @intCast(len)));
        },
        .field_name => {
            try assertDirectiveArgs(self, expr, args, "<ty>, <index>");

            const ty = try self.resolveAnonTy(args[0]);
            if (ty.data() != .Struct) {
                return self.report(args[0], "expected struct type, {} is not", .{ty});
            }
            var idx_value = try self.emitTyped(.{}, .uint, args[1]);
            const idx = try self.partialEval(args[1], &idx_value);
            const fields: []const tys.Struct.Field = ty.data().Struct.getFields(self.types);
            if (idx >= fields.len) {
                return self.report(
                    args[1],
                    "index is {}, but struct has only {} fields",
                    .{ idx, fields.len },
                );
            }
            return self.emitString(ctx, self.types.pool.arena.dupe(u8, fields[@intCast(idx)].name), expr);
        },
        .name_of => {
            try assertDirectiveArgs(self, expr, args, "<ty/enum-variant>");

            var value = try self.emit(.{}, args[0]);

            const data = if (value.ty == .type) dt: {
                const ty = try self.unwrapTyConst(args[0], &value);
                break :dt std.fmt.allocPrint(
                    self.types.pool.arena.allocator(),
                    "{}",
                    .{ty.fmt(self.types)},
                ) catch unreachable;
            } else switch (value.ty.data()) {
                .Enum => |enum_ty| dt: {
                    if (self.target == .@"comptime") {
                        var vl = try self.emit(.{}, args[0]);
                        if (vl.ty.data() != .Enum) {
                            return self.report(args[0], "this only works on enum" ++
                                " values, {} is not", .{vl.ty});
                        }

                        const string = self.types.makeSlice(null, .u8);
                        return self.emitInternalEca(
                            ctx,
                            .name_of,
                            &.{ self.emitTyConst(vl.ty).id.Value, vl.getValue(sloc, self) },
                            string,
                        );
                    }

                    const fields = enum_ty.getFields(self.types);
                    if (fields.len == 1) {
                        break :dt self.types.pool.arena.dupe(u8, fields[0].name);
                    }

                    const id = try self.partialEval(args[0], &value);
                    if (id >= fields.len)
                        return self.report(args[0], "the enum value is" ++
                            " out of range or the enum", .{});
                    break :dt self.types.pool.arena.dupe(u8, fields[@intCast(id)].name);
                },
                else => return self.report(
                    args[0],
                    "can't compute a name of {}",
                    .{value.ty},
                ),
            };

            return self.emitString(ctx, data, expr);
        },
        .align_of => {
            try assertDirectiveArgs(self, expr, args, "<ty>");
            if (self.target == .@"comptime") {
                return self.emitComptimeDirectiveEca(ctx, args[0], .align_of, .uint);
            }
            const ty = try self.resolveAnonTy(args[0]);
            return .mkv(.uint, self.bl.addIntImm(sloc, .i64, @bitCast(ty.alignment(self.types))));
        },
        .size_of => {
            try assertDirectiveArgs(self, expr, args, "<ty>");
            if (self.target == .@"comptime") {
                return self.emitComptimeDirectiveEca(ctx, args[0], .size_of, .uint);
            }
            const ty = try self.resolveAnonTy(args[0]);
            return .mkv(.uint, self.bl.addIntImm(sloc, .i64, @bitCast(ty.size(self.types))));
        },
        .target => {
            try assertDirectiveArgs(self, expr, args, "<string>");
            const content = ast.exprs.getTyped(.String, args[0]) orelse
                return self.report(expr, "@target takes a \"string\"", .{});
            const str_content = ast.source[content.pos.index + 1 .. content.end - 1];
            const triple = self.types.target;
            const matched = matchTriple(str_content, triple) catch |err| {
                return self.report(args[0], "{}", .{@errorName(err)});
            };
            return .mkv(.bool, self.bl.addIntImm(sloc, .i8, @intFromBool(matched)));
        },
        .is_comptime => return .mkv(.bool, self.bl.addIntImm(
            sloc,
            .i8,
            @intFromBool(self.target == .@"comptime"),
        )),
        .ecall, .syscall => {
            if (self.target == .@"comptime") {
                return self.report(expr, "cant do na ecall/syscall during comptime", .{});
            }

            if (e.kind == .ecall and self.abi.cc != .ablecall) {
                return self.report(expr, "@ecall is specific to vm" ++
                    " targets use @syscall instead", .{});
            }

            try assertDirectiveArgs(self, expr, args, "<expr>..");
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const ret = ctx.ty orelse {
                return reportInferrence(self, expr, "ty", name);
            };

            const arg_nodes = tmp.arena.alloc(Value, args.len);
            const argums = tmp.arena.alloc(Types.Id, args.len);
            for (args, arg_nodes, argums) |arg, *slot, *argum| {
                slot.* = try self.emit(.{}, arg);
                argum.* = slot.ty;
            }

            var dummy_func: tys.FnPtr = undefined;
            dummy_func.args = argums;
            dummy_func.ret = ret;

            const params, const returns, const ret_abi =
                dummy_func.computeAbi(.ableos, self.types, tmp.arena) orelse unreachable;
            const call_args = self.bl.allocCallArgs(tmp.arena, params, returns, null);

            var i: usize = self.pushReturn(expr, call_args, ret_abi, ret, ctx);

            for (arg_nodes, args) |*arg, argn| {
                i += self.pushParam(self.src(argn), call_args, self.abiCata(arg.ty), i, arg);
            }

            return self.assembleReturn(expr, Comptime.eca, call_args, ctx, ret, ret_abi, .ablecall);
        },
        .as => {
            try assertDirectiveArgs(self, expr, args, "<ty>, <expr>");
            const ty = try self.resolveAnonTy(args[0]);
            return self.emitTyped(ctx, ty, args[1]);
        },
        .@"error" => {
            try assertDirectiveArgs(self, expr, args, "<ty/string>..");
            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var msg = std.ArrayList(u8).init(tmp.arena.allocator());
            for (args) |arg| switch (arg.tag()) {
                .String => {
                    const s = ast.exprs.getTyped(.String, arg).?;
                    msg.appendSlice(ast.source[s.pos.index + 1 .. s.end - 1]) catch unreachable;
                },
                else => {
                    var value = try self.emit(.{}, arg);
                    if (value.ty == .type) {
                        msg.writer().print("{}", .{
                            (try self.unwrapTyConst(arg, &value)).fmt(self.types),
                        }) catch unreachable;
                    } else {
                        return self.report(arg, "only types and strings" ++
                            " are supported here, {} is not", .{value.ty});
                    }
                },
            };

            return self.report(expr, "{}", .{msg.items});
        },
        .Any => return self.emitTyConst(.any),
        .has_decl => {
            try assertDirectiveArgs(self, expr, args, "<expr>, <string-name>");

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const name_ast = ast.exprs.get(args[1]);
            if (name_ast != .String)
                return self.report(args[1], "the name needs to be hardcoded (for now)", .{});
            const name_str = ast.source[name_ast.String.pos.index + 1 .. name_ast.String.end - 1];

            var ty_val = try self.emitTyped(.{}, .type, args[0]);
            const ty = try self.unwrapTyConst(args[0], &ty_val);

            const has_decl = (ty.index(self.types) orelse
                return .mkv(.bool, self.bl.addIntImm(sloc, .i8, 0)))
                .search(name_str) != null;

            return .mkv(.bool, self.bl.addIntImm(sloc, .i8, @intFromBool(has_decl)));
        },
        .handler, .@"export" => return self.report(expr, "can only be used in the file scope", .{}),
        .import => return self.report(expr, "can be only used as a body of the function", .{}),
        .frame_pointer => return .mkv(.uint, self.bl.addFramePointer(sloc, .i64)),
        .SrcLoc => return self.emitTyConst(self.types.source_loc),
    }
}
