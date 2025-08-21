const std = @import("std");
const aro = @import("aro");
const hb = @import("hb");
const utils = hb.utils;
const backend = hb.backend;
const Machine = backend.Machine;
const Builder = backend.Builder;
const graph = hb.backend.graph;
const Node = Builder.BuildNode;

pub fn isSigned(ty: aro.QualType, comp: *const aro.Compilation) bool {
    return switch (ty.type(comp)) {
        .int => |int| int.isSigned(),
        .typedef => |typedef| isSigned(typedef.base, comp),
        else => false,
    };
}

pub fn main() !void {
    utils.Arena.initScratch(1024 * 1024 * 4);

    const gpa = std.heap.smp_allocator;
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    var pool = hb.utils.Pool{ .arena = hb.utils.Arena.init(1024 * 1024 * 4) };

    var stdout = std.fs.File.stdout().writer(&.{});

    var stderr = std.fs.File.stderr().writer(&.{});

    var diags = aro.Diagnostics{
        .output = .{ .to_writer = .{
            .writer = &stderr.interface,
            .color = std.io.tty.detectConfig(std.fs.File.stderr()),
        } },
    };
    var comp = try aro.Compilation.initDefault(gpa, arena.allocator(), &diags, std.fs.cwd());

    try comp.addBuiltinIncludeDir("zig-out/include/", null);
    try comp.addSystemIncludeDir("/usr/include/");
    const source = try comp.addSourceFromPath("main.c");
    const macros = try comp.addSourceFromBuffer("foo.c", "");

    var d = aro.Driver{ .comp = &comp, .diagnostics = &diags, .aro_name = "arocc" };

    const builtin_macros = comp.generateBuiltinMacros(d.system_defines) catch |er| switch (er) {
        error.FileTooBig => return d.fatal("builtin macro source exceeded max size", .{}),
        else => |e| return e,
    };

    const tree, var pp = try processSource(&d, source, builtin_macros, macros);

    const target = Machine.SupportedTarget.fromStr("x86_64-linux").?;

    const bckend = target.toMachine(&pool);
    const call_conv = target.toCallConv();
    var gen = Codegen{
        .gpa = gpa,
        .call_conv = call_conv,
        .comp = &comp,
        .tree = tree,
        .preprocessor = &pp,
        .bd = Builder.init(pool.allocator()),
        .backend = bckend,
    };

    for (tree.root_decls.items) |decl| {
        const dcl = decl.get(&tree);
        switch (dcl) {
            .function => |fn_decl| {
                defer _ = gen.bd.func.reset();

                const name = try comp.internString(tree.tokSlice(fn_decl.name_tok));
                try gen.functions.put(gpa, name, {});

                const body = fn_decl.body orelse continue;

                const func: aro.TypeStore.Type.Func = fn_decl.qt.get(&comp, .func).?;

                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();

                var params = std.ArrayList(graph.AbiParam).empty;

                for (func.params) |param| {
                    try params.appendSlice(
                        tmp.arena.allocator(),
                        categorize(param.qt, &comp, tmp.arena),
                    );
                }

                var returns = std.ArrayList(graph.AbiParam).empty;
                try returns.appendSlice(
                    tmp.arena.allocator(),
                    categorize(func.return_type, &comp, tmp.arena),
                );

                const token = gen.bd.begin(call_conv, params.items, returns.items);

                for (func.params, 0..) |param, i| {
                    try gen.scope.put(gpa, param.name, .mkp(param.qt, gen.bd.addSpill(
                        .none,
                        gen.bd.addParam(.none, i, 0),
                        0,
                    )));
                }

                _ = try gen.emit(.{}, body);

                if (!gen.bd.isUnreachable()) {
                    const return_values = tmp.arena.alloc(*Node, returns.items.len);
                    for (returns.items, return_values) |ret, *return_value| {
                        return_value.* = gen.bd.addIntImm(.none, ret.Reg, 0);
                    }
                    gen.bd.addReturn(return_values);
                }

                gen.bd.end(token);

                bckend.emitFunc(&gen.bd.func, .{
                    .id = @intCast(gen.functions.getIndex(name).?),
                    .is_inline = fn_decl.@"inline",
                    .linkage = if (fn_decl.static) .local else .exported,
                    .optimizations = .{ .opts = .{ .mode = .release } },
                    .builtins = .{},
                    .name = tree.tokSlice(fn_decl.name_tok),
                });
            },
            else => {},
        }
    }

    try tree.dump(.escape_codes, &stderr.interface);

    bckend.finalize(.{
        .output = &stdout.interface,
        .optimizations = .{ .mode = .release },
        .builtins = .{},
    });
}

const Value = struct {
    qt: aro.QualType,
    data: union(enum) {
        Imaginary,
        Pointer: *Node,
        Value: *Node,
    } = .Imaginary,

    const none = Value{ .qt = .void };

    pub fn mkv(ty: aro.QualType, data: *Node) Value {
        return Value{ .qt = ty, .data = .{ .Value = data } };
    }

    pub fn mkp(ty: aro.QualType, data: *Node) Value {
        return Value{ .qt = ty, .data = .{ .Pointer = data } };
    }

    pub fn asValue(self: Value, codegen: *Codegen) *Node {
        return switch (self.data) {
            .Imaginary => unreachable,
            .Pointer => codegen.bd.addLoad(.none, self.data.Pointer, codegen.cata(self.qt)),
            .Value => self.data.Value,
        };
    }

    pub fn asNode(self: Value) ?*Node {
        return switch (self.data) {
            .Imaginary => null,
            .Pointer => self.data.Pointer,
            .Value => self.data.Value,
        };
    }
};

const Ctx = struct {
    loc: ?*Node = null,
};

const Codegen = struct {
    gpa: std.mem.Allocator,
    call_conv: graph.CallConv,
    comp: *aro.Compilation,
    preprocessor: *aro.Preprocessor,
    tree: aro.Tree,
    bd: Builder,
    scope: std.AutoArrayHashMapUnmanaged(aro.StringInterner.StringId, Value) = .empty,
    functions: std.AutoArrayHashMapUnmanaged(aro.StringInterner.StringId, void) = .empty,
    globals: std.AutoArrayHashMapUnmanaged(aro.StringInterner.StringId, void) = .empty,
    backend: Machine,
    loops: std.ArrayListUnmanaged(Builder.Loop) = .empty,

    pub fn cata(self: *Codegen, qt: aro.QualType) graph.DataType {
        var tmp = utils.Arena.scrath(null);
        defer tmp.deinit();
        return categorize(qt, self.comp, tmp.arena)[0].Reg;
    }

    pub fn emitGenericStore(self: *Codegen, slot: *Node, value: Value) void {
        if (value.data == .Imaginary) return;
        if (value.data == .Pointer and value.data.Pointer == slot) return;

        const ct = self.cata(value.qt);
        self.bd.addStore(.none, slot, ct, value.data.Value);
    }

    pub fn emit(self: *Codegen, ctx: Ctx, ast: aro.Tree.Node.Index) !Value {
        return switch (ast.get(&self.tree)) {
            .compound_stmt => |compound_stmt| {
                for (compound_stmt.body) |stmt| {
                    _ = try self.emit(.{}, stmt);
                }
                return .none;
            },
            .return_stmt => |return_stmt| {
                const scope_frame = self.scope.entries.len;
                defer self.scope.entries.len = scope_frame;

                if (return_stmt.operand == .expr) {
                    // TODO: pass the return loc if needed
                    const value = try self.emit(.{}, return_stmt.operand.expr);
                    self.bd.addReturn(&.{value.data.Value});
                }

                return .none;
            },
            .int_literal => |int_literal| {
                const ty = self.cata(int_literal.qt);

                const is_signed = isSigned(int_literal.qt, self.comp);

                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();
                var value_str = self.tree.tokSlice(int_literal.literal_tok);
                var radix: u8 = 10;

                if (std.mem.startsWith(u8, value_str, "0x")) {
                    value_str = value_str[2..];
                    radix = 16;
                }

                if (std.mem.startsWith(u8, value_str, "0b")) {
                    value_str = value_str[2..];
                    radix = 2;
                }

                if (std.mem.startsWith(u8, value_str, "0o")) {
                    value_str = value_str[2..];
                    radix = 8;
                }

                if (std.mem.endsWith(u8, value_str, "u") or
                    std.mem.endsWith(u8, value_str, "U") or
                    std.mem.endsWith(u8, value_str, "l") or
                    std.mem.endsWith(u8, value_str, "L"))
                {
                    value_str = value_str[0 .. value_str.len - 1];
                }

                if (std.mem.endsWith(u8, value_str, "ul")) {
                    value_str = value_str[0 .. value_str.len - 2];
                }

                const value: i64 = switch (ty) {
                    .i8, .i16, .i32, .i64 => if (is_signed)
                        try std.fmt.parseInt(i64, value_str, radix)
                    else
                        @bitCast(try std.fmt.parseInt(u64, value_str, radix)),
                    .f32 => @as(u32, @bitCast(try std.fmt.parseFloat(f32, value_str))),
                    .f64 => @bitCast(try std.fmt.parseFloat(f64, value_str)),
                    else => unreachable,
                };
                return .mkv(int_literal.qt, self.bd.addIntImm(.none, ty, value));
            },
            .float_literal => |float_literal| {
                const ty = self.cata(float_literal.qt);
                const value_str = self.tree.tokSlice(float_literal.literal_tok);
                const value: i64 = switch (ty) {
                    .f32 => @as(u32, @bitCast(try std.fmt.parseFloat(f32, value_str))),
                    .f64 => @bitCast(try std.fmt.parseFloat(f64, value_str)),
                    else => unreachable,
                };
                return .mkv(float_literal.qt, self.bd.addIntImm(.none, ty, value));
            },
            .add_expr,
            .sub_expr,
            .mul_expr,
            .div_expr,
            .mod_expr,
            .bit_or_expr,
            .bit_and_expr,
            .bit_xor_expr,
            .shl_expr,
            .shr_expr,
            .less_than_expr,
            => |expr| {
                const lhs = try self.emit(.{}, expr.lhs);
                const rhs = try self.emit(.{}, expr.rhs);

                const is_signed = isSigned(expr.qt, self.comp);
                const is_float = expr.qt.type(self.comp) == .float;

                const op: graph.BinOp = switch (ast.get(&self.tree)) {
                    .add_expr => if (is_float) .fadd else .iadd,
                    .sub_expr => if (is_float) .fsub else .isub,
                    .mul_expr => if (is_float) .fmul else .imul,
                    .div_expr => if (is_signed) .sdiv else .udiv,
                    .mod_expr => if (is_signed) .smod else .umod,
                    .bit_or_expr => .bor,
                    .bit_and_expr => .band,
                    .bit_xor_expr => .bxor,
                    .shl_expr => .ishl,
                    .shr_expr => if (is_signed) .sshr else .ushr,
                    .less_than_expr => if (is_float) .flt else if (is_signed) .slt else .ult,
                    else => utils.panic("not implemented yet: {any}", .{ast.get(&self.tree)}),
                };

                return .mkv(expr.qt, self.bd.addBinOp(
                    .none,
                    op,
                    self.cata(expr.qt),
                    lhs.asValue(self),
                    rhs.asValue(self),
                ));
            },
            .addr_of_expr => |addr_of_expr| {
                const value = try self.emit(.{}, addr_of_expr.operand);

                switch (value.data) {
                    .Imaginary => unreachable,
                    .Pointer => |ptr| return .mkv(addr_of_expr.qt, ptr),
                    .Value => |val| return .mkv(addr_of_expr.qt, self.bd.addSpill(.none, val, 0)),
                }
            },
            .post_inc_expr, .post_dec_expr => |post_inc_expr| {
                const value = try self.emit(.{}, post_inc_expr.operand);
                const op: graph.BinOp = switch (ast.get(&self.tree)) {
                    .post_inc_expr => .iadd,
                    .post_dec_expr => .isub,
                    else => unreachable,
                };

                const ct = self.cata(value.qt);
                const post = self.bd.addBinOp(
                    .none,
                    op,
                    ct,
                    value.asValue(self),
                    self.bd.addIntImm(.none, ct, 1),
                );

                self.bd.addStore(.none, value.data.Pointer, ct, post);

                return .mkv(value.qt, value.asValue(self));
            },
            .compound_literal_expr => |literal| {
                return self.emit(.{}, literal.initializer);
            },
            .member_access_expr => |access_expr| {
                const base = try self.emit(.{}, access_expr.base);
                switch (base.qt.type(self.comp)) {
                    .@"struct" => |strct| {
                        const field = strct.fields[access_expr.member_index];
                        const offset = field.layout.offset_bits / 8;
                        return .mkp(access_expr.qt, self.bd.addFieldOffset(.none, base.asNode().?, @intCast(offset)));
                    },
                    .@"union" => {
                        return .mkp(access_expr.qt, base.asNode().?);
                    },
                    else => unreachable,
                }
            },
            .cast => |cast| {
                const value = try self.emit(.{}, cast.operand);

                switch (cast.kind) {
                    .no_op => return value,
                    .lval_to_rval => return .mkv(value.qt, value.asValue(self)),
                    .function_to_pointer => return .mkv(cast.qt, value.data.Value),
                    .array_to_pointer => return value,
                    .int_cast => {
                        switch (cast.qt.sizeCompare(value.qt, self.comp)) {
                            .gt => return .mkv(cast.qt, self.bd.addUnOp(
                                .none,
                                if (isSigned(value.qt, self.comp)) .sext else .uext,
                                self.cata(cast.qt),
                                value.data.Value,
                            )),
                            .eq => return value,
                            .lt => return .mkv(cast.qt, self.bd.addUnOp(
                                .none,
                                .ired,
                                self.cata(cast.qt),
                                value.data.Value,
                            )),
                            else => |e| utils.panic("not implemented yet: {any}", .{e}),
                        }
                    },
                    else => |e| utils.panic("not implemented yet: {any}", .{e}),
                }
            },
            .array_init_expr => |init_expr| {
                const elem = init_expr.container_qt.type(self.comp).array.elem;
                const elem_ty = self.cata(elem);
                const size = init_expr.container_qt.sizeof(self.comp);

                const slot = ctx.loc orelse self.bd.addLocal(.none, size, 0);

                var i: usize = 0;
                for (init_expr.items) |item| {
                    const itm = item.get(&self.tree);
                    if (itm == .array_filler_expr) {
                        const len = itm.array_filler_expr.count;
                        const value = self.bd.addIntImm(.none, elem_ty, 0);
                        for (0..len) |j| {
                            const offset = (i + j) * elem.sizeof(self.comp);
                            self.bd.addFieldStore(.none, slot, @intCast(offset), elem_ty, value);
                        }
                        i += len;
                    } else {
                        const offset = self.bd.addFieldOffset(.none, slot, @intCast(i * elem.sizeof(self.comp)));
                        const value = try self.emit(.{ .loc = offset }, item);
                        self.emitGenericStore(offset, value);
                        i += 1;
                    }
                }

                return .mkp(init_expr.container_qt, slot);
            },
            .struct_init_expr => |init_expr| {
                const slot = ctx.loc orelse self.bd.addLocal(.none, init_expr.container_qt.sizeof(self.comp), 0);

                const ty = init_expr.container_qt.type(self.comp).@"struct";
                for (init_expr.items, ty.fields) |item, field| {
                    const loc = self.bd.addFieldOffset(.none, slot, @intCast(field.layout.offset_bits / 8));
                    const value = try self.emit(.{ .loc = loc }, item);
                    self.emitGenericStore(loc, value);
                }

                return .mkp(init_expr.container_qt, slot);
            },
            .assign_expr => |assign_expr| {
                const lhs = try self.emit(.{}, assign_expr.lhs);
                const rhs = try self.emit(.{ .loc = lhs.data.Pointer }, assign_expr.rhs);
                self.emitGenericStore(lhs.data.Pointer, rhs);
                return .none;
            },
            .array_access_expr => |access_expr| {
                const base = try self.emit(.{}, access_expr.base);
                const index = try self.emit(.{}, access_expr.index);

                const elem = if (base.qt.type(self.comp) == .pointer)
                    base.qt.type(self.comp).pointer.child
                else
                    base.qt.type(self.comp).array.elem;
                return .mkp(elem, self.bd.addIndexOffset(.none, base.asNode().?, .iadd, elem.sizeof(self.comp), index.data.Value));
            },
            .decl_ref_expr => |decl_ref_expr| {
                switch (decl_ref_expr.decl.get(&self.tree)) {
                    .function => |fn_decl| {
                        const func_id = self.functions.getIndex(try self.comp.internString(self.tree.tokSlice(decl_ref_expr.name_tok))).?;
                        return .mkv(fn_decl.qt, self.bd.addFuncAddr(.none, @intCast(func_id)));
                    },
                    .param, .variable => {
                        return self.scope.get(try self.comp.internString(self.tree.tokSlice(decl_ref_expr.name_tok))).?;
                    },
                    else => |vl| utils.panic("not implemented yet: {any}", .{vl}),
                }
            },
            .paren_expr => |paren_expr| {
                return try self.emit(ctx, paren_expr.operand);
            },
            .string_literal_expr => |string_literal_expr| {
                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();

                const lvalue = self.tree.tokSlice(string_literal_expr.literal_tok);

                var buf = tmp.arena.makeArrayList(u8, lvalue.len);

                var i: usize = 0;
                while (i < lvalue.len) : (i += 1) {
                    buf.appendAssumeCapacity(lvalue[i]);
                    if (lvalue[i] == '\\') {
                        i += 1;
                        switch (lvalue[i]) {
                            'n' => buf.appendAssumeCapacity('\n'),
                            't' => buf.appendAssumeCapacity('\t'),
                            'r' => buf.appendAssumeCapacity('\r'),
                            '\\' => buf.appendAssumeCapacity('\\'),
                            '"' => buf.appendAssumeCapacity('"'),
                            else => unreachable,
                        }
                    }
                }

                self.backend.emitData(.{
                    .id = @intCast(self.globals.entries.len),
                    .name = lvalue,
                    .value = .{ .init = buf.items },
                    .readonly = true,
                });
                try self.globals.put(self.gpa, .empty, {});

                return .mkv(
                    try self.comp.type_store.put(self.gpa, .{ .pointer = .{
                        .child = .char,
                        .decayed = null,
                    } }),
                    self.bd.addGlobalAddr(.none, @intCast(self.globals.entries.len - 1)),
                );
            },
            .for_stmt => |for_stmt| {
                const scope_frame = self.scope.entries.len;
                defer self.scope.entries.len = scope_frame;

                for (for_stmt.init.decls) |init| {
                    _ = try self.emit(.{}, init);
                }

                try self.loops.append(
                    self.gpa,
                    self.bd.addLoopAndBeginBody(.none),
                );

                if (for_stmt.cond) |cond| {
                    const cnd = try self.emit(.{}, cond);
                    var ifb = self.bd.addIfAndBeginThen(.none, cnd.data.Value);
                    _ = try self.emit(.{}, for_stmt.body);
                    const end = ifb.beginElse(&self.bd);
                    self.loops.items[self.loops.items.len - 1]
                        .addControl(&self.bd, .@"break");
                    ifb.end(&self.bd, end);
                } else {
                    _ = try self.emit(.{}, for_stmt.body);
                }

                var loop = self.loops.pop().?;

                if (for_stmt.incr) |incr| {
                    loop.joinContinues(&self.bd);
                    _ = try self.emit(.{}, incr);
                }

                loop.end(&self.bd);

                return .none;
            },
            .variable => |variable| {
                const name = try self.comp.internString(self.tree.tokSlice(variable.name_tok));

                const slot = self.bd.addLocal(.none, variable.qt.sizeof(self.comp), 0);

                if (variable.initializer) |some| {
                    const value = try self.emit(.{ .loc = slot }, some);
                    self.emitGenericStore(slot, value);
                }

                try self.scope.put(self.gpa, name, .mkp(variable.qt, slot));

                return .none;
            },
            .struct_decl => return .none,
            .call_expr => |call_expr| {
                // TODO: struct return
                const callee = try self.emit(.{}, call_expr.callee);

                var tmp = utils.Arena.scrath(null);
                defer tmp.deinit();

                const func = callee.qt.type(self.comp).pointer.child.type(self.comp).func;

                var params = std.ArrayList(graph.AbiParam).empty;

                for (func.params) |param| {
                    try params.append(tmp.arena.allocator(), .{ .Reg = self.cata(param.qt) });
                }

                var varargs: []Value = &.{};
                if (func.kind == .variadic) {
                    varargs = tmp.arena.alloc(Value, call_expr.args.len - func.params.len);
                    for (call_expr.args[func.params.len..], varargs) |arg, *slot| {
                        slot.* = try self.emit(.{}, arg);
                    }
                }

                for (varargs) |arg| {
                    try params.append(tmp.arena.allocator(), .{ .Reg = self.cata(arg.qt) });
                }

                var returns = std.ArrayList(graph.AbiParam).empty;
                try returns.append(tmp.arena.allocator(), .{ .Reg = self.cata(func.return_type) });

                const args = self.bd.allocCallArgs(tmp.arena, params.items, returns.items, callee.data.Value);
                for (call_expr.args, args.arg_slots) |arg, *arg_slot| {
                    arg_slot.* = (try self.emit(.{}, arg)).asNode().?;
                }

                for (varargs, args.arg_slots[func.params.len..]) |arg, *arg_slot| {
                    arg_slot.* = arg.data.Value;
                }

                const rets = self.bd.addCall(.none, self.call_conv, graph.indirect_call, args);
                return .mkv(call_expr.qt, rets.?[0]);
            },
            inline else => |v, t| utils.panic("not implemented yet: {any} {any}", .{ t, v }),
        };
    }
};

fn categorize(param: aro.QualType, comp: *const aro.Compilation, arena: *utils.Arena) []graph.AbiParam {
    return arena.dupe(graph.AbiParam, &.{switch (param.type(comp)) {
        .void => return &.{},
        .int => |i| .{ .Reg = switch (i.bits(comp)) {
            8 => .i8,
            16 => .i16,
            32 => .i32,
            64 => .i64,
            else => unreachable,
        } },
        .pointer => .{ .Reg = switch (comp.target.ptrBitWidth()) {
            32 => .i32,
            64 => .i64,
            else => unreachable,
        } },
        .float => |float| switch (float.bits(comp)) {
            32 => .{ .Reg = .f32 },
            64 => .{ .Reg = .f64 },
            else => unreachable,
        },
        .typedef => |td| return categorize(td.base, comp, arena),
        else => utils.panic("not implemented yet: {any}", .{param.type(comp)}),
    }});
}

fn processSource(
    d: *aro.Driver,
    source: aro.Source,
    builtin: aro.Source,
    user_macros: aro.Source,
) !struct { aro.Tree, aro.Preprocessor } {
    d.comp.generated_buf.items.len = 0;

    var pp = try aro.Preprocessor.initDefault(d.comp);

    if (d.comp.langopts.ms_extensions) {
        d.comp.ms_cwd_source_id = source.id;
    }
    const dump_mode = d.debug_dump_letters.getPreprocessorDumpMode();
    if (d.verbose_pp) pp.verbose = true;
    if (d.only_preprocess) {
        pp.preserve_whitespace = true;
        if (d.line_commands) {
            pp.linemarkers = if (d.use_line_directives) .line_directives else .numeric_directives;
        }
        switch (dump_mode) {
            .macros_and_result, .macro_names_and_result => pp.store_macro_tokens = true,
            .result_only, .macros_only => {},
        }
    }

    try pp.preprocessSources(&.{ source, builtin, user_macros });

    return .{ try pp.parse(), pp };
}
