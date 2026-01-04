bsc := @use("../hb-basic/lib.hb")
mod := @CurrentScope()

Args := struct {
	.root: ^u8;
}

emit := fn(bytes: []u8): void return @syscall(1, 1, bytes)

main := fn(argc: uint, argv: ^^u8): int {
	bsc.Arena.init_scratch(4096 * 128)

	args := Args.{root: argv[..argc][1]}

	fd := bsc.sys.openat(bsc.sys.at_fdcwd, args.root, .readonly, .empty).unwrap()

	stat: bsc.sys.Stat = idk
	_ = bsc.sys.stat(fd, &stat).unwrap()

	tmp := bsc.Arena.scratch(null)
	defer tmp.pop()

	file_bytes := tmp.arena.alloc(u8, @int_cast(stat.size + 1))
	i := 0
	while i < file_bytes.len - 1 {
		i += @int_cast(bsc.sys.read(fd, file_bytes[i..]).unwrap())
	}
	file_bytes[file_bytes.len - 1] = 0

	lexer := Lexer.(0, file_bytes)

	parser := Parser.{
		path: bsc.mem.str_to_slice(args.root),
		lexer: .(0, file_bytes),
		tok: idk,
		tmp: tmp.arena,
	}

	parser.tok = parser.lexer.next()

	num_buf: [10]u8 = idk

	loop:m {
		if parser.tok.kind == .eof break:m

		fn_name := parser.expect_or_skip(.ident) || continue:m

		parser.begin_fn(parser.src(fn_name))

		emit(parser.src(fn_name))
		emit(":\n")

		_ = parser.expect(.decl) || continue:m

		match parser.tok.kind {
			.k_fn => {
				parser.tok = parser.lexer.next()

				_ = parser.expect(.lpar) || continue:m

				par_idx := 0
				while parser.tok.kind != .rpar {
					if parser.tok.kind == .eof {
						parser.report(parser.tok.pos, "expected )")
						break:m
					}

					var_name := parser.expect_or_skip(.ident) || continue

					idx := parser.next_tmp()
					parser.scope.push(tmp.arena, .{
						name: parser.src(var_name),
						idx,
					})

					emit("  set ")
					parser.access(.{tmp: idx})
					emit(" param")
					emit(bsc.fmt.display_int(par_idx, num_buf[..]))
					emit("\n")
				}
				_ = parser.expect(.rpar) || continue:m

				_ = parser.expr()

				if bsc.mem.eql(u8, parser.curr_fn, "main") {
					emit("  end\n")
				}
			},
			_ => {
				msg := bsc.ArrayList(u8).empty
				msg.push_slice(tmp.arena, "expected function, got ")
				msg.push_slice(tmp.arena, parser.tok.kind.name())

				parser.report(parser.tok.pos, msg.items)
				continue:m
			},
		}
	}

	return 0
}

Parser := struct {
	.curr_fn: []u8 = "";
	.tmp_lable_idx: uint = 0;
	.tmp_value_idx: uint = 0;
	.path: []u8;
	.lexer: Lexer;
	.tok: Lexer.Token;
	.scope: bsc.ArrayList(Var) = .empty;
	.loops: bsc.ArrayList(Loop) = .empty;
	.tmp: ^bsc.Arena

	Var := struct{.name: []u8; .idx: uint}
	Loop := struct{.id: uint}

	begin_fn := fn(self: ^Parser, fn_name: []u8): void {
		self.curr_fn = fn_name
		self.tmp_lable_idx = 0
		self.tmp_value_idx = 0
	}

	src := fn(self: ^Parser, tok: Lexer.Token): []u8 {
		return self.lexer.source[tok.pos..tok.end]
	}

	report := fn(self: ^Parser, pos: uint, msg: []u8): void {
		mod.report(self.path, self.lexer.source, pos, msg)
	}

	expect_or_skip := fn(self: ^Parser, kind: Lexer.Token.Kind): ?Lexer.Token {
		tok := self.expect(kind)
		if tok == null {
			self.tok = self.lexer.next()
		}
		return tok
	}

	expect := fn(self: ^Parser, kind: Lexer.Token.Kind): ?Lexer.Token {
		if self.tok.kind != kind {
			tmp := bsc.Arena.scratch(null)
			defer tmp.pop()

			msg := bsc.ArrayList(u8).empty

			msg.push_slice(tmp.arena, "expected ")
			msg.push_slice(tmp.arena, kind.name())
			msg.push_slice(tmp.arena, ", got ")
			msg.push_slice(tmp.arena, self.tok.kind.name())

			self.report(self.tok.pos, msg.items)

			return null
		}

		// TODO: formatting bug
		defer self.tok = self.lexer.next()

		return self.tok
	}

	Value := union(enum) {
		.tmp: uint;
		.sym: []u8;
	}

	expr := fn(self: ^Parser): Value {
		return self.expr_prec(255)
	}

	expr_prec := fn(self: ^Parser, prec: u8): Value {
		ptok := self.tok
		self.tok = self.lexer.next()

		res: Value = .{tmp: 0}
		match ptok.kind {
			.lbrc => {
				prev_scope := self.scope.items.len
				defer self.scope.items.len = prev_scope

				while self.tok.kind != .rbrc {
					if self.tok.kind == .eof {
						self.report(self.tok.pos, "expected }")
						break
					}

					_ = self.expr()
				}
				_ = self.expect(.rbrc)
			},
			.k_return => {
				if self.tok.kind != .semi {
					ret := self.expr()
					emit("  set retval0 ")
					self.access(ret)
					emit("\n")
				}

				emit("  op add @counter ")
				emit(self.curr_fn)
				emit(".ret_addr 1\n")
			},
			.k_loop => {
				id := self.next_lable()
				self.render_lable(id, "loopback")
				emit(":\n")

				self.loops.push(self.tmp, .{id})

				_ = self.expr()

				emit("  jump ")
				self.render_lable(id, "loopback")
				emit(" always x false\n")

				self.render_lable(id, "loopend")
				emit(":\n")

				self.loops.items.len -= 1
			},
			.k_continue => {
				if self.loops.items.len == 0 {
					self.report(self.tok.pos, "continue outside of loop")
					return .{tmp: 0}
				}

				@loop := self.loops.items[self.loops.items.len - 1]

				emit("  jump ")
				self.render_lable(@loop.id, "loopback")
				emit(" always x false\n")
			},
			.k_break => {
				if self.loops.items.len == 0 {
					self.report(self.tok.pos, "break outside of loop")
					return .{tmp: 0}
				}

				@loop := self.loops.items[self.loops.items.len - 1]

				emit("  jump ")
				self.render_lable(@loop.id, "loopend")
				emit(" always x false\n")
			},
			.k_if => {
				cond := self.expr()

				id := self.next_lable()

				emit("  jump ")
				self.render_lable(id, "iffalse")
				emit(" notEqual ")
				self.access(cond)
				emit(" true\n")

				_ = self.expr()

				has_else := self.tok.kind == .k_else

				if has_else {
					self.tok = self.lexer.next()

					emit("  jump ")
					self.render_lable(id, "ifend")
					emit(" always x false\n")

					_ = self.expr()
				}

				self.render_lable(id, "iffalse")
				emit(":\n")

				if has_else {
					self.render_lable(id, "ifend")
					emit(":\n")
				}
			},
			.number => {
				tmp := self.next_tmp()
				emit("  set ")
				self.access(.{tmp})
				emit(" ")
				emit(self.src(ptok))
				emit("\n")

				res = .{tmp: tmp}
			},
			.string => {
				tmp := self.next_tmp()
				emit("  set ")
				self.access(.{tmp})
				emit(" ")
				emit(self.src(ptok))
				emit("\n")

				res = .{tmp: tmp}
			},
			.ident => loop:blck {
				for var := self.scope.items {
					if bsc.mem.eql(u8, var.name, self.src(ptok)) {
						res = .{tmp: var.idx}
						break:blck
					}
				}

				res = .{sym: self.src(ptok)}
				break:blck
			},
			.intrinsic => self.intrinsic(ptok),
			.semi => {},
			_ => {
				tmp := bsc.Arena.scratch(null)

				msg := bsc.ArrayList(u8).empty

				msg.push_slice(tmp.arena, "expected expression, got ")
				msg.push_slice(tmp.arena, ptok.kind.name())

				self.report(ptok.pos, msg.items)
			},
		}

		loop if self.tok.kind == .lpar {
			if res != .sym {
				self.report(self.tok.pos, "call position needs to be a symbol")
			}

			self.tok = self.lexer.next()

			tmp := bsc.Arena.scratch(self.tmp)
			defer tmp.pop()

			args := bsc.ArrayList(uint).empty

			while self.tok.kind != .rpar {
				if self.tok.kind == .eof {
					self.report(self.tok.pos, "expected )")
					break
				}

				pos := self.tok.pos
				arg := self.expr()
				if arg != .tmp {
					self.report(pos, "expected temporary")
					break
				}

				args.push(tmp.arena, arg.tmp)
			}
			_ = self.expect(.rpar)

			num_buf: [10]u8 = idk

			for i := 0.., arg := args.items {
				emit("  set param")
				emit(bsc.fmt.display_int(i, num_buf[..]))
				emit(" ")
				self.access(.{tmp: arg.*})
				emit("\n")
			}

			emit("  set ")
			emit(res.sym)
			emit(".ret_addr @counter\n")

			emit("  jump ")
			emit(res.sym)
			emit(" always x false\n")

			ret := self.next_tmp()
			emit("  set ")
			self.access(.{tmp: ret})
			emit(" retval0\n")

			res = .{tmp: ret}
		} else if next_prec := self.tok.kind.prec() && prec > next_prec {
			pos := self.tok.pos
			op := self.tok.kind
			self.tok = self.lexer.next()

			rhs := self.expr()
			if rhs != .tmp {
				self.report(self.tok.pos, "expected temporary")
				return .{tmp: 0}
			}

			if op == .decl {
				if res != .sym {
					self.report(ptok.pos, "expected symbol")
					return .{tmp: 0}
				}

				new_tmp := self.next_tmp()
				self.scope.push(self.tmp, .{
					name: res.sym,
					idx: new_tmp,
				})

				emit("  set ")
				self.access(.{tmp: new_tmp})
				emit(" ")
				self.access(rhs)
				emit("\n")

				return .{tmp: 0}
			}

			if op == .assign {
				emit("  set ")
				self.access(res)
				emit(" ")
				self.access(rhs)
				emit("\n")

				return .{tmp: 0}
			}

			op_str := ""
			match op {
				.plus => op_str = "add",
				.minus => op_str = "sub",
				.star => op_str = "mul",
				.slash => op_str = "div",
				.eq => op_str = "equal",
				_ => {
					self.report(pos, "TODO: implement operator")
					die
				},
			}

			new_tmp := self.next_tmp()

			emit("  op ")
			emit(op_str)
			emit(" ")
			self.access(.{tmp: new_tmp})
			emit(" ")
			self.access(res)
			emit(" ")
			self.access(rhs)
			emit("\n")

			res = .{tmp: new_tmp}
		} else break

		return res
	}

	IntrinsicSpec := struct {
		.name: []u8;
		.prefix: []u8;
		.args: [][]u8

		simple := fn(name: []u8, prefix: []u8, args: [][]u8): IntrinsicSpec {
			return .{name, prefix, args: @alloc_global(args)}
		}
	}

	intrinsic := fn(self: ^Parser, ptok: Lexer.Token): void {
		name := self.src(ptok)[1..]
		prefix := ""

		tmp := bsc.Arena.scratch(self.tmp)
		defer tmp.pop()

		_ = self.expect(.lpar) || return;

		args := bsc.ArrayList(Value).empty
		while self.tok.kind != .rpar {
			if self.tok.kind == .eof {
				self.report(self.tok.pos, "expected )")
				break
			}

			args.push(tmp.arena, self.expr())

			if self.tok.kind == .comma {
				self.tok = self.lexer.next()
			}
		}
		self.tok = self.lexer.next()

		emit("  ")
		emit(name)
		for i := 0.., arg := args.items {
			emit(" ")
			self.access(arg.*)
		}
		emit("\n")
	}

	next_tmp := fn(self: ^Parser): uint {
		defer self.tmp_value_idx += 1
		return self.tmp_value_idx
	}

	next_lable := fn(self: ^Parser): uint {
		defer self.tmp_lable_idx += 1
		return self.tmp_lable_idx
	}

	render_lable := fn(self: ^Parser, lable: uint, kind: []u8): void {
		num_buf: [10]u8 = idk

		emit(self.curr_fn)
		emit(".")
		emit(kind)
		emit(bsc.fmt.display_int(lable, num_buf[..]))
	}

	access := fn(self: ^Parser, val: Value): void {
		num_buf: [10]u8 = idk

		match val {
			.tmp => {
				emit(self.curr_fn)
				emit(".tmp")
				emit(bsc.fmt.display_int(val.tmp, num_buf[..]))
			},
			.sym => {
				emit(val.sym)
			},
		}
	}
}

report := fn(path: []u8, source: []u8, pos: uint, msg: []u8): void {
	line := 1
	col := 0

	for i := 0..pos {
		if source[i] == '\n' {
			line += 1
			col = 0
		} else {
			col += 1
		}
	}

	buf: [10]u8 = idk

	_ = bsc.sys.write(2, path).unwrap()
	_ = bsc.sys.write(2, ":").unwrap()
	_ = bsc.sys.write(2, bsc.fmt.display_int(line, buf[..])).unwrap()
	_ = bsc.sys.write(2, ":").unwrap()
	_ = bsc.sys.write(2, bsc.fmt.display_int(col, buf[..])).unwrap()
	_ = bsc.sys.write(2, ": ").unwrap()
	_ = bsc.sys.write(2, msg).unwrap()
	_ = bsc.sys.write(2, "\n").unwrap()

	line_start := pos
	while line_start > 0 && source[line_start] != '\n' {
		line_start -= 1
	}

	line_end := pos
	while line_end < source.len && source[line_end] != '\n' {
		line_end += 1
	}

	_ = bsc.sys.write(2, source[line_start..line_end]).unwrap()
	_ = bsc.sys.write(2, "\n").unwrap()

	for i := 0..col + 1 {
		if source[line_start + i] == '\t' {
			_ = bsc.sys.write(2, "\t").unwrap()
		} else {
			_ = bsc.sys.write(2, " ").unwrap()
		}
	}

	_ = bsc.sys.write(2, "^\n").unwrap()
}

Lexer := struct {
	.pos: uint;
	.source: []u8

	Token := struct {
		.kind: Kind;
		.pos: uint;
		.end: uint

		Kind := enum(u8) {
			.eof := 0;
			.ident;
			.number;
			.decl;
			.eq;
			.string;
			.k_fn;
			.k_loop;
			.k_break;
			.k_continue;
			.k_if;
			.k_else;
			.k_return;
			.t_void;
			.intrinsic;
			.dot := '.';
			.comma := ',';
			.colon := ':';
			.semi := ';';
			.assign := '=';
			.lpar := '(';
			.rpar := ')';
			.lbrc := '{';
			.rbrc := '}';
			.plus := '+';
			.minus := '-';
			.star := '*';
			.slash := '/';
			.unknown := 128

			prec := fn(self: Kind): ?u8 {
				match self {
					.star => return 1,
					.slash => return 1,
					.plus => return 2,
					.minus => return 2,
					.eq => return 3,
					.decl => return 15,
					.assign => return 15,
					_ => return null,
				}
			}

			EnumRange := fn(prefix: []u8): type {
				tmp := bsc.Arena.ct_scratch(null)
				defer tmp.pop()

				base_fields := @type_info(Kind).@enum.fields
				fields := bsc.ArrayList(@TypeOf(base_fields[0])).empty
				for var := base_fields {
					if bsc.mem.starts_with(u8, var.name, prefix) {
						cpy := var.*
						cpy.name = cpy.name[prefix.len..]
						fields.push(tmp.arena, cpy)
					}
				}

				return @Type(.{@enum: .{
					backing_int: u8,
					fields: fields.items,
					decls: &.[],
				}})
			}

			name := fn(self: Kind): []u8 {
				for kv := @eval(@type_info(Kind)).@enum.fields {
					if kv.value == self {
						return kv.name
					}
				}

				return "unknown"
			}

			Keywords := EnumRange("k_")
			Types := EnumRange("t_")
		}
	}

	next := fn(self: ^Lexer): Token {
		loop {
			c := self.source[self.pos]
			kind: Token.Kind = .unknown
			pos := self.pos
			if c == 0 {
				kind = .eof
			} else if c <= ' ' {
				self.pos += 1
				continue
			} else if c == '"' {
				self.pos += 1
				while self.source[self.pos] != '"' {
					if self.source[self.pos] == 0 {
						break
					}

					if self.source[self.pos] == '\\' {
						self.pos += 1
					}

					self.pos += 1
				}

				self.pos += 1

				kind = .string
			} else if c >= '0' & c <= '9' {
				while c >= '0' & c <= '9' {
					self.pos += 1
					c = self.source[self.pos]
				}

				kind = .number
			} else if c >= 'a' & c <= 'z' | (c >= 'A' & c <= 'Z') | c == '@' {
				self.eat_ident()

				for kv := @eval(@type_info(Token.Kind.Keywords)).@enum.fields {
					if bsc.mem.eql(u8, kv.name, self.source[pos..self.pos]) {
						kind = @bit_cast(@as(u8, @int_cast(kv.value)))
					}
				}

				for kv := @eval(@type_info(Token.Kind.Types)).@enum.fields {
					if bsc.mem.eql(u8, kv.name, self.source[pos..self.pos]) {
						kind = @bit_cast(@as(u8, @int_cast(kv.value)))
					}
				}

				if kind == .unknown {
					kind = .ident
				}
			} else if c == '#' {
				self.pos += 1
				self.eat_ident()
				kind = .intrinsic
			} else if c == ':' && self.source[self.pos + 1] == '=' {
				self.pos += 2
				kind = .decl
			} else if c == '=' && self.source[self.pos + 1] == '=' {
				self.pos += 2
				kind = .eq
			} else {
				self.pos += 1
				kind = @bit_cast(c)
			}

			return .(kind, pos, self.pos)
		}
	}

	eat_ident := fn(self: ^Lexer): void {
		c := self.source[self.pos]
		while c >= 'a' & c <= 'z' |
			(c >= 'A' & c <= 'Z') |
			(c >= '0' & c <= '9') |
			c == '_' {
			self.pos += 1
			c = self.source[self.pos]
		}
	}
}
