Type := union(enum) {
	.builtin: void;
	.option: Option;
	.pointer: Pointer;
	.slice: Slice;
	.array: Array;
	.fnty: FuncTy;
	.@struct: Struct;
	.@enum: Enum;
	.@union: Union

	Option := struct {
		.inner: type;
	}

	Pointer := struct {
		.ty: type;
	}

	Slice := struct {
		.elem: type;
	}

	Array := struct {
		.elem: type;
		.size: u64;
	}

	FuncTy := struct {
		.args: []type;
		.ret: type;
	}

	Struct := struct {
		.alignment: uint;
		.fields: []Field;
		.decls: [][]u8

		Field := struct {
			.name: []u8;
			.ty: type;
			.offset: uint;
			.default: ?^void

			get_default := fn($self: ^Field): ?^self.ty {
				return @bit_cast(self.default || return null)
			}
		}
	}

	Union := struct {
		.tag: ?type;
		.fields: []Field;
		.decls: [][]u8

		Field := struct {
			.name: []u8;
			.ty: type;
		}
	}

	Enum := struct {
		.backing_int: type;
		.fields: []Field;
		.decls: [][]u8

		Field := struct {
			.name: []u8;
			.value: i64;
		}
	}
}
