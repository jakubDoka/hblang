Type := union(enum) {
	.builtin: void;
	.option: Option;
	.pointer: Pointer;
	.slice: Slice;
	.array: Array;
	.func_ty: FuncTy;
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
			.default: u32

			get_default := fn($self: ^Field): ^self.ty {
				$if @size_of(self.ty) <= 4 return @bit_cast(&self.default)
				return @bit_cast(@as(uint, self.default))
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
