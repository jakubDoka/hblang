Type := union(enum) {
	.builtin: void;
	.option: Option;
	.pointer: Pointer;
	.slice: Slice;
	.array: Array;
	.simd: type;
	.fnty: FuncTy;
	.@struct: Struct;
	.@enum: Enum;
	.@union: Union;

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
		.len: u64;
	}

	FuncTy := struct {
		.args: []type;
		.ret: type;
	}

	Struct := struct {
		.alignment: uint;
		.fields: []Field;
		.decls: [][]u8;

		Field := struct {
			.name: []u8;
			.ty: type;
			.offset: uint;
			.default: ?^void;

			get_default := fn($self: ^Field): ?^self.ty {
				return @bit_cast(self.default || return null)
			}
		}
	}

	Union := struct {
		.tag: ?type;
		.fields: []Field;
		.decls: [][]u8;

		Field := struct {
			.name: []u8;
			.ty: type;
		}
	}

	Enum := struct {
		.backing_int: type;
		.fields: []Field;
		.decls: [][]u8;

		Field := struct {
			.name: []u8;
			.value: i64;
		}
	}
}

SrcLoc := struct {
	.file: []u8;
	.line: u32;
	.col: u32;
}

debruijn_table := u8.[0, 1, 2, 53, 3, 7, 54, 27, 4, 38, 41, 8, 34, 55, 48, 28, 62, 5, 39, 46, 44, 42, 22, 9, 35, 56, 49, 29, 63, 57, 45, 53, 6, 26, 37, 40, 33, 47, 61, 50, 45, 43, 21, 34, 55, 48, 28, 62, 36, 32, 60, 20, 23, 10, 51, 44, 25, 31, 19, 24, 30, 18, 17, 16]

count_trailing_zeroes := fn(v: int, size: u8): u8 {
	if v == 0 return size
	v |= ~((1 << size) - 1)
	return debruijn_table[@int_cast(((v & -v) * 0x022FDD63CC95386D) >> 58)]
}
