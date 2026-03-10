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

debruijn_table := u8.[0, 1, 2, 53, 3, 7, 54, 27, 4, 38, 41, 8, 34, 55, 48, 28, 62, 5, 39, 46, 44, 42, 22, 9, 24, 35, 59, 56, 49, 18, 29, 11, 63, 52, 6, 26, 37, 40, 33, 47, 61, 45, 43, 21, 23, 58, 17, 10, 51, 25, 36, 32, 60, 20, 57, 16, 50, 31, 19, 15, 30, 14, 13, 12]

count_trailing_zeros := fn(v: uint, size: u8): u8 {
	if v == 0 return size
	v |= ~(0xffffffffffffffff >> size)
	return debruijn_table[@int_cast(((v & -v) * 0x022FDD63CC95386D) >> 58)]
}
