
Type := struct {
	.kind: enum {
	.builtin;
	.pointer;
	.slice;
	.nullable;
	.tuple;
	.@enum;
	.@union;
	.@struct;
	.template;
	.func;
	.global;
	.fnptr;
	.simd;
	.array;
};
	.data: union {
		.builtin: void;
		.pointer: type;
		.slice: type;
		.nullable: type;
		.tuple: []type;
		.@enum: struct {
			.backing_int: ?type;
			.fields: []struct {
				.name: []u8;
				.value: i64;
			};
		};
		.@union: struct {
			.fields: []struct {
				.name: []u8;
				.ty: type;
			};
		};
		.@struct: struct {
			.alignment: ?u64;
			.fields: []struct {
				.name: []u8;
				.ty: type;
				.defalut_value: ^void;
			};
		};
		.template: struct {
			.is_inline: bool;
		};
		.func: struct {
			.args: []type;
			.ret: type;
		};
		.global: struct {
			.ty: type;
			.readonly: bool;
		};
		.fnptr: struct {
			.args: []type;
			.ret: type;
		};
		.simd: struct {
			.elem: type;
			.len: u32;
		};
		.array: struct {
			.elem: type;
			.len: u64;
		};
	};
}
