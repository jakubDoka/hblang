Base := union {
	extend := fn($ty: type): type return _extend(@CurrentScope(), ty)
	new := fn(_val: @Any()): never @error("invalid injection", @TypeOf(_val))
	visit := fn(self: ^@CurrentScope(), x: @Any()): never die
	_visit := fn(self: ^@CurrentScope(), tag: u8, x: @Any()): never die
	U := @CurrentScope()
	size: u8 = 0
}
_extend := fn($_base: type, $ty: type): type {
	$TagTy := @TypeOf(_base.size)
	$NextTagTy := TagTy
	$if _base.size == @as(TagTy, -1) {
		$if TagTy == u8 TagTy = u16 else if TagTy == u16 TagTy = u32 else if TagTy == u32 TagTy = u64
	}
	return struct {
		.tag: TagTy;
		.val: U
		U := union {
			.base: _base.U;
			.variant: ty
			_visit := fn(self: ^@CurrentScope(), tag: TagTy, x: @Any()): @TypeOf(x.call(ty, idk)) {
				if tag == _base.size return x.call(ty, &self.variant)
				return self.base._visit(@int_cast(tag), x)
			}
		}
		new := fn(_val: @Any()): @CurrentScope() {
			$if @TypeOf(_val) == ty return .(_base.size, .{variant: _val}) else {
				b := _base.new(_val)
				return .(b.tag, .{base: b.val})
			}
		}
		visit := fn(self: ^@CurrentScope(), x: @Any()): @TypeOf(U._visit(idk, idk, x)) {
			return self.val._visit(self.tag, x)
		}
		extend := fn($_ty: type): type return _extend(@CurrentScope(), _ty)
		size: NextTagTy = @as(NextTagTy, @int_cast(_base.size)) + 1
	}
}

A := struct {
	.x: u64;
	.y: u32;
}
B := struct {
	.x: bool;
	.y: u32;
}
C := struct {
	.x: []u8;
	.y: u32;
}

X := Base.extend(A).extend(B)
Y := X.extend(C)

main := fn(): u32 {
	a := X.new(A.(123, 0))
	return a.visit(struct {
		call := fn(self: ^@CurrentScope(), $ty: type, x: ^ty): Y return Y.new(x.*)
	}.()).visit(struct {
		call := fn(self: ^@CurrentScope(), $ty: type, x: ^ty): u32 {
			return x.y
		}
	}.())
}
