lily := @use("vendored-tests/lily/src/lib.hb")

main := fn(): u32 {
	arena := lily.alloc.Arena.new()
	if slc := arena.alloc_zeroed(u8, 0) {
		len := slc.len
		if slc_2 := arena.realloc(u8, slc, 100) {
			len += slc_2.len
		} else return 2
		return len == 100
	}
	return 1
}
