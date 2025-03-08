
main := fn(): uint {
    Map := fn(I: type, F: type): type return struct{}

	foo := fn(vl: int, $foo: type): Map(u8, foo) return .()

	foo()

	return 0
}
