foo := @use("bar")
goo := @use("fa.hb")

main := fn(): uint {
	return goo.fun + foo.fun
}
