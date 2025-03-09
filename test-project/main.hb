foo := @use("bar")
goo := @use("fa.hb")
mfoo := @use("../foo.hb")

main := fn(): uint {
	_ = mfoo.main()
	return goo.fun + foo.fun
}
