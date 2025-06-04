lily := @use("lily")

main := fn(): uint {
	arena := lily.alloc.Arena.new()
	defer arena.deinit()

	map := lily.collections.HashMap(
		uint,
		uint,
		lily.alloc.Arena,
		lily.hash.RapidHasher,
	).new(&arena)
	defer map.deinit()

	i := 0
	loop if i == 10 break else {
		_ = map.insert(i, i)
		i += 1
	}

	lily.log.print(map)

	return 0
}
