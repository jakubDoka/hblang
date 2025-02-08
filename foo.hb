main := fn(): uint {
    return not_fib(10)
}

not_fib := fn(size: uint): uint {
	acc := 0
    y := 0
    loop if y == size break else {
        x := 0
		loop if x == size break else {
			acc += x * y
			x += 1
		}
			y += 1
    }
    return acc
}
