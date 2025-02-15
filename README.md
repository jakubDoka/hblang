# holey-bytes

## vendored tests

```bash
git submodule add https://git.ablecorp.us/lily-org/lily.git vendored-tests/lily # add a new
git submodule update --init --recursive                                         # fetch
git submodule update --remote --rebase -- vendored-tests/lily/                  # update a
```

### Tour

#### main fn 1
```hb
main := fn(): uint {
	return 42
}
```

#### arithmetic 1
```hb
main := fn(): uint {
	return 10 - 20 / 2 + 4 * (2 + 2) - 4 * 4 + 1 - 1
}
```

#### arithmetic 2
```hb
main := fn(): int {
	a: i8 = 0
	b: u8 = 0
	c: i16 = a - 1
	d: u16 = b + 1
	e: i32 = c - 1
	f: u32 = d + 1
	return f + e
}
```

#### arithmetic 3
```hb
main := fn(): uint {
	{
		// no opts unsigned
		o := one()
		z := zero()

		if cond(o < z) return 1
		if cond(o < o) return 2
		if cond(o <= z) return 3
		if cond(z > o) return 4
		if cond(o > o) return 5
		if cond(z >= o) return 6
	}

	{
		// no opts signed
		o := mne()
		z := mero()

		if cond(o > z) return 7
		if cond(o > o) return 8
		if cond(o >= z) return 9
		if cond(z < o) return 10
		if cond(o < o) return 11
		if cond(z <= o) return 12
	}

	{
		// branch opts unsigned
		o := one()
		z := zero()

		if o < z return 13
		if o < o return 14
		if o <= z return 15
		if z > o return 16
		if o > o return 17
		if z >= o return 18
	}

	{
		// branch opts signed
		o := mne()
		z := mero()

		if o > z return 19
		if o > o return 20
		if o >= z return 21
		if z < o return 22
		if o < o return 23
		if z <= o return 24
	}

	return 0
}

cond := fn(v: bool): bool return v

one := fn(): u8 return 1
zero := fn(): u8 return 0

mne := fn(): i8 return -1
mero := fn(): i8 return 0
```

#### functions 1
```hb
main := fn(): uint {
	return add_one(10) + add_two(20)
}

add_two := fn(x: uint): uint {
	return x + 2
}

add_one := fn(x: uint): uint {
	return x + 1
}
```

#### comments 1
```hb
// commant is an item
main := fn(): uint {
	// comment is a statement
	foo(/* comment is an exprression /* if you are crazy */ */)
	return 0
}

foo := fn(comment: void): void return /* comment evaluates to void */

// comments might be formatted in the future
```

#### if statements 1
```hb
main := fn(): uint {
	return fib(3)
}

fib := fn(x: uint): uint {
	if x <= 2 {
		return 1
	} else {
		return fib(x - 1) + fib(x - 2)
	}
}
```

#### if statements 2
```hb
main := fn(): uint {
	return fib(3)
}

fib := fn(x: uint): uint {
	if x <= 2 {
		x = 1
	} else {
		x = fib(x - 1) + fib(x - 2)
	}
	return x
}
```

#### variables 1
```hb
main := fn(): uint {
	ඞ := 1
	b := 2
	ඞ += 1
	return ඞ - b
}
```


#### loops 1
```hb
main := fn(): uint {
	return fib(10)
}

fib := fn(n: uint): uint {
	b := 1
	a := 0
	loop {
		if n == 0 break
		c := a + b
		a = b
		b = c
		n -= 1
		continue
	}
	return a
}
```

#### loops 2
```hb
main := fn(): uint {
	return not_fib(3)
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
```

#### loops 3
```hb
main := fn(): uint {
	i := 0
	loop if i == 4 break else {
		i += 1
	}
	return i
}
```

#### pointers 1
```hb
main := fn(): uint {
	a := 1
	b := &a
	modify(b)
	drop(a);
	*b += 2
	stack_reclamation_edge_case := 0
	return *b - 4
}

modify := fn(a: ^uint): void {
	*a = 2
	return
}

drop := fn(a: uint): void {
	return
}
```

#### pointers 2
```hb
main := fn(): uint {
	a := 1
	b := 2

	c := &a
	d := &b

	swap(c, d)

	return a - b
}

swap := fn(a: ^uint, b: ^uint): void {
	tmp := *b;
	*b = *a;
	*a = tmp
}
```

#### pointers 3
```hb
main := fn(): uint {
	a := 1
	_ = do_stuff(&a)
	return a
}

do_stuff := fn(v: ^uint): uint {
	if *v == 0 {
		return 0;
		*v = 2
	} else {
		return 1;
		*v = 3
	}
}
```

#### structs 1
```hb
Ty := struct {
	a: int,
	b: int,
}

Ty2 := struct {
	ty: Ty,
	c: int,
}

main := fn(): int {
	finst := Ty2.{ty: Ty.{a: 4, b: 1}, c: 3}
	inst := odher_pass(finst)
	if inst.c != 3 {
		return 0
	}
	if sum(inst.ty) != 0 {
		return 100
	}
	return pass(&inst.ty)
}

sum := fn(t: Ty): int {
	t.a -= 2
	t.b += 1
	return t.a - t.b
}

pass := fn(t: ^Ty): int {
	t.a -= 1
	t.a += 1
	return t.a - t.b
}

odher_pass := fn(t: Ty2): Ty2 {
	return t
}
```
