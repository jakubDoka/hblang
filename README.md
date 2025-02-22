# hblang

## Tour

Note: the examples are used to generate unit tests, `n = 1` from each group is most interesting, others are more for testing purposes.

#### main fn 1
```hb
expectations := .{
    .return_value: 42;
}

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

#### arithmetic 4
```hb
expectations := .{
    .return_value: 1;
}

main := fn(): bool {
    return 3 == 2 * 2 - 1
}
```

#### functions 1
```hb
expectations := .{
    .return_value: 33;
}

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

#### functions 2
```hb
expectations := .{
    .return_value: 33;
}

main := @use("main.hb").main

// in: main.hb

one := @use("one.hb")
two := @use("two.hb")

main := fn(): uint {
    return one.add(10) + two.add(20)
}

// in: two.hb

add := fn(x: uint): uint {
    return x + 2
}

// in: one.hb

add := fn(x: uint): uint {
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
expectations := .{
    .return_value: 2;
}

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
expectations := .{
    .return_value: 2;
}

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
expectations := .{
    .return_value: 55;
}

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
expectations := .{
    .return_value: 9;
}

main := fn(): uint {
    return square(3)
}

square := fn(size: uint): uint {
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
expectations := .{
    .return_value: 4;
}

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
expectations := .{
    .return_value: 1;
}

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
expectations := .{
    .return_value: 1;
}

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
expectations := .{
    .return_value: 3;
}

Ty := struct {
    .a: int;
    .b: int

    sum := fn(t: Ty): int {
        t.a -= 2
        t.b += 1
        return t.a - t.b
    }
}

Ty2 := struct {
    .ty: Ty;
    .c: int;
}

main := fn(): int {
    finst := Ty2.{.ty: Ty.{.a: 4; .b: 1}; .c: 3}
    inst := odher_pass(finst)
    if inst.c != 3 {
        return 0
    }
    if inst.ty.sum() != 0 {
        return 100
    }
    return pass(&inst.ty)
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

#### structs 2
```hb
expectations := .{
    .return_value: 3;
}

Ty := struct {
    .a: int;
    .b: int;
    .c: int;
}

main := fn(): int {
    a := Ty.{.a: 0; .b: 0; .c: 0}
    b := Ty.{.a: 1; .b: 1; .c: 1}
    swap(&a, &b)
    return a.a + a.b + a.c
}

swap := fn(a: ^Ty, b: ^Ty): void {
    tmp := *a;
    *a = *b;
    *b = tmp
}
```

#### structs 3 (call stress test)
```hb
Pair := struct{.a: u8; .b: uint}
Triple := struct{.a: uint; .b: uint; .c: u8}

main := fn(): uint {
    pr := return_pair()
    tpl := return_triple()

    if take_pair(pr) != take_triple(tpl) return 1

    return 0
}

return_pair := fn(): Pair {
    return .{.a: 1; .b: 5}
}

return_triple := fn(): Triple {
    return .{.a: 1; .b: 2; .c: 3}
}

take_pair := fn(pair: Pair): uint {
    return pair.a + pair.b
}

take_triple := fn(triple: Triple): uint {
    return triple.a + triple.b + triple.c
}
```

#### file structs 1
```hb
main := fn(): uint {
    foo := @use("Foo.hb").init(2)
    return foo.a - foo.b
}

// in: Foo.hb
.a: uint;
.b: uint

init := fn(v: uint): @CurrentScope() {
    return .(v, v)
}
```

#### generic structs 1
```hb
main := fn(): uint {
    vl: Vec(uint) = nvec(uint, 1)
    return vl.sub()
}

nvec := fn($E: type, v: uint): Vec(E) {
    return .(v, v)
}

Vec := fn(E: type): type return struct {
    .x: E;
    .y: E

    sub := fn(self: @CurrentScope()): E {
        return self.x - self.y
    }
}
```

#### generic structs 2
```hb
main := fn(): uint {
    vl: Foo(uint).Bar(u8) = .(1, 1)
    return vl.sub()
}

Foo := fn(F: type): type return struct {
    Bar := fn(B: type): type return struct {
        .foo: F;
        .bar: B

        sub := fn(self: @CurrentScope()): uint {
            return self.foo - self.bar
        }
    }
}
```

#### generic structs 3
```hb
expectations := .{
    .return_value: 10;
}

main := fn(): uint {
    vl: Foo(Foo(uint)) = .(.(10))
    return vl.sub().sub()
}

Foo := fn(F: type): type return struct {
    .foo: F

    sub := fn(self: @CurrentScope()): F {
        return self.foo
    }
}
```

#### struct operators 1
```hb
expectations := .{
    .return_value: 10;
}

Point := struct {
    .x: uint;
    .y: uint;
}

Rect := struct {
    .a: Point;
    .b: Point;
}

Color := struct{.b: u8; .g: u8; .r: u8; .a: u8}

main := fn(): uint {
    i := Color.(0, 0, 0, 0)
    i += .(1, 1, 1, 1)
    if i.r + i.g + i.b + i.a != 4 return 1001

    //if Point.(1, 1) != Point.(1, 1) return 1002
    //if Point.(1, 2) == Point.(1, 1) return 1003

    a := Point.(1, 2)
    b := Point.(3, 4)

    d := Rect.(a + b, b - a)
    zp := Point.(0, 0)
    d2 := Rect.(zp - b, a)
    d2 += d

    c := d2.a + d2.b
    return c.x + c.y
}
```

#### global variables 1
```hb
counter: uint = 0

dec := fn(): void {
    counter -= 1
}

main := fn(): uint {
    counter = 1
    dec()
    return counter
}
```

#### global variables 2
```hb
expectations := .{
    .return_value: 55;
}

some_other: uint = 10

some_fib: uint = fib(some_other)

fib := fn(n: uint): uint {
    if n != 10 return 0
    return 55
}

bigon_era: uint = some_other - 10

main := fn(): uint {
    return some_fib - bigon_era
}
```

#### global variables 3
```hb
expectations := .{
    .return_value: 3;
}

a: uint = 0
b: uint = a + 1
c: uint = b + 1
d: uint = c + 1

main := fn(): uint {
    return d
}
```

## progress

- [ ] diagnostics
  - [ ] don't crash on cycles
- [ ] control flow
  - [x] functions
    - [ ] inlining
    - [ ] comptime parameters
  - [x] ifs
    - [ ] comptime
  - [x] loops
    - [ ] comptime
    - [x] break
    - [x] continue
    - [ ] labels
  - [x] blocks
    - [ ] labels
  - [ ] match
    - [ ] comptime
  - [ ] defer
  - [ ] `die`
- [x] global variables
  - [x] comptime evaluation
- [ ] types
  - [ ] `idk`
  - [x] integers/bool
    - [x] bool literals
    - [ ] integer literals
      - [ ] binary
      - [ ] octal
      - [x] decimal
      - [ ] hexadecimal
    - [ ] binary operators
      - [x] `- + * / == != <= >= < >`
      - [ ] others
    - [ ] unary operators
      - [x] `-`
      - [ ] `! ~`
  - [ ] floats
    - [ ] binary operators
      - [ ] all
    - [ ] unary operators
      - [ ] all
  - [x] structs
    - [ ] indexing
    - [ ] packed
    - [X] constructors
      - [x] dictionary
      - [x] tuple
    - [ ] default values
    - [ ] scope
    - [ ] file
    - [ ] operators
  - [ ] enums
    - [ ] specific values
    - [ ] backing integer
    - [ ] scope
  - [ ] unions
    - [ ] tag + customizable
    - [ ] scope
  - [ ] pointers
    - [ ] slicing
  - [ ] slices
    - [ ] known size (arrays)
    - [ ] field access
  - [ ] tuples
  - [ ] nullable types
- [ ] directives
  - [x] `@use(<string>)`
  - [ ] `@TypeOf(<expr>)`
  - [ ] `@as(<ty>, <expr>)`
  - [ ] `@intcast(<expr>)`
  - [ ] `@sizeof(<ty>)`
  - [ ] `@alignof(<ty>)`
  - [ ] `@bitcast(<expr>)`
  - [ ] `@eca(...<expr>)`
  - [ ] `@embed(<string>)`
  - [ ] `@inline(<func>, ...<args>)`
  - [ ] `@lenof(<ty>)`
  - [ ] `@kindof(<ty>)`
  - [ ] `@Any()`
  - [ ] `@error(...<expr>)`
  - [ ] `@ChildOf(<ty>)`
  - [ ] `@target("<pat>")`
  - [ ] `@unwrap(<expr>)`

## vendored tests

```bash
git submodule add https://git.ablecorp.us/lily-org/lily.git vendored-tests/lily # add a new
git submodule update --init --recursive                                         # fetch
git submodule update --remote --rebase -- vendored-tests/lily/                  # update a
```

## Contributing

When contributing make sure to:
1. Mark what you completed in [progress](#progress), as the part of your changes. Stuff that is not in the checklist needs an issue. TODO: make an issue template
2. Add apropriate examples to test the functionality, `zig build test` will automatically generate a test for the example and run it with rverithing else. It's preferable to add `#### <feature> <n>` and use `n = 1` for demonstration and other examples to cover all ways to use the frature you can think of.
3. Extend the fuzzer to generate newly added syntax and run `zig build fuzz`.
