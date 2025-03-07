# hblang

## Tour

Note: the examples are used to generate unit tests, `n = 1` from each group is most interesting, others are more for testing purposes.
Note: `expectations` contain the test case ecpectations that are asserted when `zig build test` is run

#### main fn 1
```hb
expectations := .{
    return_value: 42,
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
    return_value: 1,
}

main := fn(): bool {
    return 3 == 2 * 2 - 1
}
```

#### arithmetic 5 (errors)
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    v := /**/
    return 1 + v * 10
}
```

#### arithmetic 6 (missing operators)
```hb
main := fn(): uint {
    return 1 << 3 % 2 - 8 >> 3 | 4 & 2 ^ 0
}
```

#### arithmetic 7 (unary operators)
```hb
main := fn(): uint {
    if !true return 1
    if ~1 != -1 - 1 return 2
    if -1 != ~1 + 1 return 3
    return 0
}
```

#### literals 1
```hb
main := fn(): uint {
    if 10 != 0xa return 16
    if 10 != 0o12 return 8
    if 10 != 0b1010 return 2
    return 0
}
```

#### functions 1
```hb
expectations := .{
    return_value: 33,
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
    return_value: 33,
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

#### functions 3 (errors)
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    imaginary := /**/
    imaginary()
    some_fn()
    _ = some_fn(0, 0, 0)
    _ = some_fn(0, 0)
    vl := some_fn(0, /**/, 0, 0)
    return some_fn(vl, /**/, 0)
}

some_fn := fn(a: uint, b: void, c: u8): uint {
    return
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
    return_value: 2,
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
    return_value: 2,
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

#### if statements 3 (comptime)
```hb
main := fn(): uint {
    $if true return 0
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
    return_value: 55,
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
    return_value: 9,
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
    return_value: 4,
}

main := fn(): uint {
    i := 0
    loop if i == 4 break else {
        i += 1
    }
    return i
}
```

#### loops 4 (comptime)
```hb
expectations := .{
    return_value: 10,
}

main := fn(): uint {
    arr := uint.[1, 2, 3, 4]
    i := 0
    sum := 0
    $loop $if i == arr.len break else {
        sum += arr[i]
        i += 1
    }
    return sum
}
```

#### loops 5 (comptime|error)
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    arr := uint.[1, 2, 3, 4]
    i := 0
    sum := 0
    $loop if i == arr.len break else {
        sum += arr[i]
        i += 1
    }
    return sum
}
```

#### loops 6 (infinite)
```hb
expectations := .{
    times_out: true,
}

main := fn(): uint {
    if true loop {
    }

    return 0
}
```

#### pointers 1
```hb
main := fn(): uint {
    a := 1
    b := &a
    modify(b)
    b.* += 2
    return b.* - 4
}

modify := fn(a: ^uint): void {
    a.* = 2
    return
}
```

#### pointers 2
```hb
expectations := .{
    return_value: 1,
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
    tmp := b.*
    b.* = a.*
    a.* = tmp
}
```

#### pointers 3
```hb
expectations := .{
    return_value: 1,
}

main := fn(): uint {
    a := 1
    _ = do_stuff(&a)
    return a
}

do_stuff := fn(v: ^uint): uint {
    if v.* == 0 {
        return 0
        v.* = 2
    } else {
        return 1
        v.* = 3
    }
}
```

#### pointers 4 (errors)
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    return 0.*
}
```

#### structs 1
```hb
expectations := .{
    return_value: 3,
}

Ty := struct {
    .a: int;
    .b: int = 1

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
    finst := Ty2.{ty: Ty.{a: 4}, c: 3}
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
    return_value: 3,
}

Ty := struct {
    .a: int;
    .b: int;
    .c: int;
}

main := fn(): int {
    a := Ty.{a: 0, b: 0, c: 0}
    b := Ty.{a: 1, b: 1, c: 1}
    swap(&a, &b)
    return a.a + a.b + a.c
}

swap := fn(a: ^Ty, b: ^Ty): void {
    tmp := a.*
    a.* = b.*
    b.* = tmp
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
    return .{a: 1, b: 5}
}

return_triple := fn(): Triple {
    return .{a: 1, b: 2, c: 3}
}

take_pair := fn(pair: Pair): uint {
    return pair.a + pair.b
}

take_triple := fn(triple: Triple): uint {
    return triple.a + triple.b + triple.c
}
```

#### structs 4 (errors)
```hb
expectations := .{
    should_error: true,
}

Ty := struct{.a: uint; .b: uint}

main := fn(): uint {
    _ = .{}
    _ = .()
    _ = uint.{}
    _ = uint.()
    _ = Ty.{}
    _ = Ty.()
    _ = Ty.{p: 10}
    _ = Ty.{a: 1, b: 2, p: 10}
    _ = Ty.{a: 1, a: 2}
    _ = Ty.(.{}, .(), /**/)
    v := Ty.(0, 0, 0)
    return Ty.(v, 0)
}
```

#### structs 5 (comptime)
```hb
expectations := .{
    return_value: 6,
}

main := fn(): uint {
    Ty := struct{.a: uint; .b: uint; .c: uint}

    vl := Ty.(1, 2, 3)

    i := 0
    sum := 0
    $loop $if i == @len_of(Ty) break else {
        sum += vl[i]
        i += 1
    }

    return sum
}
```

#### structs 6 (packed)
```hb
expectations := .{
    return_value: 4,
}

main := fn(): uint {
    Pckd := struct align(1){.a: u8; .b: u16}
    return @size_of(Pckd) + @align_of(Pckd)
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
    vl: Foo(uint).Bar(u8) = .init()
    return vl.sub()
}

Foo := fn(F: type): type return struct {
    Bar := fn(B: type): type return struct {
        .foo: F;
        .bar: B

        init := fn(): @CurrentScope() return .(1, 1)

        sub := fn(self: @CurrentScope()): uint {
            return self.foo - self.bar
        }
    }
}
```

#### generic structs 3
```hb
expectations := .{
    return_value: 10,
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

#### generic structs 4
```hb
expectations := .{
    return_value: 6,
}

main := fn(): uint {
    val: Array(uint, 3) = .(1, .(2, .(3, .())))
    return val.get(0) + val.get(1) + val.get(2)
}

Array := fn(E: type, len: uint): type if len == 0 {
    return struct {
        get := fn(self: @CurrentScope(), i: uint): E die
    }
} else {
    Next := Array(E, len - 1)
    return struct {
        .elem: E;
        .next: Next

        get := fn(self: @CurrentScope(), i: uint): E {
            if i == 0 return self.elem

            return self.next.get(i - 1)
        }
    }
}
```

#### generic structs 5 (iterators)
```hb
main := fn(): uint {
    ref := "abcd"

    start := "ab"
    end := "cd"

    Next := fn(T: type): type return struct {
        .next: bool;
        .val: T
        none := fn(): @CurrentScope() {
            return .(false, idk)
        }
        some := fn(val: T): @CurrentScope() {
            return .(true, val)
        }
    }

    Chars := struct {
        .slc: []u8
        next := fn(self: ^@CurrentScope()): Next(u8) {
            if self.slc.len == 0 return .none()
            defer self.slc = self.slc[1..]
            return .some(self.slc[0])
        }
    }


    Chain := fn(A: type, B: type): type return struct {
        .state: enum {.a; .b; .done};
        .a: A;
        .b: B

        Elem := @TypeOf(A.next(idk))

        next := fn(self: ^@CurrentScope()): Elem {
            loop match self.state {
                .a => {
                    nxt := (&self.a).next()
                    if nxt.next return nxt
                    self.state = .b
                },
                .b => {
                    nxt := (&self.b).next()
                    if nxt.next return nxt
                    self.state = .done
                },
                .done => return .none(),
            }
        }
    }

    siter := Chars.(start)
    riter := Chars.(ref)
    citer := Chain(Chars, Chars).(.a, .(start), .(end))

    loop {
        sc := (&siter).next()
        if !sc.next break
        rc := (&riter).next()
        if !rc.next return 1

        if sc != rc return 2
    }

    riter = .(ref)
    loop {
        rc := (&riter).next()
        if !rc.next break
        sc := (&citer).next()
        if !sc.next return 3

        if sc != rc return 4
    }

    return 0
}
```

#### comptime 1
```hb
main := fn(): uint {
    some_int := uint
    some_fn := fn($ui: type, x: some_int): ui {
        val: some_int = x + 1
        return val * val
    }

    return some_fn(some_int, 9) - (some_fn(some_int, 5) + some_fn(some_int, 7))
}
```

#### comptime 2
```hb
expectations := .{
    return_value: 33,
}

main := fn(): uint {
    some_int := uint

    some_fn := fn(): some_int {
        return 1
    }

    some_fn2 := fn(): some_int {
        return some_fn() + 1
    }

    some_fn3 := fn($fnc: type): type {
        return fn(): some_int {
            return fnc() + 10
        }
    }

    return some_fn3(some_fn)() + some_fn3(some_fn3(some_fn2))()
}
```

#### comptime 3 (errors)
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    some_int := 1

    not_a_closure := fn(): uint {
        return some_int
    }

    return not_a_closure()
}
```

#### comptime 4 (@TypeOf)
```hb
main := fn(): uint {
    some_int := 0

    Ty := struct{.field: @TypeOf(some_int)}

    return Ty.(some_int).field
}
```

#### struct operators 1
```hb
expectations := .{
    return_value: 10,
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

    if Point.(1, 1) != Point.(1, 1) return 1002
    if Point.(1, 2) == Point.(1, 1) return 1003

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

#### unions 1
```hb
expectations := .{
    return_value: 257,
}

main := fn(): uint {
    Union := union {
        .single: u16;
        .pair: struct{.l: u8; .r: u8};
    }

    val := Union.{pair: .(1, 1)}

    return val.single
}
```

#### unions 2
```hb
expectations := .{
    return_value: 42,
}

main := fn(): int {
    Number := union {
        ._int: int;
        ._uint: uint;
    }

    n1 := Number.{_int: 42}

    return n1._int
}
```

#### enums 1
```hb
expectations := .{
    return_value: 1,
}

main := fn(): uint {
    Enum := enum{.A; .B; .C}

    n1 := Enum.A
    n2: Enum = .B

    if n1 == n2 return 10

    return @as(u8, n1) + n2
}
```

#### match 1
```hb
main := fn(): uint {
    Nm := enum{.a; .b; .c}

    match Nm.a {
        .a => {
        },
        Nm.b => return 1,
        .c => return 2,
    }

    match Nm.b {
        .a => return 3,
        _ => return 0,
    }
}
```

#### match 2 (comptime)
```hb
main := fn(): uint {
    $match enum{.a; .b}.a {
        .a => return 0,
        .b => return 1,
    }
}
```

#### defer 1
```hb
main := fn(): uint {
    i := 0
    {
        defer i += 1
        if i == 1 return 1
    }

    if i != 1 return 2

    loop {
        defer i += 1
        if i == 3 continue
        if i == 4 break
    }

    if i != 5 return 3

    ret_defer := fn(str: ^uint): void {
        defer str.* += 1
    }

    v := 0
    ret_defer(&v)
    if v != 1 return 4

    return 0
}
```

#### die
```hb
expectations := .{
    unreaches: true,
}

main := fn(): uint {
    if false return 1
    die
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
    return_value: 55,
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
    return_value: 3,
}

a: uint = 0
b: uint = a + 1
c: uint = b + 1
d: uint = c + 1

main := fn(): uint {
    return d
}
```

#### strings
```hb
expectations := .{
    return_value: 69,
}

main := fn(): uint {
    return "\t\{45}dvard\r\nඞ\0"[1]
}
```

#### arrays 1
```hb
expectations := .{
    return_value: 28,
}

main := fn(): uint {
    arr: [8]uint = idk

    i := 0
    loop if i == arr.len break else {
        arr[i] = i
        i += 1
    }

    i = 0
    sum := 0
    loop if i == arr.len break else {
        sum += arr[i]
        i += 1
    }

    return sum
}
```

#### arrays 2
```hb
expectations := .{
    return_value: 9,
}

dim: uint = 3

main := fn(): uint {
    narr: [dim][dim]uint = idk

    y := 0
    loop if y == narr.len break else {
        x := 0
        loop if x == narr[y].len break else {
            narr[y][x] = x * y
            x += 1
        }
        y += 1
    }

    linarr: ^[dim * dim]uint = @bit_cast(&narr)

    sum := 0
    i := 0
    loop if i == linarr.len break else {
        sum += linarr[i]
        i += 1
    }

    return sum
}
```

#### slices 1
```hb
expectations := .{
    return_value: 50,
}

main := fn(): uint {
    arr := u8.[1, 2, 3, 4]
    slice := arr[..]

    slices := ([]u8).[arr[..], arr[..2], arr[2..], arr[1..3], slice[..], slice[..2], slice[2..], slice[1..3]]

    sum := 0
    i := 0
    loop if i == slices.len break else {
        j := 0
        loop if j == slices[i].len break else {
            sum += slices[i][j]
            j += 1
        }
        i += 1
    }

    return sum
}
```

#### slices 2
```hb
expectations := .{
    return_value: 25,
}

main := fn(): uint {
    arr := uint.[1, 2, 3, 4]
    slice := arr[..]

    slices := ([]uint).[arr[..], arr.ptr[..arr[1]], arr[arr[1]..], arr.ptr[arr[0]..arr[2]]]

    sum := 0
    i := 0
    loop if i == slices.len break else {
        j := 0
        loop if j == slices[i].len break else {
            sum += slices[i][j]
            j += 1
        }
        i += 1
    }

    return sum
}
```

#### nullable types 1
```hb
expectations := .{
    return_value: 10,
}

main := fn(): uint {
    ten := mkval(uint, 10)

    if ten == null return 1

    if mknull(uint) != null return 2

    return ten.?
}

mknull := fn($T: type): ?T return null
mkval := fn($T: type, val: T): ?T return val
```

#### nullable types 2
```hb
Stru := struct {
    .a: uint;
    .b: uint;
}

main := fn(): uint {
    nlbl: ?Stru = .(0, 0)
    other: ?Stru = .{a: 0, b: 0}
    othera: ?[2]uint = .[0, 0]

    if nlbl == null return 1
    if other == null return 2
    if othera == null return 3

    nlbl.?.b = 1
    take(&nlbl.?)

    return nlbl.?.a - nlbl.?.b
}

take := fn(s: ^Stru): void {
    s.a += 1
}
```

#### struct patters 1
```hb
expectations := .{
    return_value: 3,
};
foo.{bar, bas: .{baz: bax}} := @use("foo.hb")

main := fn(): uint {
    return foo.foo() + bar() + bax()
}

// in: foo.hb
foo := fn(): uint return 0
bar := fn(): uint return 1
bas := @use("bas.hb")
// in: bas.hb
baz := fn(): uint return 2
```

#### directives 1 (@size_of, @align_of)
```hb
expectations := .{
    return_value: 3,
}

main := fn(): uint {
    return @size_of(struct{.b: u16; .a: u8}) - @align_of(u8)
}
```

#### directives 2 (@as)
```hb
expectations := .{
    return_value: 3,
}

main := fn(): uint {
    val := @as(struct{.a: uint}, .(3))
    return val.a
}
```

#### directives 3 (@ecall)
```hb
expectations := .{
    return_value: 3,
    ecalls: .(
        .(0, 1, 2): 3,
    ),
}

main := fn(): uint {
    return @ecall(
        0,
        struct{.a: uint; .b: uint}.(1, 2),
        struct{.a: uint; .b: uint; .c: uint}.(3, 4, 5),
    )
}
```

#### directives 4 (@int_cast)
```hb
main := fn(): u8 {
    v: uint = 0
    return @int_cast(v)
}
```

#### directives 5 (@bit_cast)
```hb
main := fn(): u32 {
    return @bit_cast(@as(struct{.l: u16; .r: u16}, @bit_cast(@as(u32, 0))))
}
```

#### directives 6 (@len_of)
```hb
expectations := .{
    return_value: 4,
}

main := fn(): uint {
    return @len_of(struct{.a: u8; .b: u32}) + @len_of([2]u8)
}
```

#### directives 7 (@kind_of)
```hb
expectations := .{
    return_value: 6,
}

main := fn(): uint {
    return @kind_of(struct{})
}
```

#### directives 8 (@ChildOf)
```hb
expectations := .{
    return_value: 1,
}

main := fn(): uint {
    vl := 1
    return deref(^uint, &vl)
}

deref := fn($T: type, arg: T): @ChildOf(T) {
    return arg.*
}
```

#### directives 9 (@embed)
```hb
expectations := .{
    return_value: 69,
}

main := fn(): uint {
    val: ^[1]u8 = &@embed("mbed.txt")
    return val[0]
}

// in: mbed.txt
E
```

#### directives 10 (@error)
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    $if false @error("never happens")
    @error("no main in sight, here is a type: ", ^u8)
}
```

#### directives 11 (@target)
```hb
global: bool = @target("ableos")

main := fn(): uint {
    $if @target("comptime") @error("unecpected")

    return global
}
```

#### directives 12 (@inline)
```hb
expectations := .{
    return_value: 10,
}

main := fn(): uint {
    // NOTE: does nothing right now
    return @inline(foo, 10)
}

foo := fn(vl: uint): uint return vl
```

#### directives 13 (@Any)
```hb
expectations := .{
    return_value: 10,
}

main := fn(): uint {
    return foo(5) + foo(@as(u8, 5))
}

foo := fn(vl: @Any()): @TypeOf(vl) {
    return vl
}
```

## progress

- [ ] ? diagnostics
  - [ ] ? don't crash on cycles
- [ ] control flow
  - [x] functions
    - [ ] ? inlining
      - [x] noop compatibility
    - [x] scope inference
    - [x] comptime parameters
  - [x] ifs
    - [x] comptime
  - [x] loops
    - [x] comptime
    - [x] break
    - [x] continue
    - [x] infinite
      - [ ] ? clean up the hacky graph hierarchy
    - [ ] ? labels
  - [x] blocks
    - [ ] ? labels
  - [x] match
    - [x] comptime
  - [x] defer
  - [x] `die`
- [x] import pattern matching
- [x] global variables
  - [x] strings
  - [x] comptime evaluation
  - [ ] ? references
  - [ ] ? immutable
    - [x] noop compatibility
- [ ] types
  - [x] `idk`
  - [x] integers/bool
    - [x] bool literals
    - [x] integer literals
      - [x] binary
      - [x] octal
      - [x] decimal
      - [x] hexadecimal
    - [x] binary operators
      - [x] `- + * / == != <= >= < > << >> | ^ & %`
    - [x] unary operators
      - [x] `- ! ~`
  - [ ] **floats**
    - [ ] **binary operators**
      - [ ] **all**
    - [ ] **unary operators**
      - [ ] **all**
  - [x] structs
    - [x] indexing
    - [x] packed
    - [x] constructors
      - [x] dictionary
      - [x] tuple
    - [x] default values
    - [x] scope
    - [x] file
    - [x] operators
    - [x] comparison
  - [x] enums
    - [ ] ? specific values
    - [ ] ? backing integer
    - [x] scope
  - [x] unions
    - [ ] ? tag + customizable
    - [x] scope
  - [x] pointers
    - [x] slicing
  - [x] slices
    - [x] known size (arrays)
    - [x] field access
    - [x] indexing
    - [x] slicing
  - [ ] **tuples** --DO
  - [x] nullable types
- [ ] ? directives
  - [x] `@use(<string>)`
  - [x] `@TypeOf(<expr>)`
  - [x] `@as(<ty>, <expr>)`
  - [x] `@int_cast(<expr>)`
  - [x] `@size_of(<ty>)`
  - [x] `@align_of(<ty>)`
  - [x] `@bit_cast(<expr>)`
  - [x] `@ecall(...<expr>)`
  - [x] `@embed(<string>)`
  - [ ] ? `@inline(<func>, ...<args>)`
    - [x] noop compatibility
  - [x] `@len_of(<ty>)`
  - [x] `@kind_of(<ty>)`
  - [x] `@Any(<fn(type): void/type>..)`
    - [ ] ? type filters
  - [x] `@error(...<expr>)`
  - [x] `@ChildOf(<ty>)`
  - [x] `@target("<pat>")`

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
