# hblang

## Build The Compiler

```bash
zig build install
./zig-out/bin/hbc --help
```

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
        if o != o return 25
        if o == z return 26
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

#### arithmetic 8
```hb
main := fn(): uint {
    return (0 < 1) - (1 + 0)
}
```

#### float arithmetic 1
```hb
main := fn(): f64 {
    return 10.0 - 20.0 / 2.0 + 4.0 * (2.0 + 2.0) - 4.0 * 4.0 + 1.0 - 1.0
}
```

#### float arithmetic 2
```hb
expectations := .{
    return_value: 826,
}

sin_table := f32.[0.0, 0.02454122852291229, 0.04906767432741801, 0.07356456359966743, 0.0980171403295606, 0.1224106751992162, 0.1467304744553617, 0.1709618887603012, 0.1950903220161282, 0.2191012401568698, 0.2429801799032639, 0.2667127574748984, 0.2902846772544623, 0.3136817403988915, 0.3368898533922201, 0.3598950365349881, 0.3826834323650898, 0.4052413140049899, 0.4275550934302821, 0.4496113296546065, 0.4713967368259976, 0.492898192229784, 0.5141027441932217, 0.5349976198870972, 0.5555702330196022, 0.5758081914178453, 0.5956993044924334, 0.6152315905806268, 0.6343932841636455, 0.6531728429537768, 0.6715589548470183, 0.6895405447370668, 0.7071067811865475, 0.7242470829514669, 0.7409511253549591, 0.7572088465064845, 0.773010453362737, 0.7883464276266062, 0.8032075314806448, 0.8175848131515837, 0.8314696123025452, 0.844853565249707, 0.8577286100002721, 0.8700869911087113, 0.8819212643483549, 0.8932243011955153, 0.9039892931234433, 0.9142097557035307, 0.9238795325112867, 0.9329927988347388, 0.9415440651830208, 0.9495281805930367, 0.9569403357322089, 0.9637760657954398, 0.970031253194544, 0.9757021300385286, 0.9807852804032304, 0.9852776423889412, 0.989176509964781, 0.99247953459871, 0.9951847266721968, 0.9972904566786902, 0.9987954562051724, 0.9996988186962042, 1.0, 0.9996988186962042, 0.9987954562051724, 0.9972904566786902, 0.9951847266721969, 0.99247953459871, 0.989176509964781, 0.9852776423889412, 0.9807852804032304, 0.9757021300385286, 0.970031253194544, 0.9637760657954398, 0.9569403357322089, 0.9495281805930367, 0.9415440651830208, 0.9329927988347388, 0.9238795325112867, 0.9142097557035307, 0.9039892931234434, 0.8932243011955152, 0.881921264348355, 0.8700869911087115, 0.8577286100002721, 0.8448535652497072, 0.8314696123025455, 0.8175848131515837, 0.8032075314806449, 0.7883464276266063, 0.7730104533627371, 0.7572088465064847, 0.740951125354959, 0.7242470829514669, 0.7071067811865476, 0.6895405447370671, 0.6715589548470186, 0.6531728429537766, 0.6343932841636455, 0.6152315905806269, 0.5956993044924335, 0.5758081914178454, 0.5555702330196022, 0.5349976198870972, 0.5141027441932218, 0.4928981922297841, 0.4713967368259979, 0.4496113296546069, 0.427555093430282, 0.4052413140049899, 0.3826834323650899, 0.3598950365349883, 0.3368898533922203, 0.3136817403988914, 0.2902846772544624, 0.2667127574748985, 0.2429801799032641, 0.21910124015687, 0.1950903220161286, 0.1709618887603012, 0.1467304744553618, 0.1224106751992163, 0.09801714032956083, 0.07356456359966773, 0.04906767432741797, 0.02454122852291233, 0.0, -0.02454122852291208, -0.04906767432741772, -0.0735645635996675, -0.09801714032956059, -0.1224106751992161, -0.1467304744553616, -0.170961888760301, -0.1950903220161284, -0.2191012401568698, -0.2429801799032638, -0.2667127574748983, -0.2902846772544621, -0.3136817403988912, -0.3368898533922201, -0.3598950365349881, -0.3826834323650897, -0.4052413140049897, -0.4275550934302818, -0.4496113296546067, -0.4713967368259976, -0.4928981922297839, -0.5141027441932216, -0.5349976198870969, -0.555570233019602, -0.5758081914178453, -0.5956993044924332, -0.6152315905806267, -0.6343932841636453, -0.6531728429537765, -0.6715589548470184, -0.6895405447370668, -0.7071067811865475, -0.7242470829514668, -0.7409511253549589, -0.7572088465064842, -0.7730104533627367, -0.7883464276266059, -0.8032075314806451, -0.8175848131515838, -0.8314696123025452, -0.844853565249707, -0.857728610000272, -0.8700869911087113, -0.8819212643483549, -0.8932243011955152, -0.9039892931234431, -0.9142097557035305, -0.9238795325112865, -0.932992798834739, -0.9415440651830208, -0.9495281805930367, -0.9569403357322088, -0.9637760657954398, -0.970031253194544, -0.9757021300385285, -0.9807852804032303, -0.9852776423889411, -0.9891765099647809, -0.9924795345987101, -0.9951847266721969, -0.9972904566786902, -0.9987954562051724, -0.9996988186962042, -1.0, -0.9996988186962042, -0.9987954562051724, -0.9972904566786902, -0.9951847266721969, -0.9924795345987101, -0.9891765099647809, -0.9852776423889412, -0.9807852804032304, -0.9757021300385286, -0.970031253194544, -0.96377606579544, -0.9569403357322089, -0.9495281805930368, -0.9415440651830209, -0.9329927988347391, -0.9238795325112866, -0.9142097557035306, -0.9039892931234433, -0.8932243011955153, -0.881921264348355, -0.8700869911087115, -0.8577286100002722, -0.8448535652497072, -0.8314696123025455, -0.817584813151584, -0.8032075314806453, -0.7883464276266061, -0.7730104533627369, -0.7572088465064846, -0.7409511253549591, -0.724247082951467, -0.7071067811865477, -0.6895405447370672, -0.6715589548470187, -0.6531728429537771, -0.6343932841636459, -0.6152315905806274, -0.5956993044924332, -0.5758081914178452, -0.5555702330196022, -0.5349976198870973, -0.5141027441932219, -0.4928981922297843, -0.4713967368259979, -0.449611329654607, -0.4275550934302825, -0.4052413140049904, -0.3826834323650904, -0.359895036534988, -0.33688985339222, -0.3136817403988915, -0.2902846772544625, -0.2667127574748986, -0.2429801799032642, -0.2191012401568702, -0.1950903220161287, -0.1709618887603018, -0.1467304744553624, -0.122410675199216, -0.09801714032956051, -0.07356456359966741, -0.04906767432741809, -0.02454122852291245]

sin := fn(theta: f32): f32 {
    PI := 3.14159265358979323846
    TABLE_SIZE := @as(i32, 256)
    si := @float_to_int(@float_cast(theta) * 0.5 * @int_to_float(TABLE_SIZE) / @float_cast(PI))
    d := theta - @int_to_float(si) * 2.0 * PI / @int_to_float(TABLE_SIZE)
    ci := si + TABLE_SIZE / 4 & TABLE_SIZE - 1
    si &= TABLE_SIZE - 1
    return sin_table[@bit_cast(si)] + (sin_table[@bit_cast(ci)] - 0.5 * sin_table[@bit_cast(si)] * d) * d
}

main := fn(): int {
    return @float_to_int(sin(1000.0) * 1000.0)
}
```

#### float arithmetic 3
```hb
main := fn(): uint {
    if 1.0 > 2.0 return 1
    if 1.0 >= 2.0 return 2
    if 2.0 <= 1.0 return 3
    if 2.0 < 1.0 return 4
    if 1.0 != 1.0 return 5
    if 2.0 == 1.0 return 6
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

#### literals 2
```hb
expectations := .{
    return_value: 0,
}

hex := fn(): uint return 0x2d
dec := fn(): uint return 45

main := fn(): uint {
    if hex() != dec() return 1
    return 0
}
```

#### literals 3
```hb
expectations := .{
    return_value: 69,
}

main := fn(): uint {
    return 'E'
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

#### functions 4 (returning stack)
```hb
expectations := .{
    should_error: true,
}

main := fn(): void {
    rstack := return_direct_stack()
    rstruct := return_indirect_stack()
    v: ?^uint = null
    ret := return_indirect_stack_but_not(&v)
}

return_direct_stack := fn(): ^uint {
    a := 0
    if true return &a

    return &a
}

return_indirect_stack := fn(): struct{.u: uint; .b: uint; .c: ^uint} {
    v := 0
    return .(0, 0, &v)
}

return_indirect_stack_but_not := fn(arg: ^?^uint): void {
    v := 0
    arg.* = &v
    arg.* = null
}
```

#### comments 1
```hb
// commant is an item
main := fn(): uint {
    // comment is a statement
    foo(/* comment is an exprression */)
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

#### loops 5 (comptime or error)
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

#### loops 7 (loop invariant break)
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    arr := uint.[1, 2, 3, 4]
    i := 0
    sum := 0
    loop if i == arr.len break else {
        sum += arr[i]
        //i += 1 // ups forgot to increment
    }
    return sum
}
```

#### loops 8 (nested)
```hb
expectations := .{
    return_value: 55,
}

main := fn(): uint {
    n_sup := 0
    m := 0
    loop if n_sup == 10 break else {
        a := 0
        b := 1
        n := 0
        loop if n == 9 break else {
            m = a + b
            a = b
            b = m
            n += 1
        }
        n_sup += 1
    }
    return m
}
```

#### loops 9
```hb
main := fn(): uint {
    abc := "abc"
    i := 0
    loop {
        if i >= 1 return 0
        if false & abc[0] != 0 {
            n := 0
            loop if n == 0 break else {
                n *= 0
            }
        }
        i += 1
    }
}
```

#### loops 10 (multiple continues)
```hb
main := fn(): uint {
    i := 0
    loop {
        if i > 0 return 0
        x := true
        if false {
            x = false
        }
        if x {
            i += 1
            continue
        }
    }
}
```

#### loops 11 (multiple breaks)
```hb
main := fn(): uint {
    i := 0
    loop {
        if i == 0 break
        if i == 1 {
            i = 1
            break
        }
        i = 1
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
    return (~0).*
}
```

#### pointers 5 (math)
```hb
main := fn(): uint {
    val := uint.[1, 0]
    return (val.ptr + 1).*
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

#### structs 7
```hb
expectations := .{
    return_value: 0,
}

A := struct {
    .a: ?^u8;
}

main := fn(): uint {
    x: u8 = 0
    a := A.(&x)
    return @size_of(@TypeOf(a.a.?.*)) != @size_of(u8)
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
    $if Vec(uint) != Vec(uint) return 100

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
        .state: enum{.a; .b; .done};
        .a: A;
        .b: B

        Elem := @TypeOf(A.next(idk))

        next := fn(self: ^@CurrentScope()): Elem {
            loop match self.state {
                .a => {
                    nxt := self.a.next()
                    if nxt.next return nxt
                    self.state = .b
                },
                .b => {
                    nxt := self.b.next()
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
        sc := siter.next()
        if !sc.next break
        rc := riter.next()
        if !rc.next return 1

        if sc != rc return 2
    }

    riter = .(ref)
    loop {
        rc := riter.next()
        if !rc.next break
        sc := citer.next()
        if !sc.next return 3

        if sc != rc return 4
    }

    return 0
}
```

#### generic structs 6 (more iterators)
```hb
main := fn(): uint {
    _ = @use("foo.hb").foo(0, u8)
    return 0
}

// in: foo.hb
Map := fn(I: type, F: type): type return struct{}
foo := fn(vl: int, $oo: type): Map(u8, oo) return .()
```

#### generic structs 7 (template method call)
```hb
A := struct {
    apply := fn(self: ^@CurrentScope(), $func: type): void {
    }
}

main := fn(): uint {
    z := A.()
    y := z.apply(fn(): void {
    })
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

#### tuples 1
```hb
expectations := .{
    return_value: 6,
}

main := fn(): uint {
    tuple := .(1, 2, 3)
    return tuple[0] + tuple[1] + tuple[2]
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

#### unions 3
```hb
expectations := .{
    return_value: 8,
}

main := fn(): uint {
    return TypeInfo(uint).builtin.size
}

TypeInfo := fn($T: type): union {
    .builtin: Builtin;
} {
    return @bit_cast(Builtin.(@size_of(T)))
}

Builtin := struct {
    .size: uint;
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

#### enums 2 (one variant)
```hb
main := fn(): uint {
    return Target.current().Lib().page_size()
}

ableos := @use("ableos.hb")

Target := enum {
    .AbleOS

    current := fn(): Target {
        $if @target("ableos") return .AbleOS
        @error("Unknown Target")
    }

    Lib := fn(target: Target): type {
        match target {
            .AbleOS => return ableos,
        }
    }
}

// in: ableos.hb
page_size := fn(): uint return 0
```

#### enums 3 (customization)
```!hb
main := fn(): uint {
    Enm := enum(u32) {
        .a = 1;
        .b;
        .c = 0
    }

    if @as(Enm, @bit_cast(@as(u32, 1))) != .a return 1
    if @as(Enm, @bit_cast(@as(u32, 2))) != .b return 2
    if @as(Enm, @bit_cast(@as(u32, 0))) != .c return 3

    return 0
}
```

#### enums 4
```hb
expectations := .{
    return_value: 69,
}

NameMap := fn($Enum: type): type {
    sum := 0
    i: u8 = 0
    $loop $if i == @len_of(Enum) break else {
        sum += @int_cast(@name_of(@as(Enum, @bit_cast(i))).len)
        i += 1
    }

    StrBuf := [sum]u8
    IndexBuf := [@len_of(Enum) + 1]uint
    return struct {
        .buf: StrBuf;
        .index: IndexBuf

        new := fn(): @CurrentScope() {
            buf: StrBuf = idk
            index: IndexBuf = idk
            index[0] = 0

            ii: u8 = 0
            bi := 0
            $loop $if ii == @len_of(Enum) break else {
                name := @name_of(@as(Enum, @bit_cast(ii)))
                ij := 0
                $loop $if ij == name.len break else {
                    buf[bi + ij] = name[ij]
                    ij += 1
                }

                bi += @int_cast(name.len)
                ii += 1
                index[ii] = bi
            }

            return .(buf, index)
        }

        get := fn(self: ^@CurrentScope(), k: Enum): []u8 {
            return self.buf[self.index[k]..self.index[@as(u8, k) + 1]]
        }
    }
}

Nm := enum{.E; .bcd; .cd}

map := NameMap(Nm).new()

main := fn(): uint {
    return map.get(.E)[0]
}
```

#### enums 5
```hb
expectations := .{
    return_value: 0,
}

Enum := enum{.A; .B; .C}

main := fn(): uint {
    if Enum.C > .A {
        return 0
    }
    return 1
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
    $match enum{.a}.a {
        .a => {
        },
    }

    $match enum{.a; .b}.a {
        .a => return 0,
        .b => return 1,
    }
}
```

#### match 3 (errors)
```hb
expectations := .{
    should_error: true,
}

main := fn(): void {
    match enum{.a; .b}.a {
    }

    match enum{.a; .b}.a {
        .a => {
        },
    }

    $match enum{.a; .b}.a {
    }

    $match enum{.a; .b}.a {
        .b => {
        },
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

#### die 1
```hb
expectations := .{
    unreaches: true,
}

main := fn(): uint {
    if false return 1
    die
}
```

#### die 2
```hb
expectations := .{
    unreaches: true,
}

fallible := fn(): ?^u8 {
    return null
}

main := fn(): void {
    a := fallible()
    if a == null die
    die
}
```

#### global variables 1
```hb
counter := 0

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

some_other := 10

some_fib := fib(some_other)

fib := fn(n: uint): uint {
    if n != 10 return 0
    return 55
}

bigon_era := some_other - 10

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

#### string errors
```hb
expectations := .{
    should_error: true,
}

main := fn(): void {
    _ = "\ඞ"
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

#### arrays 3 (errors)
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    arr := uint.[0, 1, 2]
    return arr[3]
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

opaque := fn(): uint return 0
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

#### slices 3
```hb
reverse := fn(slice: []u8): []u8 {
    if slice.len == 0 return slice
    j := slice.len - 1
    i := 0
    temp: u8 = 0
    loop if i < j {
        temp = slice[i]
        slice[i] = slice[j]
        slice[j] = temp
        i += 1
        j -= 1
    } else return slice
}

main := fn(): uint {
    arr := u8.[1, 2, 3]
    _ = reverse(&.[])
    _ = reverse(arr[..])
    return arr[0] - arr[1] - arr[2]
}
```

#### slices 4
```hb
equals := fn(lhs: []u8, rhs: []u8): bool {
    if lhs.len != rhs.len return false
    if lhs.ptr == rhs.ptr return true
    i := 0
    loop if i == lhs.len break else {
        if lhs[i] != rhs[i] return false
        i += 1
    }
    return true
}

main := fn(): uint {
    abc := "abc"
    a_b_c := u8.['a', 'b', 'c'][..]
    if !equals(abc, abc) return 1
    if !equals(a_b_c, abc) return 1

    return 0
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

#### nullable types 3 (unwrap inference)
``` hb
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

    nlbl.b = 1
    take(&nlbl)

    return nlbl.a - nlbl.b
}

take := fn(s: ^Stru): void {
    s.a += 1
}
```

#### nullable types 4 (pointer optimization)
```hb
main := fn(): uint {
    if @size_of(?^u8) != @size_of(^u8) return 1
    if @size_of(?struct{.v: ^u8}) != @size_of(^u8) return 2

    v := 3
    ptr := opaque(&v)
    ptr.?.* = 0

    return v
}

opaque := fn(v: @Any()): ?@TypeOf(v) return v
```

#### struct patters 1
```hb
expectations := .{
    return_value: 3,
}

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
}

main := fn(): uint {
    return @ecall(
        100,
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
    return_value: 7,
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

#### directives 11 (@target, @is_comptime)
```hb
expectations := .{
    return_value: 1,
}

global: bool = @target("ableos")

main := fn(): uint {
    $if @is_comptime() @error("unecpected")

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
    _ = func(@as(uint, 1), 2)
    return foo(5) + foo(@as(u8, 5))
}

foo := fn(vl: @Any()): @TypeOf(vl) {
    return vl
}

func := fn(a: @Any(), b: @TypeOf(a)): uint {
    return 0
}
```

#### directives 14 (@name_of)
```hb
expectations := .{
    return_value: 7,
}

main := fn(): uint {
    return @name_of(uint).len + @name_of(enum{.foo}.foo).len
}
```


## progress

- [x] hbvm-ableos target
- [ ] x86_64-linux target
- [ ] x86_64-windows target
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
      - [x] clean up the hacky graph hierarchy
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
      - [x] `- + * / % == != <= >= < > << >> | ^ &`
    - [x] unary operators
      - [x] `- ! ~`
  - [x] floats
    - [x] binary operators
      - [x] `- + * / == != <= >= < >`
    - [x] unary operators
      - [x] `-`
  - [x] structs
    - [x] indexing
    - [x] alignment
    - [ ] ? field alignment
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
    - [ ] ? alignment
    - [ ] ? field alignment
    - [ ] ? tag + customizable
    - [x] scope
  - [x] pointers
    - [x] slicing
  - [x] slices
    - [x] known size (arrays)
    - [x] field access
    - [x] indexing
    - [x] slicing
    - [x] empty
    - [ ] ? array slicing
  - [x] tuples
  - [x] nullable types
- [ ] ? directives
  - [x] `@use(<string>): <struct>`
  - [x] `@TypeOf(<expr>): type`
  - [x] `@as(<ty>, <expr>): <ty>`
  - [x] `@int_cast(<int>): <infered-int>`
  - [x] `@size_of(<ty>): uint`
    - [ ] comptime interrupt
  - [x] `@align_of(<ty>): uint`
    - [ ] comptime interrupt
  - [x] `@bit_cast(<expr>): <infered-ty>`
  - [x] `@ecall(...<expr>): <infered-ty>`
  - [x] `@embed(<string>): [len]u8`
  - [ ] ? `@inline(<func>, ...<args>): <func>.ret`
    - [x] noop compatibility
  - [x] `@len_of(<ty>): uint`
    - [ ] comptime interrupt
  - [x] `@kind_of(<ty>): u8`
    - [ ] comptime interrupt
  - [x] `@Any(<fn(type): void/type>..): type`
    - [ ] ? type filters
  - [x] `@error(...<expr>): never`
  - [ ] ? `@compiles(<expr>): bool`
  - [x] `@ChildOf(<ty>): type`
    - [ ] comptime interrupt
  - [x] `@target("<pat>"): bool`
  - [x] `@is_comptime(): bool`
  - [x] `@int_to_float(<int>): <float>`
  - [x] `@float_to_int(<float>): int`
  - [x] `@float_cast(<float>): <float>`
  - [x] `@name_of(<ty>): []u8`
    - [ ] comptime interrupt
  - [ ] ? `@recall(..<args>): never`
- [ ] optimizations
  - [ ] assumptions
  - [ ] memory
    - [ ] uninitialized global memory
    - [ ] constant global loads
    - [x] stack elimination
    - [x] load alias reordering
      - [x] around stores
      - [ ] around calls
    - [x] store->load forwarding
    - [ ] splitting
    - [ ] mem2reg
      - [x] scalar locals
      - [ ] arbitrary locals
  - [ ] compute
    - [ ] folding
    - [ ] algebra
  - [ ] control flow
    - [ ] inlining (heuristic)
    - [ ] loop unrolling
    - [ ] folding
  - [ ] clonable insructions
  - [x] allocate abi registers
- [ ] static analisys
  - [ ] source locations
  - [ ] constraint propagation
    - [ ] provenance
  - [x] returning stack reference
    - [x] trivial direct pointer
    - [x] trough memory
    - [ ] ? trough memcpy
  - [ ] uninitialized reads
  - [ ] unreachable loop breaks
  - [x] loop invariant conditions
  - [ ] dead code reporting
  - [x] local out of bounds read/write
    - [x] scalar read/write
    - [ ] memcpy
  - [ ] semantic assertions
    - [ ] null checks
    - [ ] bound checks

## vendored tests

```bash
git submodule add https://git.ablecorp.eu/lily-org/lily.git vendored-tests/lily # add a new
git submodule update --init --recursive                                         # fetch
git submodule update --remote vendored-tests/lily                               # update a
```

## Contributing

When contributing make sure to:
1. Mark what you completed in [progress](#progress), as the part of your changes. Stuff that is not in the checklist needs an issue. TODO: make an issue template
1. Add apropriate examples to test the functionality, `zig build test` will automatically generate a test for the example and run it with rverithing else. It's preferable to add `#### <feature> <n>` and use `n = 1` for demonstration and other examples to cover all ways to use the frature you can think of.

### Relevant things to contribute with

- implementing frontend features mentioned in progress
- implementing more peephole optimizations (located inside `fn idealize*`)
- implementing new target triple (the [Machine](./src/backend/Machine.zig))
  - look at [HbvmGen](./src/hbvm/HbvmGen.zig)
