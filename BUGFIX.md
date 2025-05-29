# Bug Fix Tests

This file contains minimal repro tests that are not a good example for learning.

#### arithmetic 8
```hb
main := fn(): uint {
    return (0 < 1) - (1 + 0)
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
