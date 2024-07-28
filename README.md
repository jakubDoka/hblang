# zoley-bytes

### Tour

#### main-fn
```hb
main := fn(): int {
    return 42
}
```

#### arithmetic
```hb
main := fn(): int {
    return 10 - 20 / 2 + 4 * (2 + 2) - 4 * 4 + 1
}
```

#### functions
```hb
main := fn(): int {
    return add_one(10) + add_two(20)
}

add_two := fn(x: int): int {
    return x + 2
}

add_one := fn(x: int): int {
    return x + 1
}
```

#### comments
```hb
// commant is an item
main := fn(): int {
    // comment is a statement
    foo(/* comment is an exprression /* if you are crazy */ */)
    return 0
}

foo := fn(comment: void): void return /* comment evaluates to void */

// comments might be formatted in the future
```

#### if-statements
```hb
main := fn(): int {
    return fib(10)
}

fib := fn(x: int): int {
    if x <= 2 {
        return 1
    } else {
        return fib(x - 1) + fib(x - 2)
    }
}
```

#### variables
```hb
main := fn(): int {
    ඞ := 1
    b := 2
    ඞ += 1
    return ඞ - b
}
```

#### loops
```hb
main := fn(): int {
    return fib(10)
}

fib := fn(n: int): int {
    a := 0
    b := 1
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

#### pointers
```hb
main := fn(): int {
    a := 1
    b := &a
    modify(b)
    drop(a);
    *b += 2
    stack_reclamation_edge_case := 0
    return *b - 4
}

modify := fn(a: ^int): void {
    *a = 2
    return
}

drop := fn(a: int): void {
    return
}
```

#### structs
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

## Edge Cases

#### register-ownership
```hb
// should use only 3 registers as last occurence should end
// the variable lifetime
main := fn(): int {
    a := 1
    b := 2
    c := 3
    e := a
    f := b
    return c + e + f - 6
}
```

## Codegen architecture brainstorming

One of the most annoying things I am trying to implement is storing structs in registers. The fact that any register can have offset is not enough, the field it self might even overlap two registers, which makes for incredibly ugly code. Most of this revolves around moving memory that produces huge amount of bit twiddling. But Then again, I need to do this somehow, and I need to emit optimal code as well. Obviously, we can't emit the field stores and loads all the time, since we would bloat the binary and slow down the program. At this point we need optimizations, that would both simplify the code that is emitted as well as compiler code that emits it.

While writing previous chunk of useless text, I came up with, brilliant idea. Lets cache the loaded fields, meaning, We can create a tree of fields that are mapped to registers and stacks by offset.
