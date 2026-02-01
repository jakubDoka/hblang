# Bug Fix Tests

This file contains minimal repro tests that are not a good example for learning.

#### const folding between func args 1
```hb
expectations := .{
    return_value: 2,
}

main := fn(): uint {
    return bar(1)
}

bar := fn(a: uint): uint {
    return foo((a + 1), (a + 1) - (a + 1))
}

foo := fn(a: uint, b: uint): uint {
    return a + b
}
```

#### comptime only leftover 1
```hb
expectations := .{
    should_error: true,
}

Aaaa := fn(): type {
    return @Type(.{@struct: .{
        alignment: @align_of(void),
        fields: &.[],
        decls: &.[],
    }})
}

main := fn(): uint {
    T := Aaaa()
    return 0
}
```

#### bad opt 1
```hb
$Result := fn($Value: type, $Error: type): type return union(enum) {
    .value: Value;
    .error: Error

    This := @CurrentScope()

    $value := fn(v: Value): This return .{value: v}
    $error := fn(e: Error): This return .{error: e}
}

main := fn(): int {
    return Result(i32, i32).value(0).value
}
```

#### type_info error 1
```hb
main := fn(): uint {
    $info := @type_info(@TypeOf(main)).@fn
    $if info.ret == uint return 0
    return 1
}
```

#### malformed global union 3
```hb
Aaa := union(enum) {
    .a: struct{};
}

func := fn(): Aaa {
    return .{a: .()}
}

main := fn(): uint {
    if func() == .a return 0
    return 1
}
```

#### malformed global union 2
```hb
Aaa := union(enum) {
    .a: struct{};
}

main := fn(): uint {
    e := Aaa.{a: .()}

    if e == .a return 0

    return 1
}
```

#### malformed global union 1
```hb
$a := (fn(): union(enum) {
    .a: u32;
    .b: u32;
} {
    $if true return .{b: 0}
    return .{a: 1}
})()

main := fn(): uint {
    $match a {
        .a => return 1,
        .b => return 0,
    }
}
```

#### nested globals 11
```hb
expectations := .{
    return_value: 69,
}

main := fn(): uint {
    return @eval(@type_info(enum{.Edward})).@enum.fields[0].name[0]
}
```

#### nested globals 10
```hb
expectations := .{
    return_value: 69,
}

strings := ([]u8).["Edward"]

string_slice := strings[..]

main := fn(): uint {
    return string_slice[0][0]
}
```

#### comptime edge cases 1
```hb
expectations := .{
    should_error: true,
}

opaque := false

main := fn(): uint {
    vl := #0

    if opaque {
        vl = 1
    }

    return @eval(vl)
}
```

#### comptime edge cases 2
```hb
expectations := .{
    should_error: true,
}

opaque := false

main := fn(): uint {
    vl := #0
    ovl := #0

    if opaque {
        vl = 1
        ovl = 1
    }

    return @eval(vl)
}
```

#### comptime edge cases 3
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    vl := #0

    while vl < 1 while vl < 1 vl += 1

    return @eval(vl)
}
```

#### comptime edge cases 4
```hb
main := fn(): uint {
    vl := #1
    ovl := #0

    while ovl < 1 while ovl < 1 ovl += vl

    return @eval(vl - 1)
}
```

#### comptime edge cases 5
```hb
main := fn(): uint {
    $parse_ty := u8
    if true && true {
        $out_ty := @eval(parse_ty)
    }

    len := 10

    $i := 0
    $while i < len {
        i += 1
    }

    return 0
}
```

#### comptime edge cases 6
```hb
main := fn(): uint {
    $len := 3
    loop {
        if true {
            break
        }
        if true {
            _ = @as(?[]u8, null) || return 0
        } else {
            _ = @as(?[]u8, null) || return 0
        }
        if true {
            fun()
            _ = @as(?[]u8, null) || return 0
        }
    }
    $i := 0
    $while i < len {
        i += 1
    }
    return 0
}

fun := fn(): void {}
```

#### comptime edge cases 7
```hb
main := fn(): uint {
    vl := #0
    v := #0

    while v < 1 while v < 1 v += 1

    vl = 1

    return @eval(vl - 1)
}
```

#### comptime edge cases 8
```hb
main := fn(): uint {
    var := #0

    modify := fn(vl: ^uint): void vl.* += 1

    capture_val1 := @eval(var)
    modify(&var)
    capture_val2 := @eval(var)

    if capture_val1 == capture_val2 return 1

    $big_var := .(0, 0, 0)

    read_only := fn(vl: @Any()): uint return vl[0]

    capture_val3 := read_only(big_var)
    modify(&big_var[0])
    capture_val4 := read_only(big_var)

    _ = @eval(big_var)

    if capture_val3 == capture_val4 return 2

    vl := .(1, 0, 0)

    _ = fun(vl)

    _ = fun_ref(&vl)

    return @eval(vl[0] - 1)
}

fun_ref := fn(vl: @Any()): uint {
    return vl.*[0] - 1
}

fun := fn(vl: @Any()): uint {
    return vl[0] - 1
}
```

#### comptime edge cases 9
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    vl := #0

    while vl < 1 {
        while vl < 1 if vl < 2 {
            while vl < 1 vl += 1
        }
    }

    return @eval(vl)
}
```

#### enum and struct
```hb
A := enum(u8) {
    .BROKEN := 0xFF;
}
B := struct {
    .a: u8;
    .b: u32;
    .c: A;
}

broken := fn(data: B): u32 return data.a
main := fn(): uint return broken(B.(0, 0, .BROKEN))
```

#### nested structs
```hb
A := struct {
    .x: struct {
        .y: []A;
    };
}

main := fn(): uint {
    a := A.(.(idk))
    return 0
}
```

#### other file span oob
```hb
expectations := .{
    should_error: true,
}

broken := @use("broken.hb")

main := fn(): uint {
    x := broken.X(u8).run()
    return 0
}

// in: broken.hb

X := fn($T: type): type return struct {
    run := fn(): void @CurrentScope().does_not_exist
}
```

#### mul reduction 1
```hb
expectations := .{
    return_value: 10,
}

main := fn(): uint {
    return foo(1, 2, 3) + bar(6, 2, 4)
}

foo := fn(a: uint, b: uint, c: uint): uint {
    return a * b + a * c
}

bar := fn(a: uint, b: uint, c: uint): uint {
    return a / b + c / b
}
```

#### scoping 1
```hb
A := struct {
    $A: u32 = 0
}
main := fn(): uint return A.A
```

#### generic structs 7 (template method call)
```hb
A := struct {
    apply := fn(self: ^@CurrentScope(), $func: fn(): void): void {}
}

main := fn(): uint {
    z := A.()
    y := z.apply(fn(): void {})
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

#### global load and store ordering 1
```hb
TRUE := true
x: bool = true
main := fn(): uint {
    orig := x
    if TRUE x = false
    return x == orig
}
```

#### for loop continues 1
```hb
main := fn(): uint {
    for i := 0..10 {
        if i == 0 continue
    }
    return 0
}
```

#### for overflow 1
```hb
expectations := .{
    return_value: 1,
}

x: [(fn(): uint {
    if @target("hbvm-ableos") return 128
    return 1 << 16
})()]u32 = idk
main := fn(): uint {
    for i := 0..x.len x[i] = 1
    return x[x.len - 1]
}
```

#### memset peephole 1
```hb
memset := fn(len: uint, dest: ^u8, src: u8): void {
    while len > 0 {
        dest.* = src
        dest += 1
        len -= 1
    }
}

main := fn(): uint {
    arr: [8]u8 = idk
    memset(arr.len, arr.ptr, 0)
    return arr[0]
}
```

#### memset peephole 2
```hb
$memset := fn(len: uint, dest: ^u8, src: u8): void {
    while len > 0 {
        dest.* = src
        dest += 1
        len -= 1
    }
}

main := fn(): uint {
    memset(0, @bit_cast(0), 0)
    return 0
}
```

#### dump asm crash 1
```hb
cache := fn($fnc: type, $Args: type): type {
    $Inner := struct {
        cached: ?@TypeOf(fnc(@as(Args, idk))) = null
        args: ?Args = null
    }
    return struct {
        do := fn(invalidate: bool, args: Args): @TypeOf(fnc(@as(Args, idk))) {
            if invalidate || Inner.args == null || Inner.args.? != args {
                Inner.cached = null
                Inner.args = args
            }

            Inner.cached ||= @inline(fnc, args)
            return Inner.cached.?
        }
    }
}

add := cache(fn(args: @Any()): i32 {
    //@syscall(1, 2, "computing...\n".ptr, "computing...\n".len)
    return args.x + args.y
}, struct{.x: i32; .y: i32}).do

main := fn(): int {
    $if !@target("x86_64-linux") return 0

    i := 0
    r: i32 = 0
    while i < 100 {
        r = add(false, .(1, 2))
        i += 1
    }
    return r - 3
}
```

#### build not terminating 1
```hb
a := false
$b := fn(): ?void {
    if a return {}
    return null
}
ignore := fn(x: uint): void {}
main := fn(): uint loop {
    x := 0
    if a x = 1
    ignore(x)
    b() || return 0
}
```

#### for loop wiredness 1
```hb
main := fn(): uint {
    a: uint = 0
    for i := a..10 {}
    return @int_cast(a)
}
```

#### nullable types 6
```hb
x := fn(y: ?never): u32 return 0
main := fn(): uint return x(null)
```

#### nullable types 7
```hb
expectations := .{
    should_error: true,
}

y := fn(w: never): uint die
x := fn(z: ?never): u32 return y(z || return 0)
main := fn(): uint return x(null)
```

#### nullable types 8
```hb
x := fn(z: ?never): u32 return z != null
main := fn(): uint return x(null)
```

#### nullable types 9
```hb
y := fn(w: never): u32 return 0
x := fn(z: ?never): u32 if z == null return 0 else return y(z.?)
main := fn(): uint return x(null)
```

#### nullable types 10
```hb
y := fn(w: @Any()): u32 die
x := fn(z: ?never): u32 return y(z || return 0)
main := fn(): uint return x(null)
```

#### custom one variant enum 1
```hb
expectations := .{
    return_value: 5,
}

A := enum(uint){.b := 5}
main := fn(): uint return @bit_cast(A.b)
```

#### custom one variant enum 2
```hb
A := enum(uint){.b := 5}
c := fn(): uint return A.b
main := fn(): uint return c() - 5
```

#### nested options 1
```hb
reset := fn(x: []u8): void for i := 0..x.len x[i] = 0xFF
defb := fn(): ??bool return null
defc := fn(): ??bool {
    x: ??bool = idk
    reset(@as(^u8, @bit_cast(&x))[0..@size_of(??bool)])
    return defb()
}
main := fn(): uint return defc() != null
```

#### duplicate instantiation in recurcive templates 1
```hb
main := fn(): uint {
    return foo(Stru.(.(0), .(.(1)), null))
}

Stru2 := struct {
    .a: u8;
}

Stru := struct {
    .a: Stru2;
    .c: f;
    .b: ?Stru2

    f := struct{.b: Stru2}
}

var := ""

foo := fn(arg: @Any()): uint {
    var = "foo"
    ty := @TypeOf(arg)
    $if @kind_of(ty) == 7 {
        i := 0
        $while i < @len_of(ty) {
            _ = foo(arg[i])
            i += 1
        }
        return 0
    } else $if @kind_of(ty) == 3 {
        if arg == null return 0
        return foo(arg.?)
    } else {
        return arg
    }
}
```

#### struct capture eca mismatch 1
```hb
cp := fn($_r0: u8, $_r1: u8): struct align(1){.op: u8 = 0; .r0: u8 = _r0; .r1: u8 = _r1} {
    return .{}
}

main := fn(): int {
    return cp(1, 0).op
}
```

#### out of range access 1
```hb
bwa := fn(x: [7]?bool): u32 return 0
main := fn(): uint return bwa(.[null, null, null, null, null, null, null])
```

#### more comptime eval 1
```hb
X := struct {
    .st: uint
    $x := fn($st: uint): X return .(st)
}
$aaa := fn($a: []X): uint {
    return a[0].st
}
bbb := aaa(X.[.x(1)][..])

main := fn(): uint {
    return bbb - 1
}
```

#### more comptime eval 2
```hb
X := struct {
    .st: uint;
    .st1: uint
    $x := fn($st: uint): X return .(st, 0)
}

$aaa := fn($a: []X): uint return a[0].st
bbb := aaa(X.[.x(1)][..])

main := fn(): uint {
    return bbb - 1
}
```

#### more comptime eval 3
```hb
X := struct {
    .st: uint;
    .st1: uint;
    .st2: uint
    $x := fn($st: uint): X return .(st, 0, 0)
}

$aaa := fn($a: []X): uint return a[0].st
bbb := aaa(X.[.x(1)][..])

main := fn(): uint {
    return bbb - 1
}
```

#### resolve mem phi during partial eval 1
```hb
expectations := .{
    should_error: true,
}

cond := false
main := fn(): uint {
    $if cond || cond {
        return 1
    }

    return 0
}
```

#### comptime array access 1
```hb
$i := 0
main := fn(): type.[uint][i] return 0
```

#### function pointers 2
```hb
X := struct {
    .func: ^fn(): void;
}

main := fn(): uint {
    X.(&fn(): void {}).func()

    return 0
}
```

#### function pointers 3
```hb
DynObj := struct {
    .do_thing: ^fn(inst: ^void): u8;
    .obj: ^void

    $new := fn($T: type, inst: ^T): DynObj {
        return .(@bit_cast(&T.do_thing), @bit_cast(inst))
    }
}

Obj := struct {
    .x: u8
    do_thing := fn(self: ^Obj): u8 return self.x + 1
}

main := fn(): uint {
    obj := Obj.(255)
    dyn_obj := DynObj.new(Obj, &obj)
    fptr := dyn_obj.do_thing
    return fptr(dyn_obj.obj)
}
```

#### function pointers 4
```hb
DynObj := struct {
    .obj: ^Obj;
    .v_func: ^fn(^Obj): u8;
    ._wth: void
    // TODO: fix the formatter here it removes semicolon incorrectly

    $func := fn(self: ^DynObj): u8 {
        return self.v_func(self.obj)
    }
    $new := fn(obj: @Any()): DynObj {
        return .(obj, &@TypeOf(obj.*).func, {})
    }
}

Obj := struct {
    .state: u8
    func := fn(self: ^Obj): u8 return self.state + 1
}

main := fn(): uint {
    obj := Obj.(255)
    dyn_obj := DynObj.new(&obj)
    return dyn_obj.func()
}
```

#### short circuit token bug 1
```!hb
main := fn(): uint {
    &&= true
}
```

#### short and op precedence 1
```hb

foo := fn(x: ?u8): bool {
    if v := x && v2 := x {
        return v == v2
    }

    return false
}

main := fn(): uint {
    if foo(null) return 1
    if !foo(1) return 2
    val := true && false
    return 0
}
```

#### various mem opts 1
```hb
opaque := true

use := fn(v: @Any()): void {}

store_pullout := fn(): uint {
    x := 1
    use(&x)
    if opaque {
        x = 0
    } else {
        x = 0
    }
    return x
}

duplicate_store := fn(): uint {
    x := 1
    use(&x)
    x = 0
    x = 0
    use(&x)
    return x
}

combine_pull_out_duplicate := fn(): uint {
    x := 1
    use(&x)
    if opaque {
        x = 0
    } else {
        x = 0
    }
    x = 0
    use(&x)
    return x
}

parallel_stores := fn(): uint {
    a := 0
    b := 0

    use(&a)
    use(&b)

    if opaque {
        a = 1
        b = 1
    } else {
        b = 1
        a = 1
    }

    return a - b
}

main := fn(): uint {
    if store_pullout() != 0 return 1
    if duplicate_store() != 0 return 2
    if combine_pull_out_duplicate() != 0 return 3
    if parallel_stores() != 0 return 4

    return 0
}
```

#### array index crash 1
```hb
awa := fn(x: u8): uint {
    buf: [3]u8 = .[0, 0, 0]
    i := 2
    while x > 0 {
        buf[i] = x
        x /= 10
        i -= 1
    }
    return 0
}
main := fn(): uint return awa(255)
```

#### bad signed div 1
```hb
x: i32 = -1200
main := fn(): uint return -(x / 10) != 120
```

#### bad signed div 2
```hb
main := fn(): uint {
    $x: i32 = -1200
    $y := -(x / 10)
    return y != 120
}
```

#### insane regalloc crash 1 (infinite)
```hb
expectations := .{
    should_error: true,
}

broken := fn(): void loop {
    $i := 0
    $while i < 64 {
        x: ?[]u8 = idk
        if y := x return;
        i += 1
    }
}
main := fn(): uint loop broken()
```

#### insane regalloc crash 1
```hb
main := fn(): uint {
    $i := 0
    $while i < 32 {
        if val := @as(?[]u8, idk) return 0
        i += 1
    }
    return 0
}
```

#### loop check 1
```hb
nextPos := fn(buf: []u8): ?uint {
    if buf.len >= 1 return 17
    return null
}
check := fn(buf: []u8): bool return true
blackbox := fn(): bool return true
main := fn(): uint {
    data := "aaaaaaaaaaaaaaaaaaaaa"
    i := 0
    while j := nextPos(data[i..]) {
        if check(data[i..j]) {
            if !blackbox() {
                i = 0
                continue
            }
            return 0
        }
        i = 0
    }
    return 1
}
```

#### comptime around the loop 1
```hb
main := fn(): uint {
    Stru := struct{}

    sum := 0
    i := 0
    while i < 10 {
        j := 0
        while j < 10 {
            sum += i + j
            j += 1
        }
        i += 1
    }

    val: Stru = .()

    return sum - 900
}
```

#### mem2reg crash 6
```hb
expectations := .{
    should_error: true,
}

$blackbox := fn(): u32 return 0
main := fn(): uint loop if false return blackbox()
```

#### regalloc crash 3
```hb
Broken := struct{.inner: ?[]u8}
broken := fn(self: Broken): ?[]u8 return self.inner

A := 5
main := fn(): uint loop if A == A return 0 else {
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
    _ = broken(.(null))
}
```

#### regalloc crash 4
```hb
blackbox := fn(self: ^u32): void {}
blackbox2: ?int = null
main := fn(): uint {
    x: ^u32 = @bit_cast(1)
    loop if sh := blackbox2 {
        if blackbox2 == null continue
        blackbox(x)
        while s := blackbox2 blackbox(x)
    } else return 0
}
```

#### regalloc crash 5
```hb
mod10 := fn(x: u32): u32 return x % 10
ignore := fn(x: ^u8): void {}
n: u16 = 10
main := fn(): uint {
    ignore("".ptr)
    return mod10(@as(u32, @int_cast(n)))
}
```

#### regalloc crash 2 (infinite)
```hb
expectations := .{
    times_out: true,
}

broken := fn(self: ?[]u8): void {}

main := fn(): uint loop {
    broken(null)
    broken(null)
    broken(null)
    broken(null)
    broken(null)
    broken(null)
    broken(null)
}
```

#### something with the machine 1 (infinite)
```hb
expectations := .{
    times_out: true,
}

broken := fn(): struct{} return .()

foo := fn(): uint {
    loop {
        _ = broken()
    }
}

main := fn(): uint {
    return @inline(foo)
}
```

#### regalloc crash 1
```hb
X := struct{.a: u8; .b: u64; .c: u8}
broken := fn(self: X, n: u8): X {
    if n == 0 return self
    return self
}
main := fn(): uint {
    _ = broken(.(0, 0, 0), ' ')
    return 0
}
```

#### field access on non scope type 1
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    return (fn(): type return struct{}).test
}
```

#### deep instantiation 1
```hb
S := fn($A: type): type return struct {
    get := fn(): u32 return A.get() + 1
}

Z := struct {
    get := fn(): u32 return 0
}

main := fn(): uint {
    $i := 0
    $T := Z
    $while i < 10 {
        i += 1
        T = S(T)
    }
    return T.get() != i
}
```

#### deep instantiation 2
```hb
S := fn($A: type): type return struct {
    get := fn(): u32 return A.get() + 1
}

Z := struct {
    get := fn(): u32 return 0
}

main := fn(): uint {
    return S(S(S(S(S(S(S(S(Z)))))))).get() != 8
}
```

#### deep dedup 1
```hb
main := fn(): uint {
    return a() - b()
}

a := fn(): uint {
    return c()
}

b := fn(): uint {
    return d()
}

c := fn(): uint {
    return 1
}

d := fn(): uint {
    return 1
}
```

#### deep dedup 2 (generics)
```hb
main := fn(): uint {
    return size(uint) - size(int)
}

size := fn($t: type): uint {
    return @size_of(t)
}
```

#### deep dedup 3 (recursive functions)
```hb
main := fn(): uint {
    return fib(3) - fib2(3)
}

fib := fn(x: uint): uint {
    if x <= 2 {
        return 1
    } else {
        return fib(x - 1) + fib(x - 2)
    }
}

fib2 := fn(x: uint): uint {
    if x <= 2 {
        return 1
    } else {
        return fib2(x - 1) + fib2(x - 2)
    }
}
```

#### deep dedup 4 (mutuali recursive)
```hb
main := fn(): uint {
    return fib(3) - fib2(3)
}

fib := fn(x: uint): uint {
    if x <= 2 {
        return 1
    } else {
        return fib_body(x)
    }
}

fib_body := fn(x: uint): uint {
    return fib(x - 1) + fib(x - 2)
}

fib2 := fn(x: uint): uint {
    if x <= 2 {
        return 1
    } else {
        return fib_body2(x)
    }
}

fib_body2 := fn(x: uint): uint {
    return fib2(x - 1) + fib2(x - 2)
}
```

#### dangling pointer in global 1
```hb
expectations := .{
    should_error: true,
}

$ptr: ^u8 = @bit_cast(0)
main := fn(): uint return @as(^u8, @bit_cast(0)) != ptr
```

#### duplicate identifier 1
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint return erm

X := struct {
    erm := 0
}

erm := 0
```

#### importing global 1
```hb
foo.{global} := @use("global2.hb")

main := fn(): uint {
    return global
}

// in: global2.hb
.{global} := @use("global.hb")

// in: global.hb
$global := 0
```

#### gcm crash 1 (infinite)
```hb
expectations := .{
    times_out: true,
}

WrapperU8 := struct {
    .x: u8;
}

func := fn(op: u8, fd: u8, event: WrapperU8): void {}

ZERO: u8 = 0

main := fn(): uint {
    buf: [1024]u8 = idk
    remaining: []u8 = buf[0..0]
    loop {
        loop if remaining.len >= 0 break else {
            remaining = buf[..]
        }
        ev: WrapperU8 = .(ZERO)
        if remaining.len == 0 remaining = remaining[..]
        func(0, ZERO, ev)
    }
    return 0
}
```

#### float sse call conv 1
```!hb
expectations := .{
    should_error: true,
}

V2 := struct{.a: f32; .b: f32}

fun := fn(v: V2): f32 return v.a + v.b

main := fn(): int {
    return @float_to_int(fun(.(1.0, 2.0)) - 3.0)
}
```

#### float sse call conv 2
```!hb
expectations := .{
    should_error: true,
}

V2 := struct{.a: f64; .b: f64}

fun := fn(v: V2): f64 return v.a + v.b

main := fn(): int {
    return @float_to_int(fun(.(1.0, 2.0)) - 3.0)
}
```

#### float sse call conv 3
```!hb
expectations := .{
    should_error: true,
}

V2 := struct{.a: f32; .b: f32; .c: f32; .d: f32}

fun := fn(v: V2): f32 return v.a + v.b + v.c + v.d

main := fn(): int {
    return @float_to_int(fun(.(1.0, 2.0, 3.0, 4.0)) - 10.0)
}
```

#### float load and store 1
```!hb
Stru := struct{.a: f32; .b: f32; .c: f32}

fun := fn(s: Stru): f32 return s.a + s.b - s.c

main := fn(): int {
    return @float_to_int(fun(.(1.0, 2.0, 3.0)))
}
```

#### carry over call float op 1
```hb
expectations := .{
    return_value: 3,
}

opaque := fn(v: @Any()): @TypeOf(v) return v

main := fn(): int {
    a := opaque(1.0)
    b := opaque(2.0)

    _ = opaque(0)

    c := a + b

    _ = opaque(c)

    return @float_to_int(c)
}
```

#### loop if folding 1 (infinite)
```hb
expectations := .{
    times_out: true,
}

main := fn(): uint {
    loop {
        n := 0
        if false n = 1
    }
    return 0
}
```

#### packed struct pass
```hb
Broken := struct align(1) {
    .a: u8;
    .b: u16;
}
broken := fn(event: Broken): void {}
main := fn(): uint {
    broken(.(0, 0))
    return 0
}
```

#### null check misshap 1
```hb
glb: u8 = 0

alloc := fn(): ?^u8 {
    return &glb
}

main := fn(): uint {
    mmapped := alloc()
    if mmapped != null {
        mmapped.?.* = 1
        return 0
    } else {
        return 1
    }
}
```

#### subsume copy 1
```hb
main := fn(): uint {
    value := u8.[1, 2, 3]

    value2 := value
    value3 := value2

    return value3[0] + value3[1] - value3[2]
}
```

#### subsume copy 2
```hb
main := fn(): uint {
    value := u8.[1, 2, 3]
    value2 := u8.[1, 2, 0]

    tmp := value
    value[2] = value2[2]
    value2[2] = tmp[2]

    return value2[0] + value2[1] - value2[2]
}
```

#### out of bounds matching 1
```hb
main := fn(): uint {
    byte_iter("hello, world").for_each(fn(x: u8): void {})
    return 0
}

$byte_iter := fn(slice: []u8): Iterator(struct {
    .slice: []u8

    $next := fn(self: ^@CurrentScope()): ?u8 {
        if self.slice.len == 0 return null
        tmp := self.slice[0]
        self.slice = self.slice[1..]
        return tmp
    }
}) {
    return .(.(slice))
}

Iterator := fn($Iter: type): type return struct {
    .inner: Iter
    Next := @TypeOf(Iter.next(idk))
    Value := @ChildOf(Next)
    Self := @CurrentScope()

    $next := fn(self: ^Self): Next return self.inner.next()
    $for_each := fn(self: ^Self, $func: fn(Value): void): void {
        while x := self.next() {
            _ = func(x)
        }
    }
}
```

#### unaligned stack 1
```hb
$check_stack := fn(): void {
    $if @target("x86_64-linux") {
        if @frame_pointer() % 16 == 0 {
            die
        }
    }
}

main := fn(): uint {
    check_stack()
    return 0
}
```

#### wired pointer edge cases
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    ptr: ^enum{} = idk
    optr: ^void = idk

    vl := ptr.*
    ovl := optr.*
    ptr.* = idk
    optr.* = {}

    return 0
}
```

#### cstring indexing
```hb
@handler("slice_ioob", fn(sloc: @SrcLoc(), slice_len: uint, start: uint, end: uint): never {
    die
})

$cstr := fn(c_str: ^u8): []u8 {
    len := 0
    while (c_str + len).* != 0 len += 1
    return c_str[..len]
}

main := fn(): uint {
    args := (^u8).["aa\0".ptr, "bb\0".ptr]

    len := 0
    while len < args.len {
        _ = cstr(args[len])
        len += 1
    }
    return 0
}
```

#### null unwrap 1
```hb
expectations := .{
    unreaches: true,
}

@handler("null_unwrap", fn(sloc: @SrcLoc()): never die)

use_opt := fn(opt: ?uint): uint return opt.? + opt.?

main := fn(): uint {
    _ = use_opt(1)
    return use_opt(null)
}
```

#### passing struct multiple times 1
```hb
S := struct{.a: uint; .b: uint; .c: uint}
B := struct{.a: u8; .b: u8; .c: u8}

main := fn(): uint {
    vl := S.(1, 2, 3)
    bl := B.(1, 2, 3)
    return foo(bl, vl)
}

foo := fn(b: B, s: S): uint {
    return bar(s, b)
}

bar := fn(s: S, v: B): uint {
    return s.a + s.b - s.c + v.a + v.b - v.c
}
```

#### proper systemv abi 1 (spilled arg)
```hb
load_of_args := fn(
    a: uint,
    b: uint,
    c: uint,
    d: uint,
    e: uint,
    f: uint,
    g: uint,
    h: uint,
): uint {
    return a + b + c + d + e + f + g + h
}

stack_args := fn(
    a: struct{.a: uint; .b: uint; .c: uint},
    b: struct{.a: uint; .b: uint; .c: uint},
    v: struct{.a: uint; .b: uint},
): uint {
    return a.a + a.b + a.c + b.a + b.b + b.c + v.a + v.b
}

main := fn(): uint {
    return load_of_args(0, 1, 2, 3, 4, 5, 6, 7)
        - stack_args(.(0, 1, 2), .(3, 4, 5), .(6, 7))
}
```

#### index-ptr precedence 1
```hb
main := fn(): uint {
    val := 0
    return (&val)[..1][0]
}
```

#### inline return stack 1
```hb
expectations := .{
    should_error: true,
}

$inlined := fn(): []u8 {
    buf: [4]u8 = idk
    return buf[..]
}

main := fn(): uint {
    return inlined().len
}
```

#### eopll 2
```hb
$epoll_wait := fn(epfd: int, events: ^void, maxevents: uint, timeout: int): void {
    _x: uint = @syscall(232, epfd, events, maxevents, timeout)
}
main := fn(): uint {
    $if !@target("x86_64-linux") return 0
    efd: i32 = @syscall(291, 0)
    if false {
        return 1
    }
    events: [16]u8 = idk
    i := 0
    loop {
        if i == 0 {
            return 0
        }
        epoll_wait(efd, @bit_cast(events.ptr), events.len, -1)
        i += 1
    }
    return 1
}
```

#### epoll 1
```hb
EPOLL_CTL_ADD: u16 = 1
main := fn(): uint {
    $if !@target("x86_64-linux") return 0

    efd: i32 = @syscall(291, 0, 0)
    if efd < 0 {
        return 1
    }
    ev: struct align(4) {
        .events: u32;
        .data: u64;
    } = .(1, 0)
    res: i32 = @syscall(233, efd, @as(int, EPOLL_CTL_ADD), 0, &ev)
    if res < 0 return 2
    return 0
}
```

#### syscall then infinite loop 1
```hb
main := fn(): uint {
    $if !@target("x86_64-linux") return 0
    @syscall(291, 0)
    loop {}
    return 0
}
```

#### exhausitve inlining 1
```hb
expectations := .{
    unreaches: true,
}

$no_op := fn(): void {}

$unreachable := fn(): void die

$double_inline := fn(): void no_op()

$some_mem_ops := fn(vl: ^uint): void {
    vl += 1
}

$loop_fn := fn(iters: uint): void {
    loop if iters == 0 break else {
        iters -= 1
    }
}

$recurcive := fn(n: uint): uint {
    if n == 0 return 0

    return recurcive(n - 1)
}

main := fn(): uint {
    no_op()

    a := 0
    some_mem_ops(&a)
    if a != 1 return 0

    if false {
        unreachable()
    }

    loop_fn(10)

    ////_ = recurcive(10)

    unreachable()

    return 0
}
```

#### false positive in cycle detection
```hb
main := fn(): uint {
    $Wrapper := fn($T: type): type return struct{.x: T}
    Wrap := fn($T: type): type return struct {
        test := fn(): Wrapper(@TypeOf(T.test())) {
            return .(T.test())
        }
    }
    A := struct {
        test := fn(): void {}
    }
    B := Wrap(A)
    C := Wrap(B)
    _ = C.test()
    return 0
}
```

#### typeof is not comptime 1
```hb

broken1 := fn(): uint {
    $if @target("hbvm-ableos") {
        AllocEcall := struct align(1){.pad: u8; .pages_new: uint; .zeroed: bool}
        @ecall(3, 2, AllocEcall.(0, 1, false), @size_of(AllocEcall))
    } else if @target("x86_64-linux") {
        @syscall(1, 2, "".ptr, 0)
    }
    return 0
}
main := fn(): @TypeOf(broken1()) {
    return broken1()
}
```

#### wired string comparison 1
```hb
Out := struct {
    .left: []u8;
    .right: []u8;
}
In := struct {
    .left: u8;
    .right: []u8;
}
broken := fn(v: In): Out {
    return .(v.right, v.right)
}

main := fn(): uint {
    data := "test"
    x := broken(.(0, data))
    return x.right.ptr != data.ptr
}
```

#### comptime short circuit failure 1
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    $if @kind_of(uint) == 7 && @align_of(uint) == 8 return 1
    return 0
}
```

#### confusing error message
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    x: []type = .[i32, i32]
}
```

#### format comment correctly
```hb
Foo := struct {
    .foo: int;
    // smh
    .boo: int;
}

main := fn(): uint {
    return 0
}
```

#### arithmetic 8
```hb
main := fn(): uint {
    return (0 < 1) - (1 + 0)
}
```

#### bad oob diagnostic 1
```hb
expectations := .{
    should_error: true,
}

Union := union {
    vl := fn(self: @CurrentScope()): uint {
        v: ^uint = @bit_cast(&self)
        return v.*
    }
}

main := fn(): uint {
    return Union.vl(idk)
}
```

#### fmt tuple 1
```hb
expectations := .{
    should_error: true,
}

main := fn(): uint {
    tpl := .(1, 2, 3)
    tr := &tpl

    stru := struct {
        foo := 0
    }

    _ = stru
        .foo

    tr.* = .(
        1,
        2,
        3,
    )
}
```

#### fmt prec 1
```hb
main := fn(): uint {
    return (fn(): uint return 0)()
}
```

#### fmt prec 3
```hb
main := fn(): uint {
    return (@as(??u8, null) || return 0) || return 1
}
```

#### zero sized structs 1
```hb
main := fn(): uint {
    X := struct {
        .x: struct {
            test := fn(self: @CurrentScope()): uint {
                return 0
            }
        }
        new := fn(): @CurrentScope() {
            return .(.())
        }
    }
    return X.new().x.test()
}
```

#### invalid item 3
```hb
expectations := .{
    should_error: true,
}

InvalidUnion := union {
    .invalid = u32;
    .invalid;
}

main := fn(): uint {
    uni := InvalidUnion.{invalid: 10}
    return uni.invalid
}
```

#### async 2
```hb
expectations := .{
    should_error: true,
}

Async := fn($T: type, $Poller: type): type return struct {
    .poller: Poller
    new := fn(x: Input): @CurrentScope() {
        return .(Poller.new1(x))
    }
    Input := T
    Poll := Poller
    poll := fn(self: @CurrentScope()): @TypeOf(Poller.poll1(idk)) {
        return self.poller.poll1()
    }
    bind := fn(self: @CurrentScope(), $f: type): Async(T, struct {
        .done1: bool;
        .poller: union {
            .left: Poll;
            .right: f.Poll;
        }
        new1 := fn(x: Poll): @CurrentScope() {
            return .(false, @bit_cast(x))
        }
        poll1 := fn(self1: @CurrentScope()): @TypeOf(f.Poll.poll1(idk)) {
            loop if self1.done1 {
                p: ^f.Poll = @bit_cast(&self.poller)
                return p.poll1()
            } else {
                p: ^Poll = @bit_cast(&self.poller)
                ret := p.poll1()
                if ret == null {
                    return null
                }
                self1.done1 = true
                self1.poller.right = f.Poll.new(ret.?)
            }
        }
    }) {
        return .(.(false, .(.left = self)))
    }
}

main := fn(): uint {
    T := Async(i32, struct {
        new1 := fn(x: i32): @CurrentScope() {
            return .()
        }
        poll1 := fn(self: @CurrentScope()): ?uint {
            return 1
        }
    })
    U := Async(uint, struct {
        new1 := fn(x: uint): @CurrentScope() {
            return .()
        }
        poll1 := fn(self: @CurrentScope()): ?i32 {
            return 2
        }
    })
    a := T.new(0).bind(U).bind(T)
    x := a.poll()
    loop if x == null break else x = a.poll()
    return x.?
}
```

#### fmt prec 2
```hb

main := fn(): uint {
    f()
    return 0
}

f := fn(): void {
    if true return;
    return
}
```

#### mixing @Any and comptime args 1
```hb
bind := fn(val: @Any(), $f: fn(@TypeOf(val.?)): @TypeOf(val)): @TypeOf(f(idk)) {
    if val != null {
        return f(val.?)
    }
    return null
}

main := fn(): uint {
    b: ?i32 = @as(i32, 0)
    a := bind(b, fn(x: i32): ?i32 return x + 5)
    return 0
}
```

#### mem2reg crash 1
```hb
main := fn(): uint {
    return insert(0, 1)
}

bar := fn(): void {}

insert := fn(a: uint, b: uint): uint {
    if a == 0 bar()
    idx := 0
    loop {
        offset := 0
        loop if offset >= 8 break else {
            if offset == b {
                return a
            }
            offset += 1
        }
        idx += 1
    }
}
```

#### mem2reg crash 2
```hb
main := fn(): uint {
    s := Self.{entries: Entry.[.{key: 1, value: 0}][..]}

    return insert(&s, 1, 0).?.*
}

Entry := struct{.key: uint; .value: uint}
Self := struct {
    .entries: []Entry;
}

insert := fn(self: ^Self, key: uint, value: uint): ?^uint {
    if true {}
    idx := 0
    loop {
        offset := 0
        loop if offset >= 8 break else {
            entry := self.entries.ptr
            if entry.key == key {
                return &entry.value
            }
            offset += 1
        }
        idx += 1
    }
}
```

#### mem2reg crash 3 (infinite)
```hb
expectations := .{
    times_out: true,
}

main := fn(): uint {
    x: []u8 = idk
    loop {
        loop if true break else {
            x = x[..]
        }
        if true x = x[..]
    }
    return 0
}
```

#### mem2reg crash 4 (infinite) (control flow)
```hb
main := fn(): uint {
    x: []u8 = idk
    loop {
        loop if true break else {
            x = x[..]
        }
    }
    return 0
}
```

#### mem2reg crash 5 (infinite)
```hb
expectations := .{
    unreaches: true,
}

main := fn(): uint {
    loop {
        val1: ?u8 = null
        loop if val1 == null break else {
            if val1.? == 0 {}
            val1 = null
        }
    }
}
```

#### static analisys 1
```hb
expectations := .{
    should_error: true,
}

obf := 1

main := fn(): uint {
    a := obf
    b := &a

    loop {
        if (b.* & 1) != 0 {
            x := 0
            loop if x >= 8 break else {
                if b.* == 0 {
                    return 1
                }
                x += 1
            }
        }
    }
}
```

#### big constant 1
```hb
main := fn(): uint {
    return uninit(&0)
}

uninit := fn(p: ^uint): uint {
    p.* = idk
    return 0
}
```

#### arithmetic 9 (force imm ops)
```hb
main := fn(): uint {
    if box(~0) ^ ~0 != 0 return 1
    return 0
}

box := fn(v: @Any()): @TypeOf(v) return v
```

#### forced shl 1
```hb
expectations := .{
    return_value: 4,
}

main := fn(): uint {
    return two() << one()
}

one := fn(): uint return 1
two := fn(): uint return 2
```

#### forced div 1
```hb
expectations := .{
    return_value: 2,
}

main := fn(): uint {
    return two() / one()
}

one := fn(): uint return 1
two := fn(): uint return 2
```

#### adding difference to a pointer 1
```hb
main := fn(): uint {
    arr := u8.[0, 1, 2, 3]
    ptr := &arr[0]
    ptr += @size_of(u8) - one()
    return ptr.*
}

one := fn(): uint return 1
```

#### error propagation 1
```hb
expectations := .{
    should_error: true,
}

Broken := fn($T: type): type struct{}
broken := fn($T: type): ?Broken(T) {
    return .()
}

main := fn(): uint {
    i := 0
    loop {
        if broken(u8) != null {
            break
        } else {
            break
        }
    }
    return 0
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
    _ = Ty.(.{}, .(), {})
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

#### slices 5 (coersion)
```hb
use_slice := fn(slice: []u8): void {}

main := fn(): uint {
    use_slice(&.[1, 2, 3, 4])
    return 0
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

#### global variables 4 (nested)
```hb
expectations := .{
    return_value: 69,
}

str := "Edward"

main := fn(): uint {
    return str[0]
}
```

#### global variables 5 (nested constant)
```hb
expectations := .{
    return_value: 69,
}

$str := "Edward"

main := fn(): uint {
    return str[0]
}
```

#### enums 2 (one variant)
```hb
main := fn(): uint {
    return Target.current().Lib().page_size()
}

ableos := @use("ableos.hb")
linux := @use("ableos.hb")
wasm_freestanding := @use("wasm_freestanding.hb")

Target := enum {
    .AbleOS;
    .x86_64_linux;
    .wasm_freestanding

    current := fn(): Target {
        $if @target("hbvm-ableos") return .AbleOS
        $if @target("x86_64-linux") return .x86_64_linux
        $if @target("wasm-freestanding") return .wasm_freestanding
        @error("Unknown target")
    }

    Lib := fn(target: Target): type {
        match target {
            .AbleOS => return ableos,
            .x86_64_linux => return linux,
            .wasm_freestanding => return wasm_freestanding,
        }
    }
}

// in: ableos.hb
page_size := fn(): uint return 0

// in: linux.hb
page_size := fn(): uint return 0

// in: wasm_freestanding.hb
page_size := fn(): uint return 0
```

#### enums 6 (custom value match)
```hb
main := fn(): uint {
    Enm := enum(u32){.a := 100; .b; .c := 0}

    match Enm.b {
        .a => return 1,
        .b => return 0,
        .c => return 2,
    }
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

#### enum range 1
```hb
Kind := enum(u8) {
    .eof := 0;
    .ident;
    .decl;
    .k_fn

    keyword_range := @type_info(Kind).@enum.fields[0].value
}

main := fn(): i64 {
    return Kind.keyword_range
}
```

#### double loop search 1
```hb
main := fn(): uint {
    kind := 1

    for kv := 0..2 {
        if kv == 0 {
            kind = 0
        }
    }

    //for kv := 0..2 {}

    return kind
}
```

#### double loop search 2
```hb
main := fn(): uint {
    kind := 1

    for kv := 0..2 {
        if kv == 0 {
            kind = 0
        }
    }

    for kv := 0..2 {}

    return kind
}
```

#### modify tmp 1
```hb
Parser := struct {
    .tok: Tok

    Tok := struct {
        .kind: Kind;
        .value: uint;
        .value2: uint

        Kind := enum(u8) {
            .ident;
            .tint;
        }
    }

    expr := fn(self: ^Parser): uint {
        ptok := self.tok

        self.tok = mm()

        return ptok.kind
    }

    mm := fn(): Tok {
        return .(.tint, 0, 0)
    }
}

main := fn(): uint {
    p := Parser.(.(.ident, 0, 0))
    return p.expr()
}

```
