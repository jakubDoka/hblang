# Bug Fix Tests

This file contains minimal repro tests that are not a good example for learning.

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
main := fn(): u32 loop if false return blackbox()
```

#### regalloc crash 3
```hb
Broken := struct{.inner: ?[]u8}
broken := fn(self: Broken): ?[]u8 return self.inner

A := 5
main := fn(): u32 loop if A == A return 0 else {
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

#### regalloc crash 2 (infinite)
```hb
expectations := .{
    times_out: true,
}

broken := fn(self: ?[]u8): void {
}

main := fn(): u32 loop {
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
main := fn(): u32 {
    _ = broken(.(0, 0, 0), ' ')
    return 0
}
```

#### field access on non scope type 1
```hb
expectations := .{
    should_error: true,
}

main := fn(): u32 {
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

main := fn(): u32 {
    $i := 0
    $T := Z
    $while i < 100 {
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

main := fn(): u32 {
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

func := fn(op: u8, fd: u8, event: WrapperU8): void {
}

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
```hb
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
```hb
expectations := .{
    should_error: true,
}

V2 := struct{.a: f64; .b: f64}

fun := fn(v: V2): f64 return v.a + v.b

main := fn(): int {
    return @float_to_int(fun(.(1.0, 2.0)) - 3.0)
}
```

#### float load and store 1
```hb
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
broken := fn(event: Broken): void {
}
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
    byte_iter("hello, world").for_each(fn(x: u8): void {
    })
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
    $for_each := fn(self: ^Self, $func: type): void {
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
    optr.* = {
    }

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
    return load_of_args(0, 1, 2, 3, 4, 5, 6, 7) -
        stack_args(.(0, 1, 2), .(3, 4, 5), .(6, 7))
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
    loop {
    }
    return 0
}
```

#### exhausitve inlining 1
```hb
expectations := .{
    unreaches: true,
}

$no_op := fn(): void {
}

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
    Wrapper := fn($T: type): type return struct{.x: T}
    Wrap := fn($T: type): type return struct {
        test := fn(): Wrapper(@TypeOf(T.test())) {
            return .(T.test())
        }
    }
    A := struct {
        test := fn(): void {
        }
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
    } else {
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
```!hb
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

#### async 1
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
}

bind := fn(self: @Any(), $f: type): Async(T, struct {
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
    b := bind(T.new(0), U)
    a := bind(b, T)
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
bind := fn(val: @Any(), $f: type): @TypeOf(f(idk)) {
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

bar := fn(): void {
}

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
    if true {
    }
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

main := fn(): u32 {
    loop {
        val1: ?u8 = null
        loop if val1 == null break else {
            if val1.? == 0 {
            }
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
    _ = Ty.(.{}, .(), {
    })
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

Target := enum {
    .AbleOS;
    .x86_64_linux

    current := fn(): Target {
        $if @target("hbvm-ableos") return .AbleOS
        $if @target("x86_64-linux") return .x86_64_linux
        @error("Unknown target")
    }

    Lib := fn(target: Target): type {
        match target {
            .AbleOS => return ableos,
            .x86_64_linux => return linux,
        }
    }
}

// in: ableos.hb
page_size := fn(): uint return 0

// in: linux.hb
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
