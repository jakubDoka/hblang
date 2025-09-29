main := fn(argn: uint, argv: ^^u8, envp: ^?^u8): uint {
	sys.env = envp

	Arena.init_scratch(4096)

	tmp := Arena.scratch(null)
	defer tmp.pop()

	cmd := Command.init("ls", tmp.arena)


	return 1
}

LazyPath := union(enum) {
	.path: []u8;
	.generated: GeneratedFile;
}

GeneratedFile := struct {
	.by: ^Step;
	.name: []u8;
}

Command := struct {
	.step: Step = .{vtable: .init(Command)};
	.args: ArrayList(Arg) = .empty;
	.env: []Var = &.[];
	.stdout: ?i32 = null

	Arg := union(enum) {
		.bytes: []u8;
		.lazy_path: LazyPath;
	}

	Var := struct{.name: []u8; .value: []u8}

	init := fn(cmd: []u8, scratch: ^Arena): Command {
		return .{args: scratch.dupe(Arg, &.[.{path: cmd}])}
	}

	execute := fn(step: ^Step): ?Step.Hash {
		self: ^Command = @parent_ptr("step", step)

		tmp := Arena.scratch(null)
		defer tmp.pop()

		args := tmp.arena.alloc(?^u8, self.args.len + 1)

		for slot := args[..args.len - 1], arg := self.args {
			slot.* = tmp.arena.dupe_z(arg.*)
		}
		args[args.len - 1] = null

		env := tmp.arena.alloc(?^u8, self.env.len + 1)

		for slot := env[..env.len - 1], var := self.env {
			scratch := tmp.arena.alloc(u8, var.name.len + 1 + var.value.len + 1)
			mem.cpy(u8, scratch[..var.name.len], var.name)
			scratch[var.name.len] = '='
			mem.cpy(u8, scratch[var.name.len + 1..][..var.value.len], var.value)
			scratch[var.name.len + 1 + var.value.len] = 0
			slot.* = scratch.ptr
		}
		env[env.len - 1] = null

		args[0] = tmp.arena.dupe_z(sys.resolve_exe_path(self.args[0], tmp.arena) || return null)

		result := sys.fork()
		if result < 0 {
			return null
		}

		if result == 0 {
			if sys.execve(args[0].?, args.ptr, env.ptr) != 0 {}
		} else {
			_ = sys.waitpid(result, &0, 0)
		}

		return null
	}
}

Step := struct {
	.vtable: ^Vtable;
	.dependencies: ArrayList(^Step) = .empty;
	.last_hash: ?Hash = null;
	.has_side_effects: bool = false

	Hash := [16]u8

	Vtable := struct {
		.execute: ^fn(self: ^Step): ?Hash

		$init := fn($T: type): ^Vtable {
			return &struct {
				vt := Vtable.(&T.execute)
			}.vt
		}
	}

	execute := fn(self: ^Step): ?Hash {
		return self.vtable.execute(self)
	}
}

Arena := struct {
	.ptr: ^u8;
	.pos: ^u8;
	.end: ^u8

	scratch_arenas: [2]Arena = @thread_local_storage()

	init_scratch := fn(cap: uint): void {
		for arena := scratch_arenas[..] {
			arena.* = .init(cap)
		}
	}

	deinit_scratch := fn(): void {
		for arena := scratch_arenas[..] {
			arena.deinit()
		}
	}

	scratch := fn(other: ?^Arena): Scope {
		for arena := scratch_arenas[..] {
			if arena != other {
				return arena.scope()
			}
		}

		die
	}

	Scope := struct {
		.arena: ^Arena;
		.pos: ^u8

		pop := fn(self: ^Scope): void {
			self.arena.pos = self.pos
		}
	}

	scope := fn(self: ^Arena): Scope {
		return .(self, self.pos)
	}

	init := fn(size: uint): Arena {
		ptr := sys.mmap(null, size, .read | .write, .private | .anonymous, -1, 0)
		return .(ptr, ptr, ptr + size)
	}

	deinit := fn(self: ^Arena): void {
		sys.munmap(self.ptr, @int_cast(self.end - self.ptr))
	}

	alloc := fn(self: ^Arena, $elem: type, count: uint): []elem {
		raw := self.alloc_raw(@size_of(elem) * count, @align_of(elem))
		return @as(^elem, @bit_cast(raw))[0..count]
	}

	grow := fn(self: ^Arena, $elem: type, slice: []elem, new_cap: uint): ^elem {
		if slice.ptr + slice.len == self.pos {
			self.pos = slice.ptr
		}

		new := self.alloc(elem, new_cap)
		mem.cpy(elem, new[..slice.len], slice)
		return new.ptr
	}

	dupe := fn(self: ^Arena, $elem: type, slice: []elem): []elem {
		slc := self.alloc(elem, slice.len)
		mem.cpy(elem, slc, slice)
		return slc
	}

	dupe_z := fn(self: ^Arena, slice: []u8): ^u8 {
		slc := self.alloc(u8, slice.len + 1)
		mem.cpy(u8, slc[..slice.len], slice)
		slc[slice.len] = 0
		return slc.ptr
	}

	alloc_raw := fn(self: ^Arena, size: uint, alignment: uint): ^u8 {
		self.pos = @bit_cast(mem.align_forward(uint, @bit_cast(self.pos), alignment))
		self.pos += size

		debug.assert(self.pos <= self.end)

		return self.pos - size
	}
}

ArrayList := fn($T: type): type return struct {
	.items: []T;
	.capacity: uint

	Self := @CurrentScope()

	empty := Self.{items: &.[], capacity: 0}

	push := fn(self: ^Self, item: T, scratch: ^Arena): void {
		if self.capacity == self.items.len {
			new_cap := max(uint, self.capacity * 2, 8)
			self.items.ptr = scratch.grow(T, self.items.ptr[0..self.capacity], new_cap)
			self.capacity = new_cap
		}

		self.items[self.items.len] = item
		self.items.len += 1
	}
}

max := fn($T: type, a: T, b: T): T {
	if a > b return a else return b
}

mem := enum {
	align_forward := fn($T: type, pos: T, alignment: T): T {
		return pos + alignment - 1 & ~(alignment - 1)
	}

	strlen := fn(str: ^u8): uint {
		len := 0
		while (str + len).* != 0 {
			len += 1
		}
		return len
	}

	str_to_slice := fn(str: ^u8): []u8 {
		len := strlen(str)
		return str[0..len]
	}

	starts_with := fn($elem: type, str: []elem, prefix: []elem): bool {
		if str.len < prefix.len {
			return false
		}

		for i := 0..prefix.len {
			if str[i] != prefix[i] {
				return false
			}
		}

		return true
	}

	set := fn(region: []u8, value: u8): void {
		ptr := region.ptr
		len := region.len

		while len > 0 {
			ptr.* = value
			ptr += 1
			len -= 1
		}
	}

	cpy := fn($elem: type, dst: []elem, src: []elem): void {
		debug.assert(dst.len == src.len)

		dstp := dst.ptr
		srcp := src.ptr
		len := dst.len

		while len > 0 {
			dstp.* = srcp.*
			dstp += 1
			srcp += 1
			len -= 1
		}
	}

	index := fn($elem: type, str: []elem, sep: []elem): ?uint {
		for i := 0..str.len - sep.len {
			if mem.starts_with(elem, str[i..], sep) {
				return i
			}
		}
		return null
	}

	SplitIter := fn($elem: type): type return struct {
		.remaining: []elem;
		.sep: []elem

		Self := @CurrentScope()

		next := fn(self: ^Self): ?[]elem {
			if self.remaining.len == 0 {
				return null
			}

			pos := mem.index(elem, self.remaining, self.sep) || {
				defer self.remaining.len = 0
				return self.remaining
			}

			ret := self.remaining[0..pos]
			self.remaining = self.remaining[pos + self.sep.len..]

			return ret
		}
	}

	split := fn($elem: type, str: []elem, sep: []elem): SplitIter($elem) {
		return .(str, sep)
	}
}

debug := enum {
	assert := fn(cond: bool): void if !cond die
}

sys := enum {
	$page_size := 4096

	access := fn(path: ^u8, mode: AccessMode): i32 {
		return @syscall(21, path, mode)
	}

	AccessMode := struct {
		.bits: uint

		exists := AccessMode.(0)
		read := AccessMode.(1)
		write := AccessMode.(2)
		execute := AccessMode.(4)
	}

	resolve_exe_path := fn(path: []u8, scratch: ^Arena): ?[]u8 {
		if mem.starts_with(u8, path, "/") || mem.starts_with(u8, path, "./") {
			return path
		}

		vl := sys.getenv("PATH") || return null

		iter := mem.split(u8, vl, ":")

		while pp := iter.next() {
			tmp := Arena.scratch(scratch)
			defer tmp.pop()

			slot := tmp.arena.alloc(u8, pp.len + 1 + path.len + 1)
			mem.cpy(u8, slot[..pp.len], pp)
			slot[pp.len] = '/'
			mem.cpy(u8, slot[pp.len + 1..slot.len - 1], path)
			slot[slot.len - 1] = 0

			if sys.access(slot.ptr, .exists) == 0 {
				return scratch.dupe(u8, slot[..slot.len - 1])
			}
		}

		return null
	}

	env: ^?^u8 = idk

	getenv := fn(name: []u8): ?[]u8 {
		cur := env
		while c := cur.* {
			str := mem.str_to_slice(c)

			if mem.starts_with(u8, str, name) &&
				str.len > name.len && str[name.len] == '=' {
				return str[name.len + 1..]
			}

			cur += 1
		}

		return null
	}

	dup2 := fn(oldfd: i32, newfd: i32): i32 {
		return @syscall(63, oldfd, newfd)
	}

	fork := fn(): i32 {
		return @syscall(57)
	}

	waitpid := fn(pid: i32, status: ^i32, options: i32): i32 {
		return @syscall(61, pid, status, options)
	}

	execve := fn(path: ^u8, argv: ^?^u8, envp: ^?^u8): uint {
		return @syscall(59, path, argv, envp)
	}

	mmap := fn(addr: ?^u8, len: uint, prot: MmapProt, flags: MmapFlags, fd: i32, offset: u64): ^u8 {
		return @syscall(9, addr, len, prot, flags, fd, offset)
	}

	munmap := fn(addr: ^u8, len: uint): void {
		@syscall(11, addr, len)
	}

	MmapProt := struct {
		.vl: uint

		read := MmapProt.(1)
		write := MmapProt.(2)
		exec := MmapProt.(4)
	}

	MmapFlags := struct {
		.vl: uint

		private := MmapFlags.(0x02)
		anonymous := MmapFlags.(0x20)
	}
}
