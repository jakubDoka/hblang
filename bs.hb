main := fn(argn: uint, argv: ^^u8): uint {
	args := argv[0..argn]

	for argp := args {
		arg := str_to_slice(argp.*)
		@syscall(1, 2, arg)
		@syscall(1, 2, "\n")
	}

	Arena.init_scratch(4096)
	defer Arena.deinit_scratch()

	tmp := Arena.scratch(null)
	defer tmp.pop()

	mem := tmp.arena.alloc(u8, 10)

	memset(mem, 'j')

	@syscall(1, 2, mem)

	return 0
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
		ptr := mmap(null, size, .read | .write, .private | .anonymous, -1, 0)
		return .(ptr, ptr, ptr + size)
	}

	deinit := fn(self: ^Arena): void {
		munmap(self.ptr, @int_cast(self.end - self.ptr))
	}

	alloc := fn(self: ^Arena, $elem: type, count: uint): []elem {
		raw := self.alloc_raw(@size_of(elem) * count, @align_of(elem))
		return @as(^elem, @bit_cast(raw))[0..count]
	}

	alloc_raw := fn(self: ^Arena, size: uint, alignment: uint): ^u8 {
		self.pos = @bit_cast(align_forward(uint, @bit_cast(self.pos), alignment))
		self.pos += size

		assert(self.pos <= self.end)

		return self.pos - size
	}
}

memset := fn(mem: []u8, value: u8): void {
	ptr := mem.ptr
	len := mem.len

	while len > 0 {
		ptr.* = value
		ptr += 1
		len -= 1
	}
}

align_forward := fn($T: type, pos: T, alignment: uint): T {
	return pos + alignment - 1 & ~(alignment - 1)
}

mmap := fn(addr: ?^u8, len: uint, prot: MmapProt, flags: MmapFlags, fd: i32, offset: u64): ^u8 {
	return @syscall(9, addr, len, prot.vl, flags.vl, fd, offset)
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

assert := fn(cond: bool): void if !cond die

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
