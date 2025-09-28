main := fn(argn: uint, argv: ^^u8): uint {
	Arena.init_scratch(4096)

	_ = Command.{args: &.["/bin/ls", "-al"]}.step.execute()

	return 1
}

Command := struct {
	.step: Step = .{vtable: .init(Command)};
	.args: [][]u8;
	.env: []Var = &.[]

	Var := struct{.name: []u8; .value: []u8}

	execute := fn(step: ^Step): ?Step.Hash {
		self: ^Command = @parent_ptr("step", step)

		tmp := Arena.scratch(null)
		defer tmp.pop()

		args := tmp.arena.alloc(?^u8, self.args.len + 1)

		for slot := args[..args.len - 1], arg := self.args {
			scratch := tmp.arena.alloc(u8, arg.len + 1)
			mem.cpy(u8, scratch[..scratch.len - 1], arg.*)
			scratch[scratch.len - 1] = 0
			slot.* = scratch.ptr
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

		sys.execve(args[0].?, args.ptr, env.ptr)

		return null
	}
}

Step := struct {
	.vtable: ^Vtable;
	.dependencies: []^Step = &.[];
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

	alloc_raw := fn(self: ^Arena, size: uint, alignment: uint): ^u8 {
		self.pos = @bit_cast(mem.align_forward(uint, @bit_cast(self.pos), alignment))
		self.pos += size

		debug.assert(self.pos <= self.end)

		return self.pos - size
	}
}

mem := enum {
	align_forward := fn($T: type, pos: T, alignment: uint): T {
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
}

debug := enum {
	assert := fn(cond: bool): void if !cond die
}

sys := enum {
	$page_size := 4096

	execve := fn(path: ^u8, argv: ^?^u8, envp: ^?^u8): void {
		@syscall(59, path, argv, envp)
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
