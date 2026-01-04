Arena := struct {
	.ptr: ^u8;
	.pos: ^u8;
	.end: ^u8

	comptime_scratch: [1024 * 4 * 2]u8 = idk
	comptime_arenas: [2]Arena = .[
		.init_slice(comptime_scratch[..comptime_scratch.len / 2]),
		.init_slice(comptime_scratch[comptime_scratch.len / 2..]),
	]

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

	ct_scratch := fn(other: ?^Arena): Scope {
		for arena := comptime_arenas[..] {
			if arena != other {
				return arena.scope()
			}
		}

		die
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

	init_slice := fn(items: []u8): Arena {
		return .(items.ptr, items.ptr, items.ptr + items.len)
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

	create := fn(self: ^Arena, $elem: type): ^elem {
		return self.alloc(elem, 1).ptr
	}

	grow := fn(self: ^Arena, $elem: type, slice: []elem, new_cap: uint): ^elem {
		if self.pos == @bit_cast(slice.ptr + slice.len) {
			self.pos += new_cap - slice.len
			return slice.ptr
		}

		new := self.alloc(elem, new_cap)
		mem.cpy(elem, new[..slice.len], slice)
		return new.ptr
	}

	spill := fn(self: ^Arena, $T: type, vl: T): ^T {
		slot := self.alloc(T, 1).ptr
		slot.* = vl
		return slot
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

	concat := fn(self: ^Arena, $elem: type, slice: [][]elem): []elem {
		len := 0
		for s := slice {
			len += s.len
		}

		new := self.alloc(elem, len)
		pos := 0
		for s := slice {
			mem.cpy(elem, new[pos..][..s.len], s.*)
			pos += s.len
		}

		return new
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

	init_slice := fn(items: []T): Self {
		return .(items, items.len)
	}

	ensure_total_capacity := fn(self: ^Self, scratch: ^Arena, total_cap: uint): void {
		if self.capacity < total_cap {
			new_cap := max(uint, total_cap, max(uint, self.capacity * 2, 8))
			self.items.ptr = scratch.grow(T, self.items.ptr[0..self.capacity], new_cap)
			self.capacity = new_cap
		}
	}

	resize := fn(self: ^Self, scratch: ^Arena, new_cap: uint): void {
		if self.capacity < new_cap {
			self.ensure_total_capacity(scratch, new_cap)
		}

		self.items.len = new_cap
	}

	push := fn(self: ^Self, scratch: ^Arena, item: T): void {
		self.ensure_total_capacity(scratch, self.items.len + 1)

		self.items.len += 1
		self.items[self.items.len - 1] = item
	}

	push_slice := fn(self: ^Self, scratch: ^Arena, slice: []T): void {
		self.ensure_total_capacity(scratch, self.items.len + slice.len)

		self.items.len += slice.len
		mem.cpy(T, self.items[self.items.len - slice.len..], slice)
	}
}

fmt := enum {
	printf := fn($tmpl: []u8, args: @Any()): void {
		_ = sys.write(1, tmpl)
	}

	display_int := fn(i: uint, buf: []u8): []u8 {
		if i == 0 {
			buf[0] = '0'
			return buf[..1]
		}

		idx := buf.len
		while i > 0 {
			idx -= 1
			buf[idx] = @int_cast('0' + i % 10)
			i /= 10
		}
		return buf[idx..]
	}
}

max := fn($T: type, a: T, b: T): T {
	if a > b return a else return b
}

mem := enum {
	eql := fn($elem: type, a: []elem, b: []elem): bool {
		if a.len != b.len return false
		for i := 0..a.len {
			if a[i] != b[i] return false
		}
		return true
	}

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

	TimeSpec := struct {
		.sec: i64;
		.nsec: i64;
	}

	Stat := struct {
		.dev: u64;
		.ino: u64;
		.mode: u32;
		.nlink: u32;
		.uid: u32;
		.gid: u32;
		._pad: u32 = 0;
		.rdev: u64;
		.size: i64;
		.blksize: i64;
		.blocks: i64;
		.atime: TimeSpec;
		.mtime: TimeSpec;
		.ctime: TimeSpec;
		.unused: [3]i64 = .[0, 0, 0];
	}

	StatError := enum(i32){
		.EACCES = 13;
		// Search permission denied for one of the directories in the path prefix
		.EBADF = 9;
		// Invalid file descriptor (when using fstatat with AT_EMPTY_PATH)
		.EFAULT = 14;
		// Stat buffer points to an invalid address
		.ELOOP = 40;
		// Too many symbolic links encountered while resolving the pathname
		.ENAMETOOLONG = 36;
		// Pathname is too long
		.ENOENT = 2;
		// A component of pathname does not exist or is a dangling symlink
		.ENOTDIR = 20;
		// A component of the path prefix is not a directory
		.EOVERFLOW = 75;
		// File size; number of blocks, or other value cannot be represented in stat structure
	}

	stat := fn(fd: i32, buf: ^Stat): Result(StatError) {
		return @syscall(5, fd, buf)
	}

	read := fn(fd: i32, buf: []u8): Result(StatError) {
		return @syscall(0, fd, buf)
	}

	Result := fn($err: type): type return struct {
		.value: i32

		Self := @CurrentScope()

		is_ok := fn(self: Self): bool {
			return self.value >= 0
		}

		is_err := fn(self: Self): bool {
			return self.value < 0
		}

		ok := fn(self: Self): ?u32 {
			if self.is_ok() {
				return @as(u32, @bit_cast(self.value))
			}
			return null
		}

		err := fn(self: Self): ?err {
			if self.is_err() {
				return @as(err, @bit_cast(-self.value))
			}
			return null
		}

		unwrap := fn(self: Self): i32 {
			debug.assert(self.is_ok())
			return self.value
		}

		unwrap_err := fn(self: Self): err {
			debug.assert(self.is_err())
			return @bit_cast(-self.value)
		}
	}

	// TODO: fix the formatter bug
	OpenatError := enum(i32){
		.ENOENT = 2;
		// File doesn’t exist
		.EACCES = 13;
		// Permission denied
		.ENOTDIR = 20;
		// A component of the path is not a directory
		.ELOOP = 40;
		// Too many symbolic links in path resolution
		.EMFILE = 24;
		// Process already has max number of file descriptors open
		.ENFILE = 23;
		// System-wide limit on file descriptors reached
		.EFAULT = 14;
		// Invalid memory address for filename pointer
	}

	OpenatFlags := struct {
		.vl: uint

		readonly := OpenatFlags.(0)
	}

	OpenatMode := struct {
		.vl: uint

		empty := OpenatMode.(0)
	}

	$at_fdcwd: i32 = -100

	openat := fn(dirfd: i32, path: ^u8, open_flags: OpenatFlags, mode: OpenatMode): Result(OpenatError) {
		return @syscall(257, dirfd, path, open_flags, mode)
	}

	WriteError := enum(i32){
		.EFAULT = 14;
		// Invalid memory address for filename pointer
	}

	write := fn(fd: i32, buf: []u8): Result(WriteError) {
		return @syscall(1, fd, buf)
	}

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

bull := enum {
	LazyPath := union(enum) {
		.src: []u8;
		.generated: ^GeneratedFile;
	}

	GeneratedFile := struct {
		.by: ^Step;
		.name: []u8;
		.path: ?[]u8 = null

		tmp_dir := "bs-build"

		path_id := 0

		init_path := fn(self: ^GeneratedFile, scratch: ^Arena): []u8 {
			buf: [10]u8 = idk
			id := fmt.display_int(path_id, buf[..])
			path_id += 1

			self.path = scratch.concat(u8, &.[tmp_dir, "/", self.name, ".", id])

			return self.path.?
		}
	}

	Command := struct {
		.step: Step = .{vtable: .init(Command)};
		.args: ArrayList(Arg) = .empty;
		.env: []Var = &.[]

		Arg := union(enum) {
			.bytes: []u8;
			.lazy_input: LazyPath;
			.lazy_output: LazyPath;
		}

		Var := struct{.name: []u8; .value: []u8}

		init := fn(scratch: ^Arena, cmd: []u8): ^Command {
			return scratch.spill(Command, .{args: .init_slice(scratch.dupe(Arg, &.[.{bytes: cmd}]))})
		}

		add_arg := fn(self: ^Command, scratch: ^Arena, arg: []u8): void {
			self.args.push(scratch, .{bytes: arg})
		}

		add_input_file_arg := fn(self: ^Command, scratch: ^Arena, file: LazyPath): void {
			match file {
				.generated => self.step.dependencies.push(scratch, file.generated.by),
				_ => {},
			}

			self.args.push(scratch, .{lazy_input: file})
		}

		add_file_output_arg := fn(self: ^Command, scratch: ^Arena, name: []u8): LazyPath {
			gf := scratch.create(GeneratedFile)
			gf.* = .{by: &self.step, name: name}
			self.args.push(scratch, .{lazy_output: .{generated: gf}})
			return .{generated: gf}
		}

		execute := fn(step: ^Step, scratch: ^Arena): ?Step.Hash {
			self: ^Command = @parent_ptr("step", step)

			tmp := Arena.scratch(scratch)
			defer tmp.pop()

			args := tmp.arena.alloc(?^u8, self.args.items.len + 1)

			exe_path := sys.resolve_exe_path(self.args.items[0].bytes, tmp.arena) || return null
			args[0] = tmp.arena.dupe_z(exe_path)

			for slot := args[1..args.len - 1], arg := self.args.items[1..] {
				res: []u8 = idk
				match arg.* {
					.bytes => res = arg.bytes,
					.lazy_input => match arg.lazy_input {
						.src => res = arg.lazy_input.src,
						.generated => res = arg.lazy_input.generated.path.?,
					},
					.lazy_output => match arg.lazy_output {
						.src => res = arg.lazy_output.src,
						.generated => res = arg.lazy_output.generated.init_path(scratch),
					},
				}
				slot.* = tmp.arena.dupe_z(res)
			}
			args[args.len - 1] = null

			env := tmp.arena.alloc(?^u8, self.env.len + 1)

			for slot := env[..env.len - 1], var := self.env {
				buf := tmp.arena.alloc(u8, var.name.len + 1 + var.value.len + 1)
				mem.cpy(u8, buf[..var.name.len], var.name)
				buf[var.name.len] = '='
				mem.cpy(u8, buf[var.name.len + 1..][..var.value.len], var.value)
				buf[var.name.len + 1 + var.value.len] = 0
				slot.* = buf.ptr
			}
			env[env.len - 1] = null

			result := sys.fork()
			if result < 0 {
				return null
			}

			if result == 0 {
				if sys.execve(args[0].?, args.ptr, sys.env) != 0 {}
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
		.has_side_effects: bool = false;
		.seen: bool = false

		Hash := [16]u8

		Vtable := struct{.execute: ^fn(self: ^Step, scratch: ^Arena): ?Hash $init := fn($T: type): ^Vtable {
			return &struct {
				vt := Vtable.(&T.execute)
			}.vt
		}}

		execute := fn(self: ^Step, scratch: ^Arena): ?Hash {
			return self.vtable.execute(self, scratch)
		}

		collect := fn(root: ^Step, scratch: ^Arena, exec_order: ^ArrayList(^Step)): void {
			if root.seen return root.seen = true

			for dep := root.dependencies.items {
				collect(dep.*, scratch, exec_order)
			}

			exec_order.push(scratch, root)
		}

		run := fn(self: ^Step): void {
			tmp := Arena.scratch(null)
			defer tmp.pop()

			exec_order := ArrayList(^Step).empty
			self.collect(tmp.arena, &exec_order)

			for step := exec_order.items {
				_ = step.*.execute(tmp.arena)
			}
		}
	}
}
