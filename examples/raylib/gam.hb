rl := @use("rl.hb")
utils := @use("../hb-basic/lib.hb")

grv := rl.get_random_value

Stats := struct {
	.max_health: u16 = 0;
	.speed: f32 = 0;
	.friction: f32 = 0;
	.size: f32 = 32;
	.ai: ^(fn(self: ^Ent): void) = &fn(self: ^Ent): void {};
}

Ent := struct {
	.id: Id;
	.pos: rl.V2 = .(0, 0);
	.vel: rl.V2 = .(0, 0);
	.color: rl.Color = rl.WHITE;
	.free: ?^Ent = null;
	.damage_taken: u16 = 0;
	.stats: ^Stats = idk;
	.timer: f32 = 0.0

	Id := struct {
		.index: u32;
		.generation: u32;
	}

	is_alive := fn(self: ^Ent): bool {
		return self.id.generation % 2 == 0
	}

	rect := fn(self: ^Ent): rl.Rect {
		return .{
			x: self.pos.x - self.stats.size / 2,
			y: self.pos.y - self.stats.size / 2,
			width: self.stats.size,
			height: self.stats.size,
		}
	}
}

Sim := struct {
	.slots: []Ent;
	.free: ?^Ent

	init := fn(scratch: ^utils.Arena): Sim {
		ents := scratch.alloc(Ent, 256)
		free_ent: ?^Ent = null

		for i := 0.., ent := ents {
			ent.* = .{
				free: free_ent,
				id: .{index: @int_cast(i), generation: 1},
			}
			free_ent = ent
		}

		return .(ents, free_ent)
	}

	get := fn(self: ^Sim, id: Ent.Id): ?^Ent {
		ent := &self.slots[id.index]
		if ent.id.generation != id.generation return null
		return ent
	}

	add := fn(self: ^Sim): ?^Ent {
		slot := self.free || return null
		self.free = slot.free
		slot.* = .{id: slot.id}
		slot.id.generation += 1
		return slot
	}

	remove := fn(self: ^Sim, id: Ent.Id): void {
		ent := self.get(id) || return;

		utils.debug.assert(ent.is_alive())

		ent.id.generation += 1
		ent.free = self.free
		self.free = ent
	}

	iter := fn(self: ^Sim): struct {
		.slots: []Ent

		next := fn(slf: ^@CurrentScope()): ?^Ent {
			loop {
				if slf.slots.len == 0 return null
				ent := &slf.slots[0]
				slf.slots = slf.slots[1..]
				if ent.is_alive() return ent
			}
		}
	} return .(self.slots)
}

$bounce := fn(ent: ^Ent): void {
	clamp := padding
	if ent.pos.x < clamp {
		ent.pos.x = clamp
		ent.vel.x *= -1
	}
	if ent.pos.x > console_width - clamp {
		ent.pos.x = console_width - clamp
		ent.vel.x *= -1
	}
}

$console_width := 600.0
$console_height := 900.0
$padding := 50.0

crash := fn(ent: ^Ent): void {
	if ent.pos.y > console_height - padding ||
		ent.pos.y < padding {
		sim.remove(ent.id)
	}
}

player_stats := Stats.{
	max_health: 100,
	speed: 3000,
	friction: 3,
	ai: &fn(player: ^Ent): void {
		delta := rl.get_frame_time()

		if rl.is_key_down('A') player.vel.x -= player.stats.speed * delta
		if rl.is_key_down('D') player.vel.x += player.stats.speed * delta

		bounce(player)

		player.pos.y = console_height - padding

		iter := sim.iter()
		while ent := iter.next() {
			if ent == player continue
			if rl.check_collision_recs(ent.rect(), player.rect()) {
				if ent.vel.y > 0 {
					ent.vel.y *= -1
				}
			}
		}
	},
}

simpleton_stats := Stats.{
	max_health: 10,
	speed: 100,
	ai: &fn(simpleton: ^Ent): void {
		bounce(simpleton)
		crash(simpleton)
	},
}

blaster_stats := Stats.{
	max_health: 30,
	speed: 100,
	size: 40,
	friction: 1,
	ai: &fn(blaster: ^Ent): void {
		bounce(blaster)
		crash(blaster)

		delta := rl.get_frame_time()

		boost_time := 2.0
		shoot_time := 1.0
		shots := 2

		if blaster.timer < boost_time {
			blaster.vel.y += blaster.stats.speed * delta
		} else if blaster.timer < boost_time + shoot_time {
			cursor := boost_time
			for i := 0..shots {
				if blaster.timer < cursor &&
					blaster.timer + delta >= cursor {
					simpleton := sim.add() || break
					simpleton.stats = &simpleton_stats
					simpleton.pos = blaster.pos
					simpleton.vel = .(0, 100)
				}

				cursor += shoot_time / @int_to_float(@int_cast(shots))
			}
		} else {
			blaster.timer = 0.0
		}

		register_hits(blaster)
	},
}

behemoth_stats := Stats.{
	max_health: 100,
	speed: 100,
	size: 100,
	ai: &fn(behemoth: ^Ent): void {
		crash(behemoth)

		delta := rl.get_frame_time()

		if behemoth.timer > 2.0 {
			behemoth.timer = 0.0

			dirs := f32.[0.5, -0.5, 0.7, -0.7]
			utils.fmt.printf("dirs: %\n", .(dirs[0]))
			for d := dirs[..] {
				dir := rl.V2.(1, 1) * .xy(200)

				ent := sim.add() || break
				ent.stats = &simpleton_stats
				ent.pos = behemoth.pos
				ent.vel = dir
			}
		}
	},
}

register_hits := fn(blaster: ^Ent): void {
	iter := sim.iter()
	while ent := iter.next() {
		if ent == blaster continue
		if ent.vel.y < 0 &&
			rl.check_collision_recs(blaster.rect(), ent.rect()) {
			sim.remove(ent.id)
			blaster.damage_taken += ent.stats.max_health
			if blaster.damage_taken >= blaster.stats.max_health {
				sim.remove(blaster.id)
				break
			}
		}
	}
}

sim: Sim = idk
player_id: Ent.Id = idk

main := fn(): uint {
	rl.set_config_flags(.WINDOW_RESIZABLE)
	rl.init_window(800, 600, "gam\0".ptr)
	rl.set_target_fps(60)

	root_arena := utils.Arena.init(1024 * 1024)
	sim = Sim.init(&root_arena)

	player := sim.add() || die
	player.stats = &player_stats
	player.pos = .(console_width / 2, 0)

	player_id = player.id

	spawn_period := 1.0
	blaster_period := 3.0
	behemoth_period := 5.0
	spawn_timer := 0.0
	blaster_timer := 0.0
	behemoth_timer := 0.0

	while:game !rl.window_should_close() {
		rl.begin_drawing()

		screen_size := rl.V2.(
			@int_to_float(rl.get_screen_width()),
			@int_to_float(rl.get_screen_height()),
		)

		origin := (screen_size - .(console_width, console_height)) / .xy(2)

		rl.clear_background(rl.BLACK)
		rl.draw_rectangle_lines_ex(
			.(origin.x, origin.y, console_width, console_height),
			1,
			rl.LIGHTGRAY,
		)
		rl.draw_fps(10, 10)

		delta := rl.get_frame_time()

		spawn_timer += delta
		if spawn_timer >= spawn_period loop:spawn {
			spawn_timer = 0

			simpleton := sim.add() || break:spawn
			simpleton.stats = &simpleton_stats
			simpleton.pos = .(
				@int_to_float(grv(
					@float_to_int(padding),
					@float_to_int(console_width - padding),
				)),
				padding,
			)
			simpleton.vel = .(0, 300)

			break:spawn
		}

		blaster_timer += delta
		if blaster_timer >= blaster_period loop:spawn {
			blaster_timer = 0

			blaster := sim.add() || break:spawn
			blaster.stats = &blaster_stats
			blaster.pos = .(
				@int_to_float(grv(
					@float_to_int(padding),
					@float_to_int(console_width - padding),
				)),
				padding,
			)

			break:spawn
		}

		behemoth_timer += delta
		if behemoth_timer >= behemoth_period loop:spawn {
			behemoth_timer = 0

			behemoth := sim.add() || break:spawn
			behemoth.stats = &behemoth_stats
			behemoth.pos = .(
				@int_to_float(grv(
					@float_to_int(padding),
					@float_to_int(console_width - padding),
				)),
				padding,
			)
			behemoth.vel = .(0, 70)

			break:spawn
		}

		iter := sim.iter()
		while ent := iter.next() {
			ent.stats.ai(ent)

			ent.timer += delta

			ent.pos += ent.vel * .xy(delta)
			ent.vel *= .xy(1 - ent.stats.friction * delta)

			health_perc: f32 = @int_to_float(ent.damage_taken) /
				@int_to_float(ent.stats.max_health)

			rl.draw_rectangle_v(
				origin + ent.pos - .xy(ent.stats.size / 2),
				.xy(ent.stats.size),
				rl.color_alpha(rl.WHITE, 1.0 - health_perc),
			)
		}

		rl.end_drawing()
	}

	return 0
}
