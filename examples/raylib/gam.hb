rl := @use("rl.hb")
utils := @use("../hb-basic/lib.hb")

Stats := struct {
	.max_health: u16 = 0;
	.speed: f32 = 0;
	// TODO: pudding a default function pointer here makes the compiler hang
	.ai: ^(fn(self: ^Ent): void) = &fn(self: ^Ent): void {};
}

Ent := struct {
	.id: Id;
	.pos: rl.V2 = .(0, 0);
	.vel: rl.V2 = .(0, 0);
	.size: f32 = 32;
	.color: rl.Color = rl.WHITE;
	.free: ?^Ent = null;
	.health: u16 = 0;
	.stats: ^Stats = idk

	Id := struct {
		.index: u32;
		.generation: u32;
	}

	is_alive := fn(self: ^Ent): bool {
		return self.id.generation % 2 == 0
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
		ent := self.slots[id.index]
		if ent.id.generation != id.generation return null
		return ent
	}

	add := fn(self: ^Sim): ?^Ent {
		slot := self.free || return null
		slot.id.generation += 1
		self.free = slot.free
		return slot
	}

	remove := fn(self: ^Sim, id: Ent.Id): void {
		ent := self.get(id) || return;

		ent.id.generation += 1
		ent.free = self.free
		self.free = ent
	}
}

main := fn(): uint {
	rl.set_config_flags(.WINDOW_RESIZABLE)
	rl.init_window(800, 600, "gam\0".ptr)
	rl.set_target_fps(60)

	root_arena := utils.Arena.init(1024 * 1024)

	sim := Sim.init(&root_arena)

	player_stats := Stats.{
		max_health: 100,
		speed: 400,
	}

	player := sim.add() || die
	player.stats = &player_stats

	charge := 0.0

	player.pos = .(100, 100)

	while:game !rl.window_should_close() {
		rl.begin_drawing()

		rl.clear_background(rl.BLACK)
		rl.draw_fps(10, 10)

		delta := rl.get_frame_time()
		screen_size := rl.V2.(
			@int_to_float(rl.get_screen_width()),
			@int_to_float(rl.get_screen_height()),
		)
		padding := 50.0

		if rl.is_key_down('A') player.pos.x -= player.stats.speed * delta
		if rl.is_key_down('D') player.pos.x += player.stats.speed * delta

		if player.pos.x < padding {
			player.pos.x = padding
		}
		if player.pos.x > screen_size.x - padding {
			player.pos.x = screen_size.x - padding
		}

		player.pos.y = screen_size.y - padding

		for ent := sim.slots {
			if !ent.is_alive() continue

			ent.stats.ai(ent)

			rl.draw_rectangle_v(
				ent.pos - .xy(ent.size / 2),
				.xy(ent.size),
				rl.WHITE,
			)
		}

		rl.end_drawing()
	}

	return 0
}
