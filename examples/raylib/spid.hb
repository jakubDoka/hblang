rl := @use("rl.hb")

Enemy := struct {
	.pos: rl.V2;
	.dir: rl.V2;
}

Bullet := struct {
	.pos: rl.V2;
	.dir: rl.V2;
	.life: f32;
}

$background := u8.[20, 20, 20, 255]
$square := u8.[200, 200, 200, 255]
$damage := 10.0
$enemy_size := 15.0
$player_speed := 500.0
$bullet_speed := 1000.0

player_size: f32 = idk
player_pos: rl.V2 = idk
reload_time: f32 = 0.0

enemyes: [1024]Enemy = idk
enemy_count: uint = idk

bullets: [1024]Bullet = idk
bullet_count: uint = idk

round: int = idk

main := fn(): uint {
	rl.init_window(800, 600, "hblang\0".ptr)
	defer rl.close_window()

	$create_enemy := fn(pos: rl.V2, dir: rl.V2): void {
		enemyes[enemy_count] = .(pos, dir)
		enemy_count += 1
	}

	$delete_enemy := fn(index: uint): void {
		enemyes[index] = enemyes[enemy_count - 1]
		enemy_count -= 1
	}

	$create_bullet := fn(pos: rl.V2, dir: rl.V2): void {
		bullets[bullet_count] = .(pos, dir, 1.0)
		bullet_count += 1
	}

	$delete_bullet := fn(index: uint): void {
		bullets[index] = bullets[bullet_count - 1]
		bullet_count -= 1
	}

	$init_world := fn(size: rl.V2): void {
		enemy_count = 0
		bullet_count = 0
		round = 0

		create_enemy(.(100.0, 100.0), .(100.0, 0.0))

		player_size = 30.0
		player_pos = size * .xy(0.5)
	}

	screen_size := rl.V2.(
		@int_to_float(rl.get_screen_width()),
		@int_to_float(rl.get_screen_height()),
	)

	init_world(screen_size)

	while:game !rl.window_should_close() {
		rl.begin_drawing()
		defer rl.end_drawing()

		rl.clear_background(background)

		rl.draw_rectangle_v(player_pos - .xy(player_size * 0.5), .xy(player_size), square)

		{
			dir := rl.V2.zero
			if rl.is_key_down('W') dir.y -= 1.0
			if rl.is_key_down('S') dir.y += 1.0
			if rl.is_key_down('A') dir.x -= 1.0
			if rl.is_key_down('D') dir.x += 1.0
			dir = dir.norm()

			player_pos += dir * .xy(player_speed) * .xy(rl.get_frame_time())

			dir = rl.V2.zero
			if rl.is_key_down('U') dir.y -= 1.0
			if rl.is_key_down('J') dir.y += 1.0
			if rl.is_key_down('H') dir.x -= 1.0
			if rl.is_key_down('K') dir.x += 1.0
			dir = dir.norm()

			if reload_time <= 0.0 & dir != rl.V2.zero {
				reload_time = 0.5
				create_bullet(player_pos, dir * .xy(player_speed * 2.0))
			}

			reload_time -= rl.get_frame_time()
		}

		$wrap_vec := fn(vec: rl.V2, by: rl.V2): rl.V2 {
			if vec.x < 0.0 vec.x += by.x
			if vec.x > by.x vec.x -= by.x
			if vec.y < 0.0 vec.y += by.y
			if vec.y > by.y vec.y -= by.y
			return vec
		}

		$intersects := fn(a_center: rl.V2, a_size: f32, b_center: rl.V2, b_size: f32): bool {
			a_size *= 0.5
			b_size *= 0.5
			return a_center.x - a_size < b_center.x + b_size &
				a_center.x + a_size > b_center.x - b_size &
				a_center.y - a_size < b_center.y + b_size &
				a_center.y + a_size > b_center.y - b_size
		}

		player_pos = wrap_vec(player_pos, screen_size)

		for enemy := enemyes[..enemy_count] {
			rl.draw_rectangle_v(enemy.pos - .xy(enemy_size * 0.5), .xy(enemy_size), square)
			enemy.pos += enemy.dir * .xy(rl.get_frame_time())
			enemy.pos = wrap_vec(enemy.pos, screen_size)

			if intersects(enemy.pos, enemy_size, player_pos, player_size) {
				player_size -= $damage
				if player_size == 0 init_world(screen_size)
				player_pos += (player_pos - enemy.pos).norm() * .xy(player_size * 2.0)
			}
		}

		for i := 0.., bullet := bullets[..bullet_count] {
			rl.draw_rectangle_v(bullet.pos - .xy(player_size * 0.25), .xy(player_size * 0.5), square)
			bullet.pos += bullet.dir * .xy(rl.get_frame_time())
			bullet.pos = wrap_vec(bullet.pos, screen_size)
			bullet.life -= rl.get_frame_time()
			if bullet.life <= 0 delete_bullet(i)

			for j := 0.., enemy := enemyes[..enemy_count] {
				if intersects(bullet.pos, player_size * 0.5, enemy.pos, enemy_size) {
					delete_bullet(i)
					delete_enemy(j)
				}
			}
		}

		if enemy_count == 0 {
			round += 1
			base_enemy_speed := round * 10
			for i := 0..@bit_cast(round) {
				pos: rl.V2 = .xy(@int_to_float(rl.get_random_value(0, rl.get_screen_width())))
				vel: rl.V2 = .xy(@int_to_float(rl.get_random_value(100, base_enemy_speed)))

				if i % 4 == 0 {
					pos.x = 0
				} else if i % 4 == 1 {
					pos.x = screen_size.x
				} else if i % 4 == 2 {
					pos.y = 0
				} else {
					pos.y = screen_size.y
				}

				if i % 2 == 0 {
					vel *= .(-1, -1)
				}

				create_enemy(pos, vel)
			}
		}
	}

	return 0
}
