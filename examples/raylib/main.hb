init_window := fn(width: uint, height: uint, title: ^u8): void @import("InitWindow")
close_window := fn(): void @import("CloseWindow")
begin_drawing := fn(): void @import("BeginDrawing")
end_drawing := fn(): void @import("EndDrawing")
clear_background := fn(color: Color): void @import("ClearBackground")
draw_rectandle_v := fn(pos: V2, size: V2, color: Color): void @import("DrawRectangleV")
window_should_close := fn(): bool @import("WindowShouldClose")
get_frame_time := fn(): f32 @import("GetFrameTime")
get_mouse_position := fn(): V2 @import("GetMousePosition")
get_screen_width := fn(): int @import("GetScreenWidth")
get_screen_height := fn(): int @import("GetScreenHeight")
is_key_pressed := fn(key: u8): bool @import("IsKeyPressed")
is_key_down := fn(key: u8): bool @import("IsKeyDown")
set_random_seed := fn(seed: uint): void @import("SetRandomSeed")
get_random_value := fn(min: int, max: int): int @import("GetRandomValue")

V2 := struct {
	.x: f32;
	.y: f32

	$zero := V2.(0.0, 0.0)

	$xy := fn(value: f32): V2 {
		return V2.(value, value)
	}

	len := fn(self: V2): f32 @import("Vector2Length")
	norm := fn(self: V2): V2 @import("Vector2Normalize")
}
Color := [4]u8

Enemy := struct {
	.pos: V2;
	.dir: V2;
}

Bullet := struct {
	.pos: V2;
	.dir: V2;
	.life: f32;
}

$background := u8.[20, 20, 20, 255]
$square := u8.[200, 200, 200, 255]
$damage := 10.0
$enemy_size := 15.0
$player_speed := 500.0
$bullet_speed := 1000.0

player_size: f32 = idk
player_pos: V2 = idk
reload_time: f32 = 0.0

enemyes: [1024]Enemy = idk
enemy_count: uint = idk

bullets: [1024]Bullet = idk
bullet_count: uint = idk

round: int = idk

main := fn(): uint {
	init_window(800, 600, "hblang\0".ptr)
	defer close_window()

	create_enemy := fn(pos: V2, dir: V2): void {
		enemyes[enemy_count] = .(pos, dir)
		enemy_count += 1
	}

	delete_enemy := fn(index: uint): void {
		enemyes[index] = enemyes[enemy_count - 1]
		enemy_count -= 1
	}

	create_bullet := fn(pos: V2, dir: V2): void {
		bullets[bullet_count] = .(pos, dir, 1.0)
		bullet_count += 1
	}

	delete_bullet := fn(index: uint): void {
		bullets[index] = bullets[bullet_count - 1]
		bullet_count -= 1
	}

	init_world := fn(size: V2): void {
		enemy_count = 0
		bullet_count = 0
		round = 0

		create_enemy(.(100.0, 100.0), .(100.0, 0.0))

		player_size = 30.0
		player_pos = size * .xy(0.5)
	}

	screen_size := V2.(
		@int_to_float(get_screen_width()),
		@int_to_float(get_screen_height()),
	)

	init_world(screen_size)

	while:game !window_should_close() {
		begin_drawing()
		defer end_drawing()

		clear_background(background)

		draw_rectandle_v(player_pos - .xy(player_size * 0.5), .xy(player_size), square)

		{
			dir := V2.zero
			if is_key_down('W') dir.y -= 1.0
			if is_key_down('S') dir.y += 1.0
			if is_key_down('A') dir.x -= 1.0
			if is_key_down('D') dir.x += 1.0
			dir = dir.norm()

			player_pos += dir * .xy(player_speed) * .xy(get_frame_time())

			dir = V2.zero
			if is_key_down('U') dir.y -= 1.0
			if is_key_down('J') dir.y += 1.0
			if is_key_down('H') dir.x -= 1.0
			if is_key_down('K') dir.x += 1.0
			dir = dir.norm()

			if reload_time <= 0.0 & dir != V2.zero {
				reload_time = 0.5
				create_bullet(player_pos, dir * .xy(player_speed * 2.0))
			}

			reload_time -= get_frame_time()
		}

		wrap_vec := fn(vec: V2, by: V2): V2 {
			if vec.x < 0.0 vec.x += by.x
			if vec.x > by.x vec.x -= by.x
			if vec.y < 0.0 vec.y += by.y
			if vec.y > by.y vec.y -= by.y
			return vec
		}

		intersects := fn(a_center: V2, a_size: f32, b_center: V2, b_size: f32): bool {
			a_size *= 0.5
			b_size *= 0.5
			return a_center.x - a_size < b_center.x + b_size &
				a_center.x + a_size > b_center.x - b_size &
				a_center.y - a_size < b_center.y + b_size &
				a_center.y + a_size > b_center.y - b_size
		}

		player_pos = wrap_vec(player_pos, screen_size)

		for enemy := enemyes[..enemy_count] {
			draw_rectandle_v(enemy.pos - .xy(enemy_size * 0.5), .xy(enemy_size), square)
			enemy.pos += enemy.dir * .xy(get_frame_time())
			enemy.pos = wrap_vec(enemy.pos, screen_size)

			if intersects(enemy.pos, enemy_size, player_pos, player_size) {
				player_size -= $damage
				if player_size == 0.0 init_world(screen_size)
				player_pos += (player_pos - enemy.pos).norm() * .xy(player_size * 2.0)
			}
		}

		for i := 0.., bullet := bullets[..bullet_count] {
			draw_rectandle_v(bullet.pos - .xy(player_size * 0.25), .xy(player_size * 0.5), square)
			bullet.pos += bullet.dir * .xy(get_frame_time())
			bullet.pos = wrap_vec(bullet.pos, screen_size)
			bullet.life -= get_frame_time()
			if bullet.life <= 0.0 delete_bullet(i)

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
				pos: V2 = .xy(@int_to_float(get_random_value(0, get_screen_width())))
				vel: V2 = .xy(@int_to_float(get_random_value(100, base_enemy_speed)))

				if i % 4 == 0 {
					pos.x = 0.0
				} else if i % 4 == 1 {
					pos.x = screen_size.x
				} else if i % 4 == 2 {
					pos.y = 0.0
				} else {
					pos.y = screen_size.y
				}

				if i % 2 == 0 {
					vel = vel * .(-1.0, -1.0)
				}

				create_enemy(pos, vel)
			}
		}
	}

	return 0
}
