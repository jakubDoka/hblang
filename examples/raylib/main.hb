init_window := fn(width: uint, height: uint, title: ^u8): void @import("InitWindow")
close_window := fn(): void @import("CloseWindow")
begin_drawing := fn(): void @import("BeginDrawing")
end_drawing := fn(): void @import("EndDrawing")
clear_background := fn(color: Color): void @import("ClearBackground")
draw_rectandle_v := fn(pos: V2, size: V2, color: Color): void @import("DrawRectangleV")
window_should_close := fn(): bool @import("WindowShouldClose")
get_frame_time := fn(): f32 @import("GetFrameTime")

V2 := struct{.x: f32; .y: f32}
Color := [4]u8

$background := u8.[255, 0, 0, 255]
$square := u8.[255, 255, 255, 255]
fls := false

main := fn(): uint {
	init_window(800, 600, "hblang\0".ptr)
	defer close_window()

	pos := V2.(0.0, 0.0)
	vel := V2.(200.0, 200.0)
	while !window_should_close() {
		begin_drawing()
		defer end_drawing()

		clear_background(background)

		draw_rectandle_v(pos, .(100.0, 100.0), square)

		next_pos := pos + vel * .(get_frame_time(), get_frame_time())

		if next_pos.x + 100.0 > 800.0 || next_pos.x < 0.0 {
			vel.x = -vel.x
			continue
		}
		if next_pos.y + 100.0 > 600.0 || next_pos.y < 0.0 {
			vel.y = -vel.y
			continue
		}

		pos = next_pos
	}

	return 0
}
