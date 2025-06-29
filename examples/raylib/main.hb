init_window := fn(width: uint, height: uint, title: ^u8): void @import("InitWindow")
close_window := fn(): void @import("CloseWindow")
begin_drawing := fn(): void @import("BeginDrawing")
end_drawing := fn(): void @import("EndDrawing")
clear_background := fn(color: Color): void @import("ClearBackground")
draw_rectandle_v := fn(pos: V2, size: V2, color: Color): void @import("DrawRectangleV")
window_should_close := fn(): bool @import("WindowShouldClose")

V2 := struct{.x: f32; .y: f32}
Color := [4]u8

main := fn(): uint {
	init_window(800, 600, "hblang\0".ptr)
	defer close_window()

	//pos := V2.(0.0, 0.0)
	//vel := V2.(1.0, 1.0)
	while !window_should_close() {
		begin_drawing()
		defer end_drawing()

		clear_background(.[255, 0, 0, 255])

		//draw_rectandle_v(pos, .(100.0, 100.0), .[255, 0, 0, 255])

		//pos += vel
	}

	return 0
}
