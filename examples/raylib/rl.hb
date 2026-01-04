init_window := fn(width: uint, height: uint, title: ^u8): void @import("InitWindow")
close_window := fn(): void @import("CloseWindow")
begin_drawing := fn(): void @import("BeginDrawing")
end_drawing := fn(): void @import("EndDrawing")
clear_background := fn(color: Color): void @import("ClearBackground")
draw_rectangle_v := fn(pos: V2, size: V2, color: Color): void @import("DrawRectangleV")
window_should_close := fn(): bool @import("WindowShouldClose")
get_frame_time := fn(): f32 @import("GetFrameTime")
get_mouse_position := fn(): V2 @import("GetMousePosition")
get_screen_width := fn(): int @import("GetScreenWidth")
get_screen_height := fn(): int @import("GetScreenHeight")
is_key_pressed := fn(key: u8): bool @import("IsKeyPressed")
is_key_down := fn(key: u8): bool @import("IsKeyDown")
set_random_seed := fn(seed: uint): void @import("SetRandomSeed")
get_random_value := fn(min: int, max: int): int @import("GetRandomValue")
set_config_flags := fn(flags: ConfigFlags): void @import("SetConfigFlags")
set_target_fps := fn(fps: uint): void @import("SetTargetFPS")

ConfigFlags := struct {
	.bits: uint

	// Set to try enabling V-Sync on GPU
	VSYNC_HINT := ConfigFlags.(0x00000040)
	// Set to run program in fullscreen
	FULLSCREEN_MODE := ConfigFlags.(0x00000002)
	// Set to allow resizable window
	WINDOW_RESIZABLE := ConfigFlags.(0x00000004)
	// Set to disable window decoration (frame and buttons)
	WINDOW_UNDECORATED := ConfigFlags.(0x00000008)
	// Set to hide window
	WINDOW_HIDDEN := ConfigFlags.(0x00000080)
	// Set to minimize window (iconify)
	WINDOW_MINIMIZED := ConfigFlags.(0x00000200)
	// Set to maximize window (expanded to monitor)
	WINDOW_MAXIMIZED := ConfigFlags.(0x00000400)
	// Set to window non focused
	WINDOW_UNFOCUSED := ConfigFlags.(0x00000800)
	// Set to window always on top
	WINDOW_TOPMOST := ConfigFlags.(0x00001000)
	// Set to allow windows running while minimized
	WINDOW_ALWAYS_RUN := ConfigFlags.(0x00000100)
	// Set to allow transparent framebuffer
	WINDOW_TRANSPARENT := ConfigFlags.(0x00000010)
	// Set to support HighDPI
	WINDOW_HIGHDPI := ConfigFlags.(0x00002000)
	// Set to support mouse passthrough, only supported when WINDOW_UNDECORATED
	WINDOW_MOUSE_PASSTHROUGH := ConfigFlags.(0x00004000)
	// Set to run program in borderless windowed mode
	BORDERLESS_WINDOWED_MODE := ConfigFlags.(0x00008000)
	// Set to try enabling MSAA 4X
	MSAA_4X_HINT := ConfigFlags.(0x00000020)
	// Set to try enabling interlaced video format (for V3D)
	INTERLACED_HINT := ConfigFlags.(0x00010000)
}

draw_text := fn(text: ^u8, pos_x: int, pos_y: int, font_size: int, color: Color): void @import("DrawText")
draw_fps := fn(pos_x: int, pos_y: int): void @import("DrawFPS")

$WHITE := u8.[255, 255, 255, 255]
$BLACK := u8.[0, 0, 0, 255]
$LIGHTGRAY := u8.[200, 200, 200, 255]

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
