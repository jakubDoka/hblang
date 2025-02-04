files: []const Ast = &.{},
errors: std.ArrayListUnmanaged(u8) = .{},
output: std.ArrayListUnmanaged(u8) = .{},

const std = @import("std");
const Ast = @import("parser.zig");
const Codegen = @This();

pub fn init(gpa: std.mem.Allocator) !Codegen {
    _ = gpa; // autofix
    return .{};
}

pub fn deinit(self: *Codegen) void {
    _ = self; // autofix
}

pub fn generate(self: *Codegen) !void {
    _ = self; // autofix
    unreachable;
}
