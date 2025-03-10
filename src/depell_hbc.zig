const hb = @import("root.zig");

export fn compile(ptr: [*c]u8, len: usize) usize {
    const source = ptr[0..len :0];

    var lexer = hb.Lexer.init(source, 0);
    var count: usize = 1;
    while (lexer.next().kind != .Eof) count += 1;
    return count;
}
