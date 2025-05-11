const std = @import("std");

pub fn printDiff(
    a: []const u8,
    b: []const u8,
    arena: std.mem.Allocator,
    out: std.io.AnyWriter,
    color: std.io.tty.Config,
) !void {
    const linesA = try splitLines(arena, a);
    const linesB = try splitLines(arena, b);
    const lcs = try lcsLines(a, b, arena);

    var i: usize = 0;
    var j: usize = 0;
    var k: usize = 0;

    while (i < linesA.len or j < linesB.len) {
        if (k < lcs.len and i < linesA.len and j < linesB.len and
            std.mem.eql(u8, linesA[i], lcs[k]) and
            std.mem.eql(u8, linesB[j], lcs[k]))
        {
            try out.print(" {s}\n", .{linesA[i]});
            i += 1;
            j += 1;
            k += 1;
        } else if (j < linesB.len and (k >= lcs.len or !std.mem.eql(u8, linesB[j], lcs[k]))) {
            try color.setColor(out, .green);
            try out.print("+{s}\n", .{linesB[j]});
            try color.setColor(out, .reset);
            j += 1;
        } else if (i < linesA.len and (k >= lcs.len or !std.mem.eql(u8, linesA[i], lcs[k]))) {
            try color.setColor(out, .red);
            try out.print("-{s}\n", .{linesA[i]});
            try color.setColor(out, .reset);
            i += 1;
        } else unreachable;
    }
}

fn lcsLines(a: []const u8, b: []const u8, arena: std.mem.Allocator) ![][]const u8 {
    const linesA = try splitLines(arena, a);
    const linesB = try splitLines(arena, b);

    const lenA = linesA.len;
    const lenB = linesB.len;

    var dp = try arena.alloc([]usize, lenA + 1);
    for (dp) |*row| {
        row.* = try arena.alloc(usize, lenB + 1);
        @memset(row.*, 0);
    }

    for (linesA, 0..) |lineA, i| {
        for (linesB, 0..) |lineB, j| {
            if (std.mem.eql(u8, lineA, lineB)) {
                dp[i + 1][j + 1] = dp[i][j] + 1;
            } else {
                dp[i + 1][j + 1] = @max(dp[i + 1][j], dp[i][j + 1]);
            }
        }
    }

    var result = try arena.alloc([]const u8, dp[lenA][lenB]);
    var i = lenA;
    var j = lenB;
    var k: usize = dp[lenA][lenB];

    while (i > 0 and j > 0) {
        if (std.mem.eql(u8, linesA[i - 1], linesB[j - 1])) {
            k -= 1;
            result[k] = linesA[i - 1];
            i -= 1;
            j -= 1;
        } else if (dp[i - 1][j] >= dp[i][j - 1]) {
            i -= 1;
        } else {
            j -= 1;
        }
    }

    return result;
}

fn splitLines(allocator: std.mem.Allocator, input: []const u8) ![][]const u8 {
    var list = std.ArrayList([]const u8).init(allocator);
    var it = std.mem.tokenizeAny(u8, input, "\n");
    while (it.next()) |line| {
        try list.append(line);
    }
    return list.toOwnedSlice();
}
