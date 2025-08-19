const graph = @import("graph.zig");
const utils = graph.utils;
const std = @import("std");

pub fn Mixin(comptime Backend: type) type {
    return struct {
        const Func = graph.Func(Backend);
        const Self = @This();
        const Node = Func.Node;

        const Set = std.DynamicBitSetUnmanaged;
        const Arry = std.ArrayListUnmanaged;

        pub fn getGraph(self: *Self) *Func {
            return @alignCast(@fieldParentPtr("alias_anal", self));
        }

        pub const BBState = struct {
            Fork: ?struct { saved: []*Node } = null,
            Join: ?struct {} = null,
        };

        pub fn run(alias: *Self) void {
            errdefer unreachable;

            const self = alias.getGraph();
            self.gcm.cfg_built.assertUnlocked();

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var visited = try Set.initEmpty(tmp.arena.allocator(), self.next_id);
            const postorder = self.collectDfs(tmp.arena.allocator(), &visited)[1..];

            const states = tmp.arena.alloc(BBState, postorder.len);
            @memset(states, .{});

            var threads = Arry(*Node){};

            if (self.start.outputs().len < 1 or
                self.start.outputs()[1].get().kind != .Mem) return;

            const root_mem = self.start.outputs()[1].get();
            try threads.append(tmp.arena.allocator(), root_mem);

            for (postorder) |bbc| {
                const bb = &bbc.base;

                if (bb.kind == .Call or bb.kind == .Return) {
                    std.debug.assert(threads.items.len != 0);
                    const join = self.addMemJoin(threads.items);
                    self.setInputNoIntern(bb, 1, join);
                }

                if (bb.outputs().len == 0) continue;

                var parent_succs: usize = 0;
                const parent = bb.inputs()[0] orelse {
                    std.debug.assert(bb.kind == .Return);
                    continue;
                };
                std.debug.assert(parent.isCfg());
                for (parent.outputs()) |o| parent_succs += @intFromBool(o.get().isCfg());
                if (!(parent_succs >= 1 and parent_succs <= 2)) utils.panic("{}\n", .{bb});
                // handle fork
                if (parent_succs == 2) {
                    // this is the second branch, restore the value
                    if (states[parent.schedule].Fork) |s| {
                        threads = .fromOwnedSlice(s.saved);
                    } else {
                        // we will visit this eventually
                        states[parent.schedule] = .{ .Fork = .{ .saved = tmp.arena.dupe(*Node, threads.items) } };
                    }
                }

                bbc.scheduleBlockAndRestoreBlockIds();

                var stmp = utils.Arena.scrath(tmp.arena);
                defer stmp.deinit();

                for (stmp.arena.dupe(Node.Out, bbc.base.outputs())) |instr| {
                    const o = instr.get();
                    if (!o.isStore()) continue;

                    var matches = Arry(*Node){};
                    var preserved = Arry(*Node){};
                    for (threads.items) |*thread| {
                        var cursor = thread.*;
                        while (cursor.isStore() and cursor.noAlias(o)) : (cursor = cursor.mem()) {}
                        if (std.mem.indexOfScalar(*Node, matches.items, cursor) == null) {
                            try matches.append(stmp.arena.allocator(), cursor);
                        }
                        if (thread.*.isStore() and !o.fullAlias(thread.*)) {
                            try preserved.append(stmp.arena.allocator(), thread.*);
                        }
                    }

                    std.debug.assert(matches.items.len != 0);

                    const join = self.addMemJoin(matches.items);
                    self.setInputNoIntern(o, 1, join);

                    // TODO: we can avoid this
                    try threads.resize(tmp.arena.allocator(), preserved.items.len);
                    @memcpy(threads.items, preserved.items);

                    try threads.append(tmp.arena.allocator(), o);
                }

                if (bb.kind == .CallEnd) {
                    threads.items[0] = for (bb.outputs()) |o| {
                        if (o.get().kind == .Mem) break o.get();
                    } else continue;
                    threads.items.len = 1;
                }

                const child: *Node = for (bb.outputs()) |o| {
                    if (o.get().isCfg()) break o.get();
                } else continue;

                var child_preds: usize = 0;
                for (child.inputs()) |b| child_preds += @intFromBool(b != null and b.?.isCfg());
                std.debug.assert((child_preds >= 1 and child_preds <= 2) or child.kind == .TrapRegion);
                // handle joins
                if (child_preds == 2 and child.kind != .TrapRegion and child.kind != .Return) {
                    if (!(child.kind == .Region or child.kind == .Loop)) {
                        utils.panic("{}\n", .{child});
                    }

                    const is_right = child.inputs()[0] != bb;

                    const mem_phi = for (child.outputs()) |o| {
                        if (o.get().kind == .Phi and !o.get().isDataPhi()) break o.get();
                    } else continue;

                    std.debug.assert(threads.items.len != 0);

                    const join = self.addMemJoin(threads.items);
                    self.setInputNoIntern(mem_phi, @as(usize, 1) + @intFromBool(is_right), join);

                    threads.items.len = 1;
                    threads.items[0] = mem_phi;
                }
            }
        }
    };
}
