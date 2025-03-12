const graph = @import("graph.zig");
const std = @import("std");
const root = @import("utils.zig");

pub const Error = union(enum) {
    ReturningStack: struct {
        slot: u32,
    },
};

pub fn StaticAnalMixin(comptime Mach: type) type {
    return struct {
        const Self = @This();
        const Func = graph.Func(Mach);
        const Node = Func.Node;

        pub fn getGraph(self: *Self) *Func {
            return @alignCast(@fieldParentPtr("static_anal", self));
        }

        pub fn analize(self: *Self, arena: *root.Arena, errors: *std.ArrayListUnmanaged(Error)) void {
            self.findTrivialStackEscapes(arena, errors);
            self.tryHardToFindMemoryEscapes(arena, errors);
        }

        pub fn tryHardToFindMemoryEscapes(self: *Self, arena: *root.Arena, errors: *std.ArrayListUnmanaged(Error)) void {
            const func = self.getGraph();
            for (func.root.outputs()[0].outputs()) |arg| if (arg.kind == .Arg) {
                var tmp = root.Arena.scrath(arena);
                defer tmp.deinit();

                var local_stores = std.ArrayListUnmanaged(*Node){};

                for (arg.outputs()) |ao| {
                    const store = Func.knownStore(ao) orelse continue;

                    if (store.value().kind == .Local) {
                        local_stores.append(tmp.arena.allocator(), store) catch unreachable;
                    }
                }

                if (local_stores.items.len == 0) return;

                for (arg.outputs()) |unmarked| {
                    const store = Func.knownStore(unmarked) orelse continue;

                    if (store.value().kind == .Local) continue;

                    var kept: usize = 0;
                    o: for (local_stores.items) |marked| {
                        if (Func.noAlias(unmarked, marked)) {
                            local_stores.items[kept] = marked;
                            kept += 1;
                            continue :o;
                        }

                        var curcor = unmarked.cfg0().?;
                        while (true) {
                            if (marked.cfg0().? == unmarked.cfg0().?) break;
                            if (marked.cfg0().? == curcor) continue :o;
                            if (curcor.idepth() < marked.cfg0().?.idepth()) {
                                local_stores.items[kept] = marked;
                                kept += 1;
                                continue :o;
                            }

                            curcor = curcor.base.cfg0().?;
                        }

                        const unmarked_is_first = for (curcor.base.outputs()) |bo| {
                            if (bo == unmarked) break false;
                            if (bo == marked) break true;
                        } else unreachable;

                        if (!unmarked_is_first) {
                            local_stores.items[kept] = marked;
                            kept += 1;
                        }
                    }
                    local_stores.items.len = kept;
                }

                for (local_stores.items) |marked| {
                    errors.append(arena.allocator(), .{ .ReturningStack = .{ .slot = marked.id } }) catch unreachable;
                }
            };
        }

        pub fn findTrivialStackEscapes(self: *Self, arena: *root.Arena, errors: *std.ArrayListUnmanaged(Error)) void {
            const func = self.getGraph();
            if (func.end.inputs()[0] == null) return;

            var tmp = root.Arena.scrath(arena);
            defer tmp.deinit();

            var frontier = std.ArrayListUnmanaged(*Node){};
            for (func.end.inputs()[3..]) |n| {
                frontier.append(tmp.arena.allocator(), n orelse continue) catch unreachable;
            }

            while (frontier.pop()) |nd| {
                if (nd.kind == .Local) {
                    errors.append(arena.allocator(), .{ .ReturningStack = .{ .slot = nd.id } }) catch unreachable;
                } else if (nd.kind == .Phi) {
                    for (nd.inputs()[1..]) |n| {
                        frontier.append(tmp.arena.allocator(), n.?) catch unreachable;
                    }
                }
            }
        }
    };
}
