const std = @import("std");
const graph = @import("graph.zig");
const root = @import("../utils.zig");

pub const Error = union(enum) {
    ReturningStack: struct {
        slot: graph.Sloc,
    },
    StackOob: struct {
        slot: graph.Sloc,
        access: graph.Sloc,
        op: u32,
    },
    LoopInvariantBreak: struct {
        if_node: graph.Sloc,
    },
    InfiniteLoopWithBreak: struct {
        loop: graph.Sloc,
    },
};

pub fn StaticAnalMixin(comptime Backend: type) type {
    return struct {
        const Self = @This();
        const Func = graph.Func(Backend);
        const Node = Func.Node;

        pub fn getGraph(self: *Self) *Func {
            return @alignCast(@fieldParentPtr("static_anal", self));
        }

        pub fn analize(self: *Self, arena: *root.Arena, errors: *std.ArrayListUnmanaged(Error)) void {
            self.findTrivialStackEscapes(arena, errors);
            self.tryHardToFindMemoryEscapes(arena, errors);
            self.findConstantOobMemOps(arena, errors);
            self.findLoopInvariantConditions(arena, errors);
            self.findInfiniteLoopsWithBreaks(arena, errors);
        }

        pub fn findInfiniteLoopsWithBreaks(
            self: *Self,
            arena: *root.Arena,
            errors: *std.ArrayListUnmanaged(Error),
        ) void {
            const func = self.getGraph();
            for (func.gcm.postorder) |bb| {
                if (bb.base.kind == .Loop and bb.base.extra(.Loop).anal_stage == .has_dead_break) {
                    errors.append(arena.allocator(), .{ .InfiniteLoopWithBreak = .{ .loop = bb.base.sloc } }) catch unreachable;
                }
            }
        }

        pub fn findLoopInvariantConditions(
            self: *Self,
            arena: *root.Arena,
            errors: *std.ArrayListUnmanaged(Error),
        ) void {
            var tmp = root.Arena.scrath(arena);
            defer tmp.deinit();

            std.debug.assert(tmp.arena != arena);

            const func = self.getGraph();

            var work = Func.WorkList.init(tmp.arena.allocator(), func.next_id) catch unreachable;

            work.add(func.root);

            var i: usize = 0;
            while (i < work.list.items.len) : (i += 1) {
                const node = work.list.items[i];
                if (node.isSub(graph.If) and node.sloc != graph.Sloc.none) b: {
                    const ld = func.loopDepth(node);
                    for (node.outputs()) |o| {
                        if (func.loopDepth(o) < ld) break;
                    } else break :b;

                    for (node.inputs()[1..]) |inp| {
                        if (func.loopDepth(inp.?) == ld) break :b;
                    }

                    errors.append(arena.allocator(), .{
                        .LoopInvariantBreak = .{ .if_node = node.sloc },
                    }) catch unreachable;
                }

                for (node.outputs()) |o| if (o.isCfg()) {
                    work.add(o);
                };
            }
        }

        pub fn findConstantOobMemOps(
            self: *Self,
            arena: *root.Arena,
            errors: *std.ArrayListUnmanaged(Error),
        ) void {
            const func = self.getGraph();

            if (func.root.outputs().len < 2 or func.root.outputs()[1].kind != .Mem) return;

            for (func.root.outputs()[1].outputs()) |local| if (local.kind == .Local) {
                for (local.outputs()) |op| {
                    const mem_op, const offset = op.knownMemOp() orelse continue;
                    if ((!mem_op.isLoad() and !mem_op.isStore()) or mem_op.isSub(graph.MemCpy)) continue;
                    if (mem_op.isStore() and mem_op.value() == local) {
                        continue;
                    }
                    const end_offset = offset + @as(i64, @intCast(mem_op.data_type.size()));
                    if (offset < 0 or end_offset > local.extra(.Local).size) {
                        errors.append(arena.allocator(), .{ .StackOob = .{
                            .slot = local.sloc,
                            .op = mem_op.id,
                            .access = op.sloc,
                        } }) catch unreachable;
                    }
                }
            };
        }

        // NOTE: this is a heuristic, it can miss things
        pub fn tryHardToFindMemoryEscapes(
            self: *Self,
            arena: *root.Arena,
            errors: *std.ArrayListUnmanaged(Error),
        ) void {
            const func = self.getGraph();
            for (func.root.outputs()[0].outputs()) |arg| if (arg.kind == .Arg) {
                var tmp = root.Arena.scrath(arena);
                defer tmp.deinit();

                var local_stores = std.ArrayListUnmanaged(*Node){};

                // find stores that store pointer to local variable
                for (arg.outputs()) |ao| {
                    // TODO: we skip MemCpy, this will miss a class of problems,
                    // but memcpy elimination might help and effort here would be redundant
                    const store = ao.knownStore(arg) orelse continue;

                    if (store.value() != null and store.value().?.kind == .Local) {
                        local_stores.append(tmp.arena.allocator(), store) catch unreachable;
                    }
                }

                if (local_stores.items.len == 0) return;

                // filter out the stores that are overriden
                for (arg.outputs()) |unmarked| {
                    const store = unmarked.knownStore(arg) orelse continue;

                    if (store.value() != null and store.value().?.kind == .Local) continue;

                    var kept: usize = 0;
                    o: for (local_stores.items) |marked| {
                        if (store.noAlias(marked)) {
                            local_stores.items[kept] = marked;
                            kept += 1;
                            continue :o;
                        }

                        var curcor = store.cfg0();
                        while (true) {
                            if (marked.cfg0() == store.cfg0()) break;
                            if (marked.cfg0() == curcor) continue :o;
                            if (curcor.idepth() < marked.cfg0().idepth()) {
                                local_stores.items[kept] = marked;
                                kept += 1;
                                continue :o;
                            }

                            curcor = curcor.base.cfg0();
                        }

                        const unmarked_is_first = for (curcor.base.outputs()) |bo| {
                            if (bo == store) break false;
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
                    errors.append(arena.allocator(), .{
                        .ReturningStack = .{ .slot = marked.value().?.sloc },
                    }) catch unreachable;
                }
            };
        }

        pub fn findTrivialStackEscapes(
            self: *Self,
            arena: *root.Arena,
            errors: *std.ArrayListUnmanaged(Error),
        ) void {
            const func = self.getGraph();
            if (func.end.inputs()[0] == null) return;

            var tmp = root.Arena.scrath(arena);
            defer tmp.deinit();

            var frontier = std.ArrayListUnmanaged(*Node){};
            for (func.end.inputs()[3..]) |n| {
                frontier.append(tmp.arena.allocator(), n orelse continue) catch unreachable;
            }

            // walk trough phis
            // note: assuming store->load peepholes are all applied, walking loads should be redundant
            while (frontier.pop()) |nd| {
                if (nd.kind == .Local) {
                    errors.append(arena.allocator(), .{ .ReturningStack = .{ .slot = nd.sloc } }) catch unreachable;
                } else if (nd.kind == .Phi) {
                    for (nd.inputs()[1..]) |n| {
                        frontier.append(tmp.arena.allocator(), n.?) catch unreachable;
                    }
                }
            }
        }
    };
}
