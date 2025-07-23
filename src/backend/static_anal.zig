const std = @import("std");
const graph = @import("graph.zig");
const utils = @import("../utils.zig");

pub const Error = union(enum) {
    ReturningStack: struct {
        slot: graph.Sloc,
    },
    StackOob: struct {
        slot: graph.Sloc,
        access: graph.Sloc,
        op: u32,
        size: u64,
        range: struct { start: i64, end: i64 },
    },
    LoopInvariantBreak: struct {
        if_node: graph.Sloc,
    },
    InfiniteLoopWithBreak: struct {
        loop: graph.Sloc,
    },
    ReadUninit: struct {
        loc: graph.Sloc,
    },
};

pub fn Mixin(comptime Backend: type) type {
    return struct {
        const Self = @This();
        const Func = graph.Func(Backend);
        const Node = Func.Node;

        pub fn getGraph(self: *Self) *Func {
            return @alignCast(@fieldParentPtr("static_anal", self));
        }

        pub fn analize(self: *Self, arena: *utils.Arena, errors: *std.ArrayListUnmanaged(Error)) void {
            self.findTrivialStackEscapes(arena, errors);
            self.tryHardToFindMemoryEscapes(arena, errors);
            self.findConstantOobMemOps(arena, errors);
            self.findLoopInvariantConditions(arena, errors);
            self.findInfiniteLoopsWithBreaks(arena, errors);
        }

        pub fn findInfiniteLoopsWithBreaks(
            self: *Self,
            arena: *utils.Arena,
            errors: *std.ArrayListUnmanaged(Error),
        ) void {
            errdefer unreachable;
            const func = self.getGraph();
            for (func.gcm.postorder) |bb| {
                if (bb.base.kind == .Loop and bb.base.extra(.Loop).anal_stage == .has_dead_break) {
                    try errors.append(arena.allocator(), .{ .InfiniteLoopWithBreak = .{ .loop = bb.base.sloc } });
                }
            }
        }

        pub fn findLoopInvariantConditions(
            self: *Self,
            arena: *utils.Arena,
            errors: *std.ArrayListUnmanaged(Error),
        ) void {
            errdefer unreachable;
            var tmp = utils.Arena.scrath(arena);
            defer tmp.deinit();

            std.debug.assert(tmp.arena != arena);

            const func = self.getGraph();

            for (func.gcm.postorder) |bb| {
                const node = bb.base.outputs()[bb.base.outputs().len - 1].get();

                if (node.isSub(graph.If) and node.sloc != graph.Sloc.none) b: {
                    const ld = func.loopDepth(node);
                    for (node.outputs()) |o| {
                        if (func.loopDepth(o.get()) < ld) break;
                    } else break :b;

                    for (node.inputs()[1..]) |inp| {
                        if (func.loopDepth(inp.?) == ld) break :b;
                    }

                    try errors.append(arena.allocator(), .{
                        .LoopInvariantBreak = .{ .if_node = node.sloc },
                    });
                }
            }
        }

        pub fn findConstantOobMemOps(
            self: *Self,
            arena: *utils.Arena,
            errors: *std.ArrayListUnmanaged(Error),
        ) void {
            const func = self.getGraph();

            if (func.start.outputs().len < 2 or func.start.outputs()[1].get().kind != .Mem) return;

            for (func.start.outputs()[1].get().outputs()) |lcl| {
                const local = lcl.get();
                if (local.kind == .LocalAlloc) {
                    for (local.outputs()) |n| {
                        const op = n.get();
                        if (op.kind == .Local) {
                            for (op.outputs()) |use| {
                                checkLocalForOob(use.get(), local, op, arena, errors);
                            }
                        } else {
                            checkLocalForOob(op, local, null, arena, errors);
                        }
                    }
                }
            }
        }

        pub fn checkLocalForOob(op: *Func.Node, local: *Func.Node, addr: ?*Func.Node, arena: *utils.Arena, errors: *std.ArrayListUnmanaged(Error)) void {
            errdefer unreachable;
            const mem_op, const offset = op.knownMemOp() orelse return;
            if ((!mem_op.isLoad() and !mem_op.isStore()) or mem_op.isSub(graph.MemCpy)) return;
            if (mem_op.isStore() and mem_op.value() == addr) return;
            const end_offset = offset + @as(i64, @intCast(mem_op.data_type.size()));
            if (offset < 0 or end_offset > local.extra(.LocalAlloc).size) {
                try errors.append(arena.allocator(), .{ .StackOob = .{
                    .slot = local.sloc,
                    .op = mem_op.id,
                    .access = op.sloc,
                    .size = local.extra(.LocalAlloc).size,
                    .range = .{ .end = end_offset, .start = offset },
                } });
            }
        }

        // NOTE: this is a heuristic, it can miss things
        pub fn tryHardToFindMemoryEscapes(
            self: *Self,
            arena: *utils.Arena,
            errors: *std.ArrayListUnmanaged(Error),
        ) void {
            errdefer unreachable;
            const func = self.getGraph();
            for (func.start.outputs()[0].get().outputs()) |ar| {
                const arg = ar.get();
                if (arg.kind != .Arg) continue;

                var tmp = utils.Arena.scrath(arena);
                defer tmp.deinit();

                var local_stores = std.ArrayListUnmanaged(*Node){};

                // find stores that store pointer to local variable
                for (arg.outputs()) |ao| {
                    // TODO: we skip MemCpy, this will miss a class of problems,
                    // but memcpy elimination might help and effort here would be redundant
                    const store = ao.get().knownStore(arg) orelse continue;

                    if (store.value() != null and store.value().?.kind == .Local) {
                        try local_stores.append(tmp.arena.allocator(), store);
                    }
                }

                if (local_stores.items.len == 0) return;

                // filter out the stores that are overriden
                for (arg.outputs()) |unmarked| {
                    const store = unmarked.get().knownStore(arg) orelse continue;

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
                            if (bo.get() == store) break false;
                            if (bo.get() == marked) break true;
                        } else unreachable;

                        if (!unmarked_is_first) {
                            local_stores.items[kept] = marked;
                            kept += 1;
                        }
                    }
                    local_stores.items.len = kept;
                }

                for (local_stores.items) |marked| {
                    try errors.append(arena.allocator(), .{
                        .ReturningStack = .{ .slot = marked.value().?.sloc },
                    });
                }
            }
        }

        pub fn findTrivialStackEscapes(
            self: *Self,
            arena: *utils.Arena,
            errors: *std.ArrayListUnmanaged(Error),
        ) void {
            errdefer unreachable;
            const func = self.getGraph();
            if (func.end.inputs()[0] == null) return;

            var tmp = utils.Arena.scrath(arena);
            defer tmp.deinit();

            var frontier = std.AutoArrayHashMapUnmanaged(*Node, void){};
            for (func.end.inputs()[3..]) |n| {
                try frontier.put(tmp.arena.allocator(), n orelse continue, {});
            }

            // walk trough phis
            // note: assuming store->load peepholes are all applied, walking loads should be redundant
            var i: usize = 0;
            while (i < frontier.entries.len) : (i += 1) {
                const nd = frontier.entries.items(.key)[i];
                if (nd.kind == .Local) {
                    try errors.append(arena.allocator(), .{ .ReturningStack = .{ .slot = nd.sloc } });
                } else if (nd.kind == .Phi) {
                    for (nd.inputs()[1..]) |n| {
                        try frontier.put(tmp.arena.allocator(), n.?, {});
                    }
                }
            }
        }
    };
}
