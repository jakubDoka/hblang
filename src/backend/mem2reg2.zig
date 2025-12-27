const graph = @import("graph.zig");
const utils = graph.utils;
const std = @import("std");
const Builder = @import("Builder.zig");

pub const dummy = Mixin(Builder);

pub fn Mixin(comptime Backend: type) type {
    return struct {
        const Func = graph.Func(Backend);
        const Self = @This();
        const Node = Func.Node;

        pub fn getGraph(self: *Self) *Func {
            return @alignCast(@fieldParentPtr("mem2reg2", self));
        }

        pub const BaseGroup = struct {
            addr: *Node,
            parallel: std.ArrayList(Slot) = .empty,

            pub const Slot = struct {
                offset: i64,
                store: *Node,
            };
        };

        pub const State = struct {
            groups: []BaseGroup,

            // TODO: convert to this
            //groups: std.ArrayList(GroupSlot),
            //free_groups: ?*GroupSlot,

            //const GroupSlot = union {
            //    free: ?*GroupSlot,
            //    slot: BaseGroup,
            //};
        };

        pub fn doesNotEscape(self: *Node, local: Node.Out) bool {
            return (self.kind == .Store and local.pos() == 2) or self.kind == .Load;
        }

        pub const escaped_schedule = std.math.maxInt(u16);

        pub fn run(m2r: *Self) void {
            errdefer unreachable;

            const self = m2r.getGraph();

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var groups = std.ArrayList(BaseGroup).empty;

            const mem = self.getMem() orelse return;

            seach_good_locals: for (mem.outputs()) |local| {
                if (local.get().kind != .LocalAlloc) continue;

                std.debug.assert(local.get().outputs().len == 1);
                const addr = local.get().outputs()[0].get();

                for (addr.outputs()) |use| {
                    if (use.get().kind == .BinOp and use.get().inputs()[2].?.kind == .CInt) {
                        for (use.get().outputs()) |use_use| {
                            if (!doesNotEscape(use_use.get(), use)) {
                                break;
                            }
                        } else continue;
                    } else if (doesNotEscape(use.get(), local)) {
                        continue;
                    }

                    addr.schedule = escaped_schedule;
                    continue :seach_good_locals;
                }

                addr.schedule = @intCast(groups.items.len);
                try groups.append(tmp.arena.allocator(), BaseGroup{ .addr = addr });
            }

            var state = State{
                .groups = groups.items,
            };
            _ = &state;

            var cursor = mem;
            while (true) {
                if (cursor.kind == .Store) {
                    const base, const off = cursor.base().knownOffset();
                    _ = off;
                    _ = base;
                }

                for (cursor.outputs()) |o| {
                    if (o.get().kind == .Load) {
                        const base, const off = o.get().base().knownOffset();
                        if (base.kind == .Local and base.schedule != escaped_schedule) {
                            const group = state.groups[base.schedule];
                            for (group.parallel.items) |p| {
                                if (p.offset > off + @as(i64, @intCast(o.get().data_type.size()))) {
                                    continue;
                                }

                                if (p.offset + @as(i64, @intCast(p.store.data_type.size())) < off) {
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
        }
    };
}
