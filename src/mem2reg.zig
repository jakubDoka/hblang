const graph = @import("graph.zig");
const root = @import("utils.zig");
const std = @import("std");

pub fn Mem2RegMixin(comptime MachNode: type) type {
    return struct {
        const Func = graph.Func(MachNode);
        const Self = @This();
        const Node = Func.Node;

        pub fn getGraph(self: *Self) *Func {
            return @alignCast(@fieldParentPtr("mem2reg", self));
        }

        const Local = union(enum) {
            Node: *Node,
            Loop: *Join,

            const Join = struct { done: bool, ctrl: *Node, items: []?L };

            const L = @This();

            fn resolve(func: *Func, scope: []?L, index: usize) *Node {
                return switch (scope[index].?) {
                    .Node => |n| n,
                    .Loop => |loop| {
                        if (!loop.done) {
                            const initVal = resolve(func, loop.items, index);

                            if (!loop.items[index].?.Node.isLazyPhi(loop.ctrl)) {
                                loop.items[index].? = .{ .Node = func.addNode(.Phi, &.{ loop.ctrl, initVal, null }, {}) };
                            }
                        }
                        scope[index] = loop.items[index];
                        return scope[index].?.Node;
                    },
                };
            }
        };

        const BBState = struct {
            Fork: ?struct {
                saved: []?Local,
            } = null,
            Join: ?*Local.Join = null,
        };

        pub fn run(m2r: *Self) void {
            const self = m2r.getGraph();
            self.gcm.cfg_built.assertUnlocked();

            // TODO: refactor to use tmpa directily
            var tmpa = root.Arena.scrath(null);
            defer tmpa.deinit();

            const tmp = tmpa.arena.allocator();

            var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
            const postorder = self.collectDfs(tmp, &visited)[1..];

            var local_count: u16 = 0;

            if (self.root.outputs().len == 1) return;

            std.debug.assert(self.root.outputs()[1].kind == .Mem);
            for (self.root.outputs()[1].outputs()) |o| {
                if (o.kind == .Local) b: {
                    for (o.outputs()) |oo| {
                        if ((!oo.isStore() and !oo.isLoad()) or oo.base() != o or oo.isSub(graph.MemCpy)) {
                            o.schedule = std.math.maxInt(u16);
                            break :b;
                        }
                    }
                    o.schedule = local_count;
                    local_count += 1;
                }
            }

            var locals = tmp.alloc(?Local, local_count) catch unreachable;
            @memset(locals, null);

            var states = tmp.alloc(BBState, postorder.len) catch unreachable;
            @memset(states, .{});

            var to_remove = std.ArrayList(*Node).init(tmp);
            for (postorder) |bbc| {
                const bb = &bbc.base;

                var parent_succs: usize = 0;
                const parent = bb.inputs()[0] orelse {
                    std.debug.assert(bb.kind == .Return);
                    continue;
                };
                std.debug.assert(parent.isCfg());
                for (parent.outputs()) |o| parent_succs += @intFromBool(o.isCfg());
                std.debug.assert(parent_succs >= 1 and parent_succs <= 2);
                // handle fork
                if (parent_succs == 2) {
                    // this is the second branch, restore the value
                    if (states[parent.schedule].Fork) |s| {
                        locals = s.saved;
                    } else {
                        // we will visit this eventually
                        states[parent.schedule].Fork = .{ .saved = tmp.dupe(?Local, locals) catch unreachable };
                    }
                }

                // we do it here because some loads are scheduled already and removing them in this loop messes up the
                // cheduling in other blocks, we need to hack this becaus there are no anty deps on loads yet, since this
                // runs before gcm
                if (bb.isBasicBlockStart()) {
                    @TypeOf(self.gcm).scheduleBlock(tmp, bb);
                }

                // TODO: this is super wastefull, we are basically fixing the block indexes
                for (postorder, 0..) |bbb, i| bbb.base.schedule = @intCast(i);

                for (tmp.dupe(*Node, bb.outputs()) catch unreachable) |o| {
                    if (o.id == std.math.maxInt(u16)) continue;
                    if (o.kind == .Phi or o.kind == .Mem or o.isStore()) {
                        if (o.isStore() and o.base().kind == .Local and o.base().schedule != std.math.maxInt(u16)) {
                            to_remove.append(o) catch unreachable;
                            locals[o.base().schedule] = .{ .Node = o.value() };
                        }

                        for (tmp.dupe(*Node, o.outputs()) catch unreachable) |lo| {
                            if (lo.isLoad() and lo.base().kind == .Local and lo.base().schedule != std.math.maxInt(u16)) {
                                const su = Local.resolve(self, locals, lo.base().schedule);
                                self.subsume(su, lo);
                            }
                        }
                    }
                }

                const child: *Node = for (bb.outputs()) |o| {
                    if (o.isCfg()) break o;
                } else continue;
                var child_preds: usize = 0;
                for (child.inputs()) |b| child_preds += @intFromBool(b != null and b.?.isCfg());
                std.debug.assert(child_preds >= 1 and child_preds <= 2);
                // handle joins
                if (child_preds == 2 and child.kind != .TrapRegion and child.kind != .Return) {
                    if (!(child.kind == .Region or child.kind == .Loop)) {
                        root.panic("{}\n", .{child});
                    }
                    // eider we arrived from the back branch or the other side of the split
                    if (states[child.schedule].Join) |s| {
                        if (s.ctrl != child) root.panic("{} {} {} {}\n", .{ s.ctrl, s.ctrl.schedule, child, child.schedule });
                        for (s.items, locals, 0..) |lhs, rhsm, i| {
                            if (lhs == null) continue;
                            if (lhs.? == .Node and lhs.?.Node.isLazyPhi(s.ctrl)) {
                                var rhs = rhsm;
                                if (rhs.? == .Loop and (rhs.?.Loop != s or s.ctrl.preservesIdentityPhys())) {
                                    rhs = .{ .Node = Local.resolve(self, locals, i) };
                                }
                                if (rhs.? == .Node) {
                                    if (self.setInput(lhs.?.Node, 2, rhs.?.Node)) |nlhs| {
                                        s.items[i].?.Node = nlhs;
                                    }
                                } else {
                                    const prev = lhs.?.Node.inputs()[1].?;
                                    self.subsume(prev, lhs.?.Node);
                                    s.items[i].?.Node = prev;
                                }
                            }
                        }
                        s.done = true;
                    } else {
                        // first time seeing, this ca also be a region, needs renaming I guess
                        const loop = tmp.create(Local.Join) catch unreachable;
                        loop.* = .{
                            .done = false,
                            .ctrl = child,
                            .items = tmp.dupe(?Local, locals) catch unreachable,
                        };
                        @memset(locals, .{ .Loop = loop });
                        states[child.schedule].Join = loop;
                    }
                }
            }

            for (to_remove.items) |tr| {
                self.subsume(tr.mem(), tr);
            }

            for (self.root.outputs()[1].outputs()) |o| {
                if (o.kind == .Local) {
                    o.schedule = std.math.maxInt(u16);
                }
            }

            for (postorder) |bb| {
                bb.base.schedule = std.math.maxInt(u16);
            }
        }
    };
}
