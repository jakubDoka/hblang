const graph = @import("graph.zig");
const root = graph.utils;
const std = @import("std");

pub fn Mem2RegMixin(comptime Backend: type) type {
    return struct {
        const Func = graph.Func(Backend);
        const Self = @This();
        const Node = Func.Node;

        pub fn getGraph(self: *Self) *Func {
            return @alignCast(@fieldParentPtr("mem2reg", self));
        }

        // TODO: make this compact
        const Local = packed struct(usize) {
            flag: enum(u2) { null, node, loop } = .null,
            data: std.meta.Int(.unsigned, @bitSizeOf(usize) - 2) = 0,

            fn expand(self: Local) ?Expanded {
                return switch (self.flag) {
                    .null => null,
                    .node => .{ .Node = @ptrFromInt(self.data << 2) },
                    .loop => .{ .Loop = @ptrFromInt(self.data << 2) },
                };
            }

            fn compact(self: Expanded) Local {
                return switch (self) {
                    .Node => |n| .{ .flag = .node, .data = @truncate(@intFromPtr(n) >> 2) },
                    .Loop => |l| .{ .flag = .loop, .data = @truncate(@intFromPtr(l) >> 2) },
                };
            }

            const Expanded = union(enum) {
                Node: *Node,
                Loop: *Join,
            };

            const Join = struct { done: bool, ctrl: *Node, items: []L };

            const L = @This();

            fn resolve(func: *Func, scope: []L, index: usize) *Node {
                return switch (scope[index].expand().?) {
                    .Node => |n| n,
                    .Loop => |loop| {
                        if (!loop.done) {
                            const initVal = resolve(func, loop.items, index);

                            if (!loop.items[index].expand().?.Node.isLazyPhi(loop.ctrl)) {
                                loop.items[index] = .compact(.{ .Node = func.addNode(
                                    .Phi,
                                    initVal.data_type,
                                    &.{ loop.ctrl, initVal, null },
                                    .{},
                                ) });
                            }
                        }
                        scope[index] = loop.items[index];
                        if (scope[index].expand().? == .Loop) {
                            scope[index] = .compact(.{ .Node = resolve(func, loop.items, index) });
                        }
                        return scope[index].expand().?.Node;
                    },
                };
            }
        };

        const BBState = packed struct(usize) {
            flag: enum(u2) { uninit, fork, join } = .uninit,
            data: std.meta.Int(.unsigned, @bitSizeOf(usize) - 2) = undefined,

            fn expand(self: BBState, len: usize) Expanded {
                return switch (self.flag) {
                    .uninit => .{},
                    .fork => .{ .Fork = .{ .saved = @as([*]Local, @ptrFromInt(self.data << 2))[0..len] } },
                    .join => .{ .Join = @ptrFromInt(self.data << 2) },
                };
            }

            fn compact(self: Expanded) BBState {
                std.debug.assert(self.Fork == null or self.Join == null);
                if (self.Fork) |f| return .{ .flag = .fork, .data = @truncate(@intFromPtr(f.saved.ptr) >> 2) };
                if (self.Join) |j| return .{ .flag = .join, .data = @truncate(@intFromPtr(j) >> 2) };
                return .{};
            }

            const Expanded = struct {
                Fork: ?struct { saved: []Local } = null,
                Join: ?*Local.Join = null,
            };
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

            var locals = tmp.alloc(Local, local_count) catch unreachable;
            @memset(locals, .{});

            var states = tmp.alloc(BBState, postorder.len) catch unreachable;
            @memset(states, .{});

            for (postorder, 0..) |bb, i| bb.base.schedule = @intCast(i);

            var to_remove = std.ArrayList(*Node).init(tmp);
            for (postorder) |bbc| {
                const bb = &bbc.base;

                if (bb.outputs().len == 0) continue;

                var parent_succs: usize = 0;
                const parent = bb.inputs()[0] orelse {
                    std.debug.assert(bb.kind == .Return);
                    continue;
                };
                std.debug.assert(parent.isCfg());
                for (parent.outputs()) |o| parent_succs += @intFromBool(o.isCfg());
                if (!(parent_succs >= 1 and parent_succs <= 2)) root.panic("{}\n", .{bb});
                // handle fork
                if (parent_succs == 2) {
                    // this is the second branch, restore the value
                    if (states[parent.schedule].expand(locals.len).Fork) |s| {
                        locals = s.saved;
                    } else {
                        // we will visit this eventually
                        states[parent.schedule] = .compact(.{ .Fork = .{ .saved = tmp.dupe(Local, locals) catch unreachable } });
                    }
                }

                // we do it here because some loads are scheduled already and removing them in this loop messes up the
                // cheduling in other blocks, we need to hack this becaus there are no anty deps on loads yet, since this
                // runs before gcm
                //
                {
                    // carefull, the scheduleBlock messes up the node.schedule
                    //
                    var buf: [2]*Func.Node = undefined;
                    var scheds: [2]u16 = undefined;
                    var len: usize = 0;
                    for (bb.outputs()) |use| {
                        if (use.isCfg()) {
                            buf[len] = use;
                            scheds[len] = use.schedule;
                            len += 1;
                        }
                    }

                    if (bb.isBasicBlockStart()) {
                        @TypeOf(self.gcm).scheduleBlock(bb);
                    }

                    for (buf[0..len], scheds[0..len]) |n, s| n.schedule = s;
                }

                for (tmp.dupe(*Node, bb.outputs()) catch unreachable) |o| {
                    if (o.id == std.math.maxInt(u16)) continue;
                    if (o.kind == .Phi or o.kind == .Mem or o.isStore()) {
                        if (o.isStore() and o.base().kind == .Local and o.base().schedule != std.math.maxInt(u16)) {
                            to_remove.append(o) catch unreachable;
                            locals[o.base().schedule] = .compact(.{ .Node = o.value() });
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
                    if (states[child.schedule].expand(locals.len).Join) |s| {
                        if (s.ctrl != child) root.panic("{} {} {} {}\n", .{ s.ctrl, s.ctrl.schedule, child, child.schedule });
                        for (s.items, locals, 0..) |clhs, crhsm, i| {
                            var lhs = clhs.expand() orelse continue;
                            if (lhs == .Node and lhs.Node.isLazyPhi(s.ctrl)) {
                                var rhs = crhsm.expand().?;
                                if (rhs == .Loop and (rhs.Loop != s or s.ctrl.preservesIdentityPhys())) {
                                    rhs = .{ .Node = Local.resolve(self, locals, i) };
                                }

                                if (rhs == .Node) {
                                    if (self.setInput(lhs.Node, 2, rhs.Node)) |nlhs| {
                                        lhs = .{ .Node = nlhs };
                                    }
                                } else {
                                    const prev = lhs.Node.inputs()[1].?;
                                    self.subsume(prev, lhs.Node);
                                    lhs = .{ .Node = prev };
                                }

                                if (child.inputs()[0] == bb) {
                                    // TODO: maybe make all previous code more
                                    // complicated so that his is not needed as
                                    // it's kind of slow
                                    const lhss, const rhss = lhs.Node.inputs()[1..3].*;
                                    if (self.setInput(lhs.Node, 1, rhss)) |v| lhs = .{ .Node = v };
                                    if (self.setInput(lhs.Node, 2, lhss)) |v| lhs = .{ .Node = v };
                                }

                                s.items[i] = .compact(lhs);
                            }
                        }
                        s.done = true;
                    } else {
                        // first time seeing, this ca also be a region, needs renaming I guess
                        const loop = tmp.create(Local.Join) catch unreachable;
                        loop.* = .{
                            .done = false,
                            .ctrl = child,
                            .items = tmp.dupe(Local, locals) catch unreachable,
                        };
                        @memset(locals, .compact(.{ .Loop = loop }));
                        states[child.schedule] = .compact(.{ .Join = loop });
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
