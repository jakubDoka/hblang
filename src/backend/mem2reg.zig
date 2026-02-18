const graph = @import("graph.zig");
const utils = graph.utils;
const std = @import("std");

pub fn Mixin(comptime Backend: type) type {
    return struct {
        const Func = graph.Func(Backend);
        const Self = @This();
        const Node = Func.Node;

        pub fn getGraph(self: *Self) *Func {
            return @alignCast(@fieldParentPtr("mem2reg", self));
        }

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

            fn resolve(func: *Func, scope: []L, index: usize, ty: graph.DataType) *Node {
                return switch (scope[index].expand() orelse {
                    return func.addUninit(.none, ty);
                }) {
                    .Node => |n| n,
                    .Loop => |loop| {
                        if (loop.items[index].expand() == null) {
                            const vl = func.addUninit(.none, ty);
                            scope[index] = .compact(.{ .Node = vl });
                            return vl;
                        }
                        if (!loop.done) {
                            const initVal = resolve(func, loop.items, index, ty);

                            if (!loop.items[index].expand().?.Node.isLazyPhi(loop.ctrl)) {
                                std.debug.assert(initVal.data_type == ty);
                                loop.items[index] = .compact(.{ .Node = func.addNode(
                                    .Phi,
                                    initVal.sloc,
                                    initVal.data_type,
                                    &.{ loop.ctrl, initVal, null },
                                    .{},
                                ) });
                            }
                        }
                        scope[index] = loop.items[index];
                        if (scope[index].expand().? == .Loop) {
                            unreachable;
                        }

                        std.debug.assert(scope[index].expand().?.Node.data_type == ty);
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

        const StackSlot = struct {
            offset: i64,
        };

        pub fn isGoodMemOp(self: *Node, local: *Node) bool {
            return (self.isStore() and !self.isSub(graph.MemCpy) and
                self.value() != local) or self.isLoad();
        }

        const Set = std.DynamicBitSetUnmanaged;
        const Arry = std.ArrayList;

        pub fn run(m2r: *Self) void {
            errdefer unreachable;

            const self = m2r.getGraph();
            self.gcm.cfg_built.assertUnlocked();

            const mem = self.getMem() orelse return;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const escaped_schedue = std.math.maxInt(u32);

            var visited = try Set.initEmpty(tmp.arena.allocator(), self.next_id);
            const postorder = self.collectDfs(tmp.arena.allocator(), &visited)[1..];

            const schedules = tmp.arena.alloc(u32, self.next_id);
            @memset(schedules, escaped_schedue);

            var slots = Arry(StackSlot){};
            var offset: i64 = 0;
            var offsets = Arry(packed struct(u64) { offset: u62, size: u2 }){};
            var store_load_nodes = Arry(*Node){};
            var alloc_offsets = Arry(i64){};

            outer: for (mem.outputs()) |n| {
                const ov = n.get();
                if (ov.kind != .LocalAlloc or ov.outputs().len != 1 or
                    ov.extra(.LocalAlloc).meta.kind != .variable) continue :outer;
                const o = ov.outputs()[0].get();
                std.debug.assert(o.kind == .Local);

                // collect all loads and stores, bail on something else
                //
                store_load_nodes.items.len = 0;
                for (o.outputs()) |us| {
                    const use = us.get();
                    if (use.kind == .BinOp and use.inputs()[2].?.kind == .CInt) {
                        for (use.outputs()) |use_use| {
                            if (isGoodMemOp(use_use.get(), o)) {
                                try store_load_nodes.append(tmp.arena.allocator(), use_use.get());
                            } else {
                                continue :outer;
                            }
                        }
                    } else if (isGoodMemOp(use, o)) {
                        try store_load_nodes.append(tmp.arena.allocator(), use);
                    } else {
                        continue :outer;
                    }
                }

                // validate that there are no viredly overlapping stores or loads
                // if so, bail
                //
                offsets.items.len = 0;
                for (store_load_nodes.items) |use| {
                    _, const offs = use.base().knownOffset();
                    // don't touch this and leave the static analysis report the soob
                    //
                    if (offs < 0 or @as(u64, @intCast(offs)) + use.data_type.size() >
                        // TODO: we ignore elems > 8 for now but we will want mem2reg to work on
                        // vectors eventually
                        o.inputs()[1].?.extra(.LocalAlloc).size or use.data_type.size() > 8)
                    {
                        continue :outer;
                    }

                    for (offsets.items) |off| {
                        if (off.offset > offs + use.data_type.size() or offs >= off.offset + (@as(u64, 1) << off.size)) {
                            continue;
                        }

                        if (off.offset != offs or (@as(u64, 1) << off.size) != use.data_type.size()) {
                            continue :outer;
                        }

                        break;
                    } else {
                        try offsets.append(tmp.arena.allocator(), .{
                            .offset = @intCast(offs),
                            .size = @intCast(std.math.log2_int(u64, use.data_type.size())),
                        });
                    }
                }

                for (offsets.items) |off| {
                    try alloc_offsets.append(tmp.arena.allocator(), offset + off.offset);
                }
                const new = alloc_offsets.items[alloc_offsets.items.len - offsets.items.len ..];
                std.sort.pdq(i64, new, {}, std.sort.asc(i64));

                schedules[o.id] = @intCast(slots.items.len);
                try slots.append(tmp.arena.allocator(), .{ .offset = offset });
                offset += @intCast(o.inputs()[1].?.extra(.LocalAlloc).size);
            }

            std.debug.assert(std.sort.isSorted(i64, alloc_offsets.items, {}, std.sort.asc(i64)));

            var locals = tmp.arena.alloc(Local, alloc_offsets.items.len);
            @memset(locals, .{});

            var states = tmp.arena.alloc(BBState, postorder.len);
            @memset(states, .{});

            for (postorder, 0..) |bb, i| {
                schedules[bb.base.id] = @intCast(i);
            }

            var to_remove = Arry(*Node){};
            for (postorder) |bbc| {
                const bb = &bbc.base;

                if (bb.outputs().len == 0) continue;

                var parent_succs: usize = 0;
                const parent = bb.inputs()[0] orelse {
                    std.debug.assert(bb.kind == .Return);
                    continue;
                };
                std.debug.assert(parent.isCfg());
                for (parent.outputs()) |o| parent_succs += @intFromBool(o.get().isCfg());
                if (!(parent_succs >= 1 and parent_succs <= 2)) utils.panic("{f}\n", .{bb});
                // handle fork
                if (parent_succs == 2) {
                    // this is the second branch, restore the value
                    if (states[schedules[parent.id]].expand(locals.len).Fork) |s| {
                        locals = s.saved;
                    } else {
                        // we will visit this eventually
                        states[schedules[parent.id]] = .compact(.{ .Fork = .{ .saved = tmp.arena.dupe(Local, locals) } });
                    }
                }

                if (bbc.base.isBasicBlockStart()) {
                    Func.CfgNode.scheduleBlock(bbc);
                }

                var stmp = utils.Arena.scrath(tmp.arena);
                defer stmp.deinit();

                for (stmp.arena.dupe(Node.Out, bb.outputs())) |n| {
                    const o = n.get();
                    if (o.isDead()) continue;
                    std.debug.assert(bb.kind != .Local);

                    if (o.isStore()) {
                        const base, const off = o.base().knownOffset();
                        if (base.kind == .Local and schedules[base.id] != escaped_schedue) {
                            try to_remove.append(tmp.arena.allocator(), o);
                            const offs = slots.items[schedules[base.id]].offset + off;
                            const idx = std.sort.binarySearch(i64, alloc_offsets.items, offs, struct {
                                pub fn inner(a: i64, b: i64) std.math.Order {
                                    return std.math.order(a, b);
                                }
                            }.inner) orelse {
                                utils.panic("{f} {any} {}", .{ o, alloc_offsets.items, offs });
                            };
                            if (locals[idx].expand() != null) {
                                _ = Local.resolve(self, locals, idx, o.data_type);
                            }
                            locals[idx] = .compact(.{ .Node = o.value().? });
                        }
                    }

                    if (o.kind == .Phi or o.kind == .Mem or o.isStore()) {
                        for (stmp.arena.dupe(Node.Out, o.outputs())) |no| {
                            const lo = no.get();
                            if (lo.isLoad()) {
                                const base, const off = lo.base().knownOffset();
                                if (base.kind == .Local and schedules[base.id] != escaped_schedue) {
                                    const offs = slots.items[schedules[base.id]].offset + off;
                                    const idx = std.sort.binarySearch(i64, alloc_offsets.items, offs, struct {
                                        pub fn inner(a: i64, b: i64) std.math.Order {
                                            return std.math.order(a, b);
                                        }
                                    }.inner).?;
                                    const su = Local.resolve(self, locals, idx, lo.data_type);
                                    self.subsume(su, lo, .intern);
                                }
                            }
                        }
                    }
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
                        utils.panic("{f}\n", .{child});
                    }

                    // either we arrived from the back branch or the other side of the split
                    if (states[schedules[child.id]].expand(locals.len).Join) |s| {
                        if (s.ctrl != child) utils.panic("{f} {} {f} {}\n", .{ s.ctrl, schedules[s.ctrl.id], child, schedules[child.id] });

                        if (child.kind == .Region) {
                            var lhs = s.items;
                            var rhs = locals;

                            if (child.inputs()[0] == bb) {
                                std.mem.swap([]Local, &lhs, &rhs);
                            }

                            const dest = locals;

                            for (lhs, rhs, dest, 0..) |l, r, *d, i| {
                                if (l == r) continue;

                                const lv = Local.resolve(self, lhs, i, .i64);
                                const rv = Local.resolve(self, rhs, i, .i64);

                                if (lv == rv) continue;

                                d.* = .compact(.{ .Node = self.addPhi(lv.sloc, child, lv, rv) });
                            }
                        } else {
                            for (s.items, locals, 0..) |clhs, crhs, i| {
                                var lhs = clhs.expand() orelse continue;
                                if (lhs == .Node and lhs.Node.isLazyPhi(s.ctrl)) {
                                    const rhs = crhs.expand() orelse Local.Expanded{
                                        .Node = self.addUninit(lhs.Node.sloc, lhs.Node.data_type),
                                    };

                                    if (rhs == .Loop and (rhs.Loop != s or s.ctrl.preservesIdentityPhys())) {
                                        unreachable;
                                    }

                                    if (rhs == .Node) {
                                        if (self.setInput(lhs.Node, 2, .intern, rhs.Node)) |nlhs| {
                                            lhs = .{ .Node = nlhs };
                                        }
                                    } else {
                                        const prev = lhs.Node.inputs()[1].?;
                                        self.subsume(prev, lhs.Node, .intern);
                                        lhs = .{ .Node = prev };
                                    }

                                    if (child.inputs()[0] == bb) unreachable;

                                    s.items[i] = .compact(lhs);
                                }
                            }
                        }
                        s.done = true;
                    } else {
                        // first time seeing, this ca also be a region, needs renaming I guess
                        const loop = tmp.arena.create(Local.Join);
                        loop.* = .{
                            .done = false,
                            .ctrl = child,
                            .items = tmp.arena.dupe(Local, locals),
                        };
                        if (child.kind == .Loop) {
                            std.debug.assert(child.kind == .Loop);
                            for (locals) |*l| {
                                if (l.expand() != null) {
                                    l.* = .compact(.{ .Loop = loop });
                                }
                            }
                        }
                        states[schedules[child.id]] = .compact(.{ .Join = loop });
                    }
                }
            }

            for (to_remove.items) |tr| {
                self.subsume(tr.mem(), tr, .intern);
            }

            if (graph.is_debug) {
                var worklist = Func.WorkList.init(tmp.arena.allocator(), self.next_id) catch unreachable;
                worklist.collectAll(self);

                for (worklist.items()) |node| {
                    if (!(node.kind != .Phi or node.inputs()[2] != null)) {
                        utils.panic("{f}", .{node});
                    }
                }
            }
        }
    };
}
