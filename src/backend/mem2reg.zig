const graph = @import("graph.zig");
const utils = graph.utils;
const std = @import("std");

pub fn Mem2RegMixin(comptime Backend: type) type {
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

            fn resolve(func: *Func, scope: []L, index: usize) *Node {
                return switch (scope[index].expand() orelse {
                    return func.addIntImm(.none, .i64, @bitCast(@as(u64, 0xaaaaaaaaaaaaaaaa)));
                }) {
                    .Node => |n| n,
                    .Loop => |loop| {
                        if (loop.items[index].expand() == null) {
                            const vl = func.addIntImm(.none, .i64, @bitCast(@as(u64, 0xaaaaaaaaaaaaaaaa)));
                            scope[index] = .compact(.{ .Node = vl });
                            return vl;
                        }
                        if (!loop.done) {
                            const initVal = resolve(func, loop.items, index);

                            if (!loop.items[index].expand().?.Node.isLazyPhi(loop.ctrl)) {
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

        const StackSlot = struct {
            offset: i64,
        };

        pub fn isGoodMemOp(self: *Node, local: *Node) bool {
            return (self.isStore() and !self.isSub(graph.MemCpy) and
                self.value() != local) or self.isLoad();
        }

        const Set = std.DynamicBitSetUnmanaged;
        const Arry = std.ArrayListUnmanaged;

        pub fn run(m2r: *Self) void {
            errdefer unreachable;

            const self = m2r.getGraph();
            self.gcm.cfg_built.assertUnlocked();

            if (self.root.outputs().len == 1) return;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var visited = try Set.initEmpty(tmp.arena.allocator(), self.next_id);
            const postorder = self.collectDfs(tmp.arena.allocator(), &visited)[1..];

            var slots = Arry(StackSlot){};
            var offset: i64 = 0;
            var offsets = Arry(packed struct(u64) { offset: u62, size: u2 }){};
            var store_load_nodes = Arry(*Node){};
            var alloc_offsets = Arry(i64){};

            //self.fmtUnscheduled(std.io.getStdErr().writer().any(), .escape_codes);
            std.debug.assert(self.root.outputs()[1].kind == .Mem);
            outer: for (self.root.outputs()[1].outputs()) |ov| {
                if (ov.kind != .LocalAlloc or ov.outputs().len != 1) continue :outer;
                const o = ov.outputs()[0];
                std.debug.assert(o.schedule == std.math.maxInt(u16));

                // collect all loads and stores, bail on something else
                //
                store_load_nodes.items.len = 0;
                for (o.outputs()) |use| {
                    if (use.kind == .BinOp and use.inputs()[2].?.kind == .CInt) {
                        for (use.outputs()) |use_use| {
                            if (isGoodMemOp(use_use, o)) {
                                try store_load_nodes.append(tmp.arena.allocator(), use_use);
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
                        if (off.offset <= offs and offs < off.offset + (@as(u64, 1) << off.size)) {
                            if (off.offset != offs or (@as(u64, 1) << off.size) != use.data_type.size()) {
                                continue :outer;
                            }
                            break;
                        }
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

                o.schedule = @intCast(slots.items.len);
                try slots.append(tmp.arena.allocator(), .{ .offset = offset });
                offset += @intCast(o.inputs()[1].?.extra(.LocalAlloc).size);
            }

            std.debug.assert(std.sort.isSorted(i64, alloc_offsets.items, {}, std.sort.asc(i64)));

            var locals = tmp.arena.alloc(Local, alloc_offsets.items.len);
            @memset(locals, .{});

            var states = tmp.arena.alloc(BBState, postorder.len);
            @memset(states, .{});

            for (postorder, 0..) |bb, i| bb.base.schedule = @intCast(i);

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
                for (parent.outputs()) |o| parent_succs += @intFromBool(o.isCfg());
                if (!(parent_succs >= 1 and parent_succs <= 2)) utils.panic("{}\n", .{bb});
                // handle fork
                if (parent_succs == 2) {
                    // this is the second branch, restore the value
                    if (states[parent.schedule].expand(locals.len).Fork) |s| {
                        locals = s.saved;
                    } else {
                        // we will visit this eventually
                        states[parent.schedule] = .compact(.{ .Fork = .{ .saved = tmp.arena.dupe(Local, locals) } });
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
                    //std.debug.print("bb {}\n", .{bb});
                    for (bb.outputs()) |use| {
                        if (use.isCfg()) {
                            //std.debug.print("use {}\n", .{use});
                            //if (use.kind == .If) {
                            //    std.debug.print("use if {?}\n", .{use.inputs()[1]});
                            //}
                            buf[len] = use;
                            scheds[len] = use.schedule;
                            len += 1;
                        }
                    }

                    if (bb.isBasicBlockStart()) {
                        @TypeOf(self.gcm).scheduleBlock(bb);
                    }

                    if (!(bb.kind == .If or len == 1)) {
                        self.fmtUnscheduled(std.io.getStdErr().writer().any(), .escape_codes);
                        unreachable;
                    }

                    for (buf[0..len], scheds[0..len]) |n, s| n.schedule = s;
                }

                for (tmp.arena.dupe(*Node, bb.outputs())) |o| {
                    if (o.id == std.math.maxInt(u16)) continue;
                    std.debug.assert(bb.kind != .Local);

                    if (o.isStore()) {
                        const base, const off = o.base().knownOffset();
                        if (base.kind == .Local and base.schedule != std.math.maxInt(u16)) {
                            try to_remove.append(tmp.arena.allocator(), o);
                            const offs = slots.items[base.schedule].offset + off;
                            const idx = std.sort.binarySearch(i64, alloc_offsets.items, offs, struct {
                                pub fn inner(a: i64, b: i64) std.math.Order {
                                    return std.math.order(a, b);
                                }
                            }.inner) orelse {
                                utils.panic("{} {any} {}", .{ o, alloc_offsets.items, offs });
                            };
                            locals[idx] = .compact(.{ .Node = o.value().? });
                        }
                    }

                    if (o.kind == .Phi or o.kind == .Mem or o.isStore()) {
                        for (tmp.arena.dupe(*Node, o.outputs())) |lo| {
                            if (lo.isLoad()) {
                                const base, const off = lo.base().knownOffset();
                                if (base.kind == .Local and base.schedule != std.math.maxInt(u16)) {
                                    const offs = slots.items[base.schedule].offset + off;
                                    const idx = std.sort.binarySearch(i64, alloc_offsets.items, offs, struct {
                                        pub fn inner(a: i64, b: i64) std.math.Order {
                                            return std.math.order(a, b);
                                        }
                                    }.inner).?;
                                    const su = Local.resolve(self, locals, idx);
                                    self.subsume(su, lo);
                                }
                            }
                        }
                    }
                }

                const child: *Node = for (bb.outputs()) |o| {
                    if (o.isCfg()) break o;
                } else continue;
                var child_preds: usize = 0;
                for (child.inputs()) |b| child_preds += @intFromBool(b != null and b.?.isCfg());
                std.debug.assert((child_preds >= 1 and child_preds <= 2) or child.kind == .TrapRegion);
                // handle joins
                if (child_preds == 2 and child.kind != .TrapRegion and child.kind != .Return) {
                    if (!(child.kind == .Region or child.kind == .Loop)) {
                        utils.panic("{}\n", .{child});
                    }
                    // eider we arrived from the back branch or the other side of the split
                    if (states[child.schedule].expand(locals.len).Join) |s| {
                        if (s.ctrl != child) utils.panic("{} {} {} {}\n", .{ s.ctrl, s.ctrl.schedule, child, child.schedule });
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
                                    self.uninternNode(lhs.Node);
                                    std.mem.reverse(?*Node, lhs.Node.inputs()[1..3]);
                                    if (self.reinternNode(lhs.Node)) |v| lhs = .{ .Node = v };
                                }

                                s.items[i] = .compact(lhs);
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
