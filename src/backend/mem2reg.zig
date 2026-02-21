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

            fn resolve(func: *Func, scope: []L, index: usize) *Node {
                return switch (scope[index].expand() orelse {
                    return func.addUninit(.none, .i64);
                }) {
                    .Node => |n| n,
                    .Loop => |loop| {
                        if (loop.items[index].expand() == null) {
                            unreachable;
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
                        } else {
                            _ = resolve(func, loop.items, index);
                        }
                        scope[index] = loop.items[index];

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

        pub const Ctx = struct {
            slot_ids: []u32,
            locals: []Local,
            states: []BBState,
            visited: Set,

            pub fn lookupOffset(ctx: *Ctx, base: *Node, off: i64) usize {
                const offs = ctx.slots[ctx.slot_ids[base.id]].offset + off;
                return std.sort.binarySearch(i64, ctx.alloc_offsets, offs, struct {
                    pub fn inner(a: i64, b: i64) std.math.Order {
                        return std.math.order(a, b);
                    }
                }.inner).?;
            }
        };

        pub fn run(m2r: *Self) void {
            errdefer unreachable;

            const self = m2r.getGraph();
            self.gcm.cfg_built.assertUnlocked();

            const mem = self.getMem() orelse return;

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const escaped_schedue = std.math.maxInt(u32);

            const slot_ids = tmp.arena.alloc(u32, self.next_id);
            @memset(slot_ids, escaped_schedue);

            var alloc_offset_count: usize = 0;

            {
                var offsets = Arry(packed struct(u64) { offset: u62, size: u2 }){};
                var store_load_nodes = Arry(*Node){};

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
                    for (store_load_nodes.items, 0..) |use, i| {
                        _, const offs = use.base().knownOffset();
                        // don't touch this and leave the static analysis report the soob
                        //
                        if (offs < 0 or @as(u64, @intCast(offs)) + use.data_type.size() >
                            // TODO: we ignore elems > 8 for now but we will want mem2reg to work on
                            // vectors eventually
                            o.inputs()[1].?.extra(.LocalAlloc).size or use.data_type.size() > 8)
                        {
                            for (store_load_nodes.items[0..i]) |us| slot_ids[us.id] = escaped_schedue;
                            continue :outer;
                        }

                        const idx = for (offsets.items, 0..) |off, j| {
                            if (off.offset > offs + use.data_type.size() or offs >= off.offset + (@as(u64, 1) << off.size)) {
                                continue;
                            }

                            if (off.offset != offs or (@as(u64, 1) << off.size) != use.data_type.size()) {
                                for (store_load_nodes.items[0..i]) |us| slot_ids[us.id] = escaped_schedue;
                                continue :outer;
                            }

                            break j;
                        } else b: {
                            try offsets.append(tmp.arena.allocator(), .{
                                .offset = @intCast(offs),
                                .size = @intCast(std.math.log2_int(u64, use.data_type.size())),
                            });
                            break :b offsets.items.len - 1;
                        } + alloc_offset_count;

                        slot_ids[o.id] = @intCast(idx);
                    }

                    alloc_offset_count += offsets.items.len;
                }
            }

            var ctx = Ctx{
                .slot_ids = slot_ids,
                .locals = tmp.arena.alloc(Local, alloc_offset_count),
                .states = tmp.arena.alloc(BBState, self.next_id),
                .visited = try Set.initEmpty(tmp.arena.allocator(), self.next_id),
            };

            @memset(ctx.locals, .{});
            @memset(ctx.states, .{});

            const postorder = self.collectDfs(tmp.arena.allocator(), &ctx.visited)[1..];

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
                    if (ctx.states[parent.id].expand(ctx.locals.len).Fork) |s| {
                        ctx.locals = s.saved;
                    } else {
                        // we will visit this eventually
                        ctx.states[parent.id] = .compact(.{ .Fork = .{
                            .saved = tmp.arena.dupe(Local, ctx.locals),
                        } });
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

                    var should_remove = false;

                    if (o.isStore()) {
                        const idx = ctx.slot_ids[o.id];
                        if (idx != escaped_schedue) {
                            ctx.locals[idx] = .compact(.{ .Node = o.value().? });
                            should_remove = true;
                        }
                    }

                    if (o.kind == .Phi or o.kind == .Mem or o.isStore()) {
                        for (stmp.arena.dupe(Node.Out, o.outputs())) |no| {
                            const lo = no.get();
                            if (lo.isLoad()) {
                                const idx = ctx.slot_ids[o.id];
                                if (idx != escaped_schedue) {
                                    const su = Local.resolve(self, ctx.locals, idx);
                                    self.subsume(su, lo, .intern);
                                }
                            }
                        }
                    }

                    if (should_remove) {
                        const vl = o.value().?;
                        vl.lockTmp();
                        self.subsume(o.mem(), o, .intern);
                        vl.unlockTmp();
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
                    if (ctx.states[child.id].expand(ctx.locals.len).Join) |s| {
                        if (s.ctrl != child) utils.panic(
                            "{f} {} {f} {}\n",
                            .{ s.ctrl, ctx.slot_ids[s.ctrl.id], child, ctx.slot_ids[child.id] },
                        );

                        if (child.kind == .Region) {
                            var lhs = s.items;
                            var rhs = ctx.locals;

                            if (child.inputs()[0] == bb) {
                                std.mem.swap([]Local, &lhs, &rhs);
                            }

                            const dest = ctx.locals;

                            for (lhs, rhs, dest, 0..) |l, r, *d, i| {
                                if (l == r) continue;

                                const lv = Local.resolve(self, lhs, i);
                                const rv = Local.resolve(self, rhs, i);

                                if (lv == rv) continue;

                                d.* = .compact(.{ .Node = self.addPhi(lv.sloc, child, lv, rv) });
                            }
                        } else {
                            for (s.items, ctx.locals, 0..) |clhs, crhs, i| {
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
                            .items = tmp.arena.dupe(Local, ctx.locals),
                        };
                        if (child.kind == .Loop) {
                            std.debug.assert(child.kind == .Loop);
                            for (ctx.locals) |*l| {
                                if (l.expand() != null) {
                                    l.* = .compact(.{ .Loop = loop });
                                }
                            }
                        }
                        ctx.states[child.id] = .compact(.{ .Join = loop });
                    }
                }
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
