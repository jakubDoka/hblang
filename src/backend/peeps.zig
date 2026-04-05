const graph = @import("graph.zig");
const std = @import("std");
const utils = @import("utils-lib");
const DataType = graph.DataType;
const Builder = @import("Builder.zig");
const Machine = @import("Machine.zig");
const matcher = @import("graph.IdealGen");

pub fn Mixin(comptime Backend: type) type {
    return struct {
        const Self = @This();
        const Func = graph.Func(Backend);
        const Node = Func.Node;

        pub const WorkList = struct {
            list: std.ArrayList(*Node),
            in_list: std.DynamicBitSetUnmanaged,
            allocator: std.mem.Allocator,

            pub fn init(gpa: std.mem.Allocator, cap: usize) !WorkList {
                return .{
                    .list = try .initCapacity(gpa, cap),
                    .in_list = try .initEmpty(gpa, cap),
                    .allocator = gpa,
                };
            }

            pub fn add(self: *WorkList, node: *Node) void {
                errdefer unreachable;
                node.assertAlive();

                if (self.in_list.bit_length <= node.id) {
                    @branchHint(.unlikely);

                    try self.in_list.resize(
                        self.allocator,
                        try std.math.ceilPowerOfTwo(usize, node.id + 1),
                        false,
                    );
                }

                if (self.in_list.isSet(node.id)) return;

                self.in_list.set(node.id);
                try self.list.append(self.allocator, node);
            }

            pub fn pop(self: *WorkList) ?*Node {
                var node = self.list.pop() orelse return null;
                while (node.isDead()) {
                    node = self.list.pop() orelse return null;
                }
                self.in_list.unset(node.id);
                return node;
            }

            pub fn collectAll(self: *WorkList, func: *Func) void {
                self.add(func.end);
                self.add(func.start);
                var i: usize = 0;
                while (i < self.items().len) : (i += 1) {
                    const n = self.items()[i];
                    n.assertAlive();
                    for (n.inputs()) |oi| if (oi) |o| self.add(o);
                    for (n.outputs()) |o| self.add(o.get());
                }
            }

            pub fn items(self: *WorkList) []*Node {
                return self.list.items;
            }
        };

        pub fn isDead(node: ?*Node) bool {
            return node == null or node.?.data_type == .bot;
        }

        pub fn idealizeDead(
            ctx: *Backend,
            self: *Func,
            node: *Node,
            work: *WorkList,
        ) ?*Node {
            const inps = node.inputs();

            var is_dead = node.kind == .Region and
                for (inps) |i| {
                    if (!isDead(i)) break false;
                } else true;
            is_dead = is_dead or (node.kind != .Start and
                node.kind != .Region and
                node.kind != .TrapRegion and node.isCfg() and isDead(inps[0]));

            if (is_dead and node.kind == .Return and inps[0] != null) {
                work.add(inps[0].?);
                work.add(inps[1].?);
                self.setInputNoIntern(node, 0, null);
                self.setInputNoIntern(node, 1, null);
                for (3..node.inputs().len) |i| {
                    if (inps[i] == null) continue;
                    work.add(inps[i].?);
                    self.setInputNoIntern(node, i, null);
                }
                return null;
            }

            if (node.kind == .TrapRegion) {
                is_dead = true;
                for (node.inputs(), 0..) |*inp, i| {
                    if (inp.* != null and isDead(inp.*)) {
                        self.removeUse(inp.*.?, i, node);
                        inp.* = null;
                    }
                    is_dead = is_dead and isDead(inp.*);
                }

                retainNulls(node);

                if (is_dead) {
                    std.debug.assert(for (node.inputs()) |i| {
                        if (i != null) break false;
                    } else true);

                    self.setInputNoIntern(self.end, 2, null);
                }

                return null;
            }

            if (node.kind == .If and node.data_type != .bot and
                node.inputs()[1].?.kind != .CInt)
            {
                var cursor = node.cfg0();
                while (cursor.base.kind != .Entry and
                    cursor.base.kind != .Loop) : (cursor = cursor.idom())
                {
                    if (cursor.base.data_type == .bot) break;
                    if (cursor.base.kind != .Then and
                        cursor.base.kind != .Else) continue;

                    const if_node = cursor.base.inputs()[0].?;
                    if (if_node.kind != .If) continue;

                    if (if_node.inputs()[1].? == node.inputs()[1].?) {
                        self.setInputNoIntern(node, 1, self.addIntImm(
                            node.sloc,
                            .i8,
                            @intFromBool(cursor.base.kind == .Then),
                        ));
                        for (node.outputs()) |o| work.add(o.get());
                        return null;
                    }
                }
            }

            if (node.kind == .If and node.inputs()[1].?.kind == .CInt) {
                for (node.outputs()) |o| work.add(o.get());
            }

            if (node.kind == .If) merge_ifs: {
                const cond = node.inputs()[1].?;
                var phi = cond;
                if (cond.kind != .Phi) {
                    break :merge_ifs;
                }

                if (phi.inputs().len != 3) break :merge_ifs;

                const other_region = phi.inputs()[0].?;
                if (other_region.kind != .Region) break :merge_ifs;

                if (other_region != node.inputs()[0].?) break :merge_ifs;

                const lhs = phi.inputs()[1].?;
                if (lhs.kind != .CInt) break :merge_ifs;
                var reverse = false;
                if (lhs.extra(.CInt).value == 0) {
                    reverse = true;
                }

                const rhs = phi.inputs()[2].?;
                if (rhs.kind != .CInt) break :merge_ifs;
                if (!reverse and rhs.extra(.CInt).value != 0) break :merge_ifs;
                if (reverse and rhs.extra(.CInt).value == 0) break :merge_ifs;

                var tmp = utils.Arena.scrath(work.allocator.ptr);
                defer tmp.deinit();

                errdefer unreachable;

                var search_worklist = try WorkList.init(tmp.arena.allocator(), self.node_count);

                for (other_region.outputs()) |ro| {
                    if (ro.get().kind == .Phi) {
                        for (ro.get().outputs()) |o| {
                            search_worklist.add(o.get());
                        }
                    }
                }

                var schedule_then = try WorkList.init(tmp.arena.allocator(), self.node_count);
                var schedule_else = try WorkList.init(tmp.arena.allocator(), self.node_count);

                var i: usize = 0;
                while (i < search_worklist.items().len) : (i += 1) {
                    const n = search_worklist.items()[i];
                    if (n == node or n == cond) continue;
                    if (n.tryCfg0()) |cfg| {
                        if (node.outputs()[0].get().asCfg().?.dominates(cfg)) {
                            schedule_then.add(n);
                        } else if (node.outputs()[1].get().asCfg().?.dominates(cfg)) {
                            schedule_else.add(n);
                        } else if (n.kind == .Phi and &n.cfg0().idom().base == node) {
                            if (n.inputs().len != 3) break :merge_ifs;
                            schedule_then.add(n.inputs()[1].?);
                            schedule_else.add(n.inputs()[2].?);
                        } else {
                            break :merge_ifs;
                        }
                    } else {
                        for (n.outputs()) |o| {
                            if (o.get().kind == .Phi and o.get().cfg0().base.kind == .Loop) {
                                const block = o.get().cfg0().base.inputs()[o.pos() - 1].?.asCfg().?;
                                if (node.outputs()[0].get().asCfg().?.dominates(block)) {
                                    schedule_then.add(n);
                                } else if (node.outputs()[1].get().asCfg().?.dominates(block)) {
                                    schedule_else.add(n);
                                }
                                continue;
                            }

                            search_worklist.add(o.get());
                        }
                    }
                }

                const worklists = [2]*WorkList{ &schedule_then, &schedule_else };

                for (worklists) |schedule| {
                    i = 0;
                    while (i < schedule.items().len) : (i += 1) {
                        const n = schedule.items()[i];
                        for (n.inputs()[1..]) |j| {
                            if (j) |jj| {
                                if (search_worklist.in_list.isSet(jj.id)) {
                                    schedule.add(jj);
                                }
                            }
                        }
                    }
                }

                for (
                    worklists,
                    [2]*WorkList{ &schedule_else, &schedule_then },
                ) |a, b| {
                    for (a.items()) |ai| if (b.in_list.isSet(ai.id)) break :merge_ifs;
                }

                const swap = reverse;
                const left: usize = @intFromBool(swap);
                const right: usize = @intFromBool(!swap);

                for (tmp.arena.dupe(Node.Out, other_region.outputs())) |o| {
                    if (o.get().kind == .Phi) {
                        for (tmp.arena.dupe(Node.Out, o.get().outputs())) |oo| {
                            const side = if (oo.get().kind == .Phi and &oo.get().cfg0().idom().base == node)
                                o.get().inputs()[if (swap) 3 - oo.pos() else oo.pos() - 1].?
                            else if (schedule_then.in_list.isSet(oo.get().id))
                                o.get().inputs()[1 + left].?
                            else if (schedule_else.in_list.isSet(oo.get().id))
                                o.get().inputs()[1 + right].?
                            else {
                                std.debug.assert(oo.get() == node);
                                continue;
                            };

                            _ = self.setInput(oo.get(), oo.pos(), .intern, side);
                        }
                    }
                }

                self.subsume(other_region.inputs()[left].?, node.outputs()[0].get(), .intern);
                self.subsume(other_region.inputs()[right].?, node.outputs()[0].get(), .intern);
            }

            if (is_dead and node.data_type != .bot) {
                node.data_type = .bot;
                for (node.outputs()) |o| {
                    work.add(o.get());
                }
                return null;
            }

            if (node.kind == .Region) eliminate_branch: {
                var reachable_count: usize = 0;
                var last_reachable_branch: usize = 0;
                for (node.ordInps(), 0..) |in, i| {
                    if (isDead(in)) {
                        for (node.outputs()) |o| {
                            if (o.get().kind == .Phi) {
                                self.setInputNoIntern(o.get(), i + 1, null);
                            }
                        }
                        self.setInputNoIntern(node, i, null);
                    } else {
                        reachable_count += 1;
                        last_reachable_branch = i;
                    }
                }

                if (reachable_count == 0) {
                    node.data_type = .bot;
                    for (node.outputs()) |o| {
                        work.add(o.get());
                    }
                    break :eliminate_branch;
                }

                if (reachable_count == 1) {
                    var iter = std.mem.reverseIterator(node.outputs());
                    while (@as(?Node.Out, iter.next())) |ot| {
                        if (ot.get().kind == .Phi) {
                            const o = ot.get();
                            for (o.outputs()) |oo| work.add(oo.get());
                            self.subsume(o.inputs()[1 + last_reachable_branch].?, o, .intern);
                        }
                    }

                    return node.inputs()[last_reachable_branch].?;
                }

                retainNulls(node);
                for (node.outputs()) |o| {
                    if (o.get().kind == .Phi) {
                        retainNulls(o.get());
                    }
                }
            }

            if (node.kind == .Region) eliminate_if: {
                for (node.outputs()) |o| {
                    if (!o.get().isCfg()) break :eliminate_if;
                }

                if (node.inputs()[0].?.inputs()[0] ==
                    node.inputs()[1].?.inputs()[0])
                {
                    return node.inputs()[0].?.inputs()[0].?.inputs()[0];
                }
            }

            if (node.kind == .Region) join_regions: {
                const ordInps = node.ordInps();

                var tmp = utils.Arena.scrath(work.allocator.ptr);
                defer tmp.deinit();

                const lhs, const rhs = .{ ordInps[0].?, ordInps[ordInps.len - 1].? };
                if (lhs.kind == .Region) left_join: {
                    var phi_count: usize = 0;
                    for (node.outputs()) |o| {
                        if (o.get().kind == .Phi) {
                            const other_phi = o.get().inputs()[1].?;
                            if (other_phi.kind != .Phi) break :left_join;
                            if (other_phi.inputs()[0].? != lhs) break :left_join;
                            if (other_phi.outputs().len != 1) break :left_join;
                            phi_count += 1;
                        }
                    }

                    if (phi_count + 1 != lhs.outputs().len) break :left_join;

                    for (tmp.arena.dupe(Node.Out, node.outputs())) |o| {
                        if (o.get().kind == .Phi) {
                            leftJoin(self, o.get(), 1);
                        }
                    }

                    leftJoin(self, node, 0);
                    break :join_regions;
                }

                if (rhs.kind == .Region) right_join: {
                    var phi_count: usize = 0;
                    for (node.outputs()) |o| {
                        if (o.get().kind == .Phi) {
                            const other_phi = o.get().ordInps()[o.get().ordInps().len - 1].?;
                            if (other_phi.kind != .Phi) break :right_join;
                            if (other_phi.inputs()[0].? != rhs) break :right_join;
                            if (other_phi.outputs().len != 1) break :right_join;
                            phi_count += 1;
                        }
                    }

                    if (phi_count + 1 != rhs.outputs().len) break :right_join;

                    for (tmp.arena.dupe(Node.Out, node.outputs())) |o| {
                        if (o.get().kind == .Phi) {
                            rightJoin(self, o.get(), 1);
                        }
                    }

                    rightJoin(self, node, 0);

                    if (!rhs.isDead()) {
                        utils.panic("{f} {f}\n", .{ node, rhs });
                    }

                    break :join_regions;
                }
            }

            if (node.kind == .Loop) remove: {
                if (!isDead(node.inputs()[1])) break :remove;

                var iter = std.mem.reverseIterator(node.outputs());
                while (iter.next()) |ot| if (ot.get().kind == .Phi) {
                    const o = ot.get();
                    for (o.outputs()) |oo| work.add(oo.get());
                    work.add(o.inputs()[2].?);
                    self.subsume(o.inputs()[1].?, o, .intern);
                };

                return node.inputs()[0].?;
            }

            if (node.kind == .Then and node.inputs()[0].?.kind == .If) {
                const if_node = node.inputs()[0].?;
                const cond = if_node.inputs()[1].?;
                if (cond.kind == .CInt and cond.extra(.CInt).value != 0) {
                    if_node.data_type = .bot;
                    work.add(if_node.outputs()[1].get());
                    return if_node.inputs()[0].?;
                }
            }

            if (node.kind == .Else and node.inputs()[0].?.kind == .If) {
                const if_node = node.inputs()[0].?;
                const cond = if_node.inputs()[1].?;
                if (cond.kind == .CInt and cond.extra(.CInt).value == 0) {
                    if_node.data_type = .bot;
                    work.add(if_node.outputs()[0].get());
                    return if_node.inputs()[0].?;
                }
            }

            if (node.kind == .Store) {
                if (node.value().?.data_type.size() == 0) {
                    return node.mem();
                }
            }

            std.debug.assert(node.kind != .Load or node.data_type.size() != 0);

            if (node.kind == .Phi) {
                if (node.ordInps().len == 2) return inps[1].?;

                const is_same = for (inps[2..]) |i| {
                    if (i != inps[1]) {
                        break false;
                    }
                } else true;

                if (is_same and !node.cfg0().base.preservesIdentityPhys()) {
                    return inps[1].?;
                }

                if (node == inps[2]) {
                    std.debug.assert(inps[0].?.kind == .Loop);
                    return inps[1].?;
                }
            }

            if (node.kind == .MemCpy) {
                const ctrl = node.inputs()[0].?;
                var mem = node.inputs()[1].?;
                const dst = node.inputs()[2].?;
                const src = node.inputs()[3].?;
                const len = node.inputs()[4].?;

                if (len.kind == .CInt) {
                    const size = len.extra(.CInt).value;

                    forward: {
                        if (Backend == Builder) break :forward;

                        if (src.kind != .Local) {
                            break :forward;
                        }

                        if (src.inputs()[1].?.extra(.LocalAlloc).meta.kind != .variable) {
                            break :forward;
                        }

                        if (src.inputs()[1].?.outputs().len != 1) {
                            break :forward;
                        }

                        if (src.inputs()[1].?.extra(.LocalAlloc).size != size) {
                            break :forward;
                        }

                        if (dst.kind == .Local and dst.inputs()[1].?.extra(.LocalAlloc).meta.kind == .parameter) {
                            break :forward;
                        }

                        if (dst != dst.knownOffset()[0]) {
                            break :forward;
                        }

                        for (dst.outputs()) |o| {
                            if (o.get() != node) {
                                break :forward;
                            }
                        }

                        var found: usize = 0;
                        var cursor = mem;
                        var last_call: ?*Node = null;
                        while (cursor.kind == .Store or cursor.kind == .MemCpy) : (cursor = cursor.mem()) {
                            if (cursor.base().knownOffset()[0] == src) found += 1;

                            if (cursor.mem().kind == .Mem and cursor.mem().inputs()[0].?.kind == .CallEnd) {
                                last_call = cursor.mem().inputs()[0].?.inputs()[0].?;
                            }
                        }

                        var output_count: usize = 0;
                        for (src.outputs()) |o| {
                            if (o.get().kind == .BinOp) {
                                output_count += o.get().outputs().len;
                            } else {
                                if (o.get() == last_call) {
                                    last_call = null;
                                    continue;
                                }
                                output_count += 1;
                            }
                        }

                        if (found != output_count -| 1) {
                            break :forward;
                        }

                        self.subsume(dst, src, .intern);

                        return mem;
                    }

                    if (len.extra(.CInt).value <= 32) mimic_structure: {
                        const src_base, const src_offset = src.knownOffset();

                        if (src_base.kind != .Local or
                            src_base.inputs()[1].?.extra(.LocalAlloc).meta.kind == .parameter)
                        {
                            break :mimic_structure;
                        }

                        if (src_base.inputs()[1].?.outputs().len != 1) break :mimic_structure;

                        var tmp = utils.Arena.scrath(work.allocator.ptr);
                        defer tmp.deinit();

                        errdefer unreachable;

                        var mem_ops = std.ArrayList(*Node).empty;
                        for (src_base.outputs()) |o| {
                            if (o.get().kind == .BinOp) {
                                for (o.get().outputs()) |oo| {
                                    if (oo.get() == node) continue;
                                    if (!oo.get().isGoodMemOp(o.get())) {
                                        break :mimic_structure;
                                    }
                                    try mem_ops.append(tmp.arena.allocator(), oo.get());
                                }
                            } else {
                                if (o.get() == node) continue;
                                if (!o.get().isGoodMemOp(src_base)) {
                                    break :mimic_structure;
                                }
                                try mem_ops.append(tmp.arena.allocator(), o.get());
                            }
                        }

                        if (mem_ops.items.len > 6) break :mimic_structure;

                        const Slot = struct { offset: i64, dt: graph.DataType, base: graph.MemOp };
                        var slots = std.ArrayList(Slot).empty;
                        for (mem_ops.items) |use| {
                            _, const offs = use.base().knownOffset();

                            if (offs < 0 or @as(u64, @intCast(offs)) + use.accessTy().size() >
                                src_base.inputs()[1].?.extra(.LocalAlloc).size or use.accessTy().size() > 8)
                            {
                                break :mimic_structure;
                            }

                            for (slots.items) |off| {
                                if (off.offset >= offs + use.accessTy().size() or offs >= off.offset + off.dt.size()) {
                                    continue;
                                }

                                if (off.offset != offs or off.dt != use.accessTy()) {
                                    break :mimic_structure;
                                }

                                break;
                            } else {
                                try slots.append(tmp.arena.allocator(), .{
                                    .offset = @intCast(offs),
                                    .dt = use.accessTy(),
                                    .base = use.subclass(graph.MemOp).?.ext,
                                });
                            }
                        }

                        for (slots.items) |s| {
                            // TODO: we should do this upfront, but eh for now
                            if (s.offset < src_offset) continue;
                            if (s.offset - src_offset + s.dt.size() > size) continue;

                            const dst_off = self.addFieldOffset(node.sloc, dst, s.offset - src_offset);
                            const src_off = self.addFieldOffset(node.sloc, src, s.offset - src_offset);
                            const ld = self.addNode(.Load, node.sloc, s.dt, &.{ ctrl, mem, src_off }, .{ .base = s.base });
                            work.add(ld);
                            mem = self.addNode(.Store, node.sloc, s.dt, &.{ ctrl, mem, dst_off, ld }, .{ .base = s.base });
                            work.add(mem);
                        }

                        return mem;
                    }

                    if (len.extra(.CInt).value <= 16) {
                        var cursor: u64 = 0;
                        var copy_elem = DataType.i64;
                        const base = node.extra(.MemCpy).base.base;

                        while (cursor != size) {
                            while (cursor + copy_elem.size() > size) : (copy_elem =
                                @enumFromInt(@intFromEnum(copy_elem) - 1))
                            {}

                            const dst_off = self.addFieldOffset(node.sloc, dst, @intCast(cursor));
                            const src_off = self.addFieldOffset(node.sloc, src, @intCast(cursor));
                            const ld = self.addNode(.Load, node.sloc, copy_elem, &.{ ctrl, mem, src_off }, .{ .base = base });
                            work.add(ld);
                            mem = self.addNode(.Store, node.sloc, copy_elem, &.{ ctrl, mem, dst_off, ld }, .{ .base = base });
                            work.add(mem);

                            cursor += copy_elem.size();
                        }

                        return mem;
                    }
                }
            }

            if (Backend != Builder and node.kind == .Call and node.data_type != .bot) {
                if (@as(*Machine, &ctx.mach).out.getInlineFunc(
                    Backend,
                    node.extra(.Call).id,
                    true,
                )) |inline_func| {
                    if (inline_func.cost < 20 and self.node_count + inline_func.node_count < 5_000) {
                        inline_func.inliner.inlineInto(self, node, work);
                    }
                    return null;
                }
            }

            return null;
        }

        pub fn assertNoUnordered(node: *Node) void {
            std.debug.assert(std.mem.allEqual(
                ?*Node,
                node.input_base[node.input_ordered_len..node.input_len],
                null,
            ));
        }

        pub fn rightJoin(self: *Func, node: *Node, from: usize) void {
            assertNoUnordered(node);
            const idx = node.ordInps().len - 1;
            const other = node.ordInps()[idx].?;
            assertNoUnordered(other);
            for (other.ordInps()[from + 1 ..]) |i| {
                self.connectOrd(i.?, node);
            }
            _ = self.setInput(node, idx, .intern, other.ordInps()[from].?);
            std.debug.assert(other.isDead());
        }

        pub fn leftJoin(self: *Func, node: *Node, from: usize) void {
            assertNoUnordered(node);
            const other = node.inputs()[from].?;
            assertNoUnordered(other);
            for (node.inputs()[from + 1 ..]) |i| {
                self.connectOrd(i.?, other);
            }
            self.subsume(other, node, .intern);
        }

        pub fn idealize(
            ctx: *Backend,
            self: *Func,
            node: *Node,
            work: *WorkList,
        ) ?*Node {
            errdefer unreachable;

            if (idealizeDead(ctx, self, node, work)) |w| return w;

            if (node.data_type == .bot) return null;

            if (matcher.idealize(ctx, self, node, work)) |w| return w;

            var tmp = utils.Arena.scrath(work.allocator.ptr);
            defer tmp.deinit();

            const inps = node.inputs();

            if (node.kind == .Store) {
                if (node.outputs().len == 1) {
                    const succ = node.outputs()[0].get();
                    if (succ.kind == .Store and
                        succ.data_type == node.data_type and
                        succ.base() == node.base())
                    {
                        return node.mem();
                    }
                }

                const base, _ = node.base().knownOffset();

                if (base.kind == .Local and
                    base.inputs()[1].?.extra(.LocalAlloc).meta.kind == .variable)
                eliminate_stack: {
                    for (base.outputs()) |o| {
                        _ = o.get().knownStore(base) orelse {
                            break :eliminate_stack;
                        };
                    }

                    for (base.outputs()) |o| {
                        if (o.get().knownStore(base).? != node) {
                            work.add(o.get().knownStore(base).?);
                        }
                    }

                    return node.mem();
                }

                if (base.kind == .Local and node.outputs().len == 1 and
                    node.outputs()[0].get().kind == .Return)
                {
                    return node.mem();
                }

                if (base.kind == .Local and node.tryCfg0() != null) {
                    const dinps = tmp.arena.dupe(?*Node, node.inputs());
                    dinps[0] = null;
                    const st = self.addNode(
                        .Store,
                        node.sloc,
                        node.data_type,
                        dinps,
                        node.extra(.Store).*,
                    );
                    work.add(st);
                    return st;
                }
            }

            // pull loads up the memory chain with hope that they find a store
            // with the same addr and type to just use the value
            //
            if (node.kind == .Load) {
                var earlier = node.mem();
                const base, const base_offset = node.base().knownOffset();

                if (base.kind == .Local and node.tryCfg0() != null) {
                    const dinps = tmp.arena.dupe(?*Node, node.inputs());
                    dinps[0] = null;
                    const st = self.addNode(
                        .Load,
                        node.sloc,
                        node.data_type,
                        dinps,
                        node.extra(.Load).*,
                    );
                    work.add(st);
                    return st;
                }

                var op_count: usize = 0;
                var all_good = base.kind == .Local;
                for (base.outputs()) |b| {
                    if (b.get().kind == .BinOp) {
                        for (b.get().outputs()) |o| {
                            all_good = all_good and o.get().isGoodMemOp(base);
                            op_count += 1;
                        }
                    } else {
                        all_good = all_good and b.get().isGoodMemOp(base);
                        op_count += 1;
                    }
                }

                const fuel: usize = 4;
                var components: [fuel]*Node = undefined;
                var collected: usize = 0;
                //std.debug.assert(node.data_type.size() <= 8);
                for (0..fuel) |i| {
                    var climb_fuel: usize = if (i == 0) 2 else 1;
                    while (climb_fuel > 0 and (earlier.kind == .Store and
                        (earlier.tryCfg0() == node.tryCfg0() or
                            node.tryCfg0() == null) and
                        earlier.noAlias(node))) : (climb_fuel -= 1)
                    {
                        earlier = earlier.mem();
                    }

                    if (earlier.kind != .Store) break;

                    var advanced = false;

                    const earlier_ty = earlier.value().?.data_type;

                    const earlier_base, const earlier_offset = earlier.base().knownOffset();
                    if (base == earlier_base and earlier.value() != null) {
                        if (base_offset == earlier_offset) {
                            if (earlier_ty == node.data_type) {
                                if (i != 0) break;
                                return earlier.value().?;
                            }

                            if (node.data_type.isSubOf(earlier_ty)) {
                                if (i != 0) break;
                                return self.addUnOp(
                                    earlier.sloc,
                                    .ired,
                                    node.data_type,
                                    earlier.value().?,
                                );
                            }
                        }

                        if (base_offset == 0 and all_good and op_count < fuel + 1 and
                            node.data_type.isInt() and earlier_ty.isInt())
                        {
                            if (0 <= earlier_offset and earlier_offset +
                                earlier_ty.size() <= node.data_type.size())
                            {
                                components[collected] = earlier;
                                collected += 1;
                                advanced = true;
                                earlier = earlier.mem();
                            }
                        }
                    }

                    if (!advanced) break;

                    if (collected == op_count - 1) {
                        var prepared: [fuel]*Node = undefined;
                        for (components[0..collected], 0..) |c, j| {
                            const value = c.value().?;
                            const exp = self.addUnOp(value.sloc, .uext, node.data_type, value);
                            work.add(exp);
                            const shift_imm = self.addIntImm(value.sloc, node.data_type, c.base().knownOffset()[1] * 8);
                            prepared[j] = self.addBinOp(value.sloc, .ishl, node.data_type, exp, shift_imm);
                        }

                        for (prepared[1..collected]) |v| {
                            prepared[0] = self.addBinOp(v.sloc, .disjoint_or, node.data_type, prepared[0], v);
                        }

                        for (components[0..collected]) |v| {
                            self.subsume(v.mem(), v, .intern);
                        }

                        return prepared[0];
                    }
                }

                if (false and earlier != node.mem()) {
                    return self.addNode(
                        .Load,
                        node.sloc,
                        node.data_type,
                        &.{ inps[0], earlier, inps[2] },
                        .{},
                    );
                }
            }

            // Is this a single memcpy to a local that is only loaded from
            // that is also the last in the memory thread?
            //
            if (node.kind == .MemCpy) memcpy: {
                const mem = inps[1].?;
                const dst = inps[2].?;
                const src = inps[3].?;

                if (dst == src) {
                    return mem;
                }

                // If store happens after us, it could be a swap so be
                // pesimiztic
                //
                for (node.outputs()) |use| {
                    if (use.get().kind == .Call) break :memcpy;
                    if (if (use.get().knownMemOp()) |op|
                        !op[0].isLoad()
                    else
                        false) break :memcpy;
                }

                // We cause side effects if our dest is not .Local
                //
                if (dst.knownOffset()[0].kind != .Local) break :memcpy;

                // NOTE: if the size of the memcpy does not match, we do not
                // care since reading uninitialized memory is undefined
                // behavior

                const scanned = if (dst.kind == .BinOp)
                    dst.inputs()[1].?
                else
                    dst;
                for (scanned.outputs()) |use| {
                    if (if (use.get().knownMemOp()) |op| !op[0].isLoad() and
                        use.get() != node else true)
                    {
                        break :memcpy;
                    }
                }

                self.subsume(src, dst, .intern);

                return mem;
            }

            if (Backend != Builder and node.isLoad()) {
                const base, const offset = node.base().knownOffset();
                if (base.kind == .GlobalAddr) fold_const_read: {
                    const res = ctx.mach.out.readFromSym(
                        base.extra(.GlobalAddr).id,
                        offset + node.getStaticOffset(),
                        node.data_type.size(),
                        false,
                    ) orelse break :fold_const_read;

                    return switch (res) {
                        .value => |v| self
                            .addIntImm(node.sloc, node.data_type, v),
                        .global => |g| self.addGlobalAddr(node.sloc, g),
                        .func => |f| self.addFuncAddr(node.sloc, f),
                    };
                }
            }

            return if (comptime Func.optApi("idealize", Func.IdealSig(@TypeOf(ctx))))
                Backend.idealize(ctx, self, node, work)
            else
                null;
        }

        pub fn getGraph(self: *Self) *Func {
            return @alignCast(@fieldParentPtr("peeps", self));
        }

        pub fn retainNulls(node: *Node) void {
            var retain: usize = 0;
            for (node.inputs(), 0..) |a, i| {
                if (a != null) {
                    if (retain != i) {
                        const idx = a.?.posOfOutput(i, node);
                        node.inputs()[retain] = a;
                        a.?.outputs()[idx] = .init(node, retain, a);
                    }
                    retain += 1;
                }
            }
            node.input_len = @intCast(retain);
            node.input_ordered_len = @intCast(retain);
        }

        pub fn run(
            mix: *Self,
            ctx: *Backend,
            strategy: fn (*Backend, *Func, *Node, *WorkList) ?*Node,
        ) void {
            const self = mix.getGraph();

            self.gcm.cfg_built.assertUnlocked();

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            var worklist = WorkList.init(
                tmp.arena.allocator(),
                self.node_count,
            ) catch unreachable;
            worklist.collectAll(self);

            while (worklist.pop()) |t| {
                if (t.isDead()) continue;

                if (t.isLocked()) {
                    utils.panic("locked leftover: {f}", .{t});
                }

                if (t.outputs().len == 0 and t.isKillable()) {
                    for (t.inputs()) |ii| {
                        if (ii) |ia| worklist.add(ia);
                    }
                    self.uninternNode(t);
                    self.kill(t);

                    continue;
                }

                if (strategy(ctx, self, t, &worklist)) |nt| {
                    for (t.inputs()) |ii| {
                        if (ii) |ia| worklist.add(ia);
                    }
                    for (t.outputs()) |o| {
                        worklist.add(o.get());
                    }

                    nt.assertAlive();

                    self.subsume(nt, t, .intern);

                    continue;
                }
            }

            if (graph.is_debug) {
                var visited = std.DynamicBitSetUnmanaged
                    .initEmpty(tmp.arena.allocator(), self.node_count) catch unreachable;
                const f = self.collectPostorder(tmp.arena.allocator(), &visited);

                for (f) |v| {
                    for (v.base.outputs()) |o| {
                        if (o.get().isCfg()) break;
                    } else {
                        utils.panic("{f}", .{v});
                    }
                }
            }
        }
    };
}
