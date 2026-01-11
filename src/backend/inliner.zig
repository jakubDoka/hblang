const std = @import("std");
const graph = @import("graph.zig");
const Machine = @This();
const utils = graph.utils;
const Set = std.DynamicBitSetUnmanaged;

pub fn Mixin(comptime Backend: type) type {
    return struct {
        pub fn cloneNodes(
            start: *graph.FuncNode(Backend),
            end: *graph.FuncNode(Backend),
            node_count: usize,
            arena: *std.heap.ArenaAllocator,
            already_present: usize,
            scrath: *utils.Arena,
        ) struct {
            new_node_table: []*graph.FuncNode(Backend),
            new_nodes: []*graph.FuncNode(Backend),
        } {
            errdefer unreachable;

            const Func = graph.Func(Backend);

            var tmp = utils.Arena.scrath(scrath);
            defer tmp.deinit();

            const new_node_table = scrath.alloc(*Func.Node, node_count);
            var new_nodes = scrath.makeArrayList(*Func.Node, node_count);

            var work = try Func.WorkList.init(tmp.arena.allocator(), node_count);
            work.add(start);
            work.add(end);
            var i: usize = 0;
            while (i < work.items().len) : (i += 1) {
                const node = work.items()[i];
                for (node.outputs()) |o| work.add(o.get());
                for (node.inputs()) |inp| if (inp != null) work.add(inp.?);

                const node_size = node.size();
                const new_slot = try arena.allocator()
                    .alignedAlloc(u8, .of(Func.Node), node_size);
                @memcpy(new_slot, @as([*]const u8, @ptrCast(node)));
                const new_node: *Func.Node = @ptrCast(new_slot);

                if (new_node.input_len != new_node.input_ordered_len) {
                    new_node.input_len = @intCast(std.mem.indexOfScalarPos(
                        ?*Func.Node,
                        node.inputs(),
                        new_node.input_ordered_len,
                        null,
                    ) orelse new_node.input_len);

                    std.debug.assert(new_node.input_len >= new_node.input_ordered_len);
                }

                if (new_node.asCfg()) |cfg| cfg.ext.idepth = 0;
                if (new_node.subclass(graph.builtin.Call)) |call|
                    call.ext.signature = call.ext.signature.dupe(arena.allocator());
                if (new_node.isSub(graph.If) and already_present != 0) new_node.sloc = .none;

                new_node.input_base = (try arena.allocator()
                    .dupe(?*Func.Node, new_node.inputs())).ptr;
                new_node.output_base = (try arena.allocator()
                    .dupe(Func.Node.Out, new_node.outputs())).ptr;
                new_node_table[new_node.id] = new_node;
                new_node.id = @intCast(already_present + i);
                new_node.output_cap = new_node.output_len;
                new_nodes.appendAssumeCapacity(new_node);
            }

            // remap inputs and outputs
            for (new_nodes.items) |node| {
                for (node.inputs()) |*inp| if (inp.* != null) {
                    inp.* = new_node_table[inp.*.?.id];
                };

                for (node.outputs()) |*out| {
                    out.* = .init(new_node_table[out.get().id], out.pos(), null);
                }

                if (node.subclass(graph.Region)) |cfg| {
                    if (cfg.ext.cached_lca != null) {
                        const lca: *Func.Node = @ptrCast(cfg.ext.cached_lca.?);
                        if (!lca.isSub(graph.If) or lca.subclass(graph.If).?.ext.id != node.id) {
                            cfg.ext.cached_lca = null;
                        } else {
                            cfg.ext.cached_lca = new_node_table[lca.id];
                        }
                    }
                }
            }

            for (new_nodes.items) |n| {
                std.debug.assert(n.id < already_present + i);
                std.debug.assert(n.id >= already_present);
            }

            return .{
                .new_node_table = new_node_table,
                .new_nodes = new_nodes.items,
            };
        }

        pub fn internBatch(
            start: *graph.FuncNode(Backend),
            end: *graph.FuncNode(Backend),
            already_present: usize,
            into: *graph.Func(Backend),
            new_nodes: []*graph.FuncNode(Backend),
        ) void {
            errdefer unreachable;

            const Func = graph.Func(Backend);

            var tmp = utils.Arena.scrath(null);
            defer tmp.deinit();

            const node_count = new_nodes.len;

            var interned = try Set.initEmpty(
                tmp.arena.allocator(),
                already_present + node_count,
            );
            var work = try Func.WorkList.init(tmp.arena.allocator(), node_count);
            work.add(start);
            work.add(end);

            var deffered_phi_stack = std.ArrayList(*Func.Node){};

            while (work.pop()) |node| {
                if (node.id < already_present) {
                    // NOTE: this can happen, dont ask me how
                    continue;
                }
                if (interned.isSet(node.id)) continue;

                if (Func.Node.isInterned(node.kind, node.inputs())) {
                    var ready = true;
                    for (node.outputs()) |us| {
                        const use = us.get();
                        if (use != node and
                            Func.Node.isInterned(use.kind, use.inputs()) and
                            !interned.isSet(use.id))
                        {
                            work.add(use);
                            ready = false;
                        }
                    }
                    if (node.kind == .Phi and node.inputs()[0].?.kind == .Loop) {
                        if (std.mem.indexOfScalar(
                            *Func.Node,
                            deffered_phi_stack.items,
                            node,
                        )) |idx| {
                            // we have a cycle so just intern
                            _ = deffered_phi_stack.swapRemove(idx);
                            ready = true;
                        } else {
                            try deffered_phi_stack.append(tmp.arena.allocator(), node);
                        }
                    }

                    if (!ready) continue;

                    interned.set(node.id);
                    const slot = into.internNode(
                        node.kind,
                        node.data_type,
                        node.inputs(),
                        node.anyextra(),
                    );
                    if (slot.found_existing) {
                        into.subsumeNoIntern(slot.key_ptr.node, node, .intern);
                    } else {
                        slot.key_ptr.node = node;
                        for (node.inputs()) |on| if (on) |n| {
                            work.add(n);
                        };
                    }
                } else {
                    interned.set(node.id);

                    for (node.inputs()) |on| if (on) |n| {
                        work.add(n);
                    };

                    for (node.outputs()) |o| work.add(o.get());
                }
            }

            for (new_nodes) |nn| if (!nn.isDead()) {
                std.debug.assert(interned.isSet(nn.id));
            };
        }

        pub fn inlineInto(
            inln: *const @This(),
            func: *graph.Func(Backend),
            dest: *graph.Func(Backend).Node,
            func_work: *graph.Func(Backend).WorkList,
        ) void {
            errdefer unreachable;

            const self: *const graph.Func(Backend) =
                @alignCast(@fieldParentPtr("inliner", inln));

            func.gcm.loop_tree_built.assertUnlocked();

            const Func = graph.Func(Backend);

            const arena = &func.arena;
            const self_start: *Func.Node = self.start;
            const self_end: *Func.Node = self.end;

            const prev_next_id = func.next_id;

            var tmp = utils.Arena.scrath(func_work.allocator.ptr);
            defer tmp.deinit();

            const cloned = cloneNodes(
                self_start,
                self_end,
                self.next_id,
                arena,
                func.next_id,
                tmp.arena,
            );

            func.next_id += @intCast(cloned.new_nodes.len);

            const end = cloned.new_node_table[self_end.id];
            const start = cloned.new_node_table[self_start.id];

            internBatch(start, end, prev_next_id, func, cloned.new_nodes);

            const entry = start.outputs()[0].get();
            std.debug.assert(entry.kind == .Entry);

            const entry_mem: ?*Func.Node = for (start.outputs()) |o| {
                if (o.get().kind == .Mem) break o.get();
            } else null;
            var exit_mem = end.inputs()[1];

            const entry_syms: ?*Func.Node = for (start.outputs()) |o| {
                if (o.get().kind == .Syms) break o.get();
            } else null;

            const into_entry_mem = func.start.outputs()[1].get();
            std.debug.assert(into_entry_mem.kind == .Mem);

            const into_entry_syms = func.start.outputs()[2].get();
            std.debug.assert(into_entry_syms.kind == .Syms);

            const call_end = dest.outputs()[0].get();
            std.debug.assert(call_end.kind == .CallEnd);

            var after_entry: *Func.Node = for (entry.outputs()) |o| {
                if (o.get().isCfg() and o.get().data_type != .bot) break o.get();
            } else unreachable;
            std.debug.assert(after_entry.isBasicBlockEnd() or
                after_entry.kind == .Region or after_entry.kind == .Loop);
            std.debug.assert(after_entry.kind != .Entry);
            std.debug.assert(after_entry.kind != .Start);

            const before_return = end.inputs()[0];
            std.debug.assert(before_return == null or before_return.?.isBasicBlockStart());

            const before_dest = dest.inputs()[0].?;
            std.debug.assert(before_dest.isBasicBlockStart());

            const call_end_entry_mem = for (call_end.outputs()) |o| {
                if (o.get().kind == .Mem) break o.get();
            } else null;

            const dest_mem = dest.inputs()[1].?;

            if (entry_mem != null) {
                for (tmp.arena.dupe(Func.Node.Out, entry_mem.?.outputs())) |use| {
                    if (use.get().kind == .LocalAlloc) {
                        func.setInputNoIntern(use.get(), 0, into_entry_mem);
                    }
                }
            }

            if (entry_syms) |syms| {
                func.subsume(into_entry_syms, syms, .intern);
            }

            // NOTE: not scheduled yet so args are on the Start
            //
            for (dest.dataDeps(), 0..) |dep, j| {
                for (start.outputs()) |n| {
                    const o = n.get();
                    if (o.kind == .Arg and o.extra(.Arg).index == j) {
                        func.subsume(dep, o, .intern);
                        break;
                    }
                    if (o.kind == .StructArg and o.extra(.StructArg).base.index == j) {
                        // we need to copy to preserve the semantics of a call
                        // TODO: decide if we need this based on the call
                        // convention of the inlined function since the default
                        // call convention should be a bit customized
                        //
                        const sarg = o.extra(.StructArg);
                        const alloc = func.addNode(
                            .LocalAlloc,
                            o.sloc,
                            .i64,
                            &.{ null, into_entry_mem },
                            .{ .size = sarg.spec.size, .debug_ty = sarg.debug_ty },
                        );
                        const copy = func.addNode(.Local, o.sloc, .i64, &.{ null, alloc }, .{});
                        func.subsume(copy, dep, .intern);
                        func.subsume(copy, o, .intern);
                        break;
                    }
                }
            }

            if (end.inputs()[0] != null)
                for (end.dataDeps(), 0..) |dep, j| {
                    const ret = for (call_end.outputs()) |o| {
                        if (o.get().kind == .Ret and o.get().extra(.Ret).index == j) break o.get();
                    } else continue;
                    func.subsume(dep, ret, .intern);
                };

            if (entry_mem == exit_mem) {
                if (entry_mem != null) {
                    // NOTE: this is still needed since there can be loads
                    func.subsume(dest_mem, entry_mem.?, .intern);
                }
                if (call_end_entry_mem != null) {
                    func.subsume(dest_mem, call_end_entry_mem.?, .intern);
                }
                exit_mem = dest_mem;
            } else {
                func.subsume(dest_mem, entry_mem.?, .intern);
                if (call_end_entry_mem != null) {
                    func.subsume(exit_mem orelse dest_mem, call_end_entry_mem.?, .intern);
                }
            }

            if (exit_mem) |em| {
                for (em.outputs()) |o| {
                    func_work.add(o.get());
                }
            }

            func.subsume(before_dest, entry, .intern);

            if (end.inputs()[2]) |trap_region| {
                if (func.end.inputs()[2] == null) {
                    func.setInputNoIntern(func.end, 2, func.addNode(.TrapRegion, .none, .top, &.{}, .{}));
                }
                const dest_trap_region = func.end.inputs()[2].?;

                for (trap_region.inputs()) |inp| {
                    func.connect(inp.?, dest_trap_region);
                }
            }

            if (after_entry.kind == .Return) {
                func.subsume(before_dest, call_end, .intern);
            } else if (before_return != null) {
                func.subsume(before_return.?, call_end, .intern);
            } else {
                func_work.add(call_end);
            }
            dest.data_type = .bot;
            func_work.add(dest);

            func.kill(end);

            for (cloned.new_nodes) |nn| if (!nn.isDead()) {
                func_work.add(nn);
            };
        }
    };
}
