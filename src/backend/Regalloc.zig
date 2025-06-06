const std = @import("std");
const utils = graph.utils;
const graph = @import("graph.zig");

pub fn ralloc(comptime Mach: type, func: *graph.Func(Mach)) []u16 {
    func.gcm.cfg_built.assertLocked();

    const Fn = graph.Func(Mach);

    const Set = std.DynamicBitSetUnmanaged;
    const Block = struct {
        start: *Fn.Node = undefined,
        end: *Fn.Node = undefined,
        liveins: Set,
        liveouts: Set,
        defs: Set,
        uses: Set,

        pub fn setMasks(s: Set) []Set.MaskInt {
            return s.masks[0 .. (s.bit_length + @bitSizeOf(Set.MaskInt) - 1) / @bitSizeOf(Set.MaskInt)];
        }
    };

    const Instr = struct {
        def: *Fn.Node = undefined,
        preds: []const *Fn.Node = undefined,
        succ: []const *Fn.Node = undefined,
        liveins: Set,
        liveouts: Set,
        defs: Set,
        uses: Set,

        pub fn isBasicBlock(k: Fn.NodeKind) bool {
            std.debug.assert(Fn.isCfg(k));
            return switch (k) {
                .Entry => true,
                else => false,
            };
        }

        pub fn setMasks(s: Set) []Set.MaskInt {
            return s.masks[0 .. (s.bit_length + @bitSizeOf(Set.MaskInt) - 1) / @bitSizeOf(Set.MaskInt)];
        }
    };

    var tmp = utils.Arena.scrath(null);
    defer tmp.deinit();

    const instrs = tmp.arena.alloc(Instr, func.instr_count);

    // TODO: we can clean this up: arena should contruct the bitset
    for (instrs) |*b| {
        b.* = .{
            .liveins = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
            .liveouts = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
            .defs = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
            .uses = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable,
        };
    }

    for (func.gcm.postorder) |bb| {
        const node = &bb.base;
        for (node.outputs(), 0..) |c, i| {
            instrs[c.schedule].def = c;

            if (i + 1 < node.outputs().len) {
                instrs[c.schedule].succ = node.outputs()[i + 1 ..][0..1];
            } else if (c.kind != .Trap) {
                instrs[c.schedule].succ = c.outputs();
            } else {
                instrs[c.schedule].succ = &.{};
            }

            if (i == 0) {
                instrs[c.schedule].preds = @ptrCast(bb.base.inputs());
            } else {
                instrs[c.schedule].preds = node.outputs()[i - 1 ..][0..1];
            }
        }
    }

    var work_list = std.ArrayListUnmanaged(u16).initBuffer(tmp.arena.alloc(u16, instrs.len));
    var in_work_list = std.DynamicBitSetUnmanaged.initEmpty(tmp.arena.allocator(), instrs.len) catch unreachable;

    {
        var i: u16 = @intCast(instrs.len);
        var iter = std.mem.reverseIterator(instrs);
        while (iter.nextPtr()) |instr_| {
            const instr: *Instr = instr_;
            i -= 1;
            var is_used = false;
            if (instr.def.outputs().len != 0 and instr.def.kind != .MachMove and (!instr.def.isStore() or instr.def.kind == .MemCpy) and
                instr.def.kind != .Mem and !instr.def.isCfg() and (instr.def.kind != .Phi or instr.def.isDataPhi()))
            {
                is_used = true;
                instr.defs.set(i);
            }

            if (instr.def.kind == .Call) {
                is_used = true;
                instr.liveouts.set(i);
            }

            if (instr.def.kind == .Phi) continue;
            for (instr.def.dataDeps()) |use| if (use) |uuse| {
                is_used = true;
                instr.uses.set(uuse.schedule);
            };

            if (is_used) {
                if (!in_work_list.isSet(i)) {
                    in_work_list.set(i);
                    work_list.appendAssumeCapacity(i);
                }
            }
        }
    }

    // compute liveins and liveouts

    while (work_list.pop()) |task| {
        in_work_list.unset(task);
        const i = instrs[task];
        var changed: Set.MaskInt = 1;
        while (changed != 0) {
            changed = 0;
            for (
                Block.setMasks(i.liveins),
                Block.setMasks(i.liveouts),
                Block.setMasks(i.uses),
                Block.setMasks(i.defs),
            ) |*livein, *liveout, use, def| {
                const previ = livein.*;
                livein.* = use | (liveout.* & ~def);

                changed |= (previ ^ livein.*);
            }

            if (changed != 0) {
                for (i.preds) |p| {
                    if (!in_work_list.isSet(p.schedule)) {
                        in_work_list.set(p.schedule);
                        work_list.appendAssumeCapacity(p.schedule);
                    }
                }
            }

            for (i.succ) |bo| {
                var sub_changed: Set.MaskInt = 0;
                const schedule = if (bo.isCfg() and bo.isBasicBlockStart()) bo.outputs()[0].schedule else bo.schedule;
                for (
                    Block.setMasks(i.liveouts),
                    Block.setMasks(instrs[schedule].liveins),
                ) |*live_outs, succ_livein| {
                    const prevo = live_outs.*;
                    live_outs.* |= succ_livein;
                    sub_changed |= (prevo ^ live_outs.*);
                }

                if (sub_changed != 0) {
                    if (!in_work_list.isSet(schedule)) {
                        in_work_list.set(schedule);
                        work_list.appendAssumeCapacity(schedule);
                    }
                }

                changed |= sub_changed;
            }
        }
    }

    if (std.debug.runtime_safety) {
        var changed: Set.MaskInt = 1;
        while (changed != 0) {
            changed = 0;

            var ite = std.mem.reverseIterator(instrs);
            while (ite.next()) |i| {
                for (
                    Block.setMasks(i.liveins),
                    Block.setMasks(i.liveouts),
                    Block.setMasks(i.uses),
                    Block.setMasks(i.defs),
                ) |*livein, *liveout, use, def| {
                    const previ = livein.*;
                    livein.* = use | (liveout.* & ~def);

                    changed |= (previ ^ livein.*);
                }

                for (i.succ) |bo| {
                    const schedule = if (bo.isCfg() and bo.isBasicBlockStart()) bo.outputs()[0].schedule else bo.schedule;
                    for (
                        Block.setMasks(i.liveouts),
                        Block.setMasks(instrs[schedule].liveins),
                    ) |*live_outs, succ_livein| {
                        const prevo = live_outs.*;
                        live_outs.* |= succ_livein;
                        changed |= (prevo ^ live_outs.*);
                    }
                }
            }

            std.debug.assert(changed == 0);
        }
    }

    for (instrs) |*i| {
        for (Block.setMasks(i.liveins), Block.setMasks(i.uses)) |a, b| {
            std.debug.assert(b & ~a == 0);
        }
    }

    for (func.gcm.postorder) |bb| {
        for (bb.base.outputs()) |o| {
            if (o.kind == .Phi) continue;
            for (o.dataDeps()) |i| if (i) |ii| {
                std.debug.assert(instrs[o.schedule].liveins.isSet(ii.schedule));
            };
        }
    }

    // build interference => very wastefull
    const interference_table = tmp.arena.alloc(Set, func.instr_count);
    for (interference_table) |*r| r.* = Set.initEmpty(tmp.arena.allocator(), func.instr_count) catch unreachable;

    for (instrs) |*ins| {
        var iter = ins.defs.iterator(.{});
        while (iter.next()) |i| {
            interference_table[i].setUnion(ins.liveouts);
        }
    }

    for (interference_table, 0..) |it_row, j| {
        var iter = it_row.iterator(.{});
        while (iter.next()) |i| {
            interference_table[i].set(j);
        }
    }

    const sentinel = std.math.maxInt(u16);

    const colors = func.arena.allocator().alloc(u16, func.instr_count) catch unreachable;
    @memset(colors, sentinel);

    var selection_set = Set.initEmpty(tmp.arena.allocator(), func.instr_count + 64) catch unreachable;
    for (interference_table, colors, instrs, 0..) |it_row, *color, instr, i| {
        @memset(Block.setMasks(selection_set), 0);

        @as(*align(@alignOf(usize)) u64, @ptrCast(&Block.setMasks(selection_set)[0])).* |=
            if (@hasDecl(Mach, "reserved_regs")) Mach.reserved_regs else 0;

        var iter = it_row.iterator(.{});
        //std.debug.print("| {}\n", .{instrs[i].def});
        while (iter.next()) |e| if (i != e) {
            //std.debug.print("|  {}\n", .{instrs[e].def});
            if (colors[e] != sentinel) selection_set.set(colors[e]);
            @as(*align(@alignOf(usize)) u64, @ptrCast(&Block.setMasks(selection_set)[0])).* |=
                instrs[e].def.clobbers();
        };

        if (instrs[i].def.carried()) |c| {
            for (instrs[i].def.dataDeps(), 0..) |d, k| {
                if (k != c) {
                    selection_set.set(colors[d.?.schedule]);
                }
            }
        }

        const bias = instr.def.regBias();
        if (bias != null and !selection_set.isSet(bias.?)) {
            color.* = bias.?;
        } else {
            var it = selection_set.iterator(.{ .kind = .unset });
            color.* = @intCast(it.next().?);
        }
    }

    return colors;
}
