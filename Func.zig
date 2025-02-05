arena: std.heap.ArenaAllocator,
tmp_arena: std.heap.ArenaAllocator,
next_id: u16 = 0,
block_count: u16 = undefined,
instr_count: u16 = undefined,
root: *Node = undefined,
end: *Node = undefined,

const std = @import("std");
const lexer = @import("lexer.zig");
const Func = @This();

pub const Node = extern struct {
    kind: NodeKind,
    id: u16,
    schedule: u16 = undefined,

    input_ordered_len: u16,
    input_len: u16,
    output_len: u16 = 0,
    output_cap: u16 = 0,

    input_base: [*]?*Node,
    output_base: [*]*Node,

    const User = packed struct(usize) {
        pointer: usize,

        pub fn node(self: User) *Node {
            return @ptrFromInt(self.pointer);
        }
    };

    fn fmt(self: *Node, scheduled: ?u16, writer: anytype, colors: std.io.tty.Config) void {
        logNid(writer, self.id, colors);
        if (scheduled) |v| {
            writer.print(" ={d} {s}", .{ if (isCfg(self.kind)) v - self.schedule - 1 else self.schedule, @tagName(self.kind) }) catch unreachable;
        } else {
            writer.print(" = {s}", .{@tagName(self.kind)}) catch unreachable;
        }

        var add_colon_space = false;

        switch (self.kind) {
            inline else => |t| {
                const ext = self.extra(t);
                if (@TypeOf(ext.*) != void) {
                    if (!add_colon_space) {
                        writer.writeAll(": ") catch unreachable;
                        add_colon_space = true;
                    }
                    writer.print("{any}", .{ext.*}) catch unreachable;
                }
            },
        }

        for (self.inputs()) |oo| if (oo) |o| {
            if (!add_colon_space) {
                writer.writeAll(": ") catch unreachable;
                add_colon_space = true;
            } else {
                writer.writeAll(", ") catch unreachable;
            }
            logNid(writer, o.id, colors);
        };

        writer.writeAll("\n") catch unreachable;
    }

    pub fn inputs(self: *Node) []?*Node {
        return self.input_base[0..self.input_len];
    }

    pub fn outputs(self: *Node) []*Node {
        return self.output_base[0..self.output_len];
    }

    pub fn extra(self: *Node, comptime kind: NodeKind) *ExtFor(kind) {
        std.debug.assert(self.kind == kind);
        const ptr: *LayoutFor(kind) = @ptrCast(self);
        return &ptr.extra;
    }

    pub fn subclass(self: *Node, comptime Ext: type) ?*SubclassFor(Ext) {
        switch (self.kind) {
            inline else => |t| if (ExtFor(t) == Ext) {
                return @ptrCast(self);
            },
        }

        return null;
    }

    pub fn cfg0(self: *Node) ?*SubclassFor(Extra.Cfg) {
        if (self.kind == .Start) return self.subclass(Extra.Cfg);
        return (self.inputs()[0] orelse return null).subclass(Extra.Cfg);
    }

    pub fn useBlock(self: *Node, use: *Node, scheds: []const ?*CfgNode) *CfgNode {
        _ = self; // autofix
        todo(.Phi, "phis need to be forwarded to a block depending which use this is");
        return scheds[use.id].?;
    }
};

pub const CfgNode = SubclassFor(Extra.Cfg);

pub const Extra = union(enum(u16)) {
    Start: Cfg,
    Entry: Cfg,
    Return: Cfg,
    CInt: i64,

    pub const Cfg = extern struct {
        idepth: u16 = 0,
    };
};

pub const NodeKind = std.meta.Tag(Extra);

pub fn isBasicBlockStart(k: NodeKind) bool {
    std.debug.assert(isCfg(k));
    return switch (k) {
        .Start => true,
        else => false,
    };
}

pub fn isPinned(k: NodeKind) bool {
    return isCfg(k);
}

pub fn isCfg(k: NodeKind) bool {
    return switch (k) {
        .Return, .Entry, .Start => true,
        else => false,
    };
}

pub fn isBasicBlockEnd(k: NodeKind) bool {
    std.debug.assert(isCfg(k));
    return switch (k) {
        .Return => true,
        else => false,
    };
}

pub fn ExtFor(comptime kind: NodeKind) type {
    return std.meta.TagPayload(Extra, kind);
}

fn LayoutFor(comptime kind: NodeKind) type {
    return extern struct {
        base: Node,
        extra: ExtFor(kind),
    };
}

fn SubclassFor(comptime Ext: type) type {
    return extern struct {
        base: Node,
        extra: Ext,

        pub fn idepth(cfg: *@This()) u16 {
            const extra: *Extra.Cfg = &cfg.extra;

            if (extra.idepth != 0) return extra.idepth;
            extra.idepth = switch (cfg.base.kind) {
                .Start => return 0,
                else => cfg.base.cfg0().?.idepth() + 1,
            };
            return extra.idepth;
        }

        fn findLce(left: *@This(), right: *@This()) *@This() {
            var lc, var rc = .{ left, right };
            while (lc != rc) {
                if (lc.idepth() >= rc.idepth()) lc = lc.base.cfg0().?;
                if (rc.idepth() >= lc.idepth()) rc = rc.base.cfg0().?;
            }
            return lc;
        }

        fn idom(cfg: *@This()) *@This() {
            return switch (cfg.base.kind) {
                else => cfg.base.cfg0().?,
            };
        }

        fn better(cfg: *@This(), best: *@This()) bool {
            return cfg.idepth() > best.idepth() or isBasicBlockEnd(best.base.kind);
        }
    };
}

pub fn init(gpa: std.mem.Allocator) Func {
    var self = Func{
        .arena = std.heap.ArenaAllocator.init(gpa),
        .tmp_arena = std.heap.ArenaAllocator.init(gpa),
    };
    self.root = self.addNode(.Start, &.{}, .{});
    return self;
}

pub fn deinit(self: *Func) void {
    self.arena.deinit();
    self.tmp_arena.deinit();
}

pub fn addNode(self: *Func, comptime kind: NodeKind, inputs: []const ?*Node, extra: ExtFor(kind)) *Node {
    const Layout = LayoutFor(kind);

    const node = self.arena.allocator().create(Layout) catch unreachable;
    const owned_inputs = self.arena.allocator().dupe(?*Node, inputs) catch unreachable;

    for (owned_inputs) |on| if (on) |def| {
        self.addUse(def, &node.base);
    };

    node.* = .{
        .base = .{
            .input_base = owned_inputs.ptr,
            .input_len = @intCast(owned_inputs.len),
            .input_ordered_len = @intCast(owned_inputs.len),
            .output_base = (self.arena.allocator().alloc(*Node, 0) catch unreachable).ptr,
            .kind = kind,
            .id = self.next_id,
        },
        .extra = extra,
    };
    self.next_id += 1;

    return &node.base;
}

pub fn setInput(self: *Func, use: *Node, idx: usize, def: *Node) void {
    if (use.inputs()[idx] == def) return;
    if (use.inputs()[idx]) |n| {
        const outs = n.outputs();
        const index = std.mem.indexOfScalar(*Node, outs, use).?;
        std.mem.swap(*Node, &outs[index], &outs[outs.len - 1]);
        n.output_len -= 1;
    }

    use.inputs()[idx] = def;
    self.addUse(def, use);
}

pub fn addUse(self: *Func, def: *Node, use: *Node) void {
    if (def.output_len == def.output_cap) {
        const new_cap = @max(def.output_cap, 1) * 2;
        const new_outputs = self.arena.allocator().realloc(def.outputs(), new_cap) catch unreachable;
        def.output_base = new_outputs.ptr;
        def.output_cap = new_cap;
    }

    def.output_base[def.output_len] = use;
    def.output_len += 1;
}

pub inline fn beginTmpAlloc(self: *Func) std.mem.Allocator {
    std.debug.assert(self.tmp_arena.reset(.retain_capacity));
    return self.tmp_arena.allocator();
}

pub const Frame = struct { *Node, []const ?*Node };

pub fn gcm(self: *Func) void {
    const tmp = self.beginTmpAlloc();

    var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
    var stack = std.ArrayList(Frame).init(tmp);

    const cfg_rpo = cfg_rpo: {
        var rpo = std.ArrayList(*CfgNode).init(tmp);

        traversePostorder(struct {
            rpo: *std.ArrayList(*CfgNode),
            const dir = "outputs";
            fn each(ctx: @This(), node: *Node) void {
                ctx.rpo.append(node.subclass(Extra.Cfg).?) catch unreachable;
            }
            fn filter(_: @This(), node: *Node) bool {
                return isCfg(node.kind);
            }
        }{ .rpo = &rpo }, self.root, &stack, &visited);

        break :cfg_rpo rpo.items;
    };

    sched_early: {
        var i = cfg_rpo.len;
        while (i > 0) {
            i -= 1;
            const cfg: *CfgNode = cfg_rpo[i];
            self.shedEarly(cfg, cfg_rpo[1], &stack, &visited);

            todo(.Phi, "phis need to be traversed");
        }

        break :sched_early;
    }

    sched_late: {
        const late_scheds = tmp.alloc(?*SubclassFor(Extra.Cfg), self.next_id) catch unreachable;
        @memset(late_scheds, null);
        const nodes = tmp.alloc(?*Node, self.next_id) catch unreachable;
        @memset(nodes, null);
        var work_list = std.ArrayList(*Node).init(tmp);

        work_list.append(self.end) catch unreachable;

        task: while (work_list.popOrNull()) |t| {
            std.debug.assert(late_scheds[t.id] == null);

            if (t.subclass(Extra.Cfg)) |c| {
                late_scheds[c.base.id] = if (isBasicBlockStart(c.base.kind)) c else c.base.cfg0();
                continue :task;
            }

            todo(.Phi, "pin phys to the region");

            todo(.Proj, "pin projs to the parent");

            for (t.outputs()) |o| {
                if (late_scheds[o.id] == null) continue :task;
            }

            schedule_late: {
                const early = t.cfg0() orelse unreachable;

                var lca: ?*CfgNode = null;
                for (t.outputs()) |o| {
                    const other = t.useBlock(o, late_scheds);
                    lca = if (lca) |l| l.findLce(other) else other;
                }

                todo(.Load, "handle loads being defered");

                var best = lca.?;
                var cursor = best.base.cfg0().?;
                while (cursor != early.idom()) {
                    if (cursor.better(best)) best = cursor;
                    cursor = early.idom();
                }

                std.debug.assert(!isBasicBlockEnd(best.base.kind));

                nodes[t.id] = t;
                late_scheds[t.id] = best;
                break :schedule_late;
            }

            for (t.inputs()) |odef| if (odef) |def| {
                if (late_scheds[def.id] == null) {
                    work_list.append(def) catch unreachable;

                    todo(.Load, "smh appent loads smh");
                }
            };
        }

        for (nodes, late_scheds) |on, l| if (on) |n| {
            todo(.Proj, "ignore them");
            self.setInput(n, 0, &l.?.base);
        };

        break :sched_late;
    }

    compact_ids: {
        visited.setRangeValue(.{ .start = 0, .end = visited.capacity() }, false);
        self.block_count = 0;
        self.instr_count = 0;

        todo(.Loop, "loops need to be handled differently due to cycles");
        std.debug.assert(!@hasDecl(Extra, "Loop"));
        Func.traversePostorder(struct {
            func: *Func,
            const dir = "outputs";
            fn each(ctx: @This(), node: *Func.Node) void {
                node.schedule = ctx.func.block_count;
                ctx.func.block_count += @intFromBool(isBasicBlockStart(node.kind));

                std.mem.reverse(*Node, node.outputs());
                for (node.outputs()) |o| if (!isCfg(o.kind)) {
                    o.schedule = ctx.func.instr_count;
                    ctx.func.instr_count += 1;
                };
            }

            fn filter(_: @This(), node: *Func.Node) bool {
                return Func.isCfg(node.kind);
            }
        }{ .func = self }, self.root, &stack, &visited);

        break :compact_ids;
    }
}

fn shedEarly(self: *Func, cfg: *CfgNode, early: *CfgNode, stack: *std.ArrayList(Frame), visited: *std.DynamicBitSet) void {
    for (cfg.base.inputs()) |oinp| if (oinp) |inp| {
        traversePostorder(struct {
            early: *CfgNode,
            func: *Func,
            const dir = "outputs";
            fn each(ctx: @This(), node: *Node) void {
                if (isPinned(node.kind)) return;

                var best = ctx.early;
                if (node.inputs()[0]) |n| if (n.subclass(Extra.Cfg)) |cn| {
                    best = cn;
                };

                for (node.inputs()) |oin| if (oin) |in| {
                    if (in.cfg0().?.idepth() > best.idepth()) {
                        best = in.cfg0().?;
                    }
                };

                ctx.func.setInput(node, 0, &best.base);
            }
        }{ .early = early, .func = self }, inp, stack, visited);
    };
}

pub fn traversePostorder(ctx: anytype, inp: *Node, stack: *std.ArrayList(Frame), visited: *std.DynamicBitSet) void {
    const dir = @TypeOf(ctx).dir;

    stack.append(.{ inp, @field(Node, dir)(inp) }) catch unreachable;
    visited.set(inp.id);
    while (stack.items.len > 0) {
        const frame = &stack.items[stack.items.len - 1];
        if (frame[1].len == 0) {
            _ = stack.pop();
            ctx.each(frame[0]);
            continue;
        }
        const node = frame[1][0];
        frame[1] = frame[1][1..];
        if (node) |n| if ((!@hasDecl(@TypeOf(ctx), "filter") or ctx.filter(n)) and !visited.isSet(n.id)) {
            visited.set(n.id);
            stack.append(.{ n, @field(Node, dir)(n) }) catch unreachable;
        };
    }
}

fn logNid(wr: anytype, nid: usize, cc: std.io.tty.Config) void {
    cc.setColor(wr, @enumFromInt(1 + nid % 15)) catch unreachable;
    wr.print("%{d}", .{nid}) catch unreachable;
    cc.setColor(wr, .reset) catch unreachable;
}

pub fn fmtScheduled(self: *Func, writer: anytype, colors: std.io.tty.Config) void {
    const tmp = self.beginTmpAlloc();

    var postorder = std.ArrayList(*CfgNode).init(tmp);
    var visited = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
    var stack = std.ArrayList(Frame).init(tmp);

    traversePostorder(struct {
        rpo: *std.ArrayList(*CfgNode),
        const dir = "inputs";
        fn each(ctx: @This(), node: *Node) void {
            ctx.rpo.append(node.subclass(Extra.Cfg).?) catch unreachable;
        }
        fn filter(_: @This(), node: *Node) bool {
            return isCfg(node.kind);
        }
    }{ .rpo = &postorder }, self.end, &stack, &visited);

    for (postorder.items) |p| {
        p.base.fmt(self.block_count, writer, colors);
        for (p.base.outputs()) |o| if (!visited.isSet(o.id)) {
            writer.writeAll("  ") catch unreachable;
            o.fmt(self.block_count, writer, colors);
        };
    }
}

pub fn fmt(self: *Func, writer: anytype, colors: std.io.tty.Config) void {
    const tmp = self.beginTmpAlloc();

    var seen = std.DynamicBitSet.initEmpty(tmp, self.next_id) catch unreachable;
    var postorder = std.ArrayList(*Node).init(tmp);
    postorder.append(self.end) catch unreachable;

    var i: usize = 0;
    while (i < postorder.items.len) {
        defer i += 1;
        const node = postorder.items[i];

        const pre_len = postorder.items.len;
        for (node.inputs()) |on| if (on) |n| {
            if (!seen.isSet(n.id)) {
                seen.set(n.id);
                postorder.append(n) catch unreachable;
            }
        };

        std.mem.reverse(*Node, postorder.items[pre_len..]);
    }

    std.mem.reverse(*Node, postorder.items);

    for (postorder.items) |p| p.fmt(null, writer, colors);
}

fn todo(comptime variant: anytype, comptime message: []const u8) void {
    if (@hasField(Extra, @tagName(variant))) @compileError(message);
}
