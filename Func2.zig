pub fn Func(comptime Mach: type) type {
    return @TypeOf(_Func(Mach));
}

const std = @import("std");
const Lexer = @import("Lexer.zig");
const Types = @import("Types.zig");

pub const Buitin = union(enum) {
    Start: Cfg,
    // [Start]
    Arg: usize,
    // [Start]
    Entry: Cfg,
    // [Start]
    Mem: void,
    // [Cfg, ret]
    Return: Cfg,
    // [?Cfg]
    CInt: i64,
    // [?Cfg, lhs, rhs]
    BinOp: Lexer.Lexeme,
    // [?Cfg, Mem]
    Local: usize,
    // [?Cfg, thread, ptr]
    Load,
    // [?Cfg, thread, ptr, value, ...antideps]
    Store,
    // [?Cfg, ...lane]
    Split,
    // [?Cfg, ...lane]
    Join,
    // [Cfg, ..args]
    Call: extern struct {
        base: Cfg = .{},
        id: Types.Func,
    },
    // [Call]
    CallEnd: Cfg,
    // [CallEnd]
    Ret: void,
    // [Cfg, cond],
    If: Cfg,
    // [If]
    Then: Cfg,
    // [If]
    Else: Cfg,
    // [lCfg, rCfg]
    Region: Cfg,
    // [entryCfg, backCfg]
    Loop: Cfg,
    // [Cfg]
    Jmp: Cfg,
    // [Region, lhs, rhs]
    Phi,
    // [Cfg, inp]
    MachMove,

    pub const Cfg = extern struct {
        idepth: u16 = 0,
        antidep: u16 = 0,
    };
};

fn _Func(comptime Mach: type) struct {
    arena: std.heap.ArenaAllocator,
    tmp_arena: std.heap.ArenaAllocator,
    interner: std.hash_map.HashMapUnmanaged(InternedNode, void, void, 70) = .{},
    next_id: u16 = 0,
    block_count: u16 = undefined,
    instr_count: u16 = undefined,
    root: *Node = undefined,
    end: *Node = undefined,

    pub const Kind = b: {
        var builtin = @typeInfo(std.meta.Tag(Buitin));
        builtin.tag_type = u16;
        const field_ref = std.meta.fields(std.meta.Tag(Mach));
        var fields = field_ref[0..field_ref.len].*;
        for (fields[builtin.@"enum".fields.len..], builtin.@"enum".fields.len) |*f, i| {
            f.value = i;
        }
        builtin.@"enum".fields = builtin.@"enum".fields ++ fields;
        break :b @Type(builtin);
    };

    pub const all_classes = std.meta.fields(Buitin) ++ std.meta.fields(Mach);

    pub fn ClassFor(comptime kind: Kind) type {
        return all_classes[@intFromEnum(kind)];
    }

    pub fn LayoutFor(comptime kind: Kind) type {
        return extern struct {
            base: Node,
            ext: ClassFor(kind),
        };
    }

    pub const DataType = enum(u16) {
        void,
        mem,
        dead,
    };

    pub const Node = extern struct {
        kind: Kind,
        id: u16,
        schedule: u16 = undefined,
        data_type: DataType = .void,

        input_ordered_len: u16,
        input_len: u16,
        output_len: u16 = 0,
        output_cap: u16 = 0,

        input_base: [*]?*Node,
        output_base: [*]*Node,

        pub fn anyextra(self: *const Node) *const anyopaque {
            const any: *const extern struct { n: Node, ex: u8 } = @ptrCast(self);
            return &any.ex;
        }

        pub fn format(self: *const Node, comptime _: anytype, _: anytype, writer: anytype) !void {
            const colors = .escape_codes;

            @import("HbvmGen.zig").gcm.fmt(self, null, writer, colors);
        }

        pub fn mem(self: *Node) *Node {
            std.debug.assert(self.kind == .Load or self.kind == .Store);
            return self.inputs()[1].?;
        }

        pub fn base(self: *Node) *Node {
            std.debug.assert(self.kind == .Load or self.kind == .Store);
            return self.inputs()[2].?;
        }

        pub fn value(self: *Node) *Node {
            std.debug.assert(self.kind == .Store);
            return self.inputs()[3].?;
        }

        pub fn isLazyPhi(self: *Node, on_loop: *Node) bool {
            return self.kind == .Phi and self.inputs()[0] == on_loop and self.inputs()[2] == null;
        }

        pub fn inputs(self: *Node) []?*Node {
            return self.input_base[0..self.input_len];
        }

        pub fn kill(self: *Node) void {
            std.debug.assert(self.output_len == 0);
            for (self.inputs()) |oi| if (oi) |i| {
                i.removeUse(self);
            };
            self.* = undefined;
            self.id = std.math.maxInt(u16);
        }

        pub fn removeUse(self: *Node, use: *Node) void {
            const outs = self.outputs();
            const index = std.mem.indexOfScalar(*Node, outs, use).?;
            std.mem.swap(*Node, &outs[index], &outs[outs.len - 1]);
            self.output_len -= 1;
        }

        pub fn outputs(self: *Node) []*Node {
            return self.output_base[0..self.output_len];
        }

        pub fn extraConst(self: *const Node, comptime kind: Kind) *const ClassFor(kind) {
            std.debug.assert(self.kind == kind);
            const ptr: *const LayoutFor(kind) = @ptrCast(self);
            return &ptr.extra;
        }

        pub fn extra(self: *Node, comptime kind: Kind) *ClassFor(kind) {
            std.debug.assert(self.kind == kind);
            const ptr: *LayoutFor(kind) = @ptrCast(self);
            return &ptr.extra;
        }

        pub fn isSubbclass(Full: type, Sub: type) bool {
            var Cursor = Full;
            while (true) {
                if (Cursor == Sub) return true;
                if (@typeInfo(Cursor) != .@"struct" or !@hasField(Cursor, "base")) return false;
                Cursor = @TypeOf(@as(Cursor, undefined).base);
            }
        }
    };

    pub fn isInterned(kind: Kind, inputs: []const ?*Node) bool {
        return switch (kind) {
            .CInt, .BinOp, .Load => true,
            .Phi => inputs[2] != null,
            else => false,
        };
    }
} {
    return undefined;
}
