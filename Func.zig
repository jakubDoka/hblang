arena: std.heap.ArenaAllocator,

const std = @import("std");
const Func = @This();

pub const Node = extern struct {
    input_base: [*]?*Node,
    output_base: [*]User,

    ordered_input_len: u16,
    input_len: u16,

    output_len: u16,
    output_cap: u16,

    const User = packed struct(usize) {
        pointer: u48,
        use_index: u16,

        pub fn node(self: User) *Node {
            return @ptrFromInt(self.pointer);
        }
    };

    pub fn inputs(self: *Node) []?*Node {
        self.input_base[0..self.input_len];
    }

    pub fn orderedInputs(self: *Node) []?*Node {
        self.input_base[0..self.ordered_input_len];
    }
};

pub const exts = struct {};

pub const NKind = std.meta.DeclEnum(exts);

pub fn ExtFor(comptime kind: NKind) type {
    return @field(exts, @tagName(kind));
}

pub fn addNode(self: *Func, comptime kind: NKind, extra: ExtFor(kind)) *Node {
    const Layout = extern struct {
        base: Node,
        extra: ExtFor(kind),
    };
    _ = Layout; // autofix

    _ = self; // autofix
    _ = extra; // autofix
}
