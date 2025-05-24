test init {
    const ExampleMachine = struct {
        const Func = graph.Func(Node);

        pub const Node = union(enum) {
            CustomNode: bool,

            pub const is_basic_block_start: []const Func.Kind = &.{};
            pub const is_mem_op: []const Func.Kind = &.{};
            pub const is_basic_block_end: []const Func.Kind = &.{.CustomNode};
            pub const is_pinned: []const Func.Kind = &.{.CustomNode};

            pub fn isInterned(kind: Func.Kind) bool {
                // this is not a good idea since its supposed to be a control flow
                return kind == .CustomNode;
            }

            pub fn isSwapped(node: *Func.Node) bool {
                // means the output basic blocks should be reversed for reducing jumps
                return node.kind == .CustomNode and node.extra(.CustomNode).*;
            }

            pub fn idealize(func: *Func, node: *Func.Node, worklist: *Func.WorkList) ?*Func.Node {
                _ = worklist;
                // relpace node whih the return value
                if (node.kind == .Start)
                    return func.addNode(.CustomNode, .top, &.{}, false);

                return null;
            }
        };

        pub fn emitFunc(self: *@This(), func: *Func, opts: EmitOptions) void {
            opts.optimizations.execute(Node, func);
            _ = self;
            unreachable;
        }

        pub fn emitData(self: *@This(), opts: DataOptions) void {
            _ = self;
            _ = opts;
            unreachable;
        }

        pub fn finalize(self: *@This(), out: std.io.AnyWriter) void {
            _ = out;
            _ = self;
            unreachable;
        }

        pub fn disasm(self: *@This(), opts: DisasmOpts) void {
            _ = self;
            _ = opts;
            unreachable;
        }

        pub fn run(self: *@This(), env: RunEnv) !usize {
            _ = self;
            _ = env;
            return 0;
        }

        pub fn deinit(self: *@This()) void {
            _ = self;
        }
    };

    var em = ExampleMachine{};
    _ = init(&em);
}

data: *anyopaque,
_emitFunc: *const fn (self: *anyopaque, func: *BuilderFunc, opts: EmitOptions) void,
_emitData: *const fn (self: *anyopaque, opts: DataOptions) void,
_finalize: *const fn (self: *anyopaque, out: std.io.AnyWriter) void,
_disasm: *const fn (self: *anyopaque, opts: DisasmOpts) void,
_run: *const fn (self: *anyopaque, env: RunEnv) anyerror!usize,
_deinit: *const fn (self: *anyopaque) void,

const std = @import("std");
const graph = @import("graph.zig");
const static_anal = @import("static_anal.zig");
const Builder = @import("Builder.zig");
const BuilderFunc = Builder.Func;
const Machine = @This();
const root = @import("../utils.zig");

pub const Data = struct {
    pub const Sym = struct {
        name: u32,
        offset: u32,
        size: u32,
        reloc_offset: u32,
        reloc_count: u32,
        kind: Kind,
        linkage: Linkage,
    };

    pub const Kind = enum(u16) {
        func,
        data,
        prealloc,

        invalid,
    };

    pub const Linkage = enum(u16) {
        local,
        exported,
        imported,
    };

    pub const Reloc = struct {
        target: SymIdx,
        offset: u32,
        addend: i16,
        slot_size: u16,
    };

    pub const SymIdx = enum(u32) { invalid = std.math.maxInt(u32), _ };

    declaring_sym: ?SymIdx = null,

    funcs: std.ArrayListUnmanaged(SymIdx) = .empty,
    globals: std.ArrayListUnmanaged(SymIdx) = .empty,
    syms: std.ArrayListUnmanaged(Sym) = .empty,
    names: std.ArrayListUnmanaged(u8) = .empty,
    code: std.ArrayListUnmanaged(u8) = .empty,
    relocs: std.ArrayListUnmanaged(Reloc) = .empty,

    pub fn reset(self: *Data) void {
        inline for (std.meta.fields(Data)[1..]) |f| {
            @field(self, f.name).items.len = 0;
        }
    }

    pub fn addFuncReloc(self: *Data, gpa: std.mem.Allocator, target: u32, slot_size: u8, addend: i16) !void {
        return self.addReloc(gpa, try root.ensureSlot(&self.funcs, gpa, target), slot_size, addend);
    }

    pub fn addGlobalReloc(self: *Data, gpa: std.mem.Allocator, target: u32, slot_size: u8, addend: i16) !void {
        return self.addReloc(gpa, try root.ensureSlot(&self.globals, gpa, target), slot_size, addend);
    }

    pub fn addReloc(self: *Data, gpa: std.mem.Allocator, target: *SymIdx, slot_size: u8, addend: i16) !void {
        try self.relocs.append(gpa, .{
            .target = try self.declSym(gpa, target),
            .offset = @intCast(self.code.items.len),
            .addend = addend,
            .slot_size = slot_size,
        });
    }

    pub fn deinit(self: *Data, gpa: std.mem.Allocator) void {
        inline for (std.meta.fields(Data)[1..]) |f| {
            @field(self, f.name).deinit(gpa);
        }
        self.* = undefined;
    }

    pub fn declGlobal(self: *Data, gpa: std.mem.Allocator, id: u32) !SymIdx {
        return self.declSym(gpa, try root.ensureSlot(&self.globals, gpa, id));
    }

    pub fn declFunc(self: *Data, gpa: std.mem.Allocator, id: u32) !SymIdx {
        return self.declSym(gpa, try root.ensureSlot(&self.funcs, gpa, id));
    }

    pub fn declSym(
        self: *Data,
        gpa: std.mem.Allocator,
        slot: *SymIdx,
    ) !SymIdx {
        if (slot.* == .invalid) {
            (try self.syms.addOne(gpa)).kind = .invalid;
            slot.* = @enumFromInt(self.syms.items.len - 1);
        }
        return slot.*;
    }

    pub fn importSym(
        self: *Data,
        gpa: std.mem.Allocator,
        sym: *SymIdx,
        name: []const u8,
        kind: Kind,
    ) !void {
        _ = try self.declSym(gpa, sym);
        self.syms.items[@intFromEnum(sym.*)] = .{
            .name = @intCast(self.names.items.len),
            .offset = 0,
            .size = 0,
            .reloc_offset = 0,
            .reloc_count = 0,
            .kind = kind,
            .linkage = .imported,
        };
        try self.names.appendSlice(gpa, name);
        try self.names.append(gpa, 0);
    }

    pub fn startDefineFunc(
        self: *Data,
        gpa: std.mem.Allocator,
        id: u32,
        name: []const u8,
        kind: Kind,
        linkage: Linkage,
    ) !void {
        return self.startDefineSym(
            gpa,
            try root.ensureSlot(&self.funcs, gpa, id),
            name,
            kind,
            linkage,
        );
    }

    pub fn defineGlobal(
        self: *Data,
        gpa: std.mem.Allocator,
        id: u32,
        name: []const u8,
        kind: Kind,
        linkage: Linkage,
        data: []const u8,
    ) !void {
        try self.startDefineSym(
            gpa,
            try root.ensureSlot(&self.globals, gpa, id),
            name,
            kind,
            linkage,
        );
        try self.code.appendSlice(gpa, data);
        self.endDefineSym(self.globals.items[id]);
    }

    pub fn startDefineSym(
        self: *Data,
        gpa: std.mem.Allocator,
        sym: *SymIdx,
        name: []const u8,
        kind: Kind,
        linkage: Linkage,
    ) !void {
        _ = try self.declSym(gpa, sym);

        std.debug.assert(self.declaring_sym == null);
        self.declaring_sym = sym.*;

        self.syms.items[@intFromEnum(sym.*)] = .{
            .name = @intCast(self.names.items.len),
            .offset = @intCast(self.code.items.len),
            .size = undefined,
            .reloc_offset = @intCast(self.relocs.items.len),
            .reloc_count = undefined,
            .kind = kind,
            .linkage = linkage,
        };
        try self.names.appendSlice(gpa, name);
        try self.names.append(gpa, 0);
    }

    pub fn endDefineFunc(self: *Data, id: u32) void {
        self.endDefineSym(self.funcs.items[id]);
    }

    pub fn endDefineSym(self: *Data, sym: SymIdx) void {
        std.debug.assert(self.declaring_sym != null);
        self.declaring_sym = null;

        const slot = &self.syms.items[@intFromEnum(sym)];
        slot.size = @intCast(self.code.items.len - slot.offset);
        slot.reloc_count = @intCast(self.relocs.items.len - slot.reloc_offset);
    }
};

pub const RunEnv = struct {
    name: []const u8,
    code: []const u8,
    output: std.io.AnyWriter = std.io.null_writer.any(),
    colors: std.io.tty.Config = .no_color,
};

pub const DataOptions = struct {
    id: u32,
    name: []const u8 = &.{},
    value: ValueSpec,

    pub const ValueSpec = union(enum) { init: []const u8, uninit: usize };
};

pub const EmitOptions = struct {
    id: u32,
    name: []const u8 = &.{},
    entry: bool = false,
    optimizations: struct {
        verbose: bool = false,
        dead_code_fuel: usize = 10000,
        mem2reg: bool = true,
        peephole_fuel: usize = 10000,
        do_gcm: bool = true,
        arena: ?*root.Arena = null,
        error_buf: ?*std.ArrayListUnmanaged(static_anal.Error) = null,

        pub const none = @This(){
            .mem2reg = false,
            .peephole_fuel = 0,
            .do_gcm = false,
        };

        pub fn execute(self: @This(), comptime MachNode: type, func: *graph.Func(MachNode)) void {
            const freestanding = @import("builtin").target.os.tag != .freestanding;

            if (self.peephole_fuel != 0) {
                func.iterPeeps(self.peephole_fuel, @TypeOf(func.*).idealizeDead);
            }

            if (self.mem2reg) {
                func.mem2reg.run();
            }

            if (self.peephole_fuel != 0) {
                func.iterPeeps(self.peephole_fuel, @TypeOf(func.*).idealize);
            }

            if (self.peephole_fuel != 0 and @hasDecl(MachNode, "idealizeMach")) {
                func.iterPeeps(self.peephole_fuel, MachNode.idealizeMach);
            }

            if (self.do_gcm) {
                func.gcm.buildCfg();
            }

            if (freestanding and self.verbose)
                func.fmtScheduled(
                    std.io.getStdErr().writer().any(),
                    std.io.tty.detectConfig(std.io.getStdErr()),
                );

            if (self.error_buf) |eb| {
                func.static_anal.analize(self.arena.?, eb);
            }
        }
    } = .{},
};

pub const DisasmOpts = struct {
    name: []const u8,
    bin: []const u8,
    out: std.io.AnyWriter = std.io.null_writer.any(),
    colors: std.io.tty.Config = .no_color,
};

pub fn init(data: anytype) Machine {
    const Type = @TypeOf(data.*);
    if (!@hasDecl(Type, "Node")) @compileError("expected `pub const Node = enum(union) { ... }` to be present");

    const fns = struct {
        fn emitFunc(self: *anyopaque, func: *BuilderFunc, opts: EmitOptions) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            const fnc: *graph.Func(Type.Node) = @alignCast(@ptrCast(func));
            slf.emitFunc(fnc, opts);
        }
        fn emitData(self: *anyopaque, opts: DataOptions) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            slf.emitData(opts);
        }
        fn finalize(self: *anyopaque, out: std.io.AnyWriter) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            return slf.finalize(out);
        }
        fn disasm(self: *anyopaque, opts: DisasmOpts) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            return slf.disasm(opts);
        }
        fn run(self: *anyopaque, env: RunEnv) !usize {
            const slf: *Type = @alignCast(@ptrCast(self));
            return slf.run(env);
        }
        fn deinit(self: *anyopaque) void {
            const slf: *Type = @alignCast(@ptrCast(self));
            slf.deinit();
        }
    };

    return .{
        .data = data,
        ._emitFunc = fns.emitFunc,
        ._emitData = fns.emitData,
        ._finalize = fns.finalize,
        ._disasm = fns.disasm,
        ._run = fns.run,
        ._deinit = fns.deinit,
    };
}

/// generate apropriate final output for a function
///
/// this also runs optimization passes
pub fn emitFunc(self: Machine, func: *BuilderFunc, opts: EmitOptions) void {
    self._emitFunc(self.data, func, opts);
}

pub fn emitData(self: Machine, opts: DataOptions) void {
    self._emitData(self.data, opts);
}

/// package the final output (.eg object file)
/// this function should also restart the state for next emmiting
pub fn finalize(self: Machine, out: std.io.AnyWriter) void {
    return self._finalize(self.data, out);
}

pub fn finalizeBytes(self: Machine, gpa: std.mem.Allocator) std.ArrayListUnmanaged(u8) {
    var out = std.ArrayListUnmanaged(u8).empty;
    self.finalize(out.writer(gpa).any());
    return out;
}

/// visualize already compiled code, its best to include different colors
/// for registers for better readability
pub fn disasm(self: Machine, opts: DisasmOpts) void {
    self._disasm(self.data, opts);
}

pub fn run(self: Machine, env: RunEnv) !usize {
    return self._run(self.data, env);
}

/// frees the internal resources
pub fn deinit(self: *Machine) void {
    self._deinit(self.data);
    self.* = undefined;
}
