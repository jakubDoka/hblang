const std = @import("std");
pub const hb = @import("hb");

test {
    std.testing.refAllDeclsRecursive(@This());
    std.testing.refAllDeclsRecursive(hb.backend.graph.Func(hb.x86_64.X86_64Gen));
    std.testing.refAllDeclsRecursive(hb.backend.graph.Func(hb.wasm.WasmGen));
    std.testing.refAllDeclsRecursive(hb.backend.graph.Func(hb.hbvm.HbvmGen));
}
