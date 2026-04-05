const std = @import("std");
pub const hbb = @import("hbb");
pub const hbf = @import("hbf");

test {
    std.testing.refAllDeclsRecursive(@This());
    std.testing.refAllDeclsRecursive(hbb.graph.Func(hbb.x86_64.X86_64Gen));
    std.testing.refAllDeclsRecursive(hbb.graph.Func(hbb.wasm.WasmGen));
    std.testing.refAllDeclsRecursive(hbb.graph.Func(hbb.hbvm.HbvmGen));
}
