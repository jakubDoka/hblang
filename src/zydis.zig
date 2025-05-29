pub const exports = @cImport({
    if (@import("builtin").target.os.tag == .freestanding) @cDefine("ZYAN_NO_LIBC", {});
    @cInclude("Zydis/Encoder.h");
    @cInclude("Zydis/Decoder.h");
    @cInclude("Zydis/Formatter.h");
});
