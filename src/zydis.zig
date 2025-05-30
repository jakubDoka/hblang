pub const exports = @cImport({
    @cDefine("ZYAN_NO_LIBC", {});
    @cInclude("Zydis/Encoder.h");
    @cInclude("Zydis/Decoder.h");
    @cInclude("Zydis/Formatter.h");
});
