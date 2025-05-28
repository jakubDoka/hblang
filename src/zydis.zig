pub const exports = @cImport({
    @cInclude("Zydis/Encoder.h");
    @cInclude("Zydis/Decoder.h");
    @cInclude("Zydis/Formatter.h");
});
