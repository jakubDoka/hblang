const hb = @import("hb");
const Lexer = hb.frontend.Lexer;
const std = @import("std");

indent: usize,
lex: Lexer,
out: *std.Io.Writer,

const Fmt = @This();
const Error = std.Io.Writer.Error || error{SyntaxError};
const ItemKind = enum {
    expr,
};

pub fn formatList(self: *Fmt, comptime item: ItemKind, force_indent: bool, comptime sep: Lexer.Lexeme, comptime end: Lexer.Lexeme) Error!void {
    var indent = force_indent;

    if (!indent) {
        const iter = self.lex.list(sep, end);

        while (true) {
            switch (iter.nextExt()) {
                .has_next => {},
                .end => break,
                .trailing_end => {
                    indent = true;
                    break;
                },
            }

            switch (item) {
                .expr => try self.lex.skipExpr(),
            }
        }
    }

    if (indent) {
        self.indent += 1;
        self.out.writeByte('\n');
        self.out.splatByte('\t', self.indent);
    }

    if (indent) {
        self.indent -= 1;
        self.out.writeByte('\n');
        self.out.splatByte('\t', self.indent);
    }
}
