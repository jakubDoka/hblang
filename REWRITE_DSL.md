# Rewrite DSL

## Introudction

The Rewrite DSL (further just DSL) is used for defining graph rewrite rules.
This rules are applied by the backend untill none can be applied. A rule is
defined as:

```bnf
<RULE> ::= <PATTERN> ':' <REPLACEMENT> [ '&&' <POSTPROCESS-EXPR> ]
<PATTERN> ::= <ATOM>
<REPLACEMENT> ::= <ATOM>
<ATOM> ::= <ATOM-IDENT> | '(' <ATOM-IDENT> { <EXPR> } ')'
<EXPR> ::= <ATOM> | <FIELD> | <BINDING> | <RANGE> | <REF> | <OR> | <ZIG-EXPR>
<FIELD> ::= ':' <NORMAL-IDENT> | '(' ':' <NORMAL-IDENT> [ <EXPR> ] ')'
<BINDING> ::= [ <OPT-PREFIX> ] <NORMAL-IDENT> [ '&' <MATCHES-EXPR> ] [ '@' <ZIG-EXPR-BINDING> ] [ '&&' <PREDICATE> ]
<MATCHES-EXPR> ::= <EXPR>
<ZIG-EXPR-BINDING> ::= { <EXPR> } '=' <ZIG-EXPR>
<PREDICATE> ::= <ZIG-EXPR>
<REF> ::= '&' <NORMAL-IDENT> | '(' '&' <NORMAL-IDENT> ')'
<OR> ::= <EXPR> '|' <EXPR>
<RANGE> ::= <EXPR> '..' <EXPR>
<POSTPROCESS-EXPR> ::= <ZIG-EXPR>
<NORMAL-IDENT> ::= \[a-z_][a-z0-9_]*\
<ATOM-IDENT> ::= \[A-Z_][a-zA-Z0-9_]*\
<OPT-PREFIX> ::= '?'
<ZIG-EXPR> ::= '{' { <ZIG-EXPR> | \.\ } '}'
```

NOTE: we will refer to these BNF declarations later.

## Matching Mechanism

Its best to explain this by example. Lets say we want to rewrite the following code:

```zig
return 1 + 2 + 3;
// into
return 6;
```

We can write the following rule:
```clj
(BinOp ?c :op :data_type
    (CInt _ (:value lhs))
    (CInt _ (:value rhs))
) : (CInt c (:value {op.eval(data_type, lhs, rhs)}))
```

Now lets make this step by step:
```clj
; First we only care about the BinOp node
(BinOp)
; Then we want to select the control flow node the node is in
(BinOp ?c)
; NOTE: that ? means c can be null
; Now we want to capture the `op` field specific to BinOp node
(BinOp ?c :op)
; After that we also want the type of the node which every node has
(BinOp ?c :op :data_type)
; NOTE: thus far we still match any binop node
; Now we want to be more specific and match only the binop nodes that
; operate on constants
(BinOp ?c :op :data_type
    (CInt _ (:value lhs))
    (CInt _ (:value rhs))
)
; NOTE: CInt also has a ref to the control flow node, we ignore that tho
;   NOTE: we in theroy dont need to do this but it demonstrates the `_`
; NOTE: CInt node has a `value` field and we bind it to the `lhs` and `rhs` respectively
; Lets construct the node which will replace the matched node
(...) : (CInt)
; NOTE: This esetnially produces a node whith no dependencies and in case of CInt we
; are missing the control flow node and value field, the compiler will give you
; an error in the generated code and in case of forgotten control flow ref, it
; mostli just crashes at runtime (be carefull and make sure you get the input
; refs right)
; Lets add the missing fields, this also demonstrates the use of zig expressions
(...) : (CInt c (:value {op.eval(data_type, lhs, rhs)}))
; NOTE: The op has a convenience function to evaluate the operation on the two values
```

How did I figure out things like how much inputs each node takes, what fields
it has and mainly what nodes are there?

This is all documented in the source code of the compiler sadly. You should
look in `graph.zig` and search for `const builtin_classes`. Then for ida
specific nodes, look into `*Gen.zig` files and search for `const classes`
declaration. That covers the node names and node specific fields.

As to how many inputs each node takes, thats not documented, (TODO).
