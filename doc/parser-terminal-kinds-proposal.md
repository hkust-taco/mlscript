# Parser Terminal Kinds Proposal

Created: 2026-04-24

## Problem

The paper's dynamic extension examples use built-in terminal syntax kinds such as
`literal` and `string-literal`:

```mlscript
#extend ["term",
  [keyword("print"), ["term", "x"], keyword("format"), ["string-literal", "f"]],
  [System.println (String.format f x)]]
```

The current parser only treats `ident` and `typevar` as built-in syntax kinds in
`Parser.parseKind`. Literals are recognized in the dedicated term/type atom
parsers, which means a dynamic rule cannot currently reference a literal as a
closed syntax kind.

## Proposed Built-Ins

Add these closed terminal syntax kinds to `parseKind`:

| Kind | Token accepted | Tree produced |
| --- | --- | --- |
| `ident` | non-keyword word identifier | `Tree.Ident(name, false)` |
| `typevar` | word identifier starting with `'` | `Tree.Ident(name, false)` |
| `literal` | any `Token.Literal(kind, value)` | `Tree.Literal(kind, value)` |
| `string-literal` | `Token.Literal(Token.LiteralKind.String, value)` | `Tree.Literal(Token.LiteralKind.String, value)` |
| `integer-literal` | `Token.Literal(Token.LiteralKind.Integer, value)` | `Tree.Literal(Token.LiteralKind.Integer, value)` |
| `decimal-literal` | `Token.Literal(Token.LiteralKind.Decimal, value)` | `Tree.Literal(Token.LiteralKind.Decimal, value)` |
| `boolean-literal` | `Token.Literal(Token.LiteralKind.Boolean, value)` | `Tree.Literal(Token.LiteralKind.Boolean, value)` |

These should remain closed categories, like `ident` and `typevar`; users should
not be able to extend them with `#extend`.

## Parser Behavior

Terminal kinds should be atomic:

- They ignore the incoming binding power.
- They consume exactly one matching token.
- They return `Tree.Error` on the wrong token and on end of input.
- They do not call `exprCont` or `typeExprCont`.

The dedicated `expr` and `typeExpr` atom parsers can continue to accept literals
directly. The terminal kinds are an additional dynamically referenceable entry
point, not a replacement for ordinary expression atom parsing.

## Dynamic Extension Impact

The paper-style `#extend` implementation should parse labeled fragments like
`["string-literal", "f"]` by creating a reference to the built-in
`string-literal` kind and binding the parsed tree to label `f` in the replacement
expression.

The extension layer should reject references to unknown terminal names early,
with a message that distinguishes unknown syntax kinds from unsupported labels.

## Diagram Impact

`ParseRuleVisualizer` should treat terminal built-ins as terminal-like leaf nodes:

- `ident`
- `typevar`
- `literal`
- `string-literal`
- `integer-literal`
- `decimal-literal`
- `boolean-literal`

They should not generate follow-up diagrams, because they have no rule body.

## Recommended Implementation Point

Implement the terminal kinds as part of PA-08, before parsing the paper-style
`#extend` replacement-expression form. That keeps the extension example in the
paper implementable without adding a separate compatibility layer.
