# Caml Light Prefix Operator Investigation

Created: 2026-04-24

## Question

Does Caml Light give prefix operators precedence, and should the parser alignment
work add a new prefix-precedence implementation?

## Sources

- Caml Light manual, expression grammar and precedence table:
  https://caml.inria.fr/pub/docs/manual-caml-light/node3.8.html
- Local parser fixtures:
  `hkmc2/shared/src/test/mlscript/apps/parsing/ParserTest.mls`
- Local precedence table:
  `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Keywords.mls`

## Findings

The Caml Light grammar has a `prefix-op expr` form. The grammar lists only
`-`, `-.`, and `!` as prefix operators. The same manual section gives these
operators precedence: `!` appears above field selection and application, while
prefix `-` and `-.` appear below function/constructor application and above
`**`.

The manual also explains that prefix and infix operator syntax is translated to
ordinary identifier application. For example, prefix `-` maps to `minus`, and
prefix `-.` maps to `minus_float`. This is a fixed syntax class in Caml Light,
not a general user-defined prefix-operator declaration mechanism.

The local parser already has behavior that covers the visible Caml Light cases:
`ParserTest.mls` includes `-2 * 3` and `let x = !true`. The implementation
currently accepts symbolic identifiers in term position, then the normal
application continuation binds the following atom. Pretty-printing uses
`Keywords.prefixPrec`, and `Keywords.mls` sets that precedence below
application and above lower infix operators.

One local behavior is intentionally broader than Caml Light: the parser accepts
`~2 * 3` as a symbolic prefix application because symbolic identifiers are
allowed as terms. Caml Light's grammar does not list `~` as a prefix operator.

## Conclusion

Caml Light does have prefix precedence. No immediate parser change is needed for
this alignment pass because the current parser already handles the existing test
coverage for prefix `-` and `!`, and adding a new general prefix-operator rule
would go beyond Caml Light's fixed prefix syntax.

If this is revisited later, the conservative target is not arbitrary prefix
operators. It is a small explicit rule for Caml Light's fixed prefix forms:
`-`, `-.`, and `!`, with the manual's precedence ordering preserved.
