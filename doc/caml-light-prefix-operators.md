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

The local parser originally had behavior that covered the visible Caml Light
cases: `ParserTest.mls` included `-2 * 3` and `let x = !true`. That behavior
was broader than Caml Light, because symbolic identifiers in term position could
act like prefix applications. For example, `~2 * 3` parsed as a symbolic prefix
application even though Caml Light's grammar does not list `~` as a prefix
operator.

The implementation now uses a fixed prefix set for Caml Light: `-`, `-.`, and
`!`. Prefix `-` and `-.` keep the existing prefix precedence below application,
while `!` has a tighter precedence than selection and application, matching the
manual's ordering.

## Conclusion

Caml Light does have prefix precedence. The parser now implements the
conservative target: a small explicit rule for Caml Light's fixed prefix forms
`-`, `-.`, and `!`, with the manual's precedence ordering preserved. It does
not add a general arbitrary-prefix-operator mechanism.
