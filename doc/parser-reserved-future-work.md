# Parser Reserved Future Work

Date: 2026-04-25

This note records the future/reserved parser items left after the parser
alignment, Caml Light workaround cleanup, and web-demo phases. Per the current
task instructions, `doc/Parsing.md` is intentionally excluded from this list.

## Current Status

The high-priority pattern items are complete: the parser now has a dedicated
`pattern` syntax kind, supports `as` aliases, and supports alternatives inside a
single match branch. The planned top-level `let` cleanup and conservative Caml
Light fixed prefix rule for `-`, `-.`, and `!` are also complete.

The workaround cleanup items are complete as well: type-level `mutable` labels,
`in_channel`, `#open`, and the `val` field name have all been restored in the
Caml Light examples where applicable.

## Remaining Reserved Items

| Item | Status | Detail | Suggested Priority |
| --- | --- | --- | --- |
| Optional `symbol` terminal kind | Reserved | Extensions still cannot request a symbolic token through a closed syntax kind such as `["symbol", "op"]`. This remains optional because `Choice.Infix` handles symbolic operator parsing without needing a separate terminal kind. Add it only if an extension needs to capture a symbolic token as data rather than parse it as an infix operator. | Low |
| `character-literal` terminal kind | Reserved | The lexer and term parser support character literals, and Caml Light word-count examples now parse. However, extension syntax supports `literal`, `string-literal`, `integer-literal`, `decimal-literal`, and `boolean-literal`, but not `character-literal`. Add this if future extension examples need to bind a character literal directly. | Low to Medium |
| Term/type/pattern Pratt-pair unification | Reserved | The parser now has separate continuation paths for terms, types, and patterns, with shared helpers for common behavior. A unification pass could reduce duplication, but it may make the paper-facing distinction between the syntactic categories less obvious. Treat this as a cleanup only after the demo behavior stabilizes. | Low |
| Reserved-keyword field names beyond current examples | No skipped work | The `val` field-name case did not require broad architecture changes: existing label parsing accepts it in record declarations, record values, and field selections. No reserved-keyword field-name work was skipped. Future work is only needed if another Caml Light field-name case exposes a concrete parser failure. | Watch |

## Explicitly Not Included

- Advanced indentation continuation rules from `doc/Parsing.md`; that document is
  outside the scope of this phase unless the user explicitly reprioritizes it.
- A built-in browser regression command for the web demo; the current task board
  marks it as deferred and explicitly says not to implement it now.
