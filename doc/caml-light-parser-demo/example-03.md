# Example 03: Sorted Integer Sets

Status: Done

## Source

- Repository path: `sources/examples/grep/ensent.ml`
- Local clone path:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight/sources/examples/grep/ensent.ml`

## Original Example

```ocaml
type t == int list;;
let vide = [];;
let rec appartient n = function
  | [] -> false
  | m :: reste ->
      if m = n then true else
        if m > n then false else appartient n reste;;

let rec ajoute n = function
  | [] -> [n]
  | m :: reste as ens ->
      if m = n then ens else
        if m > n then n :: ens else m :: ajoute n reste;;
```

## Adapted Example

```ocaml
type t == int list;;
let empty = [];;
let rec belongs n = function
  | [] -> false
  | m :: rest ->
      if m = n then true else
        if m > n then false else belongs n rest
;;
let rec add n = function
  | [] -> [n]
  | m :: rest as set ->
      if m = n then set else
        if m > n then n :: set else m :: add n rest
;;
```

## Adaptation Notes

- Translated French names: `vide` to `empty`, `appartient` to `belongs`,
  `reste` to `rest`, and `ajoute` to `add`.
- Restored the source's alias pattern shape as `m :: rest as set` after adding
  dedicated pattern parsing with `as` alias support.

## Parser Fixes

- Added term-level `=` parsing so Caml Light equality expressions such as
  `m = n` are represented as infix syntax trees instead of being left as
  stray tokens.
- Added a `binding` parse kind for let-binding left-hand sides. This lets the
  parser stop at the binding `=` while still allowing structured function
  bindings and tuple-style left-hand sides.
- Propagated the binding stop marker through same-kind recursive references so
  binding patterns do not accidentally consume the `=` as expression equality.
- Added dedicated pattern parsing with `as` alias support.
