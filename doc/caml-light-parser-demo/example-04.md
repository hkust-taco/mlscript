# Example 04: Pascal Values

Status: Done

## Source

- Repository path: `sources/examples/pascal/valeur.ml`
- Local clone path:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight/sources/examples/pascal/valeur.ml`

## Original Example

```ocaml
#open "interp";;
let ent_val = function
  | Ent n -> n
  | _ -> raise(Erreur_execution "entier attendu")
and bool_val = function
  | Bool b -> b
  | _ -> raise(Erreur_execution "booleen attendu")
and tableau_val = function
  | Tableau(inf, t) -> (inf, t)
  | _ -> raise(Erreur_execution "tableau attendu");;
let affiche_valeur v =
  print_int(ent_val v); print_newline();;

let lire_valeur () =
  let entree = read_line() in
  try Ent(int_of_string entree)
  with Failure _ -> raise(Erreur_execution "erreur de lecture");;
```

## Adapted Example

```ocaml
#open "interp";;
let int_val = function
  | Int n -> n
  | _ -> raise(Runtime_error "integer expected")
and bool_val = function
  | Bool b -> b
  | _ -> raise(Runtime_error "boolean expected")
and array_val = function
  | Array(lower, values) -> (lower, values)
  | _ -> raise(Runtime_error "array expected")
;;
let print_value v =
  print_int(int_val v); print_newline()
;;
let read_value () =
  let input = read_line() in
  try Int(int_of_string input)
  with Failure _ -> raise(Runtime_error "read error")
;;
```

## Adaptation Notes

- Restored the `#open "interp"` bootstrap directive now that the parser models
  Caml Light source directives.
- Translated French identifiers and diagnostic strings to English.
- Replaced accented source identifiers with ASCII names.

## Parser Fixes

- The parser changes from example 3 already cover the `try`/`with` and
  equality-related syntax used by this example.
- Added source-level `#open` directive parsing.
