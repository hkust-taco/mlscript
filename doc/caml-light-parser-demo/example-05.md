# Example 05: Picomach Constants

Status: Done

## Source

- Repository path: `sources/examples/picomach/code.ml`
- Local clone path:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight/sources/examples/picomach/code.ml`

## Original Example

```ocaml
let nombre_de_registres = 32
and sp = 30
and ra = 31
and taille_du_mot = 4;;
```

## Adapted Example

```ocaml
let register_count = 32
and sp = 30
and ra = 31
and word_size = 4
;;
```

## Adaptation Notes

- Translated French constant names to English.
- Kept the original chained `and` binding shape.

## Parser Fixes

- None.
