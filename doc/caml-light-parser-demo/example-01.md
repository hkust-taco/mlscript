# Example 01: Fibonacci

Status: Done

## Source

- Repository path: `sources/examples/basics/fib.ml`
- Local clone path:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight/sources/examples/basics/fib.ml`

## Original Example

```ocaml
(* The Fibonacci function, once more. *)

let rec fib n =
  if n < 2 then 1 else fib(n-1) + fib(n-2)
;;

if sys__interactive then () else
if vect_length sys__command_line <> 2 then begin
  print_string "Usage: fib <number>";
  print_newline()
end else begin
  try
    print_int(fib(int_of_string sys__command_line.(1)));
    print_newline()
  with Failure "int_of_string" ->
    print_string "Bad integer constant";
    print_newline()
end
;;
```

## Adapted Example

```ocaml
let rec fib n =
  if n < 2 then 1 else fib(n-1) + fib(n-2)
;;

if sys__interactive then () else
if vect_length sys__command_line <> 2 then begin
  print_string "Usage: fib <number>";
  print_newline()
end else begin
  try
    print_int(fib(int_of_string sys__command_line.(1)));
    print_newline()
  with Failure "int_of_string" ->
    print_string "Bad integer constant";
    print_newline()
end
;;
```

## Adaptation Notes

- Removed only the leading comment from the parsed snippet.
- Kept the command-line wrapper because it parses useful nested conditionals,
  exception handling, sequencing, and vector access.

## Parser Fixes

- Added a general `try ... with ...` parser rule.
- Added `Tree.Try` so exception handling is represented explicitly in syntax
  trees.
- Set the `try` body precedence low enough for sequence bodies such as
  `try a; b with ...`.
