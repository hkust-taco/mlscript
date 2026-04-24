# Example 02: Sieve of Eratosthenes

Status: Done

## Source

- Repository path: `sources/examples/basics/sieve.ml`
- Local clone path:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight/sources/examples/basics/sieve.ml`

## Original Example

```ocaml
let rec interval min max =
  if min > max then [] else min :: interval (succ min) max
;;

let rec filter p = function
  | []  -> []
  | a::r -> if p a then a :: filter p r else filter p r
;;

let remove_multiples_of n =
  filter (fun m -> m mod n <> 0)
;;

let sieve max =
  let rec filter_again = function
  | [] -> []
  | n::r as l ->
      if n*n > max then l else n :: filter_again (remove_multiples_of n r)
  in
    filter_again (interval 2 max)
;;
```

## Adapted Example

```ocaml
let rec interval min max =
  if min > max then [] else min :: interval (succ min) max
;;
let rec filter p = function
  | [] -> []
  | a :: r -> if p a then a :: filter p r else filter p r
;;
let remove_multiples_of n =
  filter (fun m -> m mod n <> 0)
;;
let sieve max =
  let rec filter_again = function
  | [] -> []
  | n :: r ->
      if n * n > max then n :: r else n :: filter_again (remove_multiples_of n r)
  in
    filter_again (interval 2 max)
;;
```

## Adaptation Notes

- Kept the core sieve implementation and omitted the command-line wrapper.
- Replaced `n::r as l` with `n :: r` and reconstructed `n :: r` in the branch,
  because the current pattern parser still treats patterns as terms and `as`
  patterns are future dedicated-pattern work.
- Removed blank lines inside the test block so HKMC2 DiffTests keep the whole
  multiline string in one block.

## Parser Fixes

- None.
