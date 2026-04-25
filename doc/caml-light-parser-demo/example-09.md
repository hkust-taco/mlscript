# Example 09: Bubble Sort Animation

Status: Done

## Source

- Repository path: `sources/examples/showsort/bubble.ml`
- Local clone path:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight/sources/examples/showsort/bubble.ml`

## Original Example

```ocaml
#open "animation";;

let sort gc =
  let ordered = ref true in
  let rec sweep i =
    if i+1 >= vect_length gc.array then
      if !ordered then
        Finished
      else begin
        ordered := false;
        sweep 0
      end
    else
      Pause(fun () ->
        if gc.array.(i+1) < gc.array.(i) then begin
          exchange gc i (i+1);
          ordered := false
        end;
        sweep(i+1))
  in sweep 0
;;
```

## Adapted Example

```ocaml
#open "animation";;
let sort context =
  let ordered = ref true in
  let rec sweep i =
    if i + 1 >= vect_length context.array then
      if !ordered then
        Finished
      else begin
        ordered := false;
        sweep 0
      end
    else
      Pause(fun () ->
        if context.array.(i + 1) < context.array.(i) then begin
          exchange context i (i + 1);
          ordered := false
        end;
        sweep(i + 1))
  in sweep 0
;;
```

## Adaptation Notes

- Restored the `#open "animation"` bootstrap directive now that the parser
  models Caml Light source directives.
- Renamed the short `gc` parameter to `context` for readability in the
  generated tree.
- Added spaces around arithmetic operators; no semantic rewrite was needed.

## Parser Fixes

- The prefix `!` fix from example 8 is used by this example.
- Added source-level `#open` directive parsing.
