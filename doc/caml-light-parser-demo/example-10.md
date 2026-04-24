# Example 10: Insertion Sort Animation

Status: Done

## Source

- Repository path: `sources/examples/showsort/insertion.ml`
- Local clone path:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight/sources/examples/showsort/insertion.ml`

## Original Example

```ocaml
#open "animation";;

let sort gc =
  let rec loop1 i =
    if i >= vect_length gc.array then Finished else
    let val_i = gc.array.(i) in
    let rec loop2 j =
      if j < 1 then begin
        assign gc j val_i;
        loop1 (i+1)
      end else
        Pause(fun () ->
          if val_i >= gc.array.(j-1) then begin
            assign gc j val_i;
            loop1 (i+1)
          end else begin
            assign gc j gc.array.(j-1);
            loop2 (j-1)
          end)
    in loop2 i
  in loop1 1
;;
```

## Adapted Example

```ocaml
let sort context =
  let rec loop_outer i =
    if i >= vect_length context.array then Finished else
    let value_i = context.array.(i) in
    let rec loop_inner j =
      if j < 1 then begin
        assign context j value_i;
        loop_outer (i + 1)
      end else
        Pause(fun () ->
          if value_i >= context.array.(j - 1) then begin
            assign context j value_i;
            loop_outer (i + 1)
          end else begin
            assign context j context.array.(j - 1);
            loop_inner (j - 1)
          end)
    in loop_inner i
  in loop_outer 1
;;
```

## Adaptation Notes

- Removed the `#open "animation"` bootstrap directive.
- Renamed `gc`, `loop1`, `loop2`, and `val_i` to more descriptive English
  names in the adapted syntax tree.
- Added spaces around arithmetic operators; no parser workaround was required.

## Parser Fixes

- None.
