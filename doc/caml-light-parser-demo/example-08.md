# Example 08: Word Count

Status: Done

## Source

- Repository path: `sources/examples/basics/wc.ml`
- Local clone path:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight/sources/examples/basics/wc.ml`

## Original Example

```ocaml
let chars = ref 0
and words = ref 0
and lines = ref 0
;;

type state = Inside_word | Outside_word;;

let count_channel in_channel =
  let rec count status =
    let c = input_char in_channel in
    incr chars;
    match c with
    | `\n` ->
        incr lines; count Outside_word
    | ` ` | `\t` ->
        count Outside_word
    | _ ->
        if status = Outside_word then begin incr words; () end;
        count Inside_word
  in
    try
      count Outside_word
    with End_of_file ->
      ()
;;

let count_file name =
  let ic = open_in name in
  count_channel ic;
  close_in ic
;;

let print_result () =
  print_int !chars; print_string " characters, ";
  print_int !words; print_string " words, ";
  print_int !lines; print_string " lines";
  print_newline()
;;

let count name =
  count_file name;
  print_result ()
;;

if sys__interactive then () else
try
  if vect_length sys__command_line <= 1 then
    count_channel std_in
  else
    for i = 1 to vect_length sys__command_line - 1 do
      count_file  sys__command_line.(i)
    done;
  print_result ();
with sys__Sys_error s ->
  print_string "I/O error: ";
  print_string s;
  print_newline()
;;
```

## Adapted Example

```ocaml
let chars = ref 0
and words = ref 0
and lines = ref 0
;;

type state = Inside_word | Outside_word;;

let count_channel input_channel =
  let rec count status =
    let c = input_char input_channel in
    incr chars;
    match c with
    | `\n` ->
        incr lines; count Outside_word
    | ` ` | `\t` ->
        count Outside_word
    | _ ->
        if status = Outside_word then begin incr words; () end;
        count Inside_word
  in
    try
      count Outside_word
    with End_of_file ->
      ()
;;

let count_file name =
  let ic = open_in name in
  count_channel ic;
  close_in ic
;;

let print_result () =
  print_int !chars; print_string " characters, ";
  print_int !words; print_string " words, ";
  print_int !lines; print_string " lines";
  print_newline()
;;

let count name =
  count_file name;
  print_result ()
;;

if sys__interactive then () else
try
  if vect_length sys__command_line <= 1 then
    count_channel std_in
  else
    for i = 1 to vect_length sys__command_line - 1 do
      count_file sys__command_line.(i)
    done;
  print_result ()
with sys__Sys_error s ->
  print_string "I/O error: ";
  print_string s;
  print_newline()
;;
```

## Adaptation Notes

- Renamed `in_channel` to `input_channel` to avoid the `in` keyword prefix in an
  identifier-like name.
- Restored the original alternative pattern `` ` ` | `\t` `` after adding
  dedicated pattern parsing for alternatives inside one branch.

## Parser Fixes

- Added Caml Light character literal tokenization for backtick character
  literals such as `` `\n` ``.
- Fixed `for` headers to parse the loop variable with the same binding-stop
  mode used for let-binding left-hand sides.
- Split prefix-only symbolic operators such as `!` from the generic symbolic
  infix path, so dereference parses as a prefix expression.
- Added dedicated pattern parsing for alternatives inside one branch.
