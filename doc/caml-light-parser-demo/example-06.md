# Example 06: Compression Bit Buffer

Status: Done

## Source

- Repository path: `sources/examples/compress/esbit.ml`
- Local clone path:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight/sources/examples/compress/esbit.ml`

## Original Example

```ocaml
type tampon = { mutable val: int; mutable nbits: int };;
let tampon = { val = 0; nbits = 0 };;
let initialise () = tampon.val <- 0; tampon.nbits <- 0;;
let ecrire_bit sortie bit =
  tampon.val <- tampon.val lor (bit lsl tampon.nbits);
  tampon.nbits <- tampon.nbits + 1;
  if tampon.nbits >= 8 then begin
    output_char sortie (char_of_int tampon.val);
    tampon.val <- 0;
    tampon.nbits <- 0
  end;;

let finir sortie =
  if tampon.nbits > 0 then
    output_char sortie (char_of_int tampon.val);;
let lire_bit entree =
  if tampon.nbits <= 0 then begin
    tampon.val <- int_of_char(input_char entree);
    tampon.nbits <- 8
  end;
  let res = tampon.val land 1 in
  tampon.val <- tampon.val lsr 1;
  tampon.nbits <- tampon.nbits - 1;
  res;;
```

## Adapted Example

```ocaml
type buffer = { mutable value: int; mutable nbits: int };;
let buffer = { value = 0; nbits = 0 };;
let initialize () = buffer.value <- 0; buffer.nbits <- 0;;
let write_bit output bit =
  buffer.value <- buffer.value lor (bit lsl buffer.nbits);
  buffer.nbits <- buffer.nbits + 1;
  if buffer.nbits >= 8 then begin
    output_char output (char_of_int buffer.value);
    buffer.value <- 0;
    buffer.nbits <- 0
  end
;;
let finish output =
  if buffer.nbits > 0 then
    output_char output (char_of_int buffer.value)
;;
let read_bit input =
  if buffer.nbits <= 0 then begin
    buffer.value <- int_of_char(input_char input);
    buffer.nbits <- 8
  end;
  let result = buffer.value land 1 in
  buffer.value <- buffer.value lsr 1;
  buffer.nbits <- buffer.nbits - 1;
  result
;;
```

## Adaptation Notes

- Translated French identifiers to English.
- Replaced `val` with `value` to avoid using a reserved-looking field name.
- Restored the type-level `mutable` annotations after adding parser support for
  mutable record labels.

## Parser Fixes

- Added general keyword-level infix parsing for Caml Light alphabetic operators:
  `mod`, `land`, `lor`, `lxor`, `lsl`, `lsr`, and `asr`.
- This also corrected the previously ported sieve example's `m mod n` tree.
- Added type-level mutable record label parsing.
