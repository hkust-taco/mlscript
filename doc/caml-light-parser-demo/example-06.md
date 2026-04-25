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
type buffer = { mutable val: int; mutable nbits: int };;
let buffer = { val = 0; nbits = 0 };;
let initialize () = buffer.val <- 0; buffer.nbits <- 0;;
let write_bit output bit =
  buffer.val <- buffer.val lor (bit lsl buffer.nbits);
  buffer.nbits <- buffer.nbits + 1;
  if buffer.nbits >= 8 then begin
    output_char output (char_of_int buffer.val);
    buffer.val <- 0;
    buffer.nbits <- 0
  end
;;
let finish output =
  if buffer.nbits > 0 then
    output_char output (char_of_int buffer.val)
;;
let read_bit input =
  if buffer.nbits <= 0 then begin
    buffer.val <- int_of_char(input_char input);
    buffer.nbits <- 8
  end;
  let result = buffer.val land 1 in
  buffer.val <- buffer.val lsr 1;
  buffer.nbits <- buffer.nbits - 1;
  result
;;
```

## Adaptation Notes

- Translated French identifiers to English.
- Restored the original `val` field name after confirming field names are
  parsed as labels in record types, record values, and field selections.
- Restored the type-level `mutable` annotations after adding parser support for
  mutable record labels.

## Parser Fixes

- Added general keyword-level infix parsing for Caml Light alphabetic operators:
  `mod`, `land`, `lor`, `lxor`, `lsl`, `lsr`, and `asr`.
- This also corrected the previously ported sieve example's `m mod n` tree.
- Added type-level mutable record label parsing.
- Verified that the existing label parsing path already accepts the
  reserved-looking `val` field name without broad parser changes.
