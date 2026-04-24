# Source Discovery

Date: 2026-04-25

## Sources

- Official Caml Light page: `https://caml.inria.fr/caml-light/`
- Official INRIA examples page: `https://caml.inria.fr/pub/old_caml_site/Examples/eng.html`
- Official example archive from that page:
  `https://caml.inria.fr/pub/old_caml_site/Examples/camllight-examples-0.75.tar.gz`
- GitHub source mirror cloned for local inspection:
  `https://github.com/camllight/camllight.git`

## Local Temporary Files

- Temporary workspace: `/tmp/caml-light-parser-demo.aWVE6K`
- Git clone: `/tmp/caml-light-parser-demo.aWVE6K/camllight`
- Example archive unpacked at:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight-examples-0.75`

## Discovery Notes

The official Caml Light page links to download/manual resources but not directly
to GitHub. The official INRIA examples page links the Caml Light example archive.
The cloned GitHub source mirror contains a matching `sources/examples` tree, so
the example ports will use `sources/examples` paths and cross-check against the
official archive when useful.

Candidate examples include:

- `basics/fib.ml`
- `basics/sieve.ml`
- `basics/wc.ml`
- `calc/calc.ml`
- `grep/ensent.ml`
- `compress/esbit.ml`
- `compress/fileprio.ml`
- `demonstr/prop.ml`
- `demonstr/demo.ml`
- `picomach/code.ml`
- `picomach/asm.ml`
- `picomach/exec.ml`
- `pascal/valeur.ml`
- `minilogo/crayon.ml`
- `hanoi/hanoi.ml`

Some examples use Caml Light features the current parser may not support, such
as stream parser syntax, `#open`, character literals, or French identifiers with
accented letters. The porting pass will translate French names to English and
adapt unsupported surface syntax when that preserves the example's parser value.
