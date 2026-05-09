This directory contains five pattern-compilation example programs, which define seven compiled entry patterns.

The table below counts non-empty lines in the generated `.mjs` files. "Referenced pattern names" means direct pattern references in the source pattern body.

| Pattern name | Referenced pattern names | Referenced pattern class SLOC | `_optimized` SLOC | `_optimized_matchOnly` SLOC |
| --- | --- | ---: | ---: | ---: |
| `Truthy` | `Truthy`, `Falsy` | 368 | 1173 | 710 |
| `Falsy` | `Falsy`, `Truthy` | 368 | 1173 | 710 |
| `OddTree` | `OddTree`, `EvenTree` | 858 | 3355 | 2006 |
| `EvenTree` | `EvenTree`, `OddTree` | 858 | 3355 | 2006 |
| `Step` | `Ctx`, `Redex` | 289 | 1266 | 516 |
| `DnfOrCnf` | `DnfOrCnf`, `Dnf`, `Cnf` | 506 | 777 | 541 |
| `DnfAndCnf` | `DnfAndCnf`, `Dnf`, `Cnf` | 506 | 326 | 222 |
