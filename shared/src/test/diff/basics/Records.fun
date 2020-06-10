
let empty = {}
/// empty: {}

let r = {u:1,v:2}
let r = {u: 1, v: 2}
let r = { u: 1, v: 2 }
let r = { u: 1,v: 2 }
/// r: {u: int, v: int}
/// r: {u: int, v: int}
/// r: {u: int, v: int}
/// r: {u: int, v: int}

r.u + r.v
/// res: int

:e
empty.w
r.w
/// /!\ Type error at line 19: missing field: w in {}
/// /!\ Type error at line 19: missing field: w in {u: int, v: int}
/// res: ⊥
/// res: ⊥

let rec sumHeads = x => x.head + sumHeads x.tail
/// sumHeads: {head: int, tail: 'a} as 'a -> int

let rec ouroboros = {head: 0, tail: ouroboros, eyes: {l: 1, r: 2}}
/// ouroboros: {eyes: {l: int, r: int}, head: int, tail: 'a} as 'a

sumHeads ouroboros
/// res: int

// FIXME newlines
let r = {
  u: 1, v: 2 }
let r = {
  u: 1
  v: 2
}
let r = { u:
  1, v: 2 }
let r = {
  u:
    1
  v:
    2
}
/// /!\ Parse error: Expected (let | lams):1:1, found "let r = {\n" at line 35:   u: 1, v: 2 }

