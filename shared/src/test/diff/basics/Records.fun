
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
r . u + r . v
r .u + r .v
r. u + r. v
/// res: int
/// res: int
/// res: int
/// res: int

:e
empty.w
r.w
/// /!\ Type error: missing field: w in {}
/// l.24: 	empty.w
///       	     ^^
/// /!\ Type error: missing field: w in {u: int, v: int}
/// l.25: 	r.w
///       	 ^^
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
/// /!\ Parse error: Expected let binding:1:1, found "let r = {\n" at l.45:1: let r = {

