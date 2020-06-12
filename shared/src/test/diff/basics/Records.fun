
let empty = {}
/// empty: unit

x : 1
x: 1
{x: 1}
x: 1, y: 2
/// res: {x: int}
/// res: {x: int}
/// res: {x: int}
/// res: {x: int, y: int}

let r = {u:1,v:2}
let r = { u:1 , v:2 }
let r = { u :1 , v :2 }
let r = {u: 1, v: 2}
let r = { u: 1, v: 2 }
let r = { u: 1,v: 2 }
/// r: {u: int, v: int}
/// r: {u: int, v: int}
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
/// /!\ Type error: cannot constrain unit <: {w: 'a}
/// l.37: 	empty.w
///       	     ^^
/// /!\ Type error: missing field: w in {u: int, v: int}
/// l.38: 	r.w
///       	 ^^
/// res: ⊥
/// res: ⊥

let rec sumHeads = x => x.head + sumHeads x.tail
/// sumHeads: {head: int, tail: 'a} as 'a -> int

let rec ouroboros = {head: 0, tail: ouroboros, eyes: {l: 1, r: 2}}
/// ouroboros: {eyes: {l: int, r: int}, head: int, tail: 'a} as 'a

sumHeads ouroboros
/// res: int

let r = {
  u: 1, v: 2 }
let r = {
  u: 1 // TODO u should be a field
  v: 2
}
/// r: {u: int, v: int}
/// r: {v: int}

let r = {
  u: // TODO u should be a field
    1
  v:
    2
}
/// r: {v: int}

// TODO disallow or warn about this?
let r = { u:
  1, v: 2 }
/// r: {u: {_1: int, v: int}}
