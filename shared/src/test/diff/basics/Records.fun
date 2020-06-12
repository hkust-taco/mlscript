
let empty = {}
/// empty: {}

1
(1)
((1))
{1}
{{1}}
{(1)}
/// res: int
/// res: int
/// res: int
/// res: int
/// res: int
/// res: int

x : 1
x: 1
{x: 1}
x: 1, y: 2
/// res: {x: int}
/// res: {x: int}
/// res: {x: int}
/// res: {x: int, y: int}

x : 1, 2, 3
x: 1, 2, z: 3
1, y: 2, z: 3
x: 1, y: 2, z: 3
/// res: {_2: int, _3: int, x: int}
/// res: {_2: int, x: int, z: int}
/// res: {_1: int, y: int, z: int}
/// res: {x: int, y: int, z: int}

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
/// /!\ Type error: missing field: w in {}
/// l.59: 	empty.w
///       	     ^^
/// /!\ Type error: missing field: w in {u: int, v: int}
/// l.60: 	r.w
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
  u: 1,
  v: 2,
}
let r = {
  u: 1
  v: 2
}
let r = {
  u: 1,
  v: 2
}
let r = {
  u: 1;
  v: 2
}
let r = {
  u: 1
  v: u + 1
}
/// r: {u: int, v: int}
/// r: {u: int, v: int}
/// r: {u: int, v: int}
/// r: {u: int, v: int}
/// r: {u: int, v: int}
/// r: {u: int, v: int}

:pe
let r = {
  u: 1;
  v: 2;
}
/// /!\ Parse error: Expected let binding:1:1, found "let r = {\n" at l.109:1: let r = {

let r = {
  u:
    1
  v:
    2
}
let r = {
  u:
    log "ok"
    1
  v:
    log "ko"
    2
}
let r = {
  u:
    let x = 1
    x
  v:
    let y = 2
    y
}
/// r: {u: int, v: int}
/// r: {u: int, v: int}
/// r: {u: {x: int}, v: {y: int}}
// ^ FIXME? field punning...

// TODO
let r = {
  u:
    x: 1
    y: 2
  v:
    x: 3
    y: 4
}
/// r: {u: {x: int, y: int}, v: {x: int, y: int}}

// TODO disallow or warn about this?
let r = { u:
  1, v: 2 }
/// r: {u: {_1: int, v: int}}

// :e // used to raise: useless fields in statement position
let r =
  u:
    x: 1
    y: 2
  v:
    x: 3
    y: 4
let r = (
  u:
    x: 1
    y: 2
  v:
    x: 3
    y: 4
)
let r = (
  u: (
    x: 1
    y: 2
  ),
  v:
    x: 3
    y: 4
)
/// r: {u: {x: int, y: int}, v: {x: int, y: int}}
/// r: {u: {x: int, y: int}, v: {x: int, y: int}}
/// r: {u: {x: int, y: int}, v: {x: int, y: int}}

let r = (
  u: (
    x: 1,
    y: 2,
  ),
  v:
    x: 3
    y: 4
)
let r = (
  u: (
    x: 1,
    y: 2,
  ),
  v: (
    x: 3,
    y: 4,
  ),
)
/// r: {u: {x: int, y: int}, v: {x: int, y: int}}
/// r: {u: {x: int, y: int}, v: {x: int, y: int}}

let r = (
  u:
    x: 1,
    y: 2,,
  v:
    x: 3,
    y: 4,
)
/// r: {u: {x: int, y: int}, v: {x: int, y: int}}

:pe
let r = (
  u:
    x: 1,
    y: 2,
    ,
  v:
    x: 3,
    y: 4,
)
/// /!\ Parse error: Expected let binding:1:1, found "let r = (\n" at l.220:1: let r = (

a:
  b:
    c:
      1
a: {
  b:
    c:
      1
  d: 2
}
a:
  b: {
    c:
      1
  }
  d: 2
/// res: {a: {b: {c: int}}}
/// res: {a: {b: {c: int}, d: int}}
/// res: {a: {b: {c: int}, d: int}}

// :e // used to raise: useless fields in statement position
a:
  b:
    c:
      1
  d: 2
/// res: {a: {b: {c: int}, d: int}}

:w
a:
  b: 1
  c: 2
  3
a: {
  b: 1
  c: 2
  3
}
/// /!\ Warning: Previous field definitions are discarded by this returned expression.
/// l.263: 	  3
///        	  ^
/// /!\ Warning: Previous field definitions are discarded by this returned expression.
/// l.267: 	  3
///        	  ^
/// res: {a: int}
/// res: {a: int}

let r =
  x: 1
  log x
  y: 2
let r =
  x: 1
  log x
  y: 2
  let _ = log y
/// r: {x: int, y: int}
/// r: {x: int, y: int}

// FIXME ignore unit expressions
:w
let r =
  x: 1
  log x
  y: 2
  log y
/// /!\ Warning: Previous field definitions are discarded by this returned expression.
/// l.296: 	  log y
///        	  ^^^^^
/// r: unit
