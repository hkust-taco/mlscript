
let empty = {}
//│ empty: {}

1
(1)
((1))
{1}
{{1}}
{(1)}
//│ res: 1
//│ res: 1
//│ res: 1
//│ res: 1
//│ res: 1
//│ res: 1

x : 1
x: 1
{x: 1}
x: 1, y: 2
//│ res: {x: 1}
//│ res: {x: 1}
//│ res: {x: 1}
//│ res: {x: 1, y: 2}

x : 1, 2, 3
x: 1, 2, z: 3
1, y: 2, z: 3
x: 1, y: 2, z: 3
//│ res: {_2: 2, _3: 3, x: 1}
//│ res: {_2: 2, x: 1, z: 3}
//│ res: {_1: 1, y: 2, z: 3}
//│ res: {x: 1, y: 2, z: 3}

let r = {u:1,v:2}
let r = { u:1 , v:2 }
let r = { u :1 , v :2 }
let r = {u: 1, v: 2}
let r = { u: 1, v: 2 }
let r = { u: 1,v: 2 }
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}

r.u + r.v
r . u + r . v
r .u + r .v
r. u + r. v
//│ res: int
//│ res: int
//│ res: int
//│ res: int

:e
empty.w
r.w
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.59: 	empty.w
//│ ║        	     ^^
//│ ╟── expression of type `{}` does not have field 'w'
//│ ║  l.2: 	let empty = {}
//│ ║       	            ^^
//│ ╟── but it flows into variable reference of expected type `{w: ?a}`
//│ ║  l.59: 	empty.w
//│ ╙──      	^^^^^
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.60: 	r.w
//│ ║        	 ^^
//│ ╟── expression of type `{u: 1, v: 2}` does not have field 'w'
//│ ║  l.41: 	let r = { u: 1,v: 2 }
//│ ║        	        ^^^^^^^^^^^^^
//│ ╟── but it flows into variable reference of expected type `{w: ?a}`
//│ ║  l.60: 	r.w
//│ ╙──      	^
//│ res: error
//│ res: error

let rec sumHeads = x => x.head + sumHeads x.tail
//│ sumHeads: {head: int, tail: 'a} as 'a -> int

let rec ouroboros = {head: 0, tail: ouroboros, eyes: {l: 1, r: 2}}
//│ ouroboros: {eyes: {l: 1, r: 2}, head: 0, tail: 'a} as 'a

sumHeads ouroboros
//│ res: int

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
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: int}

:pe
let r = {
  u: 1;
  v: 2;
}
//│ /!\ Parse error: Expected let binding:1:1, found "let r = {\n" at l.121:1: let r = {

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
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}
//│ r: {u: {x: 1}, v: {y: 2}}
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
//│ r: {u: {x: 1, y: 2}, v: {x: 3, y: 4}}

// TODO disallow or warn about this?
let r = { u:
  1, v: 2 }
//│ r: {u: {_1: 1, v: 2}}

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
//│ r: {u: {x: 1, y: 2}, v: {x: 3, y: 4}}
//│ r: {u: {x: 1, y: 2}, v: {x: 3, y: 4}}
//│ r: {u: {x: 1, y: 2}, v: {x: 3, y: 4}}

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
//│ r: {u: {x: 1, y: 2}, v: {x: 3, y: 4}}
//│ r: {u: {x: 1, y: 2}, v: {x: 3, y: 4}}

let r = (
  u:
    x: 1,
    y: 2,,
  v:
    x: 3,
    y: 4,
)
//│ r: {u: {x: 1, y: 2}, v: {x: 3, y: 4}}

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
//│ /!\ Parse error: Expected let binding:1:1, found "let r = (\n" at l.232:1: let r = (

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
//│ res: {a: {b: {c: 1}}}
//│ res: {a: {b: {c: 1}, d: 2}}
//│ res: {a: {b: {c: 1}, d: 2}}

// :e // used to raise: useless fields in statement position
a:
  b:
    c:
      1
  d: 2
//│ res: {a: {b: {c: 1}, d: 2}}

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
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.275: 	  3
//│ ╙──       	  ^
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.279: 	  3
//│ ╙──       	  ^
//│ res: {a: 3}
//│ res: {a: 3}

let r =
  x: 1
  log x
  y: 2
let r =
  x: 1
  log x
  y: 2
  let _ = log y
//│ r: {x: 1, y: 2}
//│ r: {x: 1, y: 2}

// TODO ignore return-position unit expressions?
:w
let r =
  x: 1
  log x
  y: 2
  log y
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.308: 	  log y
//│ ╙──       	  ^^^^^
//│ r: unit


// Funnily, because of dependent record literals, one can do:
:w
let res =
  arg: 0
  arg + 1
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.319: 	  arg + 1
//│ ╙──       	  ^^^^^^^
//│ res: int

