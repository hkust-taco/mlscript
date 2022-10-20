
let empty = {}
//│ empty: anything

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
//│ res: (x: 1,)
//│ res: (x: 1,)
//│ res: {x: 1}
//│ res: (x: 1, y: 2,)

x : 1, 2, 3
x: 1, 2, z: 3
1, y: 2, z: 3
x: 1, y: 2, z: 3
//│ res: (x: 1, 2, 3,)
//│ res: (x: 1, 2, z: 3,)
//│ res: (1, y: 2, z: 3,)
//│ res: (x: 1, y: 2, z: 3,)

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
//│ ╟── tuple of type `anything` does not have field 'w'
//│ ║  l.2: 	let empty = {}
//│ ║       	            ^^
//│ ╟── but it flows into reference with expected type `{w: ?w}`
//│ ║  l.59: 	empty.w
//│ ╙──      	^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.60: 	r.w
//│ ║        	 ^^
//│ ╟── record of type `{u: 1, v: 2}` does not have field 'w'
//│ ║  l.41: 	let r = { u: 1,v: 2 }
//│ ║        	        ^^^^^^^^^^^^^
//│ ╟── but it flows into reference with expected type `{w: ?w}`
//│ ║  l.60: 	r.w
//│ ╙──      	^
//│ res: error







let rec sumHeads = x => x.head + sumHeads x.tail
//│ sumHeads: 'a -> int
//│   where
//│     'a <: {head: int, tail: 'a}

let rec ouroboros = {head: 0, tail: ouroboros, eyes: {l: 1, r: 2}}
//│ ouroboros: 'ouroboros
//│   where
//│     'ouroboros :> {eyes: {l: 1, r: 2}, head: 0, tail: 'ouroboros}

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
//│ /!\ Parse error: Expected let binding:1:1, found "let r = {\n" at l.131:1: let r = {

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
// ^ FIXME? field punning...
//│ r: {u: 1, v: 2}
//│ r: {u: 1, v: 2}
//│ r: {u: {x: 1}, v: {y: 2}}

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

:w // Disallow or warn about this?
let r = { u:
  1, v: 2 }
//│ ╔══[WARNING] Missing name for record field
//│ ║  l.177: 	  1, v: 2 }
//│ ╙──       	  ^
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
//│ r: (u: (x: 1, y: 2,), v: (x: 3, y: 4,),)
//│ r: (u: (x: 1, y: 2,), v: (x: 3, y: 4,),)
//│ r: (u: (x: 1, y: 2,), v: (x: 3, y: 4,),)

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
//│ r: (u: (x: 1, y: 2,), v: (x: 3, y: 4,),)
//│ r: (u: (x: 1, y: 2,), v: (x: 3, y: 4,),)

let r = (
  u:
    x: 1,
    y: 2,,
  v:
    x: 3,
    y: 4,
)
//│ r: (u: (x: 1, y: 2,), v: (x: 3, y: 4,),)

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
//│ /!\ Parse error: Expected let binding:1:1, found "let r = (\n" at l.246:1: let r = (

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
//│ res: (a: (b: (c: 1,),),)
//│ res: (a: {b: {c: 1}, d: 2},)
//│ res: (a: (b: {c: 1}, d: 2,),)

// :e // used to raise: useless fields in statement position
a:
  b:
    c:
      1
  d: 2
//│ res: (a: (b: (c: 1,), d: 2,),)

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
//│ ║  l.289: 	  3
//│ ╙──       	  ^
//│ res: (a: 3,)
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.293: 	  3
//│ ╙──       	  ^
//│ res: (a: 3,)



let r =
  x: 1
  log x
  y: 2
let r =
  x: 1
  log x
  y: 2
  let _ = log y
//│ r: (x: 1, y: 2,)
//│ r: (x: 1, y: 2,)

// TODO ignore return-position unit expressions?
:w
let r =
  x: 1
  log x
  y: 2
  log y
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.324: 	  log y
//│ ╙──       	  ^^^^^
//│ r: unit



// Funnily, because of dependent record literals, one can do:
:w
let res =
  arg: 0
  arg + 1
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.336: 	  arg + 1
//│ ╙──       	  ^^^^^^^
//│ res: int


