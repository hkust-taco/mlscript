
let t3 = 1, 2, 3
let t3 = 1, 2, 3,
let t2 = 1, 2,
let t1 = 1,
let t0 = ()
//│ t3: {_1: 1, _2: 2, _3: 3}
//│ t3: {_1: 1, _2: 2, _3: 3}
//│ t2: {_1: 1, _2: 2}
//│ t1: {_1: 1}
//│ t0: {}

let t = 1, y: 2, 3
let t = x: 1, y: 2, z: 3
//│ t: {_1: 1, _3: 3, y: 2}
//│ t: {x: 1, y: 2, z: 3}

(1, true, "hey")._2
//│ res: bool

:p
:e
(1, true, "hey").2
//│ Parsed: (((1, true, "hey",);) 0.2);
//│ /!\ Type error: cannot constrain {_1: 1, _2: bool, _3: "hey"} <: 0.2 -> 'a
//│ l.23: 	(1, true, "hey").2
//│       	^^^^^^^^^^^^^^^^^^
//│ res: ⊥

:w
let not-tup = (
  1
  2
)
//│ /!\ Warning: Pure expression does nothing in statement position.
//│ l.32: 	  1
//│       	  ^
//│ not-tup: 2

:w
let tup = (
  1,
  2
)
//│ /!\ Warning: Previous field definitions are discarded by this returned expression.
//│ l.43: 	  2
//│       	  ^
//│ tup: 2

:w
let tup =
  1,
  2,
  3
//│ /!\ Warning: Previous field definitions are discarded by this returned expression.
//│ l.54: 	  3
//│       	  ^
//│ tup: 3

let tup =
  1,
  2,
  3,
//│ tup: {_1: 1, _2: 2, _3: 3}

