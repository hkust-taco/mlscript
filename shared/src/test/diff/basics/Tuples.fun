
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
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.23: 	(1, true, "hey").2
//│ ║        	^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `{_1: 1, _2: bool, _3: "hey"}` is not a function
//│ ║  l.23: 	(1, true, "hey").2
//│ ║        	 ^^^^^^^^^^^^^^
//│ ╟── but it flows into applied expression
//│ ║  l.23: 	(1, true, "hey").2
//│ ║        	^^^^^^^^^^^^^^^^
//│ ╙── which is not a function
//│ res: nothing

:w
let not-tup = (
  1
  2
)
//│ ╔══[WARNING] Pure expression does nothing in statement position.
//│ ║  l.39: 	  1
//│ ╙──      	  ^
//│ not-tup: 2

:w
let tup = (
  1,
  2
)
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.50: 	  2
//│ ╙──      	  ^
//│ tup: 2

:w
let tup =
  1,
  2,
  3
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.61: 	  3
//│ ╙──      	  ^
//│ tup: 3

let tup =
  1,
  2,
  3,
//│ tup: {_1: 1, _2: 2, _3: 3}

