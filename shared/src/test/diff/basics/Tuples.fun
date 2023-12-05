
let t3 = 1, 2, 3
let t3 = 1, 2, 3,
let t2 = 1, 2,
let t1 = 1,
let t0 = ()
//│ t3: (1, 2, 3,)
//│ t3: (1, 2, 3,)
//│ t2: (1, 2,)
//│ t1: (1,)
//│ t0: ()

let t = 1, y: 2, 3
let t = x: 1, y: 2, z: 3
//│ t: (1, y: 2, 3,)
//│ t: (x: 1, y: 2, z: 3,)

(1, true, "hey").1
(1, true, "hey").2
//│ res: true
//│ res: "hey"

:e
(1, true, "hey").3
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.24: 	(1, true, "hey").3
//│ ║        	                ^^
//│ ╟── tuple of type `{0: 1, 1: true, 2: "hey"}` does not have field '3'
//│ ║  l.24: 	(1, true, "hey").3
//│ ║        	 ^^^^^^^^^^^^^^
//│ ╟── but it flows into receiver with expected type `{3: ?a}`
//│ ║  l.24: 	(1, true, "hey").3
//│ ╙──      	^^^^^^^^^^^^^^^^
//│ res: error

(1, true, "hey").1
//│ res: true

:w
let not-tup = (
  1
  2
)
//│ ╔══[WARNING] Pure expression does nothing in statement position.
//│ ║  l.41: 	  1
//│ ╙──      	  ^
//│ not-tup: 2

:w
let tup = (
  1,
  2
)
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.52: 	  2
//│ ╙──      	  ^
//│ tup: 2

:w
let tup =
  1,
  2,
  3
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.63: 	  3
//│ ╙──      	  ^
//│ tup: 3

let tup =
  1,
  2,
  3,
//│ tup: (1, 2, 3,)

