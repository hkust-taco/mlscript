
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

(1, true, "hey")._2
(1, true, "hey")._3
//│ res: true
//│ res: "hey"

:e
(1, true, "hey")._4
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.24: 	(1, true, "hey")._4
//│ ║        	                ^^^
//│ ╟── tuple of type `{_1: 1, _2: true, _3: "hey"}` does not have field '_4'
//│ ║  l.24: 	(1, true, "hey")._4
//│ ║        	 ^^^^^^^^^^^^^^
//│ ╟── but it flows into receiver with expected type `{_4: ?a}`
//│ ║  l.24: 	(1, true, "hey")._4
//│ ╙──      	^^^^^^^^^^^^^^^^
//│ res: error

:p
:e
(1, true, "hey").2
//│ Parsed: '(' {1, true, "hey",} ')' 0.2;
//│ Desugared: '(' {1, true, "hey",} ')' 0.2
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.38: 	(1, true, "hey").2
//│ ║        	^^^^^^^^^^^^^^^^^^
//│ ╟── tuple of type `(1, true, "hey",)` is not a function
//│ ║  l.38: 	(1, true, "hey").2
//│ ║        	 ^^^^^^^^^^^^^^
//│ ╟── but it flows into applied expression with expected type `0.2 -> ?a`
//│ ║  l.38: 	(1, true, "hey").2
//│ ╙──      	^^^^^^^^^^^^^^^^
//│ res: error

:w
let not-tup = (
  1
  2
)
//│ ╔══[WARNING] Pure expression does nothing in statement position.
//│ ║  l.54: 	  1
//│ ╙──      	  ^
//│ not-tup: 2

:w
let tup = (
  1,
  2
)
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.65: 	  2
//│ ╙──      	  ^
//│ tup: 2

:w
let tup =
  1,
  2,
  3
//│ ╔══[WARNING] Previous field definitions are discarded by this returned expression.
//│ ║  l.76: 	  3
//│ ╙──      	  ^
//│ tup: 3

let tup =
  1,
  2,
  3,
//│ tup: (1, 2, 3,)

