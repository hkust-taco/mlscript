
let t3 = 1, 2, 3
let t3 = 1, 2, 3,
let t2 = 1, 2,
let t1 = 1,
let t0 = ()
/// t3: {_1: int, _2: int, _3: int}
/// t3: {_1: int, _2: int, _3: int}
/// t2: {_1: int, _2: int}
/// t1: {_1: int}
/// t0: {}

let t = 1, y: 2, 3
let t = x: 1, y: 2, z: 3
/// t: {_1: int, _3: int, y: int}
/// t: {x: int, y: int, z: int}

(1, true, "hey")._2
/// res: bool

:p
:e
(1, true, "hey").2
/// Parsed: (((1, true, "hey",);) 0.2);
/// /!\ Type error: cannot constrain {_1: int, _2: bool, _3: string} <: number -> 'a
/// l.23: 	(1, true, "hey").2
///       	^^^^^^^^^^^^^^^^^^
/// res: ⊥

:e
let not-tup = (
  1
  2
)
/// /!\ Type error: Pure expression does nothing in statement position.
/// l.32: 	  1
///       	  ^
/// not-tup: int

:e
let tup = (
  1,
  2
)
/// /!\ Type error: Previous field definitions are discarded by this returned expression.
/// l.43: 	  2
///       	  ^
/// tup: int

:e
let tup =
  1,
  2,
  3
/// /!\ Type error: Previous field definitions are discarded by this returned expression.
/// l.54: 	  3
///       	  ^
/// tup: int

let tup =
  1,
  2,
  3,
/// tup: {_1: int, _2: int, _3: int}

