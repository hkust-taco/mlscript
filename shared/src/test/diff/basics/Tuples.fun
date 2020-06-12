
let t3 = 1, 2, 3
let t3 = 1, 2, 3,
let t2 = 1, 2,
let t1 = 1,
let t0 = ()
/// t3: {_1: int, _2: int, _3: int}
/// t3: {_1: int, _2: int, _3: int}
/// t2: {_1: int, _2: int}
/// t1: {_1: int}
/// t0: unit

(1, true, "hey")._2
/// res: bool

:p
:e
(1, true, "hey").2
/// Parsed: {({(1, true, "hey")} 0.2)}
/// /!\ Type error: cannot constrain {_1: int, _2: bool, _3: string} <: number -> 'a
/// l.18: 	(1, true, "hey").2
///       	^^^^^^^^^^^^^^^^^^
/// res: ⊥


let not-tup = (
  1
  2
)
/// not-tup: int

// TODO treat this as tuple...
let tup = (
  1,
  2
)
/// tup: int

