
let a = succ
/// a: int -> int

let b = a 1
/// b: int


// identifier not found

:e
log 1
log / c + 1
log / abc + 1
c + 1
abc + 1
1 + c
let d = c + 1
let d = 1 + abc + 1 + 1
d + 1
/// /!\ Type error: identifier not found: c
/// l.13: 	log / c + 1
///       	      ^
/// /!\ Type error: identifier not found: abc
/// l.14: 	log / abc + 1
///       	      ^^^
/// /!\ Type error: identifier not found: c
/// l.15: 	c + 1
///       	^
/// /!\ Type error: identifier not found: abc
/// l.16: 	abc + 1
///       	^^^
/// /!\ Type error: identifier not found: c
/// l.17: 	1 + c
///       	    ^
/// /!\ Type error: identifier not found: c
/// l.18: 	let d = c + 1
///       	        ^
/// /!\ Type error: identifier not found: abc
/// l.19: 	let d = 1 + abc + 1 + 1
///       	            ^^^
/// res: unit
/// res: unit
/// res: unit
/// res: int
/// res: int
/// res: int
/// d: int
/// d: int
/// res: int


// cannot constrain

:e
1 2 3
a b c
let oops = succ false
false + 1
1 + false
true + false
log / false + 1
/// /!\ Type error: cannot constrain int <: int -> 'a
/// l.56: 	1 2 3
///       	^^^
/// /!\ Type error: identifier not found: c
/// l.57: 	a b c
///       	    ^
/// /!\ Type error: cannot constrain int <: 'a -> 'b
/// l.57: 	a b c
///       	^^^^^
/// /!\ Type error: cannot constrain bool <: int
/// l.58: 	let oops = succ false
///       	           ^^^^^^^^^^
/// /!\ Type error: cannot constrain bool <: int
/// l.59: 	false + 1
///       	^^^^^^^
/// /!\ Type error: cannot constrain bool <: int
/// l.60: 	1 + false
///       	^^^^^^^^^
/// /!\ Type error: cannot constrain bool <: int
/// l.61: 	true + false
///       	^^^^^^
/// /!\ Type error: cannot constrain bool <: int
/// l.61: 	true + false
///       	^^^^^^^^^^^^
/// /!\ Type error: cannot constrain bool <: int
/// l.62: 	log / false + 1
///       	      ^^^^^^^
/// res: ⊥
/// res: ⊥
/// oops: int
/// res: int
/// res: int
/// res: int
/// res: unit

:e
succ succ
  1
(
  succ
) false
/// /!\ Type error: cannot constrain int -> int <: int
/// l.99: 	succ succ
///       	^^^^^^^^^
/// /!\ Type error: cannot constrain int <: int -> 'a
/// l.99: 	succ succ
///       	^^^^^^^^^
/// l.100: 	  1
///        	^^^
/// /!\ Type error: cannot constrain bool <: int
/// l.101: 	(
///        	^
/// l.102: 	  succ
///        	^^^^^^
/// l.103: 	) false
///        	^^^^^^^
/// res: ⊥
/// res: int

:e
:w
log
  1
    2
log 1
  2
log
  1
  2
/// /!\ Type error: cannot constrain int <: int -> 'a
/// l.125: 	  1
///        	  ^
/// l.126: 	    2
///        	^^^^^
/// /!\ Type error: cannot constrain unit <: int -> 'a
/// l.127: 	log 1
///        	^^^^^
/// l.128: 	  2
///        	^^^
/// /!\ Warning: Pure expression does nothing in statement position.
/// l.130: 	  1
///        	  ^
/// res: unit
/// res: ⊥
/// res: unit


// missing field, cannot constrain

:e
1.u
{}.u
{a: 1}.u
{a: 1}.a 1
1 + {a: true}.a
{a: true}.a + 1
succ {a: 1}
{a: 1} succ
/// /!\ Type error: cannot constrain int <: {u: 'a}
/// l.153: 	1.u
///        	 ^^
/// /!\ Type error: missing field: u in {}
/// l.154: 	{}.u
///        	  ^^
/// /!\ Type error: missing field: u in {a: int}
/// l.155: 	{a: 1}.u
///        	      ^^
/// /!\ Type error: cannot constrain int <: int -> 'a
/// l.156: 	{a: 1}.a 1
///        	      ^^^^
/// /!\ Type error: cannot constrain bool <: int
/// l.157: 	1 + {a: true}.a
///        	^^^^^^^^^^^^^^^
/// /!\ Type error: cannot constrain bool <: int
/// l.158: 	{a: true}.a + 1
///        	         ^^^^
/// /!\ Type error: cannot constrain {a: int} <: int
/// l.159: 	succ {a: 1}
///        	^^^^^^^^^^^
/// /!\ Type error: cannot constrain {a: int} <: (int -> int) -> 'a
/// l.160: 	{a: 1} succ
///        	^^^^^^^^^^^
/// res: ⊥
/// res: ⊥
/// res: ⊥
/// res: ⊥
/// res: int
/// res: int
/// res: int
/// res: ⊥

let f = x =>
  log / succ x.prop
  x.prop
f { prop: 42 }
/// f: {prop: 'a ∧ int} -> 'a
/// res: int

// FIXME 'prop' requirement is added twice
:e
f 42
f { prap: false }
f { prop: false }
/// /!\ Type error: cannot constrain int <: {prop: 'a}
/// l.203: 	f 42
///        	^^^^
/// /!\ Type error: cannot constrain int <: {prop: 'a}
/// l.203: 	f 42
///        	^^^^
/// /!\ Type error: missing field: prop in {prap: bool}
/// l.204: 	f { prap: false }
///        	^^^^^^^^^^^^^^^^^
/// /!\ Type error: missing field: prop in {prap: bool}
/// l.204: 	f { prap: false }
///        	^^^^^^^^^^^^^^^^^
/// /!\ Type error: cannot constrain bool <: int
/// l.205: 	f { prop: false }
///        	^^^^^^^^^^^^^^^^^
/// res: ⊥
/// res: ⊥
/// res: bool


// parse error

:pe
foo
ba)r
baz
/// /!\ Parse error: Expected end-of-input:2:3, found ")r\nbaz" at l.230:3: ba)r
