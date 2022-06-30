
// * This `as` feature, as implemented, does not play well with cosntrained types arguments:

let f x =
  discard / x as { v: _ }
  v + 1
//│ f: {v: anything} -> int

// * Should be rejected:

f { v: true }
//│ res: int


// :NoConstrainnedTypes
:NoArgGen

let f x =
  discard / x as { v: (y) } // TODO accept plain `y`
  log / v
  log / y + 1
//│ f: {v: int} -> unit

let f x =
  discard / x as { v: _ }
  v + 1
//│ f: {v: int} -> int

let f x =
  let y = x.v
  log / y + 1
  log / y
//│ f: {v: int} -> unit

:e
f { v: true }
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.36: 	f { v: true }
//│ ║        	^^^^^^^^^^^^^
//│ ╟── reference of type `true` is not an instance of type `int`
//│ ║  l.36: 	f { v: true }
//│ ║        	       ^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.31: 	  log / y + 1
//│ ║        	        ^
//│ ╟── from field selection:
//│ ║  l.30: 	  let y = x.v
//│ ╙──      	           ^^
//│ res: error | unit

