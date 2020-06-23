
// Overloading is not yet really supported...
// the simplifier thinks it's an impossible type!
let foo = _ as (_: (Int => Int) & (Bool => Bool))
//│ foo: (_: nothing,)

:ns
let foo = _ as (_: (Int => Int) & (Bool => Bool))
let foo = (_ as (_: (Int => Int) & (Bool => Bool)))._1
//│ foo: (_: 'a,)
//│ foo: 'a

foo(1)
//│ res: nothing

:ns
foo(1)
//│ res: 'a

succ / foo(1)
//│ res: int

// Q: why does this one work without :ns and not the one above?
// :ns
let foo = (Int => Int) & (Bool => Bool)
//│ foo: (int -> int) & (bool -> bool)

foo(1)
succ / foo(1)
foo(true)
not / foo(true)
//│ res: int
//│ res: int
//│ res: bool
//│ res: bool

:e
not / foo(1)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.38: 	not / foo(1)
//│ ║        	^^^^^^^^^^^^
//│ ╟── expression of type `int` does not match type `bool`
//│ ║  l.25: 	let foo = (Int => Int) & (Bool => Bool)
//│ ║        	                  ^^^
//│ ╟── but it flows into application with expected type `bool`
//│ ║  l.38: 	not / foo(1)
//│ ╙──      	      ^^^^^^
//│ res: bool | error

:e
let oops = (&)
//│ ╔══[ERROR] Illegal use of operator: &
//│ ║  l.51: 	let oops = (&)
//│ ╙──      	           ^^^
//│ ╔══[ERROR] identifier not found: &
//│ ║  l.51: 	let oops = (&)
//│ ╙──      	           ^^^
//│ oops: error

