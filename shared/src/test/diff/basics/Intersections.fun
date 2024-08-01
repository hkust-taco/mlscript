
// Overloading is not yet really supported...
// the simplifier thinks it's an impossible type!
let foo = _ as (_: (Int => Int) & (Bool => Bool))
//│ foo: (_: nothing,)

:ns
let foo = _ as (_: (Int => Int) & (Bool => Bool))
let foo = (_ as (_: (Int => Int) & (Bool => Bool))).0
//│ foo: forall 'a. (_: 'a,)
//│   where
//│     'a <: int -> int & bool -> bool
//│ foo: forall 'a. 'a

foo(1)
//│ res: nothing

:ns
foo(1)
//│ res: 'a

succ / foo(1)
//│ res: int

// Intersection-based overloading is not actually supported... a value of this type is impossible to provide:
let foo = (Int => Int) & (Bool => Bool)
//│ foo: int -> int & bool -> bool

// used to return int & bool, equivalent to nothing
// or approximated as int | bool in MLscript
// overloaded function foo can now be used as either int -> int or bool -> bool
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
foo(1) as Nothing
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.39: 	not / foo(1)
//│ ║        	^^^^^^^^^^^^
//│ ╟── application of type `int` is not an instance of type `bool`
//│ ║  l.39: 	not / foo(1)
//│ ╙──      	      ^^^^^^
//│ res: bool | error
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.40: 	foo(1) as Nothing
//│ ║        	^^^^^^^^^^^^^^^^^
//│ ╟── application of type `int` does not match type `nothing`
//│ ║  l.40: 	foo(1) as Nothing
//│ ║        	^^^^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.40: 	foo(1) as Nothing
//│ ╙──      	          ^^^^^^^
//│ res: nothing

:e
foo as Nothing
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.60: 	foo as Nothing
//│ ║        	^^^^^^^^^^^^^^
//│ ╟── type intersection of type `int -> int & bool -> bool` does not match type `nothing`
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ║        	          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── but it flows into reference with expected type `nothing`
//│ ║  l.60: 	foo as Nothing
//│ ║        	^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.60: 	foo as Nothing
//│ ╙──      	       ^^^^^^^
//│ res: nothing

:e
let oops = (&)
//│ ╔══[ERROR] Illegal use of reserved operator: &
//│ ║  l.76: 	let oops = (&)
//│ ╙──      	           ^^^
//│ ╔══[ERROR] identifier not found: &
//│ ║  l.76: 	let oops = (&)
//│ ╙──      	           ^^^
//│ oops: error

