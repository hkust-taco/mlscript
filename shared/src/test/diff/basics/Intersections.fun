
// Overloading is not yet really supported...
// the simplifier thinks it's an impossible type!
let foo = _ as (_: (Int => Int) & (Bool => Bool))
//│ foo: (_: nothing,)

:ns
let foo = _ as (_: (Int => Int) & (Bool => Bool))
let foo = (_ as (_: (Int => Int) & (Bool => Bool)))._1
//│ foo: (_: 'a,)
//│   where
//│     'a <: (int | bool) -> (int & bool)
//│ foo: 'a

foo(1)
//│ res: nothing

:ns
foo(1)
//│ res: 'a

succ / foo(1)
//│ res: int

// Intersection-based overloading is not actually supported... a value of this type is impossible to provide:
let foo = (Int => Int) & (Bool => Bool)
//│ foo: (bool | int) -> nothing

foo(1) // returns int & bool, equivalent to nothing
succ / foo(1)
foo(true)
not / foo(true)
//│ res: nothing
//│ res: int
//│ res: nothing
//│ res: bool

not / foo(1)
foo(1) as Nothing
//│ res: bool
//│ res: nothing

:e
foo as Nothing
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.44: 	foo as Nothing
//│ ║        	^^^^^^^^^^^^^^
//│ ╟── type intersection of type `(bool | int) -> nothing` does not match type `nothing`
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ║        	          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── but it flows into reference with expected type `nothing`
//│ ║  l.44: 	foo as Nothing
//│ ║        	^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.44: 	foo as Nothing
//│ ╙──      	       ^^^^^^^
//│ res: nothing





:e
let oops = (&)
//│ ╔══[ERROR] Illegal use of operator: &
//│ ║  l.64: 	let oops = (&)
//│ ╙──      	           ^^^
//│ ╔══[ERROR] identifier not found: &
//│ ║  l.64: 	let oops = (&)
//│ ╙──      	           ^^^
//│ oops: error



