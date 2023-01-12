
// Overloading is not yet really supported...
// the simplifier thinks it's an impossible type!
let foo = _ as (_: (Int => Int) & (Bool => Bool))
//│ foo: (_: nothing,)

:ns
let foo = _ as (_: (Int => Int) & (Bool => Bool))
let foo = (_ as (_: (Int => Int) & (Bool => Bool)))._1
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

:e
foo(1) // returns int & bool, equivalent to nothing
succ / foo(1)
foo(true)
not / foo(true)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.30: 	foo(1) // returns int & bool, equivalent to nothing
//│ ║        	^^^^^^
//│ ╟── integer literal of type `1` is not an instance of type `bool`
//│ ║  l.30: 	foo(1) // returns int & bool, equivalent to nothing
//│ ║        	    ^
//│ ╟── but it flows into argument with expected type `bool`
//│ ║  l.30: 	foo(1) // returns int & bool, equivalent to nothing
//│ ║        	   ^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ╙──      	                          ^^^^
//│ res: bool | error | int
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.31: 	succ / foo(1)
//│ ║        	       ^^^^^^
//│ ╟── integer literal of type `1` is not an instance of type `bool`
//│ ║  l.31: 	succ / foo(1)
//│ ║        	           ^
//│ ╟── but it flows into argument with expected type `bool`
//│ ║  l.31: 	succ / foo(1)
//│ ║        	          ^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ╙──      	                          ^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.31: 	succ / foo(1)
//│ ║        	^^^^^^^^^^^^^
//│ ╟── reference of type `bool` is not an instance of type `int`
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ║        	                                  ^^^^
//│ ╟── but it flows into application with expected type `int`
//│ ║  l.31: 	succ / foo(1)
//│ ╙──      	       ^^^^^^
//│ res: error | int
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.32: 	foo(true)
//│ ║        	^^^^^^^^^
//│ ╟── reference of type `true` is not an instance of type `int`
//│ ║  l.32: 	foo(true)
//│ ║        	    ^^^^
//│ ╟── but it flows into argument with expected type `int`
//│ ║  l.32: 	foo(true)
//│ ║        	   ^^^^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ╙──      	           ^^^
//│ res: bool | error | int
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.33: 	not / foo(true)
//│ ║        	      ^^^^^^^^^
//│ ╟── reference of type `true` is not an instance of type `int`
//│ ║  l.33: 	not / foo(true)
//│ ║        	          ^^^^
//│ ╟── but it flows into argument with expected type `int`
//│ ║  l.33: 	not / foo(true)
//│ ║        	         ^^^^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ╙──      	           ^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.33: 	not / foo(true)
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── reference of type `int` is not an instance of type `bool`
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ║        	                  ^^^
//│ ╟── but it flows into application with expected type `bool`
//│ ║  l.33: 	not / foo(true)
//│ ╙──      	      ^^^^^^^^^
//│ res: bool | error

:e
not / foo(1)
foo(1) as Nothing
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.106: 	not / foo(1)
//│ ║         	      ^^^^^^
//│ ╟── integer literal of type `1` is not an instance of type `bool`
//│ ║  l.106: 	not / foo(1)
//│ ║         	          ^
//│ ╟── but it flows into argument with expected type `bool`
//│ ║  l.106: 	not / foo(1)
//│ ║         	         ^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ╙──      	                          ^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.106: 	not / foo(1)
//│ ║         	^^^^^^^^^^^^
//│ ╟── reference of type `int` is not an instance of type `bool`
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ║        	                  ^^^
//│ ╟── but it flows into application with expected type `bool`
//│ ║  l.106: 	not / foo(1)
//│ ╙──       	      ^^^^^^
//│ res: bool | error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.107: 	foo(1) as Nothing
//│ ║         	^^^^^^
//│ ╟── integer literal of type `1` is not an instance of type `bool`
//│ ║  l.107: 	foo(1) as Nothing
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `bool`
//│ ║  l.107: 	foo(1) as Nothing
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ╙──      	                          ^^^^
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.107: 	foo(1) as Nothing
//│ ║         	^^^^^^^^^^^^^^^^^
//│ ╟── reference of type `int` does not match type `nothing`
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ║        	                  ^^^
//│ ╟── but it flows into application with expected type `nothing`
//│ ║  l.107: 	foo(1) as Nothing
//│ ║         	^^^^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.107: 	foo(1) as Nothing
//│ ╙──       	          ^^^^^^^
//│ res: nothing

:e
foo as Nothing
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.157: 	foo as Nothing
//│ ║         	^^^^^^^^^^^^^^
//│ ╟── type intersection of type `int -> int & bool -> bool` does not match type `nothing`
//│ ║  l.26: 	let foo = (Int => Int) & (Bool => Bool)
//│ ║        	          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── but it flows into reference with expected type `nothing`
//│ ║  l.157: 	foo as Nothing
//│ ║         	^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.157: 	foo as Nothing
//│ ╙──       	       ^^^^^^^
//│ res: nothing

:e
let oops = (&)
//│ ╔══[ERROR] Illegal use of reserved operator: &
//│ ║  l.173: 	let oops = (&)
//│ ╙──       	           ^^^
//│ ╔══[ERROR] identifier not found: &
//│ ║  l.173: 	let oops = (&)
//│ ╙──       	           ^^^
//│ oops: error

