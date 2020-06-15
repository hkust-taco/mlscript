:ShowRelativeLineNums

let a = succ
//│ a: int -> int

let b = a 1
//│ b: int


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
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.+2: 	log / c + 1
//│ ╙──      	      ^
//│ ╔══[ERROR] identifier not found: abc
//│ ║  l.+3: 	log / abc + 1
//│ ╙──      	      ^^^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.+4: 	c + 1
//│ ╙──      	^
//│ ╔══[ERROR] identifier not found: abc
//│ ║  l.+5: 	abc + 1
//│ ╙──      	^^^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.+6: 	1 + c
//│ ╙──      	    ^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.+7: 	let d = c + 1
//│ ╙──      	        ^
//│ ╔══[ERROR] identifier not found: abc
//│ ║  l.+8: 	let d = 1 + abc + 1 + 1
//│ ╙──      	            ^^^
//│ res: unit
//│ res: unit
//│ res: unit
//│ res: int
//│ res: int
//│ res: int
//│ d: int
//│ d: int
//│ res: int


// cannot constrain

:e
1 2 3
a b c
let oops = succ false
false + 1
1 + false
true + false
log / false + 1
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	1 2 3
//│ ║        	^^^
//│ ╟── expression of type `1` is not a function
//│ ║  l.+1: 	1 2 3
//│ ╙──      	^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.+2: 	a b c
//│ ╙──      	    ^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	a b c
//│ ║        	^^^^^
//│ ╟── expression of type `int` is not a function
//│ ║  l.+2: 	a b c
//│ ╙──      	^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+3: 	let oops = succ false
//│ ║        	           ^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+3: 	let oops = succ false
//│ ╙──      	                ^^^^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.+4: 	false + 1
//│ ║        	^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+4: 	false + 1
//│ ╙──      	^^^^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.+5: 	1 + false
//│ ║        	^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+5: 	1 + false
//│ ╙──      	    ^^^^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.+6: 	true + false
//│ ║        	^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+6: 	true + false
//│ ╙──      	^^^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.+6: 	true + false
//│ ║        	^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+6: 	true + false
//│ ╙──      	       ^^^^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.+7: 	log / false + 1
//│ ║        	      ^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+7: 	log / false + 1
//│ ╙──      	      ^^^^^
//│ res: nothing
//│ res: nothing
//│ oops: int
//│ res: int
//│ res: int
//│ res: int
//│ res: unit

:e
succ succ
  1
(
  succ
) false
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	succ succ
//│ ║        	^^^^^^^^^
//│ ╟── expression of type `int -> int` does not match type `int`
//│ ║  l.+1: 	succ succ
//│ ╙──      	     ^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	succ succ
//│ ║        	^^^^^^^^^
//│ ║  l.+2: 	  1
//│ ║        	^^^
//│ ╟── expression of type `int` is not a function
//│ ║  l.+1: 	succ succ
//│ ╙──      	^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+3: 	(
//│ ║        	^
//│ ║  l.+4: 	  succ
//│ ║        	^^^^^^
//│ ║  l.+5: 	) false
//│ ║        	^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+5: 	) false
//│ ╙──      	  ^^^^^
//│ res: nothing
//│ res: int

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
log
  let f = 1
  f 2
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	  1
//│ ║        	  ^
//│ ║  l.+3: 	    2
//│ ║        	^^^^^
//│ ╟── expression of type `1` is not a function
//│ ║  l.+2: 	  1
//│ ╙──      	  ^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+4: 	log 1
//│ ║        	^^^^^
//│ ║  l.+5: 	  2
//│ ║        	^^^
//│ ╟── expression of type `unit` is not a function
//│ ║  l.+4: 	log 1
//│ ╙──      	^^^^^
//│ ╔══[WARNING] Pure expression does nothing in statement position.
//│ ║  l.+7: 	  1
//│ ╙──      	  ^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+11: 	  f 2
//│ ║         	  ^^^
//│ ╟── expression of type `1` is not a function
//│ ║  l.+10: 	  let f = 1
//│ ║         	          ^
//│ ╟── but it flows into variable reference
//│ ║  l.+11: 	  f 2
//│ ║         	  ^
//│ ╙── which is not a function
//│ res: unit
//│ res: nothing
//│ res: unit
//│ res: unit

:e
log
  succ 1
  2
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	  succ 1
//│ ║        	  ^^^^^^
//│ ╟── expression of type `int` does not match type `unit`
//│ ║  l.+2: 	  succ 1
//│ ╙──      	  ^^^^^^
//│ res: unit

:ex // TODO better error
let rec f = n => if n then 0 else f (miss + 1)
//│ ╔══[ERROR] identifier not found: miss
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ╙──      	                                     ^^^^
//│ ╔══[ERROR] Type mismatch in binding of lambda expression:
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `int` does not match type `bool`
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	                                     ^^^^^^^^
//│ ╟── but it flows into argument of type `?a | int`
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	                                    ^^^^^^^^^^
//│ ╟── which does not match type `bool`
//│ ╟── [info] Additional Explanations below:
//│ ╟── [info] While constraining argument of type ?a | int
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	                                    ^^^^^^^^^^
//│ ╟── [info] to be a subtype of parameter type ?b & bool
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	            ^
//│ ╟── [info] While constraining argument of type ?a | int
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	                                    ^^^^^^^^^^
//│ ╟── [info] to be a subtype of function application type bool
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	                    ^
//│ ╟── [info] While constraining operator application of type ?a | int
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	                                     ^^^^^^^^
//│ ╟── [info] to be a subtype of function application type bool
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	                    ^
//│ ╟── [info] While constraining operator application of type int
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	                                     ^^^^^^^^
//│ ╟── [info] to be a subtype of function application type bool
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	                    ^
//│ ╟── [info] While constraining expression of type int
//│ ╟── [info] to be a subtype of function application type bool
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ╙──      	                    ^
//│ f: bool -> 0


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
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.+1: 	1.u
//│ ║        	 ^^
//│ ╟── expression of type `1` does not have field 'u'
//│ ║  l.+1: 	1.u
//│ ╙──      	^
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.+2: 	{}.u
//│ ║        	  ^^
//│ ╟── expression of type `{}` does not have field 'u'
//│ ║  l.+2: 	{}.u
//│ ╙──      	^^
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.+3: 	{a: 1}.u
//│ ║        	      ^^
//│ ╟── expression of type `{a: 1}` does not have field 'u'
//│ ║  l.+3: 	{a: 1}.u
//│ ╙──      	^^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+4: 	{a: 1}.a 1
//│ ║        	      ^^^^
//│ ╟── expression of type `1` is not a function
//│ ║  l.+4: 	{a: 1}.a 1
//│ ║        	    ^
//│ ╟── but it flows into field selection
//│ ║  l.+4: 	{a: 1}.a 1
//│ ║        	      ^^
//│ ╙── which is not a function
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.+5: 	1 + {a: true}.a
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+5: 	1 + {a: true}.a
//│ ║        	        ^^^^
//│ ╟── but it flows into field selection
//│ ║  l.+5: 	1 + {a: true}.a
//│ ║        	             ^^
//│ ╙── which does not match type `int`
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.+6: 	{a: true}.a + 1
//│ ║        	         ^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+6: 	{a: true}.a + 1
//│ ║        	    ^^^^
//│ ╟── but it flows into field selection
//│ ║  l.+6: 	{a: true}.a + 1
//│ ║        	         ^^
//│ ╙── which does not match type `int`
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+7: 	succ {a: 1}
//│ ║        	^^^^^^^^^^^
//│ ╟── expression of type `{a: 1}` does not match type `int`
//│ ║  l.+7: 	succ {a: 1}
//│ ╙──      	     ^^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+8: 	{a: 1} succ
//│ ║        	^^^^^^^^^^^
//│ ╟── expression of type `{a: 1}` is not a function
//│ ║  l.+8: 	{a: 1} succ
//│ ╙──      	^^^^^^
//│ res: nothing
//│ res: nothing
//│ res: nothing
//│ res: nothing
//│ res: int
//│ res: int
//│ res: int
//│ res: nothing

let f = x =>
  log / succ x.prop
  x.prop
f { prop: 42 }
//│ f: {prop: 'a & int} -> 'a
//│ res: 42

// FIXME 'prop' requirement is added twice
:e
f 42
f { prap: 1 }
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	f 42
//│ ║        	^^^^
//│ ╟── expression of type `42` does not have field 'prop'
//│ ║  l.+1: 	f 42
//│ ║        	  ^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.344: 	  x.prop
//│ ╙──       	   ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	f 42
//│ ║        	^^^^
//│ ╟── expression of type `42` does not have field 'prop'
//│ ║  l.+1: 	f 42
//│ ║        	  ^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.343: 	  log / succ x.prop
//│ ╙──       	              ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	f { prap: 1 }
//│ ║        	^^^^^^^^^^^^^
//│ ╟── expression of type `{prap: 1}` does not have field 'prop'
//│ ║  l.+2: 	f { prap: 1 }
//│ ║        	  ^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.344: 	  x.prop
//│ ╙──       	   ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	f { prap: 1 }
//│ ║        	^^^^^^^^^^^^^
//│ ╟── expression of type `{prap: 1}` does not have field 'prop'
//│ ║  l.+2: 	f { prap: 1 }
//│ ║        	  ^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.343: 	  log / succ x.prop
//│ ╙──       	              ^^^^^
//│ res: nothing
//│ res: nothing

:e
f { prop: false }
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	f { prop: false }
//│ ║        	^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+1: 	f { prop: false }
//│ ║        	          ^^^^^
//│ ╟── but it flows into tuple expression of type `{prop: bool}`
//│ ║  l.+1: 	f { prop: false }
//│ ║        	  ^^^^^^^^^^^^^^^
//│ ╟── which does not match type `{prop: ?a & int}`
//│ ╟── Note: constraint arises from function application:
//│ ║  l.343: 	  log / succ x.prop
//│ ╙──       	        ^^^^^^^^^^^
//│ res: bool

:e
let arg = 0
f arg
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	f arg
//│ ║        	^^^^^
//│ ╟── expression of type `0` does not have field 'prop'
//│ ║  l.+1: 	let arg = 0
//│ ║        	          ^
//│ ╟── but it flows into variable reference
//│ ║  l.+2: 	f arg
//│ ║        	  ^^^
//│ ╟── which does not match type `{prop: ?a}`
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.344: 	  x.prop
//│ ╙──       	   ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	f arg
//│ ║        	^^^^^
//│ ╟── expression of type `0` does not have field 'prop'
//│ ║  l.+1: 	let arg = 0
//│ ║        	          ^
//│ ╟── but it flows into variable reference
//│ ║  l.+2: 	f arg
//│ ║        	  ^^^
//│ ╟── which does not match type `{prop: ?a & int}`
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.343: 	  log / succ x.prop
//│ ╙──       	              ^^^^^
//│ arg: 0
//│ res: nothing

:e
let arg = {prop: not true}
f arg
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	f arg
//│ ║        	^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+1: 	let arg = {prop: not true}
//│ ║        	                 ^^^^^^^^
//│ ╟── but it flows into variable reference of type `{prop: ?a | bool}`
//│ ║  l.+2: 	f arg
//│ ║        	  ^^^
//│ ╟── which does not match type `{prop: ?b & int}`
//│ ╟── Note: constraint arises from function application:
//│ ║  l.343: 	  log / succ x.prop
//│ ╙──       	        ^^^^^^^^^^^
//│ arg: {prop: bool}
//│ res: bool

// parse error

:pe
foo
ba)r
baz
//│ /!\ Parse error: Expected end-of-input:2:3, found ")r\nbaz" at l.464:3: ba)r
