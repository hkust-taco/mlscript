
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
//│ ║  l.13: 	log / c + 1
//│ ╙──      	      ^
//│ ╔══[ERROR] identifier not found: abc
//│ ║  l.14: 	log / abc + 1
//│ ╙──      	      ^^^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.15: 	c + 1
//│ ╙──      	^
//│ ╔══[ERROR] identifier not found: abc
//│ ║  l.16: 	abc + 1
//│ ╙──      	^^^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.17: 	1 + c
//│ ╙──      	    ^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.18: 	let d = c + 1
//│ ╙──      	        ^
//│ ╔══[ERROR] identifier not found: abc
//│ ║  l.19: 	let d = 1 + abc + 1 + 1
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
//│ ║  l.56: 	1 2 3
//│ ║        	^^^
//│ ╟── expression of type `1` is not a function
//│ ║  l.56: 	1 2 3
//│ ╙──      	^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.57: 	a b c
//│ ╙──      	    ^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.57: 	a b c
//│ ║        	^^^^^
//│ ╟── expression of type `int` is not a function
//│ ║  l.57: 	a b c
//│ ╙──      	^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.58: 	let oops = succ false
//│ ║        	           ^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.58: 	let oops = succ false
//│ ╙──      	                ^^^^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.59: 	false + 1
//│ ║        	^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.59: 	false + 1
//│ ╙──      	^^^^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.60: 	1 + false
//│ ║        	^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.60: 	1 + false
//│ ╙──      	    ^^^^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.61: 	true + false
//│ ║        	^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.61: 	true + false
//│ ╙──      	^^^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.61: 	true + false
//│ ║        	^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.61: 	true + false
//│ ╙──      	       ^^^^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.62: 	log / false + 1
//│ ║        	      ^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.62: 	log / false + 1
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
//│ ║  l.123: 	succ succ
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `int -> int` does not match type `int`
//│ ║  l.123: 	succ succ
//│ ╙──       	     ^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.123: 	succ succ
//│ ║         	^^^^^^^^^
//│ ║  l.124: 	  1
//│ ║         	^^^
//│ ╟── expression of type `int` is not a function
//│ ║  l.123: 	succ succ
//│ ╙──       	^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.125: 	(
//│ ║         	^
//│ ║  l.126: 	  succ
//│ ║         	^^^^^^
//│ ║  l.127: 	) false
//│ ║         	^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.127: 	) false
//│ ╙──       	  ^^^^^
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
//│ ║  l.158: 	  1
//│ ║         	  ^
//│ ║  l.159: 	    2
//│ ║         	^^^^^
//│ ╟── expression of type `1` is not a function
//│ ║  l.158: 	  1
//│ ╙──       	  ^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.160: 	log 1
//│ ║         	^^^^^
//│ ║  l.161: 	  2
//│ ║         	^^^
//│ ╟── expression of type `unit` is not a function
//│ ║  l.160: 	log 1
//│ ╙──       	^^^^^
//│ ╔══[WARNING] Pure expression does nothing in statement position.
//│ ║  l.163: 	  1
//│ ╙──       	  ^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.167: 	  f 2
//│ ║         	  ^^^
//│ ╟── expression of type `1` is not a function
//│ ║  l.166: 	  let f = 1
//│ ║         	          ^
//│ ╟── but it flows into variable reference
//│ ║  l.167: 	  f 2
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
//│ ║  l.204: 	  succ 1
//│ ║         	  ^^^^^^
//│ ╟── expression of type `int` does not match type `unit`
//│ ║  l.204: 	  succ 1
//│ ╙──       	  ^^^^^^
//│ res: unit

:ex // TODO better error
let rec f = n => if n then 0 else f (miss + 1)
//│ ╔══[ERROR] identifier not found: miss
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ╙──       	                                     ^^^^
//│ ╔══[ERROR] Type mismatch in binding of lambda expression:
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `int` does not match type `bool`
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	                                     ^^^^^^^^
//│ ╟── but it flows into argument of type `?a | int`
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	                                    ^^^^^^^^^^
//│ ╟── which does not match type `bool`
//│ ╟── [info] Additional Explanations below:
//│ ╟── [info] While constraining argument of type ?a | int
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	                                    ^^^^^^^^^^
//│ ╟── [info] to be a subtype of parameter type ?b & bool
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	            ^
//│ ╟── [info] While constraining argument of type ?a | int
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	                                    ^^^^^^^^^^
//│ ╟── [info] to be a subtype of function application type bool
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	                    ^
//│ ╟── [info] While constraining operator application of type ?a | int
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	                                     ^^^^^^^^
//│ ╟── [info] to be a subtype of function application type bool
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	                    ^
//│ ╟── [info] While constraining operator application of type int
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	                                     ^^^^^^^^
//│ ╟── [info] to be a subtype of function application type bool
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║         	                    ^
//│ ╟── [info] While constraining expression of type int
//│ ╟── [info] to be a subtype of function application type bool
//│ ║  l.215: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ╙──       	                    ^
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
//│ ║  l.264: 	1.u
//│ ║         	 ^^
//│ ╟── expression of type `1` does not have field 'u'
//│ ║  l.264: 	1.u
//│ ╙──       	^
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.265: 	{}.u
//│ ║         	  ^^
//│ ╟── expression of type `{}` does not have field 'u'
//│ ║  l.265: 	{}.u
//│ ╙──       	^^
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.266: 	{a: 1}.u
//│ ║         	      ^^
//│ ╟── expression of type `{a: 1}` does not have field 'u'
//│ ║  l.266: 	{a: 1}.u
//│ ╙──       	^^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.267: 	{a: 1}.a 1
//│ ║         	      ^^^^
//│ ╟── expression of type `1` is not a function
//│ ║  l.267: 	{a: 1}.a 1
//│ ║         	    ^
//│ ╟── but it flows into field selection
//│ ║  l.267: 	{a: 1}.a 1
//│ ║         	      ^^
//│ ╙── which is not a function
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.268: 	1 + {a: true}.a
//│ ║         	^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.268: 	1 + {a: true}.a
//│ ║         	        ^^^^
//│ ╟── but it flows into field selection
//│ ║  l.268: 	1 + {a: true}.a
//│ ║         	             ^^
//│ ╙── which does not match type `int`
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.269: 	{a: true}.a + 1
//│ ║         	         ^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.269: 	{a: true}.a + 1
//│ ║         	    ^^^^
//│ ╟── but it flows into field selection
//│ ║  l.269: 	{a: true}.a + 1
//│ ║         	         ^^
//│ ╙── which does not match type `int`
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.270: 	succ {a: 1}
//│ ║         	^^^^^^^^^^^
//│ ╟── expression of type `{a: 1}` does not match type `int`
//│ ║  l.270: 	succ {a: 1}
//│ ╙──       	     ^^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.271: 	{a: 1} succ
//│ ║         	^^^^^^^^^^^
//│ ╟── expression of type `{a: 1}` is not a function
//│ ║  l.271: 	{a: 1} succ
//│ ╙──       	^^^^^^
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
//│ ║  l.350: 	f 42
//│ ║         	^^^^
//│ ╟── expression of type `42` does not have field 'prop'
//│ ║  l.350: 	f 42
//│ ║         	  ^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.343: 	  x.prop
//│ ╙──       	   ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.350: 	f 42
//│ ║         	^^^^
//│ ╟── expression of type `42` does not have field 'prop'
//│ ║  l.350: 	f 42
//│ ║         	  ^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.342: 	  log / succ x.prop
//│ ╙──       	              ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.351: 	f { prap: 1 }
//│ ║         	^^^^^^^^^^^^^
//│ ╟── expression of type `{prap: 1}` does not have field 'prop'
//│ ║  l.351: 	f { prap: 1 }
//│ ║         	  ^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.343: 	  x.prop
//│ ╙──       	   ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.351: 	f { prap: 1 }
//│ ║         	^^^^^^^^^^^^^
//│ ╟── expression of type `{prap: 1}` does not have field 'prop'
//│ ║  l.351: 	f { prap: 1 }
//│ ║         	  ^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.342: 	  log / succ x.prop
//│ ╙──       	              ^^^^^
//│ res: nothing
//│ res: nothing

:e
f { prop: false }
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.392: 	f { prop: false }
//│ ║         	^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.392: 	f { prop: false }
//│ ║         	          ^^^^^
//│ ╟── but it flows into tuple expression of type `{prop: bool}`
//│ ║  l.392: 	f { prop: false }
//│ ║         	  ^^^^^^^^^^^^^^^
//│ ╟── which does not match type `{prop: ?a & int}`
//│ ╟── Note: constraint arises from function application:
//│ ║  l.342: 	  log / succ x.prop
//│ ╙──       	        ^^^^^^^^^^^
//│ res: bool

:e
let arg = 0
f arg
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.410: 	f arg
//│ ║         	^^^^^
//│ ╟── expression of type `0` does not have field 'prop'
//│ ║  l.409: 	let arg = 0
//│ ║         	          ^
//│ ╟── but it flows into variable reference
//│ ║  l.410: 	f arg
//│ ║         	  ^^^
//│ ╟── which does not match type `{prop: ?a}`
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.343: 	  x.prop
//│ ╙──       	   ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.410: 	f arg
//│ ║         	^^^^^
//│ ╟── expression of type `0` does not have field 'prop'
//│ ║  l.409: 	let arg = 0
//│ ║         	          ^
//│ ╟── but it flows into variable reference
//│ ║  l.410: 	f arg
//│ ║         	  ^^^
//│ ╟── which does not match type `{prop: ?a & int}`
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.342: 	  log / succ x.prop
//│ ╙──       	              ^^^^^
//│ arg: 0
//│ res: nothing

:e
let arg = {prop: not true}
f arg
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.442: 	f arg
//│ ║         	^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.441: 	let arg = {prop: not true}
//│ ║         	                 ^^^^^^^^
//│ ╟── but it flows into variable reference of type `{prop: ?a | bool}`
//│ ║  l.442: 	f arg
//│ ║         	  ^^^
//│ ╟── which does not match type `{prop: ?b & int}`
//│ ╟── Note: constraint arises from function application:
//│ ║  l.342: 	  log / succ x.prop
//│ ╙──       	        ^^^^^^^^^^^
//│ arg: {prop: bool}
//│ res: bool

// parse error

:pe
foo
ba)r
baz
//│ /!\ Parse error: Expected end-of-input:2:3, found ")r\nbaz" at l.463:3: ba)r
