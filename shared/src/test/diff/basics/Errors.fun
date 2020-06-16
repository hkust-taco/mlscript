:ShowRelativeLineNums

let a = succ
//│ a: int -> int

let b = a 1
//│ b: int


// identifier not found

:e
c
id c
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
//│ ║  l.+1: 	c
//│ ╙──      	^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.+2: 	id c
//│ ╙──      	   ^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.+4: 	log / c + 1
//│ ╙──      	      ^
//│ ╔══[ERROR] identifier not found: abc
//│ ║  l.+5: 	log / abc + 1
//│ ╙──      	      ^^^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.+6: 	c + 1
//│ ╙──      	^
//│ ╔══[ERROR] identifier not found: abc
//│ ║  l.+7: 	abc + 1
//│ ╙──      	^^^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.+8: 	1 + c
//│ ╙──      	    ^
//│ ╔══[ERROR] identifier not found: c
//│ ║  l.+9: 	let d = c + 1
//│ ╙──      	        ^
//│ ╔══[ERROR] identifier not found: abc
//│ ║  l.+10: 	let d = 1 + abc + 1 + 1
//│ ╙──       	            ^^^
//│ res: error
//│ res: error
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
//│ res: error
//│ res: error
//│ oops: int | error
//│ res: error | int
//│ res: int | error
//│ res: int | error
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
//│ res: error
//│ res: int | error

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
//│ ╟── but it flows into variable reference of expected type `2 -> ?a`
//│ ║  l.+11: 	  f 2
//│ ╙──       	  ^
//│ res: unit
//│ res: error
//│ res: unit
//│ res: unit

:w
log
  succ 1
  2
//│ ╔══[WARNING] Expression in statement position should have type `unit`.
//│ ╟── Use the `discard` function to discard non-unit values, making the intent clearer.
//│ ╟── Type mismatch in function application:
//│ ║  l.+2: 	  succ 1
//│ ║        	  ^^^^^^
//│ ╙── expression of type `int` does not match type `unit`
//│ res: unit

:e
succ ((((false))))
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	succ ((((false))))
//│ ║        	^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+1: 	succ ((((false))))
//│ ║        	         ^^^^^
//│ ╟── but it flows into argument of expected type `int`
//│ ║  l.+1: 	succ ((((false))))
//│ ╙──      	     ^^^^^^^^^^^^^
//│ res: int | error

:e
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
//│ ╟── but it flows into argument of expected type `bool`
//│ ║  l.+1: 	let rec f = n => if n then 0 else f (miss + 1)
//│ ║        	                                    ^^^^^^^^^^
//│ ╟── Note: constraint arises from argument:
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
//│ ╟── but it flows into field selection of expected type `1 -> ?a`
//│ ║  l.+4: 	{a: 1}.a 1
//│ ╙──      	      ^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.+5: 	1 + {a: true}.a
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+5: 	1 + {a: true}.a
//│ ║        	        ^^^^
//│ ╟── but it flows into field selection of expected type `int`
//│ ║  l.+5: 	1 + {a: true}.a
//│ ╙──      	             ^^
//│ ╔══[ERROR] Type mismatch in operator application:
//│ ║  l.+6: 	{a: true}.a + 1
//│ ║        	         ^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+6: 	{a: true}.a + 1
//│ ║        	    ^^^^
//│ ╟── but it flows into field selection of expected type `int`
//│ ║  l.+6: 	{a: true}.a + 1
//│ ╙──      	         ^^
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
//│ res: error
//│ res: error
//│ res: error
//│ res: error
//│ res: int | error
//│ res: error | int
//│ res: int | error
//│ res: error

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
//│ ║  l.336: 	  x.prop
//│ ╙──       	   ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	f { prap: 1 }
//│ ║        	^^^^^^^^^^^^^
//│ ╟── expression of type `{prap: 1}` does not have field 'prop'
//│ ║  l.+2: 	f { prap: 1 }
//│ ║        	  ^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.336: 	  x.prop
//│ ╙──       	   ^^^^^
//│ res: error
//│ res: error

:e
f { prop: false }
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	f { prop: false }
//│ ║        	^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+1: 	f { prop: false }
//│ ║        	          ^^^^^
//│ ╟── but it flows into tuple expression of expected type `{prop: ?a & int}`
//│ ║  l.+1: 	f { prop: false }
//│ ║        	  ^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.335: 	  log / succ x.prop
//│ ╙──       	             ^^^^^^
//│ res: bool | error

:e
let arg = 0
f arg
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	f arg
//│ ║        	^^^^^
//│ ╟── expression of type `0` does not have field 'prop'
//│ ║  l.+1: 	let arg = 0
//│ ║        	          ^
//│ ╟── but it flows into variable reference of expected type `{prop: ?a}`
//│ ║  l.+2: 	f arg
//│ ║        	  ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.336: 	  x.prop
//│ ╙──       	   ^^^^^
//│ arg: 0
//│ res: error

:e
let arg = {prop: not true}
f arg
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	f arg
//│ ║        	^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+1: 	let arg = {prop: not true}
//│ ║        	                 ^^^^^^^^
//│ ╟── but it flows into variable reference of expected type `{prop: ?a & int}`
//│ ║  l.+2: 	f arg
//│ ║        	  ^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.335: 	  log / succ x.prop
//│ ╙──       	             ^^^^^^
//│ arg: {prop: bool}
//│ res: bool | error


let g = y =>
  f { prop: y.fld }
g { fld: 42 }
//│ g: {fld: 'a & int} -> 'a
//│ res: 42

:e
g 1
g { fld: false }
g { fld: { oops: 1 } }
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	g 1
//│ ║        	^^^
//│ ╟── expression of type `1` does not have field 'fld'
//│ ║  l.+1: 	g 1
//│ ║        	  ^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.420: 	  f { prop: y.fld }
//│ ╙──       	             ^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	g { fld: false }
//│ ║        	^^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+2: 	g { fld: false }
//│ ║        	         ^^^^^
//│ ╟── but it flows into tuple expression of expected type `{fld: ?a & int}`
//│ ║  l.+2: 	g { fld: false }
//│ ║        	  ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.335: 	  log / succ x.prop
//│ ║         	             ^^^^^^
//│ ╟── from field selection:
//│ ║  l.420: 	  f { prop: y.fld }
//│ ╙──       	             ^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+3: 	g { fld: { oops: 1 } }
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `{oops: 1}` does not match type `int`
//│ ║  l.+3: 	g { fld: { oops: 1 } }
//│ ║        	         ^^^^^^^^^^^
//│ ╟── but it flows into tuple expression of expected type `{fld: ?a & int}`
//│ ║  l.+3: 	g { fld: { oops: 1 } }
//│ ║        	  ^^^^^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.335: 	  log / succ x.prop
//│ ║         	             ^^^^^^
//│ ╟── from field selection:
//│ ║  l.420: 	  f { prop: y.fld }
//│ ╙──       	             ^^^^
//│ res: error
//│ res: bool | error
//│ res: error | {oops: 1}

:e
let arg1 = {fld: not true}
let arg2 = {fld: arg}
f arg1
f arg2
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+3: 	f arg1
//│ ║        	^^^^^^
//│ ╟── expression of type `{fld: ?a | bool}` does not have field 'prop'
//│ ║  l.+1: 	let arg1 = {fld: not true}
//│ ║        	           ^^^^^^^^^^^^^^^
//│ ╟── but it flows into variable reference of expected type `{prop: ?b}`
//│ ║  l.+3: 	f arg1
//│ ║        	  ^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.336: 	  x.prop
//│ ╙──       	   ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+4: 	f arg2
//│ ║        	^^^^^^
//│ ╟── expression of type `{fld: {prop: ?a | bool}}` does not have field 'prop'
//│ ║  l.+2: 	let arg2 = {fld: arg}
//│ ║        	           ^^^^^^^^^^
//│ ╟── but it flows into variable reference of expected type `{prop: ?b}`
//│ ║  l.+4: 	f arg2
//│ ║        	  ^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.336: 	  x.prop
//│ ╙──       	   ^^^^^
//│ arg1: {fld: bool}
//│ arg2: {fld: {prop: bool}}
//│ res: error
//│ res: error

let h = y =>
  succ / f y
succ / h { prop: 42 }
//│ h: {prop: int} -> int
//│ res: int

:e
h arg2
h arg
h / 42
x => h / succ x
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	h arg2
//│ ║        	^^^^^^
//│ ╟── expression of type `{fld: {prop: ?a | bool}}` does not have field 'prop'
//│ ║  l.474: 	let arg2 = {fld: arg}
//│ ║         	           ^^^^^^^^^^
//│ ╟── but it flows into variable reference of expected type `{prop: ?b & int}`
//│ ║  l.+1: 	h arg2
//│ ║        	  ^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.335: 	  log / succ x.prop
//│ ║         	              ^^^^^
//│ ╟── from argument:
//│ ║  l.507: 	  succ / f y
//│ ╙──       	           ^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	h arg
//│ ║        	^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.401: 	let arg = {prop: not true}
//│ ║         	                 ^^^^^^^^
//│ ╟── but it flows into variable reference of expected type `{prop: ?a & int}`
//│ ║  l.+2: 	h arg
//│ ║        	  ^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.335: 	  log / succ x.prop
//│ ║         	             ^^^^^^
//│ ╟── from argument:
//│ ║  l.507: 	  succ / f y
//│ ╙──       	           ^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+3: 	h / 42
//│ ║        	^^^^^^
//│ ╟── expression of type `42` does not have field 'prop'
//│ ║  l.+3: 	h / 42
//│ ║        	    ^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.335: 	  log / succ x.prop
//│ ║         	              ^^^^^
//│ ╟── from argument:
//│ ║  l.507: 	  succ / f y
//│ ╙──       	           ^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+4: 	x => h / succ x
//│ ║        	     ^^^^^^^^^^
//│ ╟── expression of type `int` does not have field 'prop'
//│ ║  l.+4: 	x => h / succ x
//│ ║        	         ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.335: 	  log / succ x.prop
//│ ║         	              ^^^^^
//│ ╟── from argument:
//│ ║  l.507: 	  succ / f y
//│ ╙──       	           ^
//│ res: int | error
//│ res: int | error
//│ res: int | error
//│ res: int -> int | error

:e
let mkArg2 = a => {prop: succ a}
h / mkArg2 false
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	h / mkArg2 false
//│ ║        	    ^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+2: 	h / mkArg2 false
//│ ║        	           ^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.+1: 	let mkArg2 = a => {prop: succ a}
//│ ╙──      	                              ^
//│ mkArg2: int -> {prop: int}
//│ res: int

let i = y =>
  succ / f y.fld
//│ i: {fld: {prop: int}} -> int

:e
i arg2
i arg
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	i arg2
//│ ║        	^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.401: 	let arg = {prop: not true}
//│ ║         	                 ^^^^^^^^
//│ ╟── but it flows into variable reference of expected type `{fld: ?a & {prop: ?b & int}}`
//│ ║  l.+1: 	i arg2
//│ ║        	  ^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.335: 	  log / succ x.prop
//│ ║         	             ^^^^^^
//│ ╟── from argument:
//│ ║  l.592: 	  succ / f y.fld
//│ ╙──       	           ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	i arg
//│ ║        	^^^^^
//│ ╟── expression of type `{prop: ?a | bool}` does not have field 'fld'
//│ ║  l.401: 	let arg = {prop: not true}
//│ ║         	          ^^^^^^^^^^^^^^^^
//│ ╟── but it flows into variable reference of expected type `{fld: ?b & {prop: ?c & int}}`
//│ ║  l.+2: 	i arg
//│ ║        	  ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.592: 	  succ / f y.fld
//│ ╙──       	            ^^^^
//│ res: int | error
//│ res: int | error


let mkArg = a => {prop: a}
h / mkArg 1
i { fld: mkArg 1 }
//│ mkArg: 'a -> {prop: 'a}
//│ res: int
//│ res: int

:e
g { fld: mkArg 1 } // TODO multi-step flow message?
h / mkArg false
i { fld: mkArg false }
i / mkArg 1
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+1: 	g { fld: mkArg 1 } // TODO multi-step flow message?
//│ ║        	^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `{prop: ?a | 1}` does not match type `int`
//│ ║  l.629: 	let mkArg = a => {prop: a}
//│ ║         	                 ^^^^^^^^^
//│ ╟── but it flows into tuple expression of expected type `{fld: ?b & int}`
//│ ║  l.+1: 	g { fld: mkArg 1 } // TODO multi-step flow message?
//│ ║        	  ^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.335: 	  log / succ x.prop
//│ ║         	             ^^^^^^
//│ ╟── from field selection:
//│ ║  l.420: 	  f { prop: y.fld }
//│ ╙──       	             ^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+2: 	h / mkArg false
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+2: 	h / mkArg false
//│ ║        	          ^^^^^
//│ ╟── but it flows into function application of expected type `{prop: ?a & int}`
//│ ║  l.+2: 	h / mkArg false
//│ ║        	    ^^^^^^^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.335: 	  log / succ x.prop
//│ ║         	             ^^^^^^
//│ ╟── from argument:
//│ ║  l.507: 	  succ / f y
//│ ╙──       	           ^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+3: 	i { fld: mkArg false }
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.+3: 	i { fld: mkArg false }
//│ ║        	               ^^^^^
//│ ╟── but it flows into tuple expression of expected type `{fld: ?a & {prop: ?b & int}}`
//│ ║  l.+3: 	i { fld: mkArg false }
//│ ║        	  ^^^^^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.335: 	  log / succ x.prop
//│ ║         	             ^^^^^^
//│ ╟── from argument:
//│ ║  l.592: 	  succ / f y.fld
//│ ╙──       	           ^^^^^
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.+4: 	i / mkArg 1
//│ ║        	^^^^^^^^^^^
//│ ╟── expression of type `{prop: ?a | 1}` does not have field 'fld'
//│ ║  l.629: 	let mkArg = a => {prop: a}
//│ ║         	                 ^^^^^^^^^
//│ ╟── but it flows into function application of expected type `{fld: ?b & {prop: ?c & int}}`
//│ ║  l.+4: 	i / mkArg 1
//│ ║        	    ^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.592: 	  succ / f y.fld
//│ ╙──       	            ^^^^
//│ res: error | {prop: 1}
//│ res: int | error
//│ res: int | error
//│ res: int | error



// parse error

:pe
foo
ba)r
baz
//│ /!\ Parse error: Expected end-of-input:2:3, found ")r\nbaz" at l.709:3: ba)r
