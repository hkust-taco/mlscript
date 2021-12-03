
:v // Note: removing this will mean not showing parameter provs in downstream errors
let f = x =>
  log / succ x.prop
  x.prop
let h = y =>
  succ / f y
let mkArg = a => {prop: a}
//│ f: {prop: int & 'a} -> 'a
//│ h: {prop: int} -> int
//│ mkArg: 'a -> {prop: 'a}

:v
:e
h / mkArg false
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.15: 	h / mkArg false
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── expression of type `false` does not match type `int`
//│ ║  l.15: 	h / mkArg false
//│ ║        	          ^^^^^
//│ ╟── but it flows into application with expected type `{prop: ?a}`
//│ ║  l.15: 	h / mkArg false
//│ ║        	    ^^^^^^^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.4: 	  log / succ x.prop
//│ ║       	             ^^^^^^
//│ ╟── from field selection:
//│ ║  l.4: 	  log / succ x.prop
//│ ║       	              ^^^^^
//│ ╟── from receiver:
//│ ║  l.4: 	  log / succ x.prop
//│ ║       	             ^
//│ ╟── from argument:
//│ ║  l.7: 	  succ / f y
//│ ║       	           ^
//│ ╟── from variable:
//│ ║  l.6: 	let h = y =>
//│ ╙──     	        ^
//│ res: int | error

:v
:e
(x => succ x) false
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.44: 	(x => succ x) false
//│ ║        	^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `false` does not match type `int`
//│ ║  l.44: 	(x => succ x) false
//│ ║        	              ^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.44: 	(x => succ x) false
//│ ║        	           ^
//│ ╟── from variable:
//│ ║  l.44: 	(x => succ x) false
//│ ╙──      	 ^
//│ res: int | error


let f = x =>
  log / succ x.prop
  x.prop
let arg = {prop: not true}
let arg2 = {fld: arg}
let i = y =>
  succ / f y.fld
let test = x => y => if x.prop then i x else y
//│ f: {prop: int & 'a} -> 'a
//│ arg: {prop: bool}
//│ arg2: {fld: {prop: bool}}
//│ i: {fld: {prop: int}} -> int
//│ test: {prop: bool, fld: {prop: int}} -> 'a -> (int | 'a)

:e
:verbose
test arg2
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.76: 	test arg2
//│ ║        	^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.63: 	let arg = {prop: not true}
//│ ║        	                 ^^^^^^^^
//│ ╟── but it flows into reference with expected type `{fld: ?a}`
//│ ║  l.76: 	test arg2
//│ ║        	     ^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.61: 	  log / succ x.prop
//│ ║        	             ^^^^^^
//│ ╟── from field selection:
//│ ║  l.61: 	  log / succ x.prop
//│ ║        	              ^^^^^
//│ ╟── from receiver:
//│ ║  l.61: 	  log / succ x.prop
//│ ║        	             ^
//│ ╟── from argument:
//│ ║  l.66: 	  succ / f y.fld
//│ ║        	           ^^^^^
//│ ╟── from field selection:
//│ ║  l.66: 	  succ / f y.fld
//│ ║        	            ^^^^
//│ ╟── from receiver:
//│ ║  l.66: 	  succ / f y.fld
//│ ║        	           ^
//│ ╟── from argument:
//│ ║  l.67: 	let test = x => y => if x.prop then i x else y
//│ ╙──      	                                      ^
//│ res: 'a -> (int | 'a) | error

