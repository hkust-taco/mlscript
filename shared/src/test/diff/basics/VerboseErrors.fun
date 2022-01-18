
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
//│ ║  l.8: 	let mkArg = a => {prop: a}
//│ ║       	            ^
//│ ╟── but it flows into application with expected type `?a`
//│ ║  l.15: 	h / mkArg false
//│ ║        	    ^^^^^^^^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.7: 	  succ / f y
//│ ║       	         ^^^
//│ ╟── from field selection:
//│ ║  l.5: 	  x.prop
//│ ║       	   ^^^^^
//│ ╟── from variable:
//│ ║  l.3: 	let f = x =>
//│ ║       	        ^
//│ ╟── from variable:
//│ ║  l.6: 	let h = y =>
//│ ╙──     	        ^
//│ res: error | int

:v
:e
(x => succ x) false
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.41: 	(x => succ x) false
//│ ║        	^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `false` does not match type `int`
//│ ║  l.41: 	(x => succ x) false
//│ ║        	              ^^^^^
//│ ╟── Note: constraint arises from variable:
//│ ║  l.41: 	(x => succ x) false
//│ ╙──      	 ^
//│ res: error | int


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
//│ test: {fld: {prop: int}, prop: bool} -> 'a -> (int | 'a)

:e
:verbose
test arg2
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.70: 	test arg2
//│ ║        	^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.57: 	let arg = {prop: not true}
//│ ║        	                 ^^^^^^^^
//│ ╟── but it flows into reference with expected type `?a`
//│ ║  l.70: 	test arg2
//│ ║        	     ^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.60: 	  succ / f y.fld
//│ ║        	         ^^^^^^^
//│ ╟── from field selection:
//│ ║  l.56: 	  x.prop
//│ ║        	   ^^^^^
//│ ╟── from field selection:
//│ ║  l.60: 	  succ / f y.fld
//│ ╙──      	            ^^^^
//│ res: 'a -> (int | 'a) | error

