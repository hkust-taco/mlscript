
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
//│ ╟── reference of type `false` does not match type `int`
//│ ║  l.15: 	h / mkArg false
//│ ║        	          ^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.7: 	  succ / f y
//│ ║       	         ^^^
//│ ╟── from field selection:
//│ ║  l.5: 	  x.prop
//│ ╙──     	   ^^^^^
//│ res: error | int

:v
:e
(x => succ x) false
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.32: 	(x => succ x) false
//│ ║        	^^^^^^^^^^^^^^^^^^^
//│ ╟── reference of type `false` does not match type `int`
//│ ║  l.32: 	(x => succ x) false
//│ ║        	              ^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.32: 	(x => succ x) false
//│ ║        	           ^
//│ ╟── from variable:
//│ ║  l.32: 	(x => succ x) false
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
//│ ║  l.64: 	test arg2
//│ ║        	^^^^^^^^^
//│ ╟── application of type `bool` does not match type `int`
//│ ║  l.51: 	let arg = {prop: not true}
//│ ║        	                 ^^^^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.54: 	  succ / f y.fld
//│ ║        	         ^^^^^^^
//│ ╟── from field selection:
//│ ║  l.50: 	  x.prop
//│ ╙──      	   ^^^^^
//│ res: 'a -> (int | 'a) | error

