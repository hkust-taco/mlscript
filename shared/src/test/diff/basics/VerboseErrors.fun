
:v // Note: removing this will mean not showing parameter provs in downstream errors
let f = x =>
  log / succ x.prop
  x.prop
let h = y =>
  succ / f y
let mkArg = a => {prop: a}
//│ f: {prop: 'prop} -> 'prop
//│ h: {prop: int} -> int
//│ mkArg: 'a -> {prop: 'a}

:v
:e
h / mkArg false
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.15: 	h / mkArg false
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── reference of type `false` is not an instance of type `int`
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
//│ ╟── reference of type `false` is not an instance of type `int`
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
//│ f: {prop: 'prop} -> 'prop
//│ arg: {prop: bool}
//│ arg2: {fld: {prop: bool}}
//│ i: {fld: {prop: int}} -> int
//│ test: ({prop: bool} & 'a) -> 'b -> (int | 'b
//│   where
//│     'a <: {fld: {prop: int}})

:e
:verbose
test arg2
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.66: 	test arg2
//│ ║        	^^^^^^^^^
//│ ╟── record of type `{fld: forall ?a. {prop: ?a}}` does not have field 'prop'
//│ ║  l.52: 	let arg2 = {fld: arg}
//│ ║        	           ^^^^^^^^^^
//│ ╟── but it flows into reference with expected type `{prop: ?prop}`
//│ ║  l.66: 	test arg2
//│ ║        	     ^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.55: 	let test = x => y => if x.prop then i x else y
//│ ╙──      	                         ^^^^^
//│ res: 'a -> (int | 'a
//│   where
//│     'b <: {fld: {prop: int}}) | error

