
:v // Note: removing this will mean not showing parameter provs in downstream errors
let f = x =>
  log / succ x.prop
  x.prop
let h = y =>
  succ / f y
let mkArg = a => {prop: a}
//│ f: {prop: 'a & int} -> 'a
//│ h: {prop: int} -> int
//│ mkArg: 'a -> {prop: 'a}

// :d
:v
:e
h / mkArg false
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.16: 	h / mkArg false
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.16: 	h / mkArg false
//│ ║        	          ^^^^^
//│ ╟── but it flows into function application of expected type `{prop: ?a & int}`
//│ ║  l.16: 	h / mkArg false
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
//│ ╟── from parameter:
//│ ║  l.6: 	let h = y =>
//│ ╙──     	        ^
//│ res: int

:v
:e
(x => succ x) false
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.45: 	(x => succ x) false
//│ ║        	^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.45: 	(x => succ x) false
//│ ║        	              ^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.45: 	(x => succ x) false
//│ ║        	           ^
//│ ╟── from parameter:
//│ ║  l.45: 	(x => succ x) false
//│ ╙──      	 ^
//│ res: int

