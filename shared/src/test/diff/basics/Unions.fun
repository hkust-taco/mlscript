

let f(x: 0 | 1) = x
//│ f: (x: 'a & (0 | 1),) -> 'a

let f(x: 0 | 1) = succ x
//│ f: (x: int & (0 | 1),) -> int

let f(x) = x as 0 | 1
//│ f: (0 | 1) -> 0 | 1

:e // TODO
f 1
f 0
f(0 as 0 | 1)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.13: 	f 1
//│ ║        	^^^
//│ ╟── expression of type `1` does not match type `0 | 1`
//│ ║  l.13: 	f 1
//│ ║        	  ^
//│ ╟── Note: constraint arises from operator application:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	                ^^^^^
//│ ╟── from variable reference:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	           ^
//│ ╟── from pattern variable:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	      ^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.14: 	f 0
//│ ║        	^^^
//│ ╟── expression of type `0` does not match type `0 | 1`
//│ ║  l.14: 	f 0
//│ ║        	  ^
//│ ╟── Note: constraint arises from operator application:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	                ^^^^^
//│ ╟── from variable reference:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	           ^
//│ ╟── from pattern variable:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	      ^
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.15: 	f(0 as 0 | 1)
//│ ║        	  ^^^^^^^^^^
//│ ╟── expression of type `0` does not match type `0 | 1`
//│ ║  l.15: 	f(0 as 0 | 1)
//│ ║        	  ^
//│ ╟── Note: constraint arises from operator application:
//│ ║  l.15: 	f(0 as 0 | 1)
//│ ╙──      	       ^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.15: 	f(0 as 0 | 1)
//│ ║        	^^^^^^^^^^^^^
//│ ╟── expression of type `0` does not match type `0 | 1`
//│ ║  l.15: 	f(0 as 0 | 1)
//│ ║        	       ^
//│ ╟── but it flows into argument of expected type `0 | 1`
//│ ║  l.15: 	f(0 as 0 | 1)
//│ ║        	 ^^^^^^^^^^^^
//│ ╟── Note: constraint arises from operator application:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	                ^^^^^
//│ ╟── from variable reference:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	           ^
//│ ╟── from pattern variable:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	      ^
//│ res: (0 | 1) | error
//│ res: (0 | 1) | error
//│ res: (0 | 1) | error

let g(x: int) = succ x
g 0
let h = y => g(y as 0 | 1)
//│ g: (x: int,) -> int
//│ res: int
//│ h: (0 | 1) -> int
:e // TODO
g (0 as 0 | 1)
h(0)
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.84: 	g (0 as 0 | 1)
//│ ║        	   ^^^^^^^^^^
//│ ╟── expression of type `0` does not match type `0 | 1`
//│ ║  l.84: 	g (0 as 0 | 1)
//│ ║        	   ^
//│ ╟── Note: constraint arises from operator application:
//│ ║  l.84: 	g (0 as 0 | 1)
//│ ╙──      	        ^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.85: 	h(0)
//│ ║        	^^^^
//│ ╟── expression of type `0` does not match type `0 | 1`
//│ ║  l.85: 	h(0)
//│ ║        	  ^
//│ ╟── but it flows into argument of expected type `0 | 1`
//│ ║  l.85: 	h(0)
//│ ║        	 ^^^
//│ ╟── Note: constraint arises from operator application:
//│ ║  l.79: 	let h = y => g(y as 0 | 1)
//│ ║        	                    ^^^^^
//│ ╟── from variable reference:
//│ ║  l.79: 	let h = y => g(y as 0 | 1)
//│ ╙──      	               ^
//│ res: int
//│ res: int | error

