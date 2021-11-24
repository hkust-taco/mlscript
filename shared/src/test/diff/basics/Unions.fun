

let f(x: 0 | 1) = x
//│ f: (x: 0 & 'a | 1 & 'a,) -> 'a

let f(x: 0 | 1) = succ x
//│ f: (x: 0 | 1,) -> int

let f(x) = x as 0 | 1
//│ f: 0 | 1 -> 0 | 1

f 1
f 0
f(0 as 0 | 1)
//│ res: 0 | 1
//│ res: 0 | 1
//│ res: 0 | 1

:e
f 3
f (0 as 1 | 3)
f (0 as 0 | 3)
f (0 as 3 | 4)
f (0 as Int)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.20: 	f 3
//│ ║        	^^^
//│ ╟── expression of type `3` does not match type `0 | 1`
//│ ║  l.20: 	f 3
//│ ║        	  ^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	                ^^^^^
//│ ╟── from reference:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	           ^
//│ res: 0 | 1 | error
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ║        	   ^^^^^^^^^^
//│ ╟── expression of type `0` does not match type `1 | 3`
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ║        	   ^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ╙──      	        ^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ║        	^^^^^^^^^^^^^^
//│ ╟── expression of type `3` does not match type `0 | 1`
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ║        	            ^
//│ ╟── but it flows into argument with expected type `0 | 1`
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ║        	  ^^^^^^^^^^^^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	                ^^^^^
//│ ╟── from reference:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	           ^
//│ res: 0 | 1 | error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.22: 	f (0 as 0 | 3)
//│ ║        	^^^^^^^^^^^^^^
//│ ╟── expression of type `3` does not match type `0 | 1`
//│ ║  l.22: 	f (0 as 0 | 3)
//│ ║        	            ^
//│ ╟── but it flows into argument with expected type `0 | 1`
//│ ║  l.22: 	f (0 as 0 | 3)
//│ ║        	  ^^^^^^^^^^^^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	                ^^^^^
//│ ╟── from reference:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	           ^
//│ res: 0 | 1 | error
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ║        	   ^^^^^^^^^^
//│ ╟── expression of type `0` does not match type `3 | 4`
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ║        	   ^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ╙──      	        ^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ║        	^^^^^^^^^^^^^^
//│ ╟── expression of type `3` does not match type `0 | 1`
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ║        	        ^
//│ ╟── but it flows into argument with expected type `0 | 1`
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ║        	  ^^^^^^^^^^^^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	                ^^^^^
//│ ╟── from reference:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	           ^
//│ res: 0 | 1 | error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.24: 	f (0 as Int)
//│ ║        	^^^^^^^^^^^^
//│ ╟── expression of type `int` does not match type `0 | 1`
//│ ║  l.24: 	f (0 as Int)
//│ ║        	        ^^^
//│ ╟── but it flows into argument with expected type `0 | 1`
//│ ║  l.24: 	f (0 as Int)
//│ ║        	  ^^^^^^^^^^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ║       	                ^^^^^
//│ ╟── from reference:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	           ^
//│ res: 0 | 1 | error

let g(x: int) = succ x
g 0
g (0 as 0 | 1)
let h = y => g(y as 0 | 1)
h(0)
//│ g: (x: int,) -> int
//│ res: int
//│ res: int
//│ h: 0 | 1 -> int
//│ res: int

let foo(r: { v: 0 } | { v: 1 }) = if r.v < 1 then r.v else 2
//│ foo: (r: {v: 0 & 'a | 1 & 'a},) -> 'a | 2

foo({ v: 0 })
foo({ v: 1 })
//│ res: 2 | 0
//│ res: 2 | 1

x => foo(x)
//│ res: (r: {v: 0 & 'a | 1 & 'a},) -> 2 | 'a

x => foo { v: x }
//│ res: 0 & 'a | 1 & 'a -> 2 | 'a


let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ bar: (r: (0, 0,) & {_2: 'a, _1: int & 'a} | (1, 1,) & {_2: 'a, _1: int & 'a},) -> 'a

// :e
bar(0, 1)
bar(2, 2)
//│ res: 1 | 0
//│ res: 2

// TODO
bar(0, 0)
bar(1, 1)
bar(0, _)
bar(_, 1)
//│ res: 0
//│ res: 1
//│ res: 0
//│ res: 1

// TODO
x => bar(x, x) // TODO simplify better
x => bar(1, x)
x => bar(x, 0)
//│ res: int & 'a -> 'a
//│ res: 'a -> 'a | 1
//│ res: int & 'a -> 0 | 'a

// :e
bar(_, _)
(x, y) => bar(x, y)
//│ res: nothing
//│ res: (int & 'a, 'a,) -> 'a

// ^ TODO allow explicit request for inferring an overloaded type in case of ambiguities

// TODO
x => bar(bar(0, x), 0)
x => bar(bar(x, x), 0)
x => bar(bar(0, x), x)
x => bar(bar(x, x), 0)
//│ res: int & 'a -> 0 | 'a
//│ res: int & 'a -> 0 | 'a
//│ res: int & 'a -> 'a | 0
//│ res: int & 'a -> 0 | 'a

// :e
x => bar(bar(x, 1), 0)
(x, y) => bar(bar(x, y), x)
//│ res: int & 'a -> 0 | 'a | 1
//│ res: (int & 'a, int & 'a,) -> 'a

// :e // TODO delay tricky constraints for later (instead of eager) resolution:
(x, y) => bar(bar(x, y), 0)
//│ res: (int & 'a, int & 'a,) -> 0 | 'a


let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: {_2: 'a, _1: int & 'a},) -> 'a

:e
baz(0)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.207: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── expression of type `0` does not have field '_2'
//│ ║  l.207: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: (0, 0,) & {_2: ?a, _1: int & ?b & ?b} & ?c | {_2: ?a, _1: int & ?b & ?b} & ?c & ?d,)`
//│ ║  l.207: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.203: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.203: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^
//│ res: error

baz(0, 0)
baz(0, 1)
baz(1, 1)
//│ res: 0
//│ res: 1 | 0
//│ res: 1

x => baz(x, 0)
x => baz(0, x)
x => baz(x, x)
(x, y) => baz(x, y)
//│ res: int & 'a -> 0 | 'a
//│ res: 'a -> 'a | 0
//│ res: int & 'a -> 'a
//│ res: (int & 'a, 'a,) -> 'a


let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: (0, 0,) & {_2: 'a, _1: int & 'a} | (1, anything,) & {_2: 'a, _1: int & 'a},) -> 'a

:e
baz(0)
baz(0, 1)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.246: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── expression of type `0` does not have field '_2'
//│ ║  l.246: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: (0, 0,) & {_2: ?a, _1: int & ?b & ?b} & ?c | (1, ?d,) & {_2: ?a, _1: int & ?b & ?b} & ?c,)`
//│ ║  l.246: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.242: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.242: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ res: 1 | 0

// TODO
baz(0, 0)
baz(1, 1)
x => baz(0, x)
x => baz(1, x)
x => baz(x, 1)
//│ res: 0
//│ res: 1
//│ res: 'a -> 'a | 0
//│ res: 'a -> 'a | 1
//│ res: int & 'a -> 1 | 'a

// :e
x => baz(x, 0)
x => baz(x, x)
(x, y) => baz(x, y)
//│ res: int & 'a -> 0 | 'a
//│ res: int & 'a -> 'a
//│ res: (int & 'a, 'a,) -> 'a

