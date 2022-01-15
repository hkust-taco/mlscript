

let f(x: 0 | 1) = x
//│ f: (x: 0 & 'a | 1 & 'a,) -> 'a

let f(x: 0 | 1) = succ x
//│ f: (x: 0 | 1,) -> int

let f(x) = x as 0 | 1
//│ f: (0 | 1) -> (0 | 1)

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
//│ ╙──     	                ^^^^^
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
//│ ╙──     	                ^^^^^
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
//│ ╙──     	                ^^^^^
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
//│ ╙──     	                ^^^^^
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
//│ ╙──     	                ^^^^^
//│ res: 0 | 1 | error

let g(x: int) = succ x
g 0
g (0 as 0 | 1)
let h = y => g(y as 0 | 1)
h(0)
//│ g: (x: int,) -> int
//│ res: int
//│ res: int
//│ h: (0 | 1) -> int
//│ res: int

let foo(r: { v: 0 } | { v: 1 }) = if r.v < 1 then r.v else 2
//│ foo: (r: {v: 0 & 'a | 1 & 'a},) -> (2 | 'a)

foo({ v: 0 })
foo({ v: 1 })
//│ res: 0 | 2
//│ res: 1 | 2

x => foo(x)
//│ res: (r: {v: 0 & 'a | 1 & 'a},) -> (2 | 'a)

x => foo { v: x }
//│ res: (0 & 'a | 1 & 'a) -> (2 | 'a)


// Notice that in MLscript, `(0, 0) | (1, 1)` is equivalent to `(0 | 1, 0 | 1)`
let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ bar: (r: (0 | 1, 0 | 1,) & {_1: int & 'a, _2: 'a},) -> 'a

bar(0, 1)
//│ res: 0 | 1

:e
bar(2, 2)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.140: 	bar(2, 2)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `2` does not match type `0 | 1`
//│ ║  l.140: 	bar(2, 2)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.140: 	bar(2, 2)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.133: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: 2 | error

bar(0, 0)
bar(1, 1)
bar(0, _)
bar(_, 1)
//│ res: 0
//│ res: 1
//│ res: 0
//│ res: 1

let f x = bar(x, x)
//│ f: (0 & 'a | 1 & 'a) -> 'a

f 0
f 1
//│ res: 0
//│ res: 1

:e
f 2
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.173: 	f 2
//│ ║         	^^^
//│ ╟── expression of type `2` does not match type `0 | 1`
//│ ║  l.173: 	f 2
//│ ╙──       	  ^
//│ res: 2 | error

x => bar(1, x)
x => bar(x, 0)
//│ res: (0 & 'a | 1 & 'a) -> (1 | 'a)
//│ res: (0 & 'a | 1 & 'a) -> (0 | 'a)

bar(_, _)
(x, y) => bar(x, y)
//│ res: nothing
//│ res: (0 & 'a | 1 & 'a, 0 & 'a | 1 & 'a,) -> 'a

// ^ TODO allow explicit request for inferring an overloaded type in case of ambiguities

x => bar(bar(0, x), 0)
x => bar(bar(x, x), 0)
x => bar(bar(0, x), x)
x => bar(bar(x, x), 0)
//│ res: (0 & 'a | 1 & 'a) -> (0 | 'a)
//│ res: (0 & 'a | 1 & 'a) -> (0 | 'a)
//│ res: (0 & 'a | 1 & 'a) -> (0 | 'a)
//│ res: (0 & 'a | 1 & 'a) -> (0 | 'a)

x => bar(bar(x, 1), 0)
(x, y) => bar(bar(x, y), x)
//│ res: (0 & 'a | 1 & 'a) -> (0 | 1 | 'a)
//│ res: (0 & 'a | 1 & 'a, 0 & 'a | 1 & 'a,) -> 'a

(x, y) => bar(bar(x, y), 0)
//│ res: (0 & 'a | 1 & 'a, 0 & 'a | 1 & 'a,) -> (0 | 'a)


let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: {_1: int & 'a, _2: 'a},) -> 'a

:e
baz(0)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.216: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── expression of type `0` does not have field '_2'
//│ ║  l.216: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.216: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.212: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.212: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^
//│ res: error

baz(0, 0)
baz(0, 1)
baz(1, 1)
//│ res: 0
//│ res: 0 | 1
//│ res: 1

x => baz(x, 0)
x => baz(0, x)
x => baz(x, x)
(x, y) => baz(x, y)
//│ res: (int & 'a) -> (0 | 'a)
//│ res: 'a -> (0 | 'a)
//│ res: (int & 'a) -> 'a
//│ res: (int & 'a, 'a,) -> 'a


let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: (0 | 1, anything,) & {_1: int & 'a, _2: 'a},) -> 'a

:e
baz(0)
baz(0, 1)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.255: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── expression of type `0` does not have field '_2'
//│ ║  l.255: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.255: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.251: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.251: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ res: 0 | 1

baz(0, 0)
baz(1, 1)
x => baz(0, x)
x => baz(1, x)
x => baz(x, 1)
//│ res: 0
//│ res: 1
//│ res: 'a -> (0 | 'a)
//│ res: 'a -> (1 | 'a)
//│ res: (0 & 'a | 1 & 'a) -> (1 | 'a)

x => baz(x, 0)
x => baz(x, x)
(x, y) => baz(x, y)
//│ res: (0 & 'a | 1 & 'a) -> (0 | 'a)
//│ res: (0 & 'a | 1 & 'a) -> 'a
//│ res: (0 & 'a | 1 & 'a, 'a,) -> 'a

