

let f(x: 0 | 1) = x
//│ f: (x: 'a & (0 | 1),) -> 'a

let f(x: 0 | 1) = succ x
//│ f: (x: int & (0 | 1),) -> int

let f(x) = x as 0 | 1
//│ f: (0 | 1) -> 0 | 1

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
//│ res: (0 | 1) | error
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
//│ res: (0 | 1) | error
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
//│ res: (0 | 1) | error
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
//│ res: (0 | 1) | error
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
//│ res: (0 | 1) | error

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
//│ foo: (r: {v: 'a & int & (0 | 1)},) -> 'a | 2

foo({ v: 0 })
foo({ v: 1 })
//│ res: 2 | 0
//│ res: 2 | 1

x => foo(x)
//│ res: (r: {v: 'a & int & (0 | 1)},) -> 'a | 2

x => foo { v: x }
//│ res: 'a & (0 | 1) & int -> 'a | 2


let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ bar: (r: ((0, 0,) | (1, 1,)) & {_1: 'a & int, _2: 'a},) -> 'a

:e
bar(0, 1)
bar(2, 2)
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.67: 	bar(0, 1)
//│ ╙──      	^^^^^^^^^
//│ res: 1 | 0 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.68: 	bar(2, 2)
//│ ╙──      	^^^^^^^^^
//│ res: 2 | error

// TODO
bar(0, 0)
bar(1, 1)
bar(0, _)
bar(_, 1)
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.79: 	bar(0, 0)
//│ ╙──      	^^^^^^^^^
//│ res: 0 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.80: 	bar(1, 1)
//│ ╙──      	^^^^^^^^^
//│ res: 1 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.81: 	bar(0, _)
//│ ╙──      	^^^^^^^^^
//│ res: 0 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.82: 	bar(_, 1)
//│ ╙──      	^^^^^^^^^
//│ res: 1 | error

// TODO
x => bar(x, x) // TODO simplify better
x => bar(1, x)
x => bar(x, 0)
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.101: 	x => bar(x, x) // TODO simplify better
//│ ╙──       	     ^^^^^^^^^
//│ res: 'a & int -> 'a | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.102: 	x => bar(1, x)
//│ ╙──       	     ^^^^^^^^^
//│ res: 'a -> 'a | 1 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.103: 	x => bar(x, 0)
//│ ╙──       	     ^^^^^^^^^
//│ res: 'a & int -> 'a | 0 | error

:e
bar(_, _)
(x, y) => bar(x, y)
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.118: 	bar(_, _)
//│ ╙──       	^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.119: 	(x, y) => bar(x, y)
//│ ╙──       	          ^^^^^^^^^
//│ res: ('a & int, 'a,) -> 'a | error

// ^ TODO allow explicit request for inferring an overloaded type in case of ambiguities

// TODO
x => bar(bar(0, x), 0)
x => bar(bar(x, x), 0)
x => bar(bar(0, x), x)
x => bar(bar(x, x), 0)
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.132: 	x => bar(bar(0, x), 0)
//│ ╙──       	         ^^^^^^^^^
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.132: 	x => bar(bar(0, x), 0)
//│ ╙──       	     ^^^^^^^^^^^^^^^^^
//│ res: 'a & int -> 'a | 0 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.133: 	x => bar(bar(x, x), 0)
//│ ╙──       	         ^^^^^^^^^
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.133: 	x => bar(bar(x, x), 0)
//│ ╙──       	     ^^^^^^^^^^^^^^^^^
//│ res: 'a & int -> 'a | 0 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.134: 	x => bar(bar(0, x), x)
//│ ╙──       	         ^^^^^^^^^
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.134: 	x => bar(bar(0, x), x)
//│ ╙──       	     ^^^^^^^^^^^^^^^^^
//│ res: 'a & int -> 'a | 0 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.135: 	x => bar(bar(x, x), 0)
//│ ╙──       	         ^^^^^^^^^
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.135: 	x => bar(bar(x, x), 0)
//│ ╙──       	     ^^^^^^^^^^^^^^^^^
//│ res: 'a & int -> 'a | 0 | error

:e
x => bar(bar(x, 1), 0)
(x, y) => bar(bar(x, y), x)
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.166: 	x => bar(bar(x, 1), 0)
//│ ╙──       	         ^^^^^^^^^
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.166: 	x => bar(bar(x, 1), 0)
//│ ╙──       	     ^^^^^^^^^^^^^^^^^
//│ res: 'a & int -> 'a | 0 | 1 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.167: 	(x, y) => bar(bar(x, y), x)
//│ ╙──       	              ^^^^^^^^^
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.167: 	(x, y) => bar(bar(x, y), x)
//│ ╙──       	          ^^^^^^^^^^^^^^^^^
//│ res: ('a & int, 'a & int,) -> 'a | error

:e // TODO delay tricky constraints for later (instead of eager) resolution:
(x, y) => bar(bar(x, y), 0)
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.184: 	(x, y) => bar(bar(x, y), 0)
//│ ╙──       	              ^^^^^^^^^
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.184: 	(x, y) => bar(bar(x, y), 0)
//│ ╙──       	          ^^^^^^^^^^^^^^^^^
//│ res: ('a & int, 'a & int,) -> 'a | 0 | error


let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: ((0, 0,) | anything) & {_1: 'a & int, _2: 'a},) -> 'a

:e
baz(0)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.198: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── expression of type `0` does not have field '_2'
//│ ║  l.198: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: ?a & ((0, 0,) | ?b) & {_1: ?c & int, _2: ?d},)`
//│ ║  l.198: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.194: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.194: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
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
//│ res: 'a & int -> 'a | 0
//│ res: 'a -> 'a | 0
//│ res: 'a & int -> 'a
//│ res: ('a & int, 'a,) -> 'a


let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: ((0, 0,) | (1, anything,)) & {_1: 'a & int, _2: 'a},) -> 'a

:e
baz(0)
baz(0, 1)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.237: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── expression of type `0` does not have field '_2'
//│ ║  l.237: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: ?a & ((0, 0,) | (1, ?b,)) & {_1: ?c & int, _2: ?d},)`
//│ ║  l.237: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.233: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.233: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.238: 	baz(0, 1)
//│ ╙──       	^^^^^^^^^
//│ res: 1 | 0 | error

// TODO
baz(0, 0)
baz(1, 1)
x => baz(0, x)
x => baz(1, x)
x => baz(x, 1)
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.261: 	baz(0, 0)
//│ ╙──       	^^^^^^^^^
//│ res: 0 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.262: 	baz(1, 1)
//│ ╙──       	^^^^^^^^^
//│ res: 1 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.263: 	x => baz(0, x)
//│ ╙──       	     ^^^^^^^^^
//│ res: 'a -> 'a | 0 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.264: 	x => baz(1, x)
//│ ╙──       	     ^^^^^^^^^
//│ res: 'a -> 'a | 1 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.265: 	x => baz(x, 1)
//│ ╙──       	     ^^^^^^^^^
//│ res: 'a & int -> 'a | 1 | error

:e
x => baz(x, 0)
x => baz(x, x)
(x, y) => baz(x, y)
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.288: 	x => baz(x, 0)
//│ ╙──       	     ^^^^^^^^^
//│ res: 'a & int -> 'a | 0 | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.289: 	x => baz(x, x)
//│ ╙──       	     ^^^^^^^^^
//│ res: 'a & int -> 'a | error
//│ ╔══[ERROR] TODO handle tuples
//│ ║  l.290: 	(x, y) => baz(x, y)
//│ ╙──       	          ^^^^^^^^^
//│ res: ('a & int, 'a,) -> 'a | error

