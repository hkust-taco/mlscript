

let f(x: 0 | 1) = x
//│ f: (x: 'a & (0 | 1),) -> 'a

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
//│ ╟── integer literal of type `3` does not match type `0 | 1`
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
//│ ╟── integer literal of type `0` does not match type `1 | 3`
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ║        	   ^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ╙──      	        ^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ║        	^^^^^^^^^^^^^^
//│ ╟── integer literal of type `3` does not match type `0 | 1`
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ║        	            ^
//│ ╟── but it flows into type union with expected type `0 | 1`
//│ ║  l.21: 	f (0 as 1 | 3)
//│ ║        	        ^^^^^
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
//│ ╟── integer literal of type `3` does not match type `0 | 1`
//│ ║  l.22: 	f (0 as 0 | 3)
//│ ║        	            ^
//│ ╟── but it flows into type union with expected type `0 | 1`
//│ ║  l.22: 	f (0 as 0 | 3)
//│ ║        	        ^^^^^
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
//│ ╟── integer literal of type `0` does not match type `3 | 4`
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ║        	   ^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ╙──      	        ^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ║        	^^^^^^^^^^^^^^
//│ ╟── integer literal of type `3` does not match type `0 | 1`
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ║        	        ^
//│ ╟── but it flows into type union with expected type `0 | 1`
//│ ║  l.23: 	f (0 as 3 | 4)
//│ ║        	        ^^^^^
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
//│ ╟── reference of type `int` does not match type `0 | 1`
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
//│ h: (0 | 1) -> int
//│ res: int

let foo(r: { v: 0 } | { v: 1 }) = if r.v < 1 then r.v else 2
//│ foo: (r: {v: 0 | 1} & 'a,) -> (forall 'a, 'v. (2 | 'v
//│   where
//│     'a <: {v: 'v}))

foo({ v: 0 })
foo({ v: 1 })
//│ res: 2 | 'v
//│   where
//│     'a <: {v: 'v}
//│ res: 2 | 'v
//│   where
//│     'a <: {v: 'v}

x => foo(x)
//│ res: (r: {v: 0 | 1} & 'a,) -> (forall 'v. (2 | 'v
//│   where
//│     'a <: {v: 'v}))

x => foo { v: x }
//│ res: (0 | 1) -> (forall 'v. (2 | 'v
//│   where
//│     'a <: {v: 'v}))


// Notice that in MLscript, `(0, 0) | (1, 1)` is equivalent to `(0 | 1, 0 | 1)`
let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ bar: (r: (0 | 1, 0 | 1,) & 'a,) -> (forall 'a, 'b. ('b
//│   where
//│     'a <: {_1: 'b}
//│     'a <: {_2: 'b}))

bar(0, 1)
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}

:e
bar(2, 2)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.171: 	bar(2, 2)
//│ ║         	^^^^^^^^^
//│ ╟── integer literal of type `2` does not match type `0 | 1`
//│ ║  l.171: 	bar(2, 2)
//│ ╙──       	    ^
//│ res: error | 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}

bar(0, 0)
bar(1, 1)
bar(0, _)
bar(_, 1)
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}

let f x = bar(x, x)
//│ f: (0 | 1) -> (forall 'a, 'b. ('b
//│   where
//│     'a <: {_2: 'b}
//│     'a <: {_1: 'b}))

f 0
f 1
//│ res: 'a
//│   where
//│     'b <: {_1: 'a}
//│     'b <: {_2: 'a}
//│ res: 'a
//│   where
//│     'b <: {_1: 'a}
//│     'b <: {_2: 'a}

:e
f 2
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.222: 	f 2
//│ ║         	^^^
//│ ╟── integer literal of type `2` does not match type `0 | 1`
//│ ║  l.222: 	f 2
//│ ║         	  ^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.204: 	let f x = bar(x, x)
//│ ╙──       	              ^
//│ res: error | 'a
//│   where
//│     'b <: {_1: 'a}
//│     'b <: {_2: 'a}

x => bar(1, x)
x => bar(x, 0)
//│ res: (0 | 1) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: (0 | 1) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))

bar(_, _)
(x, y) => bar(x, y)
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}
//│ res: (0 | 1, 0 | 1,) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))

// ^ TODO allow explicit request for inferring an overloaded type in case of ambiguities

x => bar(bar(0, x), 0)
x => bar(bar(x, x), 0)
x => bar(bar(0, x), x)
x => bar(bar(x, x), 0)
//│ res: (0 | 1) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: (0 | 1) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: (0 | 1) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: (0 | 1) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))

x => bar(bar(x, 1), 0)
(x, y) => bar(bar(x, y), x)
//│ res: (0 | 1) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: (0 | 1, 0 | 1,) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))

(x, y) => bar(bar(x, y), 0)
//│ res: (0 | 1, 0 | 1,) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))


let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: {_1: int} & 'a,) -> (forall 'a, 'b. ('b
//│   where
//│     'a <: {_1: 'b}
//│     'a <: {_2: 'b}))

:e
baz(0)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.307: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── integer literal of type `0` does not have field '_1'
//│ ║  l.307: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `{_1: ?a}`
//│ ║  l.307: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.300: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                             ^^^
//│ ╟── from binding:
//│ ║  l.300: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	        ^^^^^^^^^^^^^
//│ res: error | 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}

baz(0, 0)
baz(0, 1)
baz(1, 1)
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}

x => baz(x, 0)
x => baz(0, x)
x => baz(x, x)
(x, y) => baz(x, y)
//│ res: int -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: anything -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: int -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: (int, anything,) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))


let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: (0 | 1, 'a,) & 'a,) -> (forall 'a, 'b. ('b
//│   where
//│     'a <: {_1: 'b}
//│     'a <: {_2: 'b}))

:e
baz(0)
baz(0, 1)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.373: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── integer literal of type `0` does not have field '_1'
//│ ║  l.373: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `{_1: ?a}`
//│ ║  l.373: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.366: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                  ^^^
//│ ╟── from binding:
//│ ║  l.366: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	        ^^^^^^^^^^^^^^^^^^
//│ res: error | 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}

baz(0, 0)
baz(1, 1)
x => baz(0, x)
x => baz(1, x)
x => baz(x, 1)
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}
//│ res: 'a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}
//│ res: anything -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: anything -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: (0 | 1) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))

x => baz(x, 0)
x => baz(x, x)
(x, y) => baz(x, y)
//│ res: (0 | 1) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: (0 | 1) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))
//│ res: (0 | 1, anything,) -> (forall 'a. ('a
//│   where
//│     'b <: {_2: 'a}
//│     'b <: {_1: 'a}))

