

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
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.151: 	bar(0, 1)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(0, 1,)` does not have field '_2'
//│ ║  l.151: 	bar(0, 1)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.151: 	bar(0, 1)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error

:e
bar(2, 2)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.170: 	bar(2, 2)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(2, 2,)` does not have field '_2'
//│ ║  l.170: 	bar(2, 2)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.170: 	bar(2, 2)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error

bar(0, 0)
bar(1, 1)
bar(0, _)
bar(_, 1)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.188: 	bar(0, 0)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(0, 0,)` does not have field '_2'
//│ ║  l.188: 	bar(0, 0)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.188: 	bar(0, 0)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.189: 	bar(1, 1)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(1, 1,)` does not have field '_2'
//│ ║  l.189: 	bar(1, 1)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.189: 	bar(1, 1)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.190: 	bar(0, _)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(0, ?a,)` does not have field '_2'
//│ ║  l.190: 	bar(0, _)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.190: 	bar(0, _)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.191: 	bar(_, 1)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(?a, 1,)` does not have field '_2'
//│ ║  l.191: 	bar(_, 1)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.191: 	bar(_, 1)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error

let f x = bar(x, x)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.257: 	let f x = bar(x, x)
//│ ║         	          ^^^^^^^^^
//│ ╟── expression of type `(?a, ?a,)` does not have field '_2'
//│ ║  l.257: 	let f x = bar(x, x)
//│ ║         	              ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.257: 	let f x = bar(x, x)
//│ ║         	             ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ f: (0 | 1) -> error

f 0
f 1
//│ res: error
//│ res: error

:e
f 2
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.281: 	f 2
//│ ║         	^^^
//│ ╟── expression of type `2` does not match type `0 | 1`
//│ ║  l.281: 	f 2
//│ ║         	  ^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.257: 	let f x = bar(x, x)
//│ ╙──       	              ^
//│ res: error

x => bar(1, x)
x => bar(x, 0)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.293: 	x => bar(1, x)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(1, ?a,)` does not have field '_2'
//│ ║  l.293: 	x => bar(1, x)
//│ ║         	         ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.293: 	x => bar(1, x)
//│ ║         	        ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1) -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.294: 	x => bar(x, 0)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(?a, 0,)` does not have field '_2'
//│ ║  l.294: 	x => bar(x, 0)
//│ ║         	         ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.294: 	x => bar(x, 0)
//│ ║         	        ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1) -> error

bar(_, _)
(x, y) => bar(x, y)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.328: 	bar(_, _)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` does not have field '_2'
//│ ║  l.328: 	bar(_, _)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?c,)`
//│ ║  l.328: 	bar(_, _)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.329: 	(x, y) => bar(x, y)
//│ ║         	          ^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` does not have field '_2'
//│ ║  l.329: 	(x, y) => bar(x, y)
//│ ║         	              ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?c,)`
//│ ║  l.329: 	(x, y) => bar(x, y)
//│ ║         	             ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1, 0 | 1,) -> error

// ^ TODO allow explicit request for inferring an overloaded type in case of ambiguities

x => bar(bar(0, x), 0)
x => bar(bar(x, x), 0)
x => bar(bar(0, x), x)
x => bar(bar(x, x), 0)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.365: 	x => bar(bar(0, x), 0)
//│ ║         	         ^^^^^^^^^
//│ ╟── expression of type `(0, ?a,)` does not have field '_2'
//│ ║  l.365: 	x => bar(bar(0, x), 0)
//│ ║         	             ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.365: 	x => bar(bar(0, x), 0)
//│ ║         	            ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.365: 	x => bar(bar(0, x), 0)
//│ ║         	     ^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(?a, 0,)` does not have field '_2'
//│ ║  l.365: 	x => bar(bar(0, x), 0)
//│ ║         	         ^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.365: 	x => bar(bar(0, x), 0)
//│ ║         	        ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1) -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.366: 	x => bar(bar(x, x), 0)
//│ ║         	         ^^^^^^^^^
//│ ╟── expression of type `(?a, ?a,)` does not have field '_2'
//│ ║  l.366: 	x => bar(bar(x, x), 0)
//│ ║         	             ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.366: 	x => bar(bar(x, x), 0)
//│ ║         	            ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.366: 	x => bar(bar(x, x), 0)
//│ ║         	     ^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(?a, 0,)` does not have field '_2'
//│ ║  l.366: 	x => bar(bar(x, x), 0)
//│ ║         	         ^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.366: 	x => bar(bar(x, x), 0)
//│ ║         	        ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1) -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.367: 	x => bar(bar(0, x), x)
//│ ║         	         ^^^^^^^^^
//│ ╟── expression of type `(0, ?a,)` does not have field '_2'
//│ ║  l.367: 	x => bar(bar(0, x), x)
//│ ║         	             ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.367: 	x => bar(bar(0, x), x)
//│ ║         	            ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.367: 	x => bar(bar(0, x), x)
//│ ║         	     ^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` does not have field '_2'
//│ ║  l.367: 	x => bar(bar(0, x), x)
//│ ║         	         ^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `(r: ?c,)`
//│ ║  l.367: 	x => bar(bar(0, x), x)
//│ ║         	        ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1) -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.368: 	x => bar(bar(x, x), 0)
//│ ║         	         ^^^^^^^^^
//│ ╟── expression of type `(?a, ?a,)` does not have field '_2'
//│ ║  l.368: 	x => bar(bar(x, x), 0)
//│ ║         	             ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.368: 	x => bar(bar(x, x), 0)
//│ ║         	            ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.368: 	x => bar(bar(x, x), 0)
//│ ║         	     ^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(?a, 0,)` does not have field '_2'
//│ ║  l.368: 	x => bar(bar(x, x), 0)
//│ ║         	         ^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.368: 	x => bar(bar(x, x), 0)
//│ ║         	        ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1) -> error

x => bar(bar(x, 1), 0)
(x, y) => bar(bar(x, y), x)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.494: 	x => bar(bar(x, 1), 0)
//│ ║         	         ^^^^^^^^^
//│ ╟── expression of type `(?a, 1,)` does not have field '_2'
//│ ║  l.494: 	x => bar(bar(x, 1), 0)
//│ ║         	             ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.494: 	x => bar(bar(x, 1), 0)
//│ ║         	            ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.494: 	x => bar(bar(x, 1), 0)
//│ ║         	     ^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(?a, 0,)` does not have field '_2'
//│ ║  l.494: 	x => bar(bar(x, 1), 0)
//│ ║         	         ^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.494: 	x => bar(bar(x, 1), 0)
//│ ║         	        ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1) -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.495: 	(x, y) => bar(bar(x, y), x)
//│ ║         	              ^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` does not have field '_2'
//│ ║  l.495: 	(x, y) => bar(bar(x, y), x)
//│ ║         	                  ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?c,)`
//│ ║  l.495: 	(x, y) => bar(bar(x, y), x)
//│ ║         	                 ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.495: 	(x, y) => bar(bar(x, y), x)
//│ ║         	          ^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` does not have field '_2'
//│ ║  l.495: 	(x, y) => bar(bar(x, y), x)
//│ ║         	              ^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `(r: ?c,)`
//│ ║  l.495: 	(x, y) => bar(bar(x, y), x)
//│ ║         	             ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1, 0 | 1,) -> error

(x, y) => bar(bar(x, y), 0)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.559: 	(x, y) => bar(bar(x, y), 0)
//│ ║         	              ^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` does not have field '_2'
//│ ║  l.559: 	(x, y) => bar(bar(x, y), 0)
//│ ║         	                  ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?c,)`
//│ ║  l.559: 	(x, y) => bar(bar(x, y), 0)
//│ ║         	                 ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.559: 	(x, y) => bar(bar(x, y), 0)
//│ ║         	          ^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(?a, 0,)` does not have field '_2'
//│ ║  l.559: 	(x, y) => bar(bar(x, y), 0)
//│ ║         	              ^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.559: 	(x, y) => bar(bar(x, y), 0)
//│ ║         	             ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.148: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1, 0 | 1,) -> error


let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: {_1: int & 'a, _2: 'a},) -> 'a

:e
baz(0)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.597: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── expression of type `0` does not have field '_2'
//│ ║  l.597: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.597: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^
//│ res: error

baz(0, 0)
baz(0, 1)
baz(1, 1)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.615: 	baz(0, 0)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(0, 0,)` does not have field '_2'
//│ ║  l.615: 	baz(0, 0)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.615: 	baz(0, 0)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.616: 	baz(0, 1)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(0, 1,)` does not have field '_2'
//│ ║  l.616: 	baz(0, 1)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.616: 	baz(0, 1)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.617: 	baz(1, 1)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(1, 1,)` does not have field '_2'
//│ ║  l.617: 	baz(1, 1)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.617: 	baz(1, 1)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^
//│ res: error

x => baz(x, 0)
x => baz(0, x)
x => baz(x, x)
(x, y) => baz(x, y)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.667: 	x => baz(x, 0)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(?a, 0,)` does not have field '_2'
//│ ║  l.667: 	x => baz(x, 0)
//│ ║         	         ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.667: 	x => baz(x, 0)
//│ ║         	        ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^
//│ res: anything -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.668: 	x => baz(0, x)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(0, ?a,)` does not have field '_2'
//│ ║  l.668: 	x => baz(0, x)
//│ ║         	         ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.668: 	x => baz(0, x)
//│ ║         	        ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^
//│ res: anything -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.669: 	x => baz(x, x)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(?a, ?a,)` does not have field '_2'
//│ ║  l.669: 	x => baz(x, x)
//│ ║         	         ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.669: 	x => baz(x, x)
//│ ║         	        ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^
//│ res: anything -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.670: 	(x, y) => baz(x, y)
//│ ║         	          ^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` does not have field '_2'
//│ ║  l.670: 	(x, y) => baz(x, y)
//│ ║         	              ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?c,)`
//│ ║  l.670: 	(x, y) => baz(x, y)
//│ ║         	             ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.593: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^
//│ res: (anything, anything,) -> error


let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: (0 | 1, anything,) & {_1: int & 'a, _2: 'a},) -> 'a

:e
baz(0)
baz(0, 1)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.741: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── expression of type `0` does not have field '_2'
//│ ║  l.741: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.741: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.742: 	baz(0, 1)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(0, 1,)` does not have field '_2'
//│ ║  l.742: 	baz(0, 1)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.742: 	baz(0, 1)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error

baz(0, 0)
baz(1, 1)
x => baz(0, x)
x => baz(1, x)
x => baz(x, 1)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.776: 	baz(0, 0)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(0, 0,)` does not have field '_2'
//│ ║  l.776: 	baz(0, 0)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.776: 	baz(0, 0)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.777: 	baz(1, 1)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(1, 1,)` does not have field '_2'
//│ ║  l.777: 	baz(1, 1)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a,)`
//│ ║  l.777: 	baz(1, 1)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.778: 	x => baz(0, x)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(0, ?a,)` does not have field '_2'
//│ ║  l.778: 	x => baz(0, x)
//│ ║         	         ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.778: 	x => baz(0, x)
//│ ║         	        ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: anything -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.779: 	x => baz(1, x)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(1, ?a,)` does not have field '_2'
//│ ║  l.779: 	x => baz(1, x)
//│ ║         	         ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.779: 	x => baz(1, x)
//│ ║         	        ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: anything -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.780: 	x => baz(x, 1)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(?a, 1,)` does not have field '_2'
//│ ║  l.780: 	x => baz(x, 1)
//│ ║         	         ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.780: 	x => baz(x, 1)
//│ ║         	        ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1) -> error

x => baz(x, 0)
x => baz(x, x)
(x, y) => baz(x, y)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.862: 	x => baz(x, 0)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(?a, 0,)` does not have field '_2'
//│ ║  l.862: 	x => baz(x, 0)
//│ ║         	         ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.862: 	x => baz(x, 0)
//│ ║         	        ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1) -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.863: 	x => baz(x, x)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(?a, ?a,)` does not have field '_2'
//│ ║  l.863: 	x => baz(x, x)
//│ ║         	         ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b,)`
//│ ║  l.863: 	x => baz(x, x)
//│ ║         	        ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1) -> error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.864: 	(x, y) => baz(x, y)
//│ ║         	          ^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` does not have field '_2'
//│ ║  l.864: 	(x, y) => baz(x, y)
//│ ║         	              ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?c,)`
//│ ║  l.864: 	(x, y) => baz(x, y)
//│ ║         	             ^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.737: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: (0 | 1, anything,) -> error

