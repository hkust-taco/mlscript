

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
//│ ║       	           ^
//│ ╟── from pattern variable:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	      ^
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
//│ ║       	           ^
//│ ╟── from pattern variable:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	      ^
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
//│ ║       	           ^
//│ ╟── from pattern variable:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	      ^
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
//│ ║       	           ^
//│ ╟── from pattern variable:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	      ^
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
//│ ║       	           ^
//│ ╟── from pattern variable:
//│ ║  l.9: 	let f(x) = x as 0 | 1
//│ ╙──     	      ^
//│ res: (0 | 1) | error
//│ res: (0 | 1) | error
//│ res: (0 | 1) | error
//│ res: (0 | 1) | error
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
//│ foo: (r: ({v: 0} | {v: 1}) & {v: 'a & int},) -> 'a | 2

foo({ v: 0 })
foo({ v: 1 })
//│ res: 2 | 0
//│ res: 2 | 1

x => foo(x)
//│ res: (r: ({v: 0} | {v: 1}) & {v: 'a & int},) -> 'a | 2

x => foo { v: x }
//│ res: 'a & (0 | 1) & int -> 'a | 2


let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ bar: (r: ((0, 0,) | (1, 1,)) & {_1: 'a & int, _2: 'a},) -> 'a

:e
bar(0, 1)
bar(2, 2)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.166: 	bar(0, 1)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(0, 1,)` does not match type `(0, 0,) | (1, 1,)`
//│ ║  l.166: 	bar(0, 1)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a & ((0, 0,) | (1, 1,)) & {_1: ?b & int, _2: ?c},)`
//│ ║  l.166: 	bar(0, 1)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.162: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.167: 	bar(2, 2)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(2, 2,)` does not match type `(0, 0,) | (1, 1,)`
//│ ║  l.167: 	bar(2, 2)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?a & ((0, 0,) | (1, 1,)) & {_1: ?b & int, _2: ?c},)`
//│ ║  l.167: 	bar(2, 2)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.162: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: 1 | 0 | error
//│ res: 2 | error

bar(0, 0)
bar(1, 1)
bar(0, _)
bar(_, 1)
//│ res: 0
//│ res: 1
//│ res: 0
//│ res: 1

x => bar(x, x) // TODO simplify better
x => bar(1, x)
x => bar(x, 0)
//│ res: 'a & (0 | 1) & int -> 'a
//│ res: 1 -> 1
//│ res: 0 -> 0

:e
bar(_, _)
(x, y) => bar(x, y)
//│ ╔══[ERROR] Ambiguous constraint in application:
//│ ║  l.212: 	bar(_, _)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` matches several possible instantiations
//│ ║  l.212: 	bar(_, _)
//│ ║         	    ^^^^
//│ ╟── where it is used in argument with expected type `(r: ?c & ((0, 0,) | (1, 1,)) & {_1: ?d & int, _2: ?e},)`
//│ ║  l.212: 	bar(_, _)
//│ ║         	   ^^^^^^
//│ ╟── A possible instantiation is:
//│ ╟──     ?a <: 0
//│ ╟──     ?b <: 0
//│ ╟── Another possible instantiation is:
//│ ╟──     ?a <: 1
//│ ╟──     ?b <: 1
//│ ╟── Use an explicit type annotation to fix the problem.
//│ ╟── Note: constraint arises from type union:
//│ ║  l.162: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Ambiguous constraint in application:
//│ ║  l.213: 	(x, y) => bar(x, y)
//│ ║         	          ^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` matches several possible instantiations
//│ ║  l.213: 	(x, y) => bar(x, y)
//│ ║         	              ^^^^
//│ ╟── where it is used in argument with expected type `(r: ?c & ((0, 0,) | (1, 1,)) & {_1: ?d & int, _2: ?e},)`
//│ ║  l.213: 	(x, y) => bar(x, y)
//│ ║         	             ^^^^^^
//│ ╟── A possible instantiation is:
//│ ╟──     ?a <: 0
//│ ╟──     ?b <: 0
//│ ╟── Another possible instantiation is:
//│ ╟──     ?a <: 1
//│ ╟──     ?b <: 1
//│ ╟── Use an explicit type annotation to fix the problem.
//│ ╟── Note: constraint arises from type union:
//│ ║  l.162: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ res: ('a & int, 'a,) -> 'a | error

// ^ TODO allow explicit request for inferring an overloaded type in case of ambiguities

x => bar(bar(0, x), 0)
x => bar(bar(x, x), 0)
x => bar(bar(0, x), x)
x => bar(bar(x, x), 0)
//│ res: 0 -> 0
//│ res: 0 & (0 | 1) -> 0
//│ res: 0 -> 0
//│ res: 0 & (0 | 1) -> 0

:e
x => bar(bar(x, 1), 0)
(x, y) => bar(bar(x, y), x)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.267: 	x => bar(bar(x, 1), 0)
//│ ║         	     ^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(?a | 1, 0,)` does not match type `(0, 0,) | (1, 1,)`
//│ ║  l.267: 	x => bar(bar(x, 1), 0)
//│ ║         	         ^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b & ((0, 0,) | (1, 1,)) & {_1: ?c & int, _2: ?d},)`
//│ ║  l.267: 	x => bar(bar(x, 1), 0)
//│ ║         	        ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.162: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Ambiguous constraint in application:
//│ ║  l.268: 	(x, y) => bar(bar(x, y), x)
//│ ║         	              ^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` matches several possible instantiations
//│ ║  l.268: 	(x, y) => bar(bar(x, y), x)
//│ ║         	                  ^^^^
//│ ╟── where it is used in argument with expected type `(r: ?c & ((0, 0,) | (1, 1,)) & {_1: ?d & int, _2: ?e},)`
//│ ║  l.268: 	(x, y) => bar(bar(x, y), x)
//│ ║         	                 ^^^^^^
//│ ╟── A possible instantiation is:
//│ ╟──     ?a <: 0
//│ ╟──     ?b <: 0
//│ ╟── Another possible instantiation is:
//│ ╟──     ?a <: 1
//│ ╟──     ?b <: 1
//│ ╟── Use an explicit type annotation to fix the problem.
//│ ╟── Note: constraint arises from type union:
//│ ║  l.162: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Ambiguous constraint in application:
//│ ║  l.268: 	(x, y) => bar(bar(x, y), x)
//│ ║         	          ^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(?a | ?b | error, ?b,)` matches several possible instantiations
//│ ║  l.268: 	(x, y) => bar(bar(x, y), x)
//│ ║         	              ^^^^^^^^^^^^
//│ ╟── where it is used in argument with expected type `(r: ?c & ((0, 0,) | (1, 1,)) & {_1: ?d & int, _2: ?e},)`
//│ ║  l.268: 	(x, y) => bar(bar(x, y), x)
//│ ║         	             ^^^^^^^^^^^^^^
//│ ╟── A possible instantiation is:
//│ ╟──     ?b <: 0
//│ ╟──     ?f <: 0
//│ ╟──     ?g <: 0
//│ ╟──     ?h <: 0
//│ ╟──     ?a | error <: 0
//│ ╟── Another possible instantiation is:
//│ ╟──     ?b <: 1
//│ ╟──     ?f <: 1
//│ ╟──     ?g <: 1
//│ ╟──     ?h <: 1
//│ ╟──     ?a | error <: 1
//│ ╟── Use an explicit type annotation to fix the problem.
//│ ╟── Note: constraint arises from type union:
//│ ║  l.162: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: int & 1 -> 0 | 1 | error
//│ res: ('a & int, 'a & int,) -> 'a | error

:e // TODO delay tricky constraints for later (instead of eager) resolution:
(x, y) => bar(bar(x, y), 0)
//│ ╔══[ERROR] Ambiguous constraint in application:
//│ ║  l.329: 	(x, y) => bar(bar(x, y), 0)
//│ ║         	              ^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` matches several possible instantiations
//│ ║  l.329: 	(x, y) => bar(bar(x, y), 0)
//│ ║         	                  ^^^^
//│ ╟── where it is used in argument with expected type `(r: ?c & ((0, 0,) | (1, 1,)) & {_1: ?d & int, _2: ?e},)`
//│ ║  l.329: 	(x, y) => bar(bar(x, y), 0)
//│ ║         	                 ^^^^^^
//│ ╟── A possible instantiation is:
//│ ╟──     ?a <: 0
//│ ╟──     ?b <: 0
//│ ╟── Another possible instantiation is:
//│ ╟──     ?a <: 1
//│ ╟──     ?b <: 1
//│ ╟── Use an explicit type annotation to fix the problem.
//│ ╟── Note: constraint arises from type union:
//│ ║  l.162: 	let bar(r: (0, 0) | (1, 1)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: ('a & 0, 0,) -> 'a | 0 | error


let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ baz: (r: ((0, 0,) | anything) & {_1: 'a & int, _2: 'a},) -> 'a

:e
baz(0)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.356: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── expression of type `0` does not have field '_2'
//│ ║  l.356: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: ?a & ((0, 0,) | ?b) & {_1: ?c & int, _2: ?d},)`
//│ ║  l.356: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.352: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                     ^^^
//│ ╟── from parameter type:
//│ ║  l.352: 	let baz(r: (0, 0) | _) = if r._1 < 1 then r._1 else r._2
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
//│ ║  l.395: 	baz(0)
//│ ║         	^^^^^^
//│ ╟── expression of type `0` does not have field '_2'
//│ ║  l.395: 	baz(0)
//│ ║         	    ^
//│ ╟── but it flows into argument with expected type `(r: ?a & ((0, 0,) | (1, ?b,)) & {_1: ?c & int, _2: ?d},)`
//│ ║  l.395: 	baz(0)
//│ ║         	   ^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.391: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ║         	                                                          ^^^
//│ ╟── from parameter type:
//│ ║  l.391: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.396: 	baz(0, 1)
//│ ║         	^^^^^^^^^
//│ ╟── expression of type `(0, 1,)` does not match type `(0, 0,) | (1, ?a,)`
//│ ║  l.396: 	baz(0, 1)
//│ ║         	    ^^^^
//│ ╟── but it flows into argument with expected type `(r: ?b & ((0, 0,) | (1, ?a,)) & {_1: ?c & int, _2: ?d},)`
//│ ║  l.396: 	baz(0, 1)
//│ ║         	   ^^^^^^
//│ ╟── Note: constraint arises from type union:
//│ ║  l.391: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: error
//│ res: 1 | 0 | error

baz(0, 0)
baz(1, 1)
x => baz(0, x)
x => baz(1, x)
x => baz(x, 1)
//│ res: 0
//│ res: 1
//│ res: 0 -> 0
//│ res: 'a -> 'a | 1
//│ res: 1 -> 1

:e
x => baz(x, 0)
x => baz(x, x)
(x, y) => baz(x, y)
//│ ╔══[ERROR] Ambiguous constraint in application:
//│ ║  l.439: 	x => baz(x, 0)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(?a, 0,)` matches several possible instantiations
//│ ║  l.439: 	x => baz(x, 0)
//│ ║         	         ^^^^
//│ ╟── where it is used in argument with expected type `(r: ?b & ((0, 0,) | (1, ?c,)) & {_1: ?d & int, _2: ?e},)`
//│ ║  l.439: 	x => baz(x, 0)
//│ ║         	        ^^^^^^
//│ ╟── A possible instantiation is:
//│ ╟──     ?a <: 0
//│ ╟── Another possible instantiation is:
//│ ╟──     ?a <: 1
//│ ╟──     ?c :> 0
//│ ╟── Use an explicit type annotation to fix the problem.
//│ ╟── Note: constraint arises from type union:
//│ ║  l.391: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Ambiguous constraint in application:
//│ ║  l.440: 	x => baz(x, x)
//│ ║         	     ^^^^^^^^^
//│ ╟── expression of type `(?a, ?a,)` matches several possible instantiations
//│ ║  l.440: 	x => baz(x, x)
//│ ║         	         ^^^^
//│ ╟── where it is used in argument with expected type `(r: ?b & ((0, 0,) | (1, ?c,)) & {_1: ?d & int, _2: ?e},)`
//│ ║  l.440: 	x => baz(x, x)
//│ ║         	        ^^^^^^
//│ ╟── A possible instantiation is:
//│ ╟──     ?a <: 0
//│ ╟── Another possible instantiation is:
//│ ╟──     ?a <: 1
//│ ╟──     ?c :> ?a
//│ ╟── Use an explicit type annotation to fix the problem.
//│ ╟── Note: constraint arises from type union:
//│ ║  l.391: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ ╔══[ERROR] Ambiguous constraint in application:
//│ ║  l.441: 	(x, y) => baz(x, y)
//│ ║         	          ^^^^^^^^^
//│ ╟── expression of type `(?a, ?b,)` matches several possible instantiations
//│ ║  l.441: 	(x, y) => baz(x, y)
//│ ║         	              ^^^^
//│ ╟── where it is used in argument with expected type `(r: ?c & ((0, 0,) | (1, ?d,)) & {_1: ?e & int, _2: ?f},)`
//│ ║  l.441: 	(x, y) => baz(x, y)
//│ ║         	             ^^^^^^
//│ ╟── A possible instantiation is:
//│ ╟──     ?a <: 0
//│ ╟──     ?b <: 0
//│ ╟── Another possible instantiation is:
//│ ╟──     ?a <: 1
//│ ╟──     ?d :> ?b
//│ ╟── Use an explicit type annotation to fix the problem.
//│ ╟── Note: constraint arises from type union:
//│ ║  l.391: 	let baz(r: (0, 0) | (1, _)) = if r._1 < 1 then r._1 else r._2
//│ ╙──       	           ^^^^^^^^^^^^^^^
//│ res: 'a & int -> 'a | 0 | error
//│ res: 'a & int -> 'a | error
//│ res: ('a & int, 'a,) -> 'a | error

