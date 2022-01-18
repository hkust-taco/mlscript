
succ / 1
succ / succ / 1
//│ res: int
//│ res: int

let foo = f => f 1
//│ foo: (1 -> 'a) -> 'a

foo / x => x
//│ res: 1

foo / x => succ x
//│ res: int

x => succ / x + 1
//│ res: int -> int

x => succ / succ / x + 1
//│ res: int -> int

:p
foo / x => succ / succ / x
//│ Parsed: (foo (x => (succ (succ x))));
//│ Desugared: (foo (x => (succ (succ x))))
//│ res: int

:e
foo / foo / x => succ / succ / x
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.29: 	foo / foo / x => succ / succ / x
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `int` is not a function
//│ ║  l.29: 	foo / foo / x => succ / succ / x
//│ ║        	                 ^^^^^^^^^^^^^^^
//│ ╟── but it flows into application with expected type `1 -> ?a`
//│ ║  l.29: 	foo / foo / x => succ / succ / x
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.7: 	let foo = f => f 1
//│ ║       	               ^^^
//│ ╟── from reference:
//│ ║  l.7: 	let foo = f => f 1
//│ ╙──     	               ^
//│ res: error

:e
foo / foo
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.48: 	foo / foo
//│ ║        	^^^^^^^^^
//│ ╟── expression of type `1` is not a function
//│ ║  l.7: 	let foo = f => f 1
//│ ║       	                 ^
//│ ╟── Note: constraint arises from application:
//│ ║  l.7: 	let foo = f => f 1
//│ ║       	               ^^^
//│ ╟── from reference:
//│ ║  l.7: 	let foo = f => f 1
//│ ╙──     	               ^
//│ res: error
