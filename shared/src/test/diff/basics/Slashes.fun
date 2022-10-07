
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
//│ Parsed: foo (x => succ (succ x));
//│ Desugared: foo (x => succ (succ x))
//│ AST: App(Var(foo), Lam(Var(x), App(Var(succ), App(Var(succ), Var(x)))))
//│ res: int

:e
foo / foo / x => succ / succ / x
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.30: 	foo / foo / x => succ / succ / x
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── application of type `int` is not a function
//│ ║  l.30: 	foo / foo / x => succ / succ / x
//│ ║        	                 ^^^^^^^^^^^^^^^
//│ ╟── but it flows into application with expected type `1 -> ?a`
//│ ║  l.30: 	foo / foo / x => succ / succ / x
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
//│ ║  l.49: 	foo / foo
//│ ║        	^^^^^^^^^
//│ ╟── integer literal of type `1` is not a function
//│ ║  l.7: 	let foo = f => f 1
//│ ║       	                 ^
//│ ╟── Note: constraint arises from application:
//│ ║  l.7: 	let foo = f => f 1
//│ ║       	               ^^^
//│ ╟── from reference:
//│ ║  l.7: 	let foo = f => f 1
//│ ╙──     	               ^
//│ res: error
