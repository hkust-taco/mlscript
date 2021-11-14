
1
//│ res: 1

"hello"
//│ res: "hello"

// TODO literal booleans
true
//│ res: bool

1 as Int
"hello" as String
true as Bool
//│ res: int
//│ res: string
//│ res: bool

:w
1 as int
"hello" as string
//│ ╔══[WARNING] Variable name 'int' already names a symbol in scope. If you want to refer to that symbol, you can use `scope.int`; if not, give your future readers a break and use another name :^)
//│ ║  l.20: 	1 as int
//│ ╙──      	     ^^^
//│ res: 1
//│ ╔══[WARNING] Variable name 'string' already names a symbol in scope. If you want to refer to that symbol, you can use `scope.string`; if not, give your future readers a break and use another name :^)
//│ ║  l.21: 	"hello" as string
//│ ╙──      	           ^^^^^^
//│ res: "hello"

1 as (_: int)
"hello" as (_: string)
//│ res: (_: 1,)
//│ res: (_: "hello",)

:e
1 as true
true as Int
false as 1
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.37: 	1 as true
//│ ║        	^^^^^^^^^
//│ ╟── expression of type `1` does not match type `bool`
//│ ║  l.37: 	1 as true
//│ ║        	^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.37: 	1 as true
//│ ╙──      	     ^^^^
//│ res: bool
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.38: 	true as Int
//│ ║        	^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.38: 	true as Int
//│ ║        	^^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.38: 	true as Int
//│ ╙──      	        ^^^
//│ res: int
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.39: 	false as 1
//│ ║        	^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `1`
//│ ║  l.39: 	false as 1
//│ ║        	^^^^^
//│ ╟── Note: constraint arises from integer literal:
//│ ║  l.39: 	false as 1
//│ ╙──      	         ^
//│ res: 1

let f = b => if b then 0 else 1
//│ f: bool -> 0 | 1

let pred = n => 0 < n
//│ pred: int -> bool

let g = x => if pred x then x else f false
//│ g: int & 'a -> 'a | 1 | 0

g 3
//│ res: 1 | 0 | 3

g / succ 3
//│ res: int

x => if x then x else f false
//│ res: bool & 'a -> 'a | 1 | 0

res false
//│ res: 1 | 0 | bool

let rec f = n =>
  if pred n then n else f (n + 1)
//│ f: int -> int

let g = n =>
  if pred n then 0 else if not (pred n) then 1 else f n
//│ g: int -> int

x => if pred x then x else f x
//│ res: int -> int

:e
f false
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.104: 	f false
//│ ║         	^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.104: 	f false
//│ ║         	  ^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.93: 	  if pred n then n else f (n + 1)
//│ ╙──      	                           ^
//│ res: bool | int | error

let take0 (x: 0) = 0
let take1 (x: 1) = 1
//│ take0: (x: 0,) -> 0
//│ take1: (x: 1,) -> 1

// FIXME later: handling of tuples
let takeWhat y = if y < 0 then take0 y else take1 y
//│ /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
//│ 	at: scala.Predef$.$qmark$qmark$qmark(Predef.scala:344)
//│ 	at: mlscript.NormalForms$LhsNf.$amp(NormalForms.scala:31)
//│ 	at: mlscript.NormalForms$LhsNf.$amp(NormalForms.scala:46)
//│ 	at: mlscript.NormalForms$Conjunct.$amp(NormalForms.scala:136)
//│ 	at: mlscript.NormalForms$DNF.$anonfun$$amp$12(NormalForms.scala:201)
//│ 	at: scala.collection.immutable.List.flatMap(List.scala:293)
//│ 	at: mlscript.NormalForms$DNF.$amp(NormalForms.scala:201)
//│ 	at: mlscript.NormalForms$DNF.$anonfun$$amp$10(NormalForms.scala:198)
//│ 	at: scala.collection.immutable.List.map(List.scala:246)
//│ 	at: mlscript.NormalForms$DNF.$amp(NormalForms.scala:198)

let takeWhat y = if y < 0 then take0 (x: y) else take1 (x: y)
//│ takeWhat: nothing -> 0 | 1

