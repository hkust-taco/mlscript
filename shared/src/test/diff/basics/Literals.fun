
1
//│ res: 1

"hello"
//│ res: "hello"

// TODO literal booleans
true
//│ res: true

:e
1 as Int
"hello" as String
true as Bool
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.13: 	1 as Int
//│ ║        	^^^^^^^^
//│ ╟── integer literal of type `1` is not a function
//│ ║  l.13: 	1 as Int
//│ ║        	^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.13: 	1 as Int
//│ ╙──      	     ^^^
//│ res: () -> Int
//│ res: string
//│ res: bool

:w
1 as int
"hello" as string
//│ ╔══[WARNING] Variable name 'int' already names a symbol in scope. If you want to refer to that symbol, you can use `scope.int`; if not, give your future readers a break and use another name :^)
//│ ║  l.30: 	1 as int
//│ ╙──      	     ^^^
//│ res: 1
//│ ╔══[WARNING] Variable name 'string' already names a symbol in scope. If you want to refer to that symbol, you can use `scope.string`; if not, give your future readers a break and use another name :^)
//│ ║  l.31: 	"hello" as string
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
//│ ║  l.47: 	1 as true
//│ ║        	^^^^^^^^^
//│ ╟── integer literal of type `1` is not an instance of type `true`
//│ ║  l.47: 	1 as true
//│ ║        	^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.47: 	1 as true
//│ ╙──      	     ^^^^
//│ res: true
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.48: 	true as Int
//│ ║        	^^^^^^^^^^^
//│ ╟── reference of type `true` is not a function
//│ ║  l.48: 	true as Int
//│ ║        	^^^^
//│ ╟── Note: constraint arises from reference:
//│ ║  l.48: 	true as Int
//│ ╙──      	        ^^^
//│ res: () -> Int
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.49: 	false as 1
//│ ║        	^^^^^^^^^^
//│ ╟── reference of type `false` does not match type `1`
//│ ║  l.49: 	false as 1
//│ ║        	^^^^^
//│ ╟── Note: constraint arises from integer literal:
//│ ║  l.49: 	false as 1
//│ ╙──      	         ^
//│ res: 1

let f = b => if b then 0 else 1
//│ f: bool -> (0 | 1)

let pred = n => 0 < n
//│ pred: number -> bool

let g = x => if pred x then x else f false
//│ g: (number & 'a) -> (0 | 1 | 'a)

g 3
//│ res: 0 | 1 | 3

g / succ 3
//│ res: int

x => if x then x else f false
//│ res: (bool & 'a) -> (0 | 1 | 'a)

res false
//│ res: 0 | 1 | false

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
//│ ║  l.114: 	f false
//│ ║         	^^^^^^^
//│ ╟── reference of type `false` is not an instance of type `int`
//│ ║  l.114: 	f false
//│ ║         	  ^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.103: 	  if pred n then n else f (n + 1)
//│ ╙──       	                           ^
//│ res: error | false | int

let take0 (x: 0) = 0
let take1 (x: 1) = 1
//│ take0: (x: 0,) -> 0
//│ take1: (x: 1,) -> 1

let takeWhat y = if y < 0 then take0 y else take1 y
//│ takeWhat: nothing -> (0 | 1)

let takeWhat y = if y < 0 then take0 (x: y) else take1 (x: y)
//│ takeWhat: nothing -> (0 | 1)

