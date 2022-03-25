
let a = succ
let x = true
//│ a: int -> int
//│ x: true

x => add (a x)
//│ res: int -> int -> int

x =>
  add (a x)
//│ res: int -> int -> int

let x =
  x =>
    add (a x)
//│ x: int -> int -> int

let id = v => v
//│ id: 'a -> 'a

f => f f
//│ /!!!\ Uncaught error: java.lang.AssertionError: assertion failed
//│ 	at: scala.Predef$.assert(Predef.scala:264)
//│ 	at: mlscript.TypeSimplifier.$anonfun$simplifyType$24(TypeSimplifier.scala:370)
//│ 	at: mlscript.TypeSimplifier.$anonfun$simplifyType$24$adapted(TypeSimplifier.scala:343)
//│ 	at: scala.collection.IterableOnceOps.foreach(IterableOnce.scala:563)
//│ 	at: scala.collection.IterableOnceOps.foreach$(IterableOnce.scala:561)
//│ 	at: scala.collection.AbstractIterator.foreach(Iterator.scala:1288)
//│ 	at: mlscript.TypeSimplifier.$anonfun$simplifyType$22(TypeSimplifier.scala:343)
//│ 	at: mlscript.TypeSimplifier.$anonfun$simplifyType$22$adapted(TypeSimplifier.scala:342)
//│ 	at: scala.collection.immutable.List.foreach(List.scala:333)
//│ 	at: mlscript.TypeSimplifier.$anonfun$simplifyType$20(TypeSimplifier.scala:342)

f => id f id f id
//│ res: (('a -> 'a) -> 'b -> ('c -> 'c) -> 'd & 'b) -> 'd

:pe
let oops = hu(h
//│ /!\ Parse error: Expected end-of-input:1:14, found "(h\n" at l.39:14: let oops = hu(h

x => x; y => y
//│ res: 'a -> 'a
//│ res: 'a -> 'a

:pe
x => let y = x; y
//│ /!\ Parse error: Expected expression:1:1, found "x => let y" at l.47:1: x => let y = x; y

x => (let y = x; y)
x =>
  let y = x; y
x =>
  let y = x
  y
//│ res: 'a -> 'a
//│ res: 'a -> 'a
//│ res: 'a -> 'a

let f x = x + 1
let f x y = x + y
let f x y z = if x then y else z
let f x y z = { log x; if y < z then y else z }
//│ f: int -> int
//│ f: int -> int -> int
//│ f: bool -> 'a -> 'a -> 'a
//│ f: anything -> (int & 'a) -> (int & 'a) -> 'a

// TODO
// let f (x: int) = x + 1

// TODO
:pe
let f / x: int = x + 1
let f / x: int, y: int = x + y
//│ /!\ Parse error: Expected (data type definition | data definition | let binding | expression):1:1, found "let f / x:" at l.74:1: let f / x: int = x + 1

// TODO
// let f (
//   x
//   y
// ) = x + 1

let f(x: int) = x + 1
//│ f: (x: int,) -> int

f 42
//│ res: int

f (x: 42)
//│ res: int

:e
f (y: 42)
//│ ╔══[ERROR] Wrong tuple field name: found 'y' instead of 'x'
//│ ║  l.94: 	f (y: 42)
//│ ╙──      	   ^^^^^
//│ res: error | int

:e
f (x: 42, y: 43)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.101: 	f (x: 42, y: 43)
//│ ║         	^^^^^^^^^^^^^^^^
//│ ╟── tuple of type `(x: 42, y: 43,)` does not match type `int`
//│ ║  l.101: 	f (x: 42, y: 43)
//│ ║         	   ^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `int`
//│ ║  l.101: 	f (x: 42, y: 43)
//│ ║         	  ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.84: 	let f(x: int) = x + 1
//│ ║        	                ^
//│ ╟── from binding:
//│ ║  l.84: 	let f(x: int) = x + 1
//│ ╙──      	      ^^^^^^
//│ res: error | int

(a, b) => a + b
//│ res: (int, int,) -> int
res(1,2)
//│ res: int

