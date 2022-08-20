
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
//│ res: ('a -> 'b & 'a) -> 'b

f => id f id f id
//│ res: (('a -> 'a) -> 'b -> ('c -> 'c) -> 'd & 'b) -> 'd

:pe
let oops = hu(h
//│ /!\ Parse error: Expected end-of-input:1:14, found "(h\n" at l.29:14: let oops = hu(h

x => x; y => y
//│ res: 'a -> 'a
//│ res: 'a -> 'a

:pe
x => let y = x; y
//│ /!\ Parse error: Expected expression:1:1, found "x => let y" at l.37:1: x => let y = x; y

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
//│ f: anything -> (number & 'a) -> (number & 'a) -> 'a

// TODO
// let f (x: int) = x + 1

// TODO
:pe
let f / x: int = x + 1
let f / x: int, y: int = x + y
//│ /!\ Parse error: Expected (data type definition | data definition | let binding | expression):1:1, found "let f / x:" at l.64:1: let f / x: int = x + 1

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
//│ ║  l.84: 	f (y: 42)
//│ ╙──      	   ^^^^^
//│ res: error | int

:e
f (x: 42, y: 43)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.91: 	f (x: 42, y: 43)
//│ ║        	^^^^^^^^^^^^^^^^
//│ ╟── tuple of type `(x: 42, y: 43,)` is not an instance of type `int`
//│ ║  l.91: 	f (x: 42, y: 43)
//│ ║        	   ^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `int`
//│ ║  l.91: 	f (x: 42, y: 43)
//│ ║        	  ^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.74: 	let f(x: int) = x + 1
//│ ║        	                ^
//│ ╟── from binding:
//│ ║  l.74: 	let f(x: int) = x + 1
//│ ╙──      	      ^^^^^^
//│ res: error | int

(a, b) => a + b
//│ res: (int, int,) -> int
res(1,2)
//│ res: int

