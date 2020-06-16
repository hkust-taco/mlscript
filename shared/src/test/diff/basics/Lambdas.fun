
let a = succ
let x = true
//│ a: int -> int
//│ x: bool

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
//│ res: 'a & ('a -> 'b) -> 'b

f => id f id f id
//│ res: 'a & (('b -> 'b) -> 'a -> ('c -> 'c) -> 'd) -> 'd

:pe
let oops = hu(h
//│ /!\ Parse error: Expected end-of-input:1:14, found "(h" at l.29:14: let oops = hu(h

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
//│ f: anything -> 'a & int -> 'a & int -> 'a

// TODO
// let f (x: int) = x + 1

// TODO
:pe
let f / x: int = x + 1
let f / x: int, y: int = x + y
//│ /!\ Parse error: Expected (let binding | expression):1:1, found "let f / x:" at l.64:1: let f / x: int = x + 1

// TODO
// let f (
//   x
//   y
// ) = x + 1
