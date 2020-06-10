
let a = succ
let x = true
/// a: int -> int
/// x: bool

:e
let oops = succ false
/// /!\ Type error at line 8: cannot constrain bool <: int
/// oops: int

let b = a 1
/// b: int

x =>
  add (a x)
/// res: int -> int -> int

let x =
  x =>
    add (a x)
/// x: int -> int -> int

let id = v => v
/// id: 'a -> 'a

f => f f
/// res: 'a ∧ ('a -> 'b) -> 'b

f => id f id f id
/// res: 'a ∧ (('b -> 'b) -> 'a -> ('c -> 'c) -> 'd) -> 'd

:e
let oops = hu(h
/// /!\ Parse error: Expected end-of-input:1:14, found "(h" at line 34: let oops = hu(h
