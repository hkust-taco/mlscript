
let a = succ
let x = true
/// a: int -> int
/// x: bool

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
/// /!\ Parse error: Expected end-of-input:1:14, found "(h" at line 26: let oops = hu(h
