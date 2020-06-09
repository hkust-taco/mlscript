
let a = succ
let x = true
/// a: int -> int
/// x: bool

let b = a 1
/// b: int

let x =
  fun x ->
    add (a x) 1
/// x: int -> int

let res = fun f -> f f
/// res: 'a ∧ ('a -> 'b) -> 'b
