
> let a = succ
a: int -> int

> let b = a 1
b: int

> let x = fun x -> add (a x)
x: int -> int -> int

> let res = fun f -> f f
res: 'a ∧ ('a -> 'b) -> 'b

