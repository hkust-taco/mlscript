
1
//│ res: 1

"hello"
//│ res: "hello"

// TODO literal booleans
true
//│ res: bool


let f = b => if b then 0 else 1
//│ f: bool -> 0 | 1

let pred = n => 0 < n
//│ pred: int -> bool

let rec f = n =>
  if pred n then n else f (n + 1)
//│ f: int -> int

let g = n =>
  if pred n then 0 else if not (pred n) then 1 else f n
//│ g: int -> int

