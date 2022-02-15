

// Inspired by [Pottier 98, chap 13.4]

let rec f = x => y => add (f x.tail y) (f x y)
let rec f = x => y => add (f x.tail y) (f y x)
let rec f = x => y => add (f x.tail y) (f x y.tail)
let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
let rec f = x => y => add (f x.tail x) (f y.tail y)
let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ f: {tail: {tail: 'a} as 'a} -> anything -> int
//│ f: {tail: {tail: 'a} as 'a} -> {tail: {tail: 'a} as 'a} -> int
//│ f: {tail: {tail: 'a} as 'a} -> {tail: {tail: 'b} as 'b} -> int
//│ f: {tail: {tail: 'a} as 'a} -> {tail: {tail: 'b} as 'b} -> int
//│ f: {tail: {tail: {tail: 'a} as 'a}} -> {tail: {tail: {tail: 'a} as 'a}} -> int
//│ f: {tail: {tail: 'a} as 'a} -> {tail: {tail: {tail: 'a} as 'a}} -> int
//│ f: {tail: {tail: 'a} as 'a} -> {tail: {tail: {tail: 'a} as 'a}} -> int

let f = x => y => if true then { l: x; r: y } else { l: y; r: x } // 2-crown
//│ f: 'a -> (forall 'b. 'b -> {l: 'a | 'b, r: 'a | 'b})


// Inspired by [Pottier 98, chap 13.5]

let rec f = x => y => if true then x else { t: f x.t y.t }
//│ f: ({t: {t: 'a} as 'a} & 'b & 'c) -> {t: {t: 'd} as 'd} -> ({t: {t: 'e} | 'c as 'e} | 'b)


