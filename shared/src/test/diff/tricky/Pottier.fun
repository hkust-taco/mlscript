

// Inspired by [Pottier 98, chap 13.4]

let rec f = x => y => add (f x.tail y) (f x y)
let rec f = x => y => add (f x.tail y) (f y x)
let rec f = x => y => add (f x.tail y) (f x y.tail)
let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
let rec f = x => y => add (f x.tail x) (f y.tail y)
let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ f: 'tail -> anything -> int
//│   where
//│     'tail <: {tail: 'tail}
//│ f: 'tail -> 'tail -> int
//│   where
//│     'tail <: {tail: 'tail}
//│ f: 'tail -> 'tail -> int
//│   where
//│     'tail <: {tail: 'tail}
//│ f: 'tail -> 'tail -> int
//│   where
//│     'tail <: {tail: 'tail}
//│ f: {tail: 'tail} -> {tail: 'tail} -> int
//│   where
//│     'tail <: {tail: 'tail}
//│ f: 'tail -> 'a -> int
//│   where
//│     'tail <: {tail: 'tail} & 'a
//│     'a <: {tail: 'tail}
//│ f: 'tail -> 'a -> int
//│   where
//│     'tail <: {tail: 'tail} & 'a
//│     'a <: {tail: 'tail}

let f = x => y => if true then { l: x; r: y } else { l: y; r: x } // 2-crown
//│ f: 'a -> (forall 'b. 'b -> {l: 'a | 'b, r: 'a | 'b})


// Inspired by [Pottier 98, chap 13.5]

let rec f = x => y => if true then x else { t: f x.t y.t }
//│ f: ('t & 'a) -> 't -> ('b | 'a)
//│   where
//│     'b :> {t: 'b}
//│     't <: {t: 't}



