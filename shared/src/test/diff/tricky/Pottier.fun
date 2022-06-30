

// Inspired by [Pottier 98, chap 13.4]

let rec f = x => y => add (f x.tail y) (f x y)
//│ f: 'a -> anything -> int
//│   where
//│     'a <: {tail: 'a}

// FIXME? now fails with constrained-arg-gen
let rec f = x => y => add (f x.tail y) (f y x)
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}

let rec f = x => y => add (f x.tail y) (f x y.tail)
let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
let rec f = x => y => add (f x.tail x) (f y.tail y)
let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}

let f = x => y => if true then { l: x; r: y } else { l: y; r: x } // 2-crown
//│ f: 'a -> 'a -> {l: 'a, r: 'a}


// Inspired by [Pottier 98, chap 13.5]

let rec f = x => y => if true then x else { t: f x.t y.t }
//│ f: 'a -> 'b -> 'a
//│   where
//│     'b <: {t: 'b}
//│     'a := {t: 'a}


