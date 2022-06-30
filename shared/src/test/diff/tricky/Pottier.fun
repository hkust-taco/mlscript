

// Inspired by [Pottier 98, chap 13.4]

let rec f = x => y => add (f x.tail y) (f x y)
//│ f: anything -> anything -> int

// FIXME? now fails with constrained-arg-gen
let rec f = x => y => add (f x.tail y) (f y x)
//│ /!!!\ Uncaught error: java.lang.StackOverflowError

let rec f = x => y => add (f x.tail y) (f x y.tail)
let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
let rec f = x => y => add (f x.tail x) (f y.tail y)
let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ f: anything -> anything -> int
//│ f: anything -> anything -> int
//│ f: anything -> anything -> int
//│ f: anything -> anything -> int
//│ f: anything -> anything -> int

let f = x => y => if true then { l: x; r: y } else { l: y; r: x } // 2-crown
//│ f: 'a -> 'a -> {l: 'a, r: 'a}


// Inspired by [Pottier 98, chap 13.5]

let rec f = x => y => if true then x else { t: f x.t y.t }
//│ f: 'a -> anything -> 'a
//│   where
//│     'a :> forall 'a. ('t | {t: 'a}
//│   where
//│     'a <: {t: 't})


