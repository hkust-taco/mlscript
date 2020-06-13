// Tests ported from Simplesub



// --- basic --- //


42
//│ res: 42

x => 42
//│ res: ⊤ -> 42

x => x
//│ res: 'a -> 'a

x => x 42
//│ res: (42 -> 'a) -> 'a

(x => x) 42
//│ res: 42

f => x => f (f x)  // twice
//│ res: ('a ∨ 'b -> 'a) -> 'b -> 'a

let twice = f => x => f (f x)
//│ twice: ('a ∨ 'b -> 'a) -> 'b -> 'a



// --- booleans --- //


true
//│ res: bool

not true
//│ res: bool

x => not x
//│ res: bool -> bool

(x => not x) true
//│ res: bool

x => y => z => if x then y else z
//│ res: bool -> 'a -> 'a -> 'a

x => y => if x then y else x
//│ res: 'a ∧ bool -> 'a -> 'a

:e
succ true
//│ /!\ Type error: cannot constrain bool <: int
//│ l.53: 	succ true
//│       	^^^^^^^^^
//│ res: int

:e
x => succ (not x)
//│ /!\ Type error: cannot constrain bool <: int
//│ l.60: 	x => succ (not x)
//│       	     ^^^^^^^^^^^^
//│ res: bool -> int

:e
(x => not x.f) { f: 123 }
//│ /!\ Type error: cannot constrain 123 <: bool
//│ l.67: 	(x => not x.f) { f: 123 }
//│       	^^^^^^^^^^^^^^^^^^^^^^^^^
//│ res: bool

:e
(f => x => not (f x.u)) false
//│ /!\ Type error: cannot constrain bool <: 'a -> 'b
//│ l.74: 	(f => x => not (f x.u)) false
//│       	^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ res: {u: ⊤} -> bool



// --- records --- //


x => x.f
//│ res: {f: 'a} -> 'a

// note: MLsub returns "⊤" (equivalent)
{}
//│ res: {}

{ f: 42 }
//│ res: {f: 42}

{ f: 42 }.f
//│ res: 42

(x => x.f) { f: 42 }
//│ res: 42

f => { x: f 42 }.x
//│ res: (42 -> 'a) -> 'a

f => { x: f 42, y: 123 }.y
//│ res: (42 -> ⊤) -> 123

if true then { a: 1, b: true } else { b: false, c: 42 }
//│ res: {b: bool}

:e
{ a: 123, b: true }.c
//│ /!\ Type error: missing field: c in {a: 123, b: bool}
//│ l.111: 	{ a: 123, b: true }.c
//│        	                   ^^
//│ res: ⊥

:e
x => { a: x }.b
//│ /!\ Type error: missing field: b in {a: 'a}
//│ l.118: 	x => { a: x }.b
//│        	             ^^
//│ res: ⊤ -> ⊥



// --- self-app --- //


x => x x
//│ res: 'a ∧ ('a -> 'b) -> 'b

x => x x x
//│ res: 'a ∧ ('a -> 'a -> 'b) -> 'b

x => y => x y x
//│ res: 'a ∧ ('b -> 'a -> 'c) -> 'b -> 'c

x => y => x x y
//│ res: 'a ∧ ('a -> 'b -> 'c) -> 'b -> 'c

(x => x x) (x => x x)
//│ res: ⊥


x => {l: x x, r: x }
//│ res: 'a ∧ ('a -> 'b) -> {l: 'b, r: 'a}


// From https://github.com/stedolan/mlsub
// Y combinator:
(f => (x => f (x x)) (x => f (x x)))
//│ res: ('a -> 'a) -> 'a

// Z combinator:
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ res: (('a -> 'b) -> 'c ∧ ('a -> 'b)) -> 'c

// Function that takes arbitrarily many arguments:
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ res: ⊤ -> (⊤ -> 'a) as 'a


let rec trutru = g => trutru (g true)
//│ trutru: (bool -> 'a) as 'a -> ⊥

i => if ((i i) true) then true else true
//│ res: 'a ∧ ('a -> bool -> bool) -> bool
// ^ for: λi. if ((i i) true) then true else true,
//    Dolan's thesis says MLsub infers: (α → ((bool → bool) ⊓ α)) → bool
//    which does seem equivalent, despite being quite syntactically different



// --- let-poly --- //


let f = x => x; {a: f 0, b: f true}
//│ f: 'a -> 'a
//│ res: {a: 0, b: bool}

y => (let f = x => x; {a: f y, b: f true})
//│ res: 'a -> {a: 'a, b: bool}

y => (let f = x => y x; {a: f 0, b: f true})
//│ res: (bool ∨ 0 -> 'a) -> {a: 'a, b: 'a}

y => (let f = x => x y; {a: f (z => z), b: f (z => true)})
//│ res: 'a -> {a: 'a, b: bool}

y => (let f = x => x y; {a: f (z => z), b: f (z => succ z)})
//│ res: 'a ∧ int -> {a: 'a, b: int}



// --- recursion --- //


let rec f = x => f x.u
//│ f: {u: 'a} as 'a -> ⊥


// from https://www.cl.cam.ac.uk/~sd601/mlsub/
let rec recursive_monster = x => { thing: x, self: recursive_monster x }
//│ recursive_monster: 'a -> {self: 'b, thing: 'a} as 'b



// --- random --- //


(let rec x = {a: x, b: x}; x)
//│ res: {a: 'a, b: 'a} as 'a

(let rec x = v => {a: x v, b: x v}; x)
//│ res: ⊤ -> {a: 'a, b: 'a} as 'a

:e
let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ /!\ Type error: cannot constrain 0 <: 'a -> 'b
//│ l.218: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ x: 0
//│ res: 0

(x => (let y = (x x); 0))
//│ res: 'a ∧ ('a -> ⊤) -> 0

(let rec x = (y => (y (x x))); x)
//│ res: ('b -> 'b ∧ 'a) as 'a -> 'b

next => 0
//│ res: ⊤ -> 0

((x => (x x)) (x => x))
//│ res: ('b ∨ ('b -> 'a)) as 'a

(let rec x = (y => (x (y y))); x)
//│ res: ('b ∧ ('b -> 'a)) as 'a -> ⊥

x => (y => (x (y y)))
//│ res: ('a -> 'b) -> 'c ∧ ('c -> 'a) -> 'b

(let rec x = (let y = (x x); (z => z)); x)
//│ res: 'a -> ('a ∨ ('a -> 'b)) as 'b

(let rec x = (y => (let z = (x x); y)); x)
//│ res: 'a -> ('a ∨ ('a -> 'b)) as 'b

(let rec x = (y => {u: y, v: (x x)}); x)
//│ res: 'a -> {u: 'a ∨ ('a -> 'b), v: 'b} as 'b

(let rec x = (y => {u: (x x), v: y}); x)
//│ res: 'a -> {u: 'b, v: 'a ∨ ('a -> 'b)} as 'b

(let rec x = (y => (let z = (y x); y)); x)
//│ res: ('b ∧ ('a -> ⊤) -> 'b) as 'a

(x => (let y = (x x.v); 0))
//│ res: {v: 'a} ∧ ('a -> ⊤) -> 0

let rec x = (let y = (x x); (z => z)); (x (y => y.u))
//│ x: 'a -> ('a ∨ ('a -> 'b)) as 'b
//│ res: ('b ∨ ('b ∧ {u: 'c} -> 'a ∨ 'c)) as 'a

