// Tests ported from Simplesub



// --- basic --- //


42
//│ res: 42

x => 42
//│ res: anything -> 42

x => x
//│ res: 'a -> 'a

x => x 42
//│ res: (42 -> 'a) -> 'a

(x => x) 42
//│ res: 42

f => x => f (f x)  // twice
//│ res: ('a | 'b -> 'a) -> 'b -> 'a

let twice = f => x => f (f x)
//│ twice: ('a | 'b -> 'a) -> 'b -> 'a



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
//│ res: 'a & bool -> 'a -> 'a

:e
succ true
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.53: 	succ true
//│ ║        	^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.53: 	succ true
//│ ╙──      	     ^^^^
//│ res: int

:e
x => succ (not x)
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.63: 	x => succ (not x)
//│ ║        	     ^^^^^^^^^^^^
//│ ╟── expression of type `bool` does not match type `int`
//│ ║  l.63: 	x => succ (not x)
//│ ║        	           ^^^^^
//│ ╟── but it flows into argument of type `?a | bool`
//│ ║  l.63: 	x => succ (not x)
//│ ║        	          ^^^^^^^
//│ ╙── which does not match type `int`
//│ res: bool -> int

:e // TODO why no constraint hint?
(x => not x.f) { f: 123 }
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.77: 	(x => not x.f) { f: 123 }
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `123` does not match type `bool`
//│ ║  l.77: 	(x => not x.f) { f: 123 }
//│ ║        	                    ^^^
//│ ╟── but it flows into tuple expression of type `{f: 123}`
//│ ║  l.77: 	(x => not x.f) { f: 123 }
//│ ║        	               ^^^^^^^^^^
//│ ╙── which does not match type `{f: ?a & bool}`
//│ res: bool

:e // TODO why no constraint hint?
(f => x => not (f x.u)) false
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.91: 	(f => x => not (f x.u)) false
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `bool` is not a function
//│ ║  l.91: 	(f => x => not (f x.u)) false
//│ ╙──      	                        ^^^^^
//│ res: {u: anything} -> bool



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
//│ res: (42 -> anything) -> 123

if true then { a: 1, b: true } else { b: false, c: 42 }
//│ res: {b: bool}

:e
{ a: 123, b: true }.c
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.131: 	{ a: 123, b: true }.c
//│ ║         	                   ^^
//│ ╟── expression of type `{a: 123, b: bool}` does not have field 'c'
//│ ║  l.131: 	{ a: 123, b: true }.c
//│ ╙──       	^^^^^^^^^^^^^^^^^^^
//│ res: nothing

:e
x => { a: x }.b
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.141: 	x => { a: x }.b
//│ ║         	             ^^
//│ ╟── expression of type `{a: ?a}` does not have field 'b'
//│ ║  l.141: 	x => { a: x }.b
//│ ╙──       	     ^^^^^^^^
//│ res: anything -> nothing



// --- self-app --- //


x => x x
//│ res: 'a & ('a -> 'b) -> 'b

x => x x x
//│ res: 'a & ('a -> 'a -> 'b) -> 'b

x => y => x y x
//│ res: 'a & ('b -> 'a -> 'c) -> 'b -> 'c

x => y => x x y
//│ res: 'a & ('a -> 'b -> 'c) -> 'b -> 'c

(x => x x) (x => x x)
//│ res: nothing


x => {l: x x, r: x }
//│ res: 'a & ('a -> 'b) -> {l: 'b, r: 'a}


// From https://github.com/stedolan/mlsub
// Y combinator:
(f => (x => f (x x)) (x => f (x x)))
//│ res: ('a -> 'a) -> 'a

// Z combinator:
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ res: (('a -> 'b) -> 'c & ('a -> 'b)) -> 'c

// Function that takes arbitrarily many arguments:
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ res: (anything -> 'a) as 'a


let rec trutru = g => trutru (g true)
//│ trutru: (bool -> 'a) as 'a -> nothing

i => if ((i i) true) then true else true
//│ res: 'a & ('a -> bool -> bool) -> bool
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
//│ res: (bool | 0 -> 'a) -> {a: 'a, b: 'a}

y => (let f = x => x y; {a: f (z => z), b: f (z => true)})
//│ res: 'a -> {a: 'a, b: bool}

y => (let f = x => x y; {a: f (z => z), b: f (z => succ z)})
//│ res: 'a & int -> {a: 'a, b: int}



// --- recursion --- //


let rec f = x => f x.u
//│ f: {u: 'a} as 'a -> nothing


// from https://www.cl.cam.ac.uk/~sd601/mlsub/
let rec recursive_monster = x => { thing: x, self: recursive_monster x }
//│ recursive_monster: 'a -> {self: 'b, thing: 'a} as 'b



// --- random --- //


(let rec x = {a: x, b: x}; x)
//│ res: {a: 'a, b: 'a} as 'a

(let rec x = v => {a: x v, b: x v}; x)
//│ res: anything -> {a: 'a, b: 'a} as 'a

:s
:e // FIXME missing (x y) in error msg
let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ╔══[ERROR] Type mismatch in binding of block of statements:
//│ ║  l.245: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ║         	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `0` is not a function
//│ ║  l.245: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ╙──       	                                           ^
//│ x: 0
//│ res: 0

(x => (let y = (x x); 0))
//│ res: 'a & ('a -> anything) -> 0

(let rec x = (y => (y (x x))); x)
//│ res: ('a -> ('a & ('a -> 'b)) as 'b) -> 'a

next => 0
//│ res: anything -> 0

((x => (x x)) (x => x))
//│ res: ('b | ('b -> 'a)) as 'a

(let rec x = (y => (x (y y))); x)
//│ res: ('b & ('b -> 'a)) as 'a -> nothing

x => (y => (x (y y)))
//│ res: ('a -> 'b) -> 'c & ('c -> 'a) -> 'b

(let rec x = (let y = (x x); (z => z)); x)
//│ res: ('b -> 'b | 'a) as 'a

(let rec x = (y => (let z = (x x); y)); x)
//│ res: ('b -> 'b | 'a) as 'a

(let rec x = (y => {u: y, v: (x x)}); x)
//│ res: ('b -> {u: 'b | 'a, v: 'c} as 'c) as 'a

(let rec x = (y => {u: (x x), v: y}); x)
//│ res: ('b -> {u: 'c, v: 'b | 'a} as 'c) as 'a

(let rec x = (y => (let z = (y x); y)); x)
//│ res: ('b & ('a -> anything) -> 'b) as 'a

(x => (let y = (x x.v); 0))
//│ res: {v: 'a} & ('a -> anything) -> 0

let rec x = (let y = (x x); (z => z)); (x (y => y.u))
//│ x: ('b -> 'b | 'a) as 'a
//│ res: ('b | ('b & {u: 'c} -> 'c | 'a)) as 'a

