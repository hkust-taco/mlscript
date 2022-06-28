// Tests ported from Simplesub

:ShowRelativeLineNums



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
//│ res: ('a -> 'b & 'c -> 'a) -> 'c -> 'b

let twice = f => x => f (f x)
//│ twice: ('a -> 'b & 'c -> 'a) -> 'c -> 'b



// --- booleans --- //


true
//│ res: true

not true
//│ res: bool

x => not x
//│ res: bool -> bool

(x => not x) true
//│ res: bool

x => y => z => if x then y else z
//│ res: bool -> 'a -> 'a -> 'a

x => y => if x then y else x
//│ res: (bool & 'a) -> 'a -> 'a

:e
succ true
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.+1: 	succ true
//│ ║        	^^^^^^^^^
//│ ╟── reference of type `true` is not an instance of type `int`
//│ ║  l.+1: 	succ true
//│ ╙──      	     ^^^^
//│ res: error | int

:e
x => succ (not x)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.+1: 	x => succ (not x)
//│ ║        	     ^^^^^^^^^^^^
//│ ╟── application of type `bool` is not an instance of type `int`
//│ ║  l.+1: 	x => succ (not x)
//│ ║        	           ^^^^^
//│ ╟── but it flows into argument with expected type `int`
//│ ║  l.+1: 	x => succ (not x)
//│ ╙──      	          ^^^^^^^
//│ res: bool -> (error | int)

:e
(x => not x.f) { f: 123 }
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.+1: 	(x => not x.f) { f: 123 }
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── integer literal of type `123` is not an instance of type `bool`
//│ ║  l.+1: 	(x => not x.f) { f: 123 }
//│ ║        	                    ^^^
//│ ╟── Note: constraint arises from argument:
//│ ║  l.+1: 	(x => not x.f) { f: 123 }
//│ ║        	          ^^^
//│ ╟── from field selection:
//│ ║  l.+1: 	(x => not x.f) { f: 123 }
//│ ╙──      	           ^^
//│ res: bool | error

:e
(f => x => not (f x.u)) false
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.+1: 	(f => x => not (f x.u)) false
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── reference of type `false` is not a function
//│ ║  l.+1: 	(f => x => not (f x.u)) false
//│ ║        	                        ^^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.+1: 	(f => x => not (f x.u)) false
//│ ║        	                ^^^^^
//│ ╟── from reference:
//│ ║  l.+1: 	(f => x => not (f x.u)) false
//│ ╙──      	                ^
//│ res: {u: anything} -> bool | error



// --- records --- //


x => x.f
//│ res: {f: 'f} -> 'f

// note: MLsub returns "⊤" (equivalent)
{}
//│ res: anything

{ f: 42 }
//│ res: {f: 42}

{ f: 42 }.f
//│ res: 42

(x => x.f) { f: 42 }
//│ res: 42

f => { x: f 42 }.x
//│ res: (42 -> 'x) -> 'x

f => { x: f 42, y: 123 }.y
//│ res: (42 -> anything) -> 123

if true then { a: 1, b: true } else { b: false, c: 42 }
//│ res: {b: bool}

:e
{ a: 123, b: true }.c
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.+1: 	{ a: 123, b: true }.c
//│ ║        	                   ^^
//│ ╟── record of type `{a: 123, b: true}` does not have field 'c'
//│ ║  l.+1: 	{ a: 123, b: true }.c
//│ ╙──      	^^^^^^^^^^^^^^^^^^^
//│ res: error

:e
x => { a: x }.b
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.+1: 	x => { a: x }.b
//│ ║        	             ^^
//│ ╟── record of type `{a: ?a}` does not have field 'b'
//│ ║  l.+1: 	x => { a: x }.b
//│ ╙──      	     ^^^^^^^^
//│ res: anything -> error



// --- self-app --- //


x => x x
//│ res: ('a -> 'b & 'a) -> 'b

res id
//│ res: 'a -> 'a


let f = (x => x + 1); {a: f; b: f 2}
//│ f: int -> int
//│ res: {a: int -> int, b: int}

x => x x x
//│ res: ('a -> 'a -> 'b & 'a) -> 'b

x => y => x y x
//│ res: ('a -> 'b -> 'c & 'b) -> 'a -> 'c

x => y => x x y
//│ res: ('a -> 'b -> 'c & 'a) -> 'b -> 'c

:e // Omega: causes divergence in first-class-polymorphic type inference, as expected
(x => x x) (x => x x)
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d. ?d -> ?c) -> ?e` exceeded recursion depth limit (200)
//│ ║  l.+1: 	(x => x x) (x => x x)
//│ ║        	^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α239 -> α240)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α239
//│ ╟── while constraining:  α237  <!<  α239
//│ ╟── while constraining:  (α239 -> α240)  <!<  (α237 -> α238)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α237 -> α238)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α237
//│ ╟── while constraining:  α235  <!<  α237
//│ ╟── while constraining:  (α237 -> α238)  <!<  (α235 -> α236)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α235 -> α236)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α235
//│ ╟── while constraining:  α233  <!<  α235
//│ ╟── while constraining:  (α235 -> α236)  <!<  (α233 -> α234)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α233 -> α234)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α233
//│ ╟── while constraining:  α231  <!<  α233
//│ ╟── while constraining:  (α233 -> α234)  <!<  (α231 -> α232)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α231 -> α232)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α231
//│ ╟── while constraining:  α229  <!<  α231
//│ ╟── while constraining:  (α231 -> α232)  <!<  (α229 -> α230)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α229 -> α230)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α229
//│ ╟── while constraining:  α227  <!<  α229
//│ ╟── while constraining:  (α229 -> α230)  <!<  (α227 -> α228)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α227 -> α228)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α227
//│ ╟── while constraining:  α222  <!<  α227
//│ ╟── while constraining:  (α227 -> α228)  <!<  (α222 -> α223)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α222 -> α223)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α222
//│ ╙── while constraining:  (α222 -> α223)  <!<  (‹∀ 0. (α224' -> α225')› -> α226)
//│ res: error


x => {l: x x, r: x }
//│ res: ('a -> 'b & 'a) -> {l: 'b, r: 'a}


// From https://github.com/stedolan/mlsub
// Y combinator:
:e // similarly to Omega
(f => (x => f (x x)) (x => f (x x)))
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d, ?e. ?c -> ?e) -> ?f` exceeded recursion depth limit (200)
//│ ║  l.+1: 	(f => (x => f (x x)) (x => f (x x)))
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  (α288 -> α289)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  α288
//│ ╟── while constraining:  α285  <!<  α288
//│ ╟── while constraining:  (α288 -> α290)  <!<  (α285 -> α286)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  (α285 -> α286)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  α285
//│ ╟── while constraining:  α282  <!<  α285
//│ ╟── while constraining:  (α285 -> α287)  <!<  (α282 -> α283)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  (α282 -> α283)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  α282
//│ ╟── while constraining:  α279  <!<  α282
//│ ╟── while constraining:  (α282 -> α284)  <!<  (α279 -> α280)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  (α279 -> α280)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  α279
//│ ╟── while constraining:  α276  <!<  α279
//│ ╟── while constraining:  (α279 -> α281)  <!<  (α276 -> α277)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  (α276 -> α277)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  α276
//│ ╟── while constraining:  α273  <!<  α276
//│ ╟── while constraining:  (α276 -> α278)  <!<  (α273 -> α274)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  (α273 -> α274)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  α273
//│ ╟── while constraining:  α270  <!<  α273
//│ ╟── while constraining:  (α273 -> α275)  <!<  (α270 -> α271)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  (α270 -> α271)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  α270
//│ ╟── while constraining:  α261  <!<  α270
//│ ╟── while constraining:  (α270 -> α272)  <!<  (α261 -> α262)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  (α261 -> α262)
//│ ╟── while constraining:  ‹∀ 0. (α264' -> α266')›  <!<  α261
//│ ╙── while constraining:  (α261 -> α263)  <!<  (‹∀ 0. (α264' -> α266')› -> α269)
//│ res: (nothing -> anything) -> error

// Z combinator:
:e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d, ?e, ?f, ?g. ?c -> ?g) -> ?h` exceeded recursion depth limit (200)
//│ ║  l.+1: 	(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  α371
//│ ╟── while constraining:  α366  <!<  α371
//│ ╟── while constraining:  (α371 -> α375)  <!<  (α366 -> α367)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  (α366 -> α367)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  α366
//│ ╟── while constraining:  α361  <!<  α366
//│ ╟── while constraining:  (α366 -> α370)  <!<  (α361 -> α362)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  (α361 -> α362)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  α361
//│ ╟── while constraining:  α356  <!<  α361
//│ ╟── while constraining:  (α361 -> α365)  <!<  (α356 -> α357)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  (α356 -> α357)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  α356
//│ ╟── while constraining:  α351  <!<  α356
//│ ╟── while constraining:  (α356 -> α360)  <!<  (α351 -> α352)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  (α351 -> α352)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  α351
//│ ╟── while constraining:  α346  <!<  α351
//│ ╟── while constraining:  (α351 -> α355)  <!<  (α346 -> α347)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  (α346 -> α347)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  α346
//│ ╟── while constraining:  α341  <!<  α346
//│ ╟── while constraining:  (α346 -> α350)  <!<  (α341 -> α342)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  (α341 -> α342)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  α341
//│ ╟── while constraining:  α319  <!<  α341
//│ ╟── while constraining:  (α341 -> α345)  <!<  (α319 -> α322)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  (α319 -> α322)
//│ ╟── while constraining:  ‹∀ 0. (α327' -> α334')›  <!<  α319
//│ ╙── while constraining:  (α319 -> α326)  <!<  (‹∀ 0. (α327' -> α334')› -> α340)
//│ res: ((anything -> nothing) -> anything) -> error

// Function that takes arbitrarily many arguments:
:e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d, ?e, ?f, ?g. ?c -> ?g) -> ?h` exceeded recursion depth limit (200)
//│ ║  l.+1: 	(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  α481
//│ ╟── while constraining:  α476  <!<  α481
//│ ╟── while constraining:  (α481 -> α485)  <!<  (α476 -> α477)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  (α476 -> α477)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  α476
//│ ╟── while constraining:  α471  <!<  α476
//│ ╟── while constraining:  (α476 -> α480)  <!<  (α471 -> α472)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  (α471 -> α472)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  α471
//│ ╟── while constraining:  α466  <!<  α471
//│ ╟── while constraining:  (α471 -> α475)  <!<  (α466 -> α467)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  (α466 -> α467)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  α466
//│ ╟── while constraining:  α461  <!<  α466
//│ ╟── while constraining:  (α466 -> α470)  <!<  (α461 -> α462)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  (α461 -> α462)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  α461
//│ ╟── while constraining:  α456  <!<  α461
//│ ╟── while constraining:  (α461 -> α465)  <!<  (α456 -> α457)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  (α456 -> α457)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  α456
//│ ╟── while constraining:  α451  <!<  α456
//│ ╟── while constraining:  (α456 -> α460)  <!<  (α451 -> α452)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  (α451 -> α452)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  α451
//│ ╟── while constraining:  α429  <!<  α451
//│ ╟── while constraining:  (α451 -> α455)  <!<  (α429 -> α432)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  (α429 -> α432)
//│ ╟── while constraining:  ‹∀ 0. (α437' -> α444')›  <!<  α429
//│ ╙── while constraining:  (α429 -> α436)  <!<  (‹∀ 0. (α437' -> α444')› -> α450)
//│ res: error


let rec trutru = g => trutru (g true)
//│ trutru: 'a -> nothing
//│   where
//│     'a <: true -> 'a

i => if ((i i) true) then true else true
//│ res: ('a -> true -> bool & 'a) -> true
// ^ for: λi. if ((i i) true) then true else true,
//    Dolan's thesis says MLsub infers: (α → ((bool → bool) ⊓ α)) → bool
//    which does seem equivalent, despite being quite syntactically different



// --- let-poly --- //


let f = x => x; {a: f 0, b: f true}
//│ f: 'a -> 'a
//│ res: {a: 0, b: true}

y => (let f = x => x; {a: f y, b: f true})
//│ res: 'a -> {a: 'a, b: true}

y => (let f = x => y x; {a: f 0, b: f true})
//│ res: ((0 | true) -> 'a) -> {a: 'a, b: 'a}

y => (let f = x => x y; {a: f (z => z), b: f (z => true)})
//│ res: 'a -> {a: 'a, b: true}

y => (let f = x => x y; {a: f (z => z), b: f (z => succ z)})
//│ res: (int & 'a) -> {a: 'a, b: int}



// --- recursion --- //


let rec f = x => f x.u
//│ f: 'a -> nothing
//│   where
//│     'a <: {u: 'a}


// from https://www.cl.cam.ac.uk/~sd601/mlsub/
let rec recursive_monster = x => { thing: x, self: recursive_monster x }
//│ recursive_monster: 'a -> 'b
//│   where
//│     'b :> {self: 'b, thing: 'a}



// --- random --- //


(let rec x = {a: x, b: x}; x)
//│ res: 'x
//│   where
//│     'x :> {a: 'x, b: 'x}

(let rec x = v => {a: x v, b: x v}; x)
//│ res: anything -> 'a
//│   where
//│     'a :> {a: 'a, b: 'a}

:e
let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ╔══[ERROR] Type mismatch in binding of block of statements:
//│ ║  l.+1: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── integer literal of type `0` is not a function
//│ ║  l.+1: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ║        	                                           ^
//│ ╟── Note: constraint arises from application:
//│ ║  l.+1: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ║        	                                    ^^^
//│ ╟── from reference:
//│ ║  l.+1: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ╙──      	                                    ^
//│ x: 0
//│ res: 0

(x => (let y = (x x); 0))
//│ res: ('a -> anything & 'a) -> 0

// TODO simplify more
(let rec x = (y => (y (x x))); x)
//│ res: 'a -> 'b
//│   where
//│     'a <: 'b -> 'b
//│     'b <: 'a

next => 0
//│ res: anything -> 0

((x => (x x)) (x => x))
//│ res: 'a -> 'a

(let rec x = (y => (x (y y))); x)
//│ res: 'a -> nothing
//│   where
//│     'a <: 'a -> 'a

x => (y => (x (y y)))
//│ res: ('a -> 'b) -> ('c -> 'a & 'c) -> 'b

(let rec x = (let y = (x x); (z => z)); x)
//│ res: 'x
//│   where
//│     'x :> 'a -> 'a
//│     'a :> 'x

(let rec x = (y => (let z = (x x); y)); x)
//│ res: 'x
//│   where
//│     'x :> 'a -> 'a
//│     'a :> 'x

(let rec x = (y => {u: y, v: (x x)}); x)
//│ res: 'x
//│   where
//│     'x :> 'a -> 'b
//│     'b :> {u: 'a, v: 'b}
//│     'a :> 'x

(let rec x = (y => {u: (x x), v: y}); x)
//│ res: 'x
//│   where
//│     'x :> 'a -> 'b
//│     'b :> {u: 'b, v: 'a}
//│     'a :> 'x

(let rec x = (y => (let z = (y x); y)); x)
//│ res: 'x
//│   where
//│     'x :> 'a -> 'a
//│     'a <: 'x -> anything

(x => (let y = (x x.v); 0))
//│ res: ('v -> anything & {v: 'v}) -> 0

let rec x = (let y = (x x); (z => z)); (x (y => y.u)) // [test:T1]
//│ x: 'x
//│   where
//│     'x :> 'a -> 'a
//│     'a :> 'x
//│ res: 'a
//│   where
//│     'a :> forall 'u. ({u: 'u} & 'a) -> ('u | 'a)

:ns
let rec x = (let y = (x x); (z => z))
//│ x: forall 'x, 'a, 'b. 'x
//│   where
//│     'x :> 'b -> 'b
//│        <: 'b & 'x -> 'a
//│     'b :> 'b -> 'b
//│        <: 'a
//│     'a :> 'b -> 'b

