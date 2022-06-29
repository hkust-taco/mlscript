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
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d. ?d -> ?c) -> ?e` exceeded recursion depth limit (400)
//│ ║  l.+1: 	(x => x x) (x => x x)
//│ ║        	^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α247
//│ ╟── while constraining:  α245  <!<  α247
//│ ╟── while constraining:  (α247 -> α248)  <!<  (α245 -> α246)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α245 -> α246)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α245
//│ ╟── while constraining:  α243  <!<  α245
//│ ╟── while constraining:  (α245 -> α246)  <!<  (α243 -> α244)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α243 -> α244)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α243
//│ ╟── while constraining:  α241  <!<  α243
//│ ╟── while constraining:  (α243 -> α244)  <!<  (α241 -> α242)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  (α241 -> α242)
//│ ╟── while constraining:  ‹∀ 0. (α224' -> α225')›  <!<  α241
//│ ╟── while constraining:  α239  <!<  α241
//│ ╟── while constraining:  (α241 -> α242)  <!<  (α239 -> α240)
//│ ╟── ......
//│ ╟── ......
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
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d, ?e. (?e -> ?d
//│   where
//│     ?f <: ?c -> ?d)) -> ?g` exceeded recursion depth limit (400)
//│ ║  l.+1: 	(f => (x => f (x x)) (x => f (x x)))
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  α312
//│ ╟── while constraining:  α309  <!<  α312
//│ ╟── while constraining:  (α312 -> α311)  <!<  (α309 -> α307)
//│ ╟── while constraining:  {(α312 -> α311) where: α272 <: (α310 -> α311)}  <!<  (α309 -> α307)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  (α309 -> α307)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  α309
//│ ╟── while constraining:  α306  <!<  α309
//│ ╟── while constraining:  (α309 -> α308)  <!<  (α306 -> α304)
//│ ╟── while constraining:  {(α309 -> α308) where: α272 <: (α307 -> α308)}  <!<  (α306 -> α304)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  (α306 -> α304)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  α306
//│ ╟── while constraining:  α303  <!<  α306
//│ ╟── while constraining:  (α306 -> α305)  <!<  (α303 -> α301)
//│ ╟── while constraining:  {(α306 -> α305) where: α272 <: (α304 -> α305)}  <!<  (α303 -> α301)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  (α303 -> α301)
//│ ╟── ......
//│ ╟── ......
//│ ╟── while constraining:  (α288 -> α287)  <!<  (α285 -> α283)
//│ ╟── while constraining:  {(α288 -> α287) where: α272 <: (α286 -> α287)}  <!<  (α285 -> α283)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  (α285 -> α283)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  α285
//│ ╟── while constraining:  α282  <!<  α285
//│ ╟── while constraining:  (α285 -> α284)  <!<  (α282 -> α280)
//│ ╟── while constraining:  {(α285 -> α284) where: α272 <: (α283 -> α284)}  <!<  (α282 -> α280)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  (α282 -> α280)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  α282
//│ ╟── while constraining:  α273  <!<  α282
//│ ╟── while constraining:  (α282 -> α281)  <!<  (α273 -> α274)
//│ ╟── while constraining:  {(α282 -> α281) where: α272 <: (α280 -> α281)}  <!<  (α273 -> α274)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  (α273 -> α274)
//│ ╟── while constraining:  ‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}›  <!<  α273
//│ ╙── while constraining:  (α273 -> α275)  <!<  (‹∀ 0. {(α276' -> α278') where: α272 <: (α277' -> α278')}› -> α279)
//│ res: (nothing -> anything) -> error

// Z combinator:
// * FIXME simplified type
// :e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ res: ((forall 'a, 'b. ('a -> 'b
//│   where
//│     'c <: 'c -> 'a -> 'b)) -> 'd) -> 'd

// * Function that takes arbitrarily many arguments:
// * FIXME type of result shouldn't be `nothing`
// :e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ res: anything -> (forall 'a, 'b. ('a -> 'b
//│   where
//│     'c <: 'c -> 'a -> 'b))

res 1 2
//│ res: 'a -> 'b
//│   where
//│     'c <: 'c -> 'a -> 'b


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

