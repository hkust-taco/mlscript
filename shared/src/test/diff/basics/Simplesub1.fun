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
//│ ╔══[ERROR] Subtyping constraint of the form `forall ?a, ?b. ?b -> ?a <: (forall ?c, ?d. ?d -> ?c) -> ?e` exceeded recursion depth limit (400)
//│ ║  l.+1: 	(x => x x) (x => x x)
//│ ║        	^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  α264
//│ ╟── while constraining:  α262  <!<  α264
//│ ╟── while constraining:  (α264 -> α265)  <!<  (α262 -> α263)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  (α262 -> α263)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  α262
//│ ╟── while constraining:  α260  <!<  α262
//│ ╟── while constraining:  (α262 -> α263)  <!<  (α260 -> α261)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  (α260 -> α261)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  α260
//│ ╟── while constraining:  α258  <!<  α260
//│ ╟── while constraining:  (α260 -> α261)  <!<  (α258 -> α259)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  (α258 -> α259)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  α258
//│ ╟── while constraining:  α256  <!<  α258
//│ ╟── while constraining:  (α258 -> α259)  <!<  (α256 -> α257)
//│ ╟── ......
//│ ╟── ......
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  α248
//│ ╟── while constraining:  α246  <!<  α248
//│ ╟── while constraining:  (α248 -> α249)  <!<  (α246 -> α247)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  (α246 -> α247)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  α246
//│ ╟── while constraining:  α244  <!<  α246
//│ ╟── while constraining:  (α246 -> α247)  <!<  (α244 -> α245)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  (α244 -> α245)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  α244
//│ ╟── while constraining:  α242  <!<  α244
//│ ╟── while constraining:  (α244 -> α245)  <!<  (α242 -> α243)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  (α242 -> α243)
//│ ╟── while constraining:  ‹∀ 0. (α239' -> α240')›  <!<  α242
//│ ╟── while constraining:  (α242 -> α243)  <!<  (‹∀ 0. (α239' -> α240')› -> α241)
//│ ╙── while constraining:  ‹∀ 0. (α237' -> α238')›  <!<  (‹∀ 0. (α239' -> α240')› -> α241)
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
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  α317'
//│ ╟── while constraining:  α314'  <!<  α317'
//│ ╟── while constraining:  (α317' -> α316')  <!<  (α314' -> α312')
//│ ╟── while constraining:  {(α317' -> α316') where: α277' <: (α315' -> α316')}  <!<  (α314' -> α312')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  (α314' -> α312')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  α314'
//│ ╟── while constraining:  α311'  <!<  α314'
//│ ╟── while constraining:  (α314' -> α313')  <!<  (α311' -> α309')
//│ ╟── while constraining:  {(α314' -> α313') where: α277' <: (α312' -> α313')}  <!<  (α311' -> α309')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  (α311' -> α309')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  α311'
//│ ╟── while constraining:  α308'  <!<  α311'
//│ ╟── while constraining:  (α311' -> α310')  <!<  (α308' -> α306')
//│ ╟── while constraining:  {(α311' -> α310') where: α277' <: (α309' -> α310')}  <!<  (α308' -> α306')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  (α308' -> α306')
//│ ╟── ......
//│ ╟── ......
//│ ╟── while constraining:  (α293' -> α292')  <!<  (α290' -> α288')
//│ ╟── while constraining:  {(α293' -> α292') where: α277' <: (α291' -> α292')}  <!<  (α290' -> α288')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  (α290' -> α288')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  α290'
//│ ╟── while constraining:  α287'  <!<  α290'
//│ ╟── while constraining:  (α290' -> α289')  <!<  (α287' -> α285')
//│ ╟── while constraining:  {(α290' -> α289') where: α277' <: (α288' -> α289')}  <!<  (α287' -> α285')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  (α287' -> α285')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  α287'
//│ ╟── while constraining:  α278'  <!<  α287'
//│ ╟── while constraining:  (α287' -> α286')  <!<  (α278' -> α279')
//│ ╟── while constraining:  {(α287' -> α286') where: α277' <: (α285' -> α286')}  <!<  (α278' -> α279')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  (α278' -> α279')
//│ ╟── while constraining:  ‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}›  <!<  α278'
//│ ╙── while constraining:  (α278' -> α280')  <!<  (‹∀ 1. {(α281'' -> α283'') where: α277' <: (α282'' -> α283'')}› -> α284')
//│ res: (nothing -> anything) -> error

// Z combinator:
// * FIXME simplified type
// :e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ res: ((forall 'a, 'b, 'c. ('b -> 'c
//│   where
//│     'a <: 'a -> 'b -> 'c)) -> 'd) -> 'd

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
//│ res: (true -> 'a & 0 -> 'b) -> {a: 'b, b: 'a}

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
//│ res: 'a -> 'a

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
//│ x: 'a -> 'a
//│ res: {u: 'u} -> 'u

:ns
let rec x = (let y = (x x); (z => z))
//│ x: forall 'x, 'a, 'b. 'x
//│   where
//│     'x :> forall 'c. 'c -> 'c
//│        <: 'b & 'x -> 'a
//│     'b :> forall 'c. 'c -> 'c
//│        <: 'a
//│     'a :> forall 'c. 'c -> 'c

