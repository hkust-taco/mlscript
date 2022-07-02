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
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d. ?d -> ?c) -> ?e` exceeded recursion depth limit (100)
//│ ║  l.+1: 	(x => x x) (x => x x)
//│ ║        	^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  α235
//│ ╟── while constraining:  α233  <!<  α235
//│ ╟── while constraining:  (α235 -> α236)  <!<  (α233 -> α234)
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  (α233 -> α234)
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  α233
//│ ╟── while constraining:  α231  <!<  α233
//│ ╟── while constraining:  (α233 -> α234)  <!<  (α231 -> α232)
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  (α231 -> α232)
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  α231
//│ ╟── while constraining:  α229  <!<  α231
//│ ╟── while constraining:  (α231 -> α232)  <!<  (α229 -> α230)
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  (α229 -> α230)
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  α229
//│ ╟── while constraining:  α227  <!<  α229
//│ ╟── while constraining:  (α229 -> α230)  <!<  (α227 -> α228)
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  (α227 -> α228)
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  α227
//│ ╟── while constraining:  α222  <!<  α227
//│ ╟── while constraining:  (α227 -> α228)  <!<  (α222 -> α223)
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  (α222 -> α223)
//│ ╟── while constraining:  ∀ 0. (α224' -> α225')  <!<  α222
//│ ╙── while constraining:  (α222 -> α223)  <!<  (∀ 0. (α224' -> α225') -> α226)
//│ res: error


x => {l: x x, r: x }
//│ res: ('a -> 'b & 'a) -> {l: 'b, r: 'a}


// From https://github.com/stedolan/mlsub
// Y combinator:
:e // similarly to Omega
(f => (x => f (x x)) (x => f (x x)))
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d, ?e. ?c -> ?e) -> ?f` exceeded recursion depth limit (100)
//│ ║  l.+1: 	(f => (x => f (x x)) (x => f (x x)))
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  α276
//│ ╟── while constraining:  α273  <!<  α276
//│ ╟── while constraining:  (α276 -> α278)  <!<  (α273 -> α274)
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  (α273 -> α274)
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  α273
//│ ╟── while constraining:  α270  <!<  α273
//│ ╟── while constraining:  (α273 -> α275)  <!<  (α270 -> α271)
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  (α270 -> α271)
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  α270
//│ ╟── while constraining:  α267  <!<  α270
//│ ╟── while constraining:  (α270 -> α272)  <!<  (α267 -> α268)
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  (α267 -> α268)
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  α267
//│ ╟── while constraining:  α264  <!<  α267
//│ ╟── while constraining:  (α267 -> α269)  <!<  (α264 -> α265)
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  (α264 -> α265)
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  α264
//│ ╟── while constraining:  α255  <!<  α264
//│ ╟── while constraining:  (α264 -> α266)  <!<  (α255 -> α256)
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  (α255 -> α256)
//│ ╟── while constraining:  ∀ 0. (α258' -> α260')  <!<  α255
//│ ╙── while constraining:  (α255 -> α257)  <!<  (∀ 0. (α258' -> α260') -> α263)
//│ res: (nothing -> anything) -> error

// Z combinator:
:e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d, ?e, ?f, ?g. ?c -> ?g) -> ?h` exceeded recursion depth limit (100)
//│ ║  l.+1: 	(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  α345
//│ ╟── while constraining:  α340  <!<  α345
//│ ╟── while constraining:  (α345 -> α349)  <!<  (α340 -> α341)
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  (α340 -> α341)
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  α340
//│ ╟── while constraining:  α335  <!<  α340
//│ ╟── while constraining:  (α340 -> α344)  <!<  (α335 -> α336)
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  (α335 -> α336)
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  α335
//│ ╟── while constraining:  α330  <!<  α335
//│ ╟── while constraining:  (α335 -> α339)  <!<  (α330 -> α331)
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  (α330 -> α331)
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  α330
//│ ╟── while constraining:  α325  <!<  α330
//│ ╟── while constraining:  (α330 -> α334)  <!<  (α325 -> α326)
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  (α325 -> α326)
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  α325
//│ ╟── while constraining:  α303  <!<  α325
//│ ╟── while constraining:  (α325 -> α329)  <!<  (α303 -> α306)
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  (α303 -> α306)
//│ ╟── while constraining:  ∀ 0. (α311' -> α318')  <!<  α303
//│ ╙── while constraining:  (α303 -> α310)  <!<  (∀ 0. (α311' -> α318') -> α324)
//│ res: ((anything -> nothing) -> anything) -> error

// Function that takes arbitrarily many arguments:
:e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d, ?e, ?f, ?g. ?c -> ?g) -> ?h` exceeded recursion depth limit (100)
//│ ║  l.+1: 	(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  α437
//│ ╟── while constraining:  α432  <!<  α437
//│ ╟── while constraining:  (α437 -> α441)  <!<  (α432 -> α433)
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  (α432 -> α433)
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  α432
//│ ╟── while constraining:  α427  <!<  α432
//│ ╟── while constraining:  (α432 -> α436)  <!<  (α427 -> α428)
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  (α427 -> α428)
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  α427
//│ ╟── while constraining:  α422  <!<  α427
//│ ╟── while constraining:  (α427 -> α431)  <!<  (α422 -> α423)
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  (α422 -> α423)
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  α422
//│ ╟── while constraining:  α417  <!<  α422
//│ ╟── while constraining:  (α422 -> α426)  <!<  (α417 -> α418)
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  (α417 -> α418)
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  α417
//│ ╟── while constraining:  α395  <!<  α417
//│ ╟── while constraining:  (α417 -> α421)  <!<  (α395 -> α398)
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  (α395 -> α398)
//│ ╟── while constraining:  ∀ 0. (α403' -> α410')  <!<  α395
//│ ╙── while constraining:  (α395 -> α402)  <!<  (∀ 0. (α403' -> α410') -> α416)
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
//│ ╔══[ERROR] Subtyping constraint of the form `{u: ?y, v: ?a} <: ?y0` exceeded recursion depth limit (100)
//│ ║  l.+1: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ║        	                         ^^^^^^^^^^^^^^^^
//│ ╟── while constraining:  {u: y824'', v: α825''}  <!<  y626'
//│ ╟── while constraining:  {u: y822'', v: α823''}  <!<  y626'
//│ ╟── while constraining:  {u: y820'', v: α821''}  <!<  y626'
//│ ╟── while constraining:  {u: y818'', v: α819''}  <!<  y626'
//│ ╟── while constraining:  {u: y816'', v: α817''}  <!<  y626'
//│ ╟── while constraining:  {u: y814'', v: α815''}  <!<  y626'
//│ ╟── while constraining:  {u: y812'', v: α813''}  <!<  y626'
//│ ╟── while constraining:  {u: y810'', v: α811''}  <!<  y626'
//│ ╟── while constraining:  {u: y808'', v: α809''}  <!<  y626'
//│ ╟── while constraining:  {u: y806'', v: α807''}  <!<  y626'
//│ ╟── while constraining:  {u: y804'', v: α805''}  <!<  y626'
//│ ╟── while constraining:  {u: y802'', v: α803''}  <!<  y626'
//│ ╟── while constraining:  {u: y800'', v: α801''}  <!<  y626'
//│ ╟── while constraining:  {u: y798'', v: α799''}  <!<  y626'
//│ ╟── while constraining:  {u: y796'', v: α797''}  <!<  y626'
//│ ╟── while constraining:  {u: y794'', v: α795''}  <!<  y626'
//│ ╟── while constraining:  {u: y792'', v: α793''}  <!<  y626'
//│ ╟── while constraining:  {u: y790'', v: α791''}  <!<  y626'
//│ ╟── while constraining:  {u: y788'', v: α789''}  <!<  y626'
//│ ╟── while constraining:  {u: y786'', v: α787''}  <!<  y626'
//│ ╟── while constraining:  {u: y784'', v: α785''}  <!<  y626'
//│ ╟── while constraining:  {u: y782'', v: α783''}  <!<  y626'
//│ ╟── while constraining:  {u: y780'', v: α781''}  <!<  y626'
//│ ╟── while constraining:  {u: y778'', v: α779''}  <!<  y626'
//│ ╟── while constraining:  {u: y776'', v: α777''}  <!<  y626'
//│ ╟── while constraining:  {u: y774'', v: α775''}  <!<  y626'
//│ ╟── while constraining:  {u: y772'', v: α773''}  <!<  y626'
//│ ╟── while constraining:  {u: y770'', v: α771''}  <!<  y626'
//│ ╟── while constraining:  {u: y768'', v: α769''}  <!<  y626'
//│ ╟── while constraining:  {u: y766'', v: α767''}  <!<  y626'
//│ ╟── while constraining:  {u: y764'', v: α765''}  <!<  y626'
//│ ╟── while constraining:  {u: y762'', v: α763''}  <!<  y626'
//│ ╟── while constraining:  {u: y760'', v: α761''}  <!<  y626'
//│ ╟── while constraining:  {u: y758'', v: α759''}  <!<  y626'
//│ ╟── while constraining:  {u: y756'', v: α757''}  <!<  y626'
//│ ╟── while constraining:  {u: y754'', v: α755''}  <!<  y626'
//│ ╟── while constraining:  {u: y752'', v: α753''}  <!<  y626'
//│ ╟── while constraining:  {u: y750'', v: α751''}  <!<  y626'
//│ ╟── while constraining:  {u: y748'', v: α749''}  <!<  y626'
//│ ╟── while constraining:  {u: y746'', v: α747''}  <!<  y626'
//│ ╟── while constraining:  {u: y744'', v: α745''}  <!<  y626'
//│ ╟── while constraining:  {u: y742'', v: α743''}  <!<  y626'
//│ ╟── while constraining:  {u: y740'', v: α741''}  <!<  y626'
//│ ╟── while constraining:  {u: y738'', v: α739''}  <!<  y626'
//│ ╟── while constraining:  {u: y736'', v: α737''}  <!<  y626'
//│ ╟── while constraining:  {u: y734'', v: α735''}  <!<  y626'
//│ ╟── while constraining:  {u: y732'', v: α733''}  <!<  y626'
//│ ╟── while constraining:  {u: y730'', v: α731''}  <!<  y626'
//│ ╟── while constraining:  {u: y728'', v: α729''}  <!<  y626'
//│ ╟── while constraining:  {u: y726'', v: α727''}  <!<  y626'
//│ ╟── while constraining:  {u: y724'', v: α725''}  <!<  y626'
//│ ╟── while constraining:  {u: y722'', v: α723''}  <!<  y626'
//│ ╟── while constraining:  {u: y720'', v: α721''}  <!<  y626'
//│ ╟── while constraining:  {u: y718'', v: α719''}  <!<  y626'
//│ ╟── while constraining:  {u: y716'', v: α717''}  <!<  y626'
//│ ╟── while constraining:  {u: y714'', v: α715''}  <!<  y626'
//│ ╟── while constraining:  {u: y712'', v: α713''}  <!<  y626'
//│ ╟── while constraining:  {u: y710'', v: α711''}  <!<  y626'
//│ ╟── while constraining:  {u: y708'', v: α709''}  <!<  y626'
//│ ╟── while constraining:  {u: y706'', v: α707''}  <!<  y626'
//│ ╟── while constraining:  {u: y704'', v: α705''}  <!<  y626'
//│ ╟── while constraining:  {u: y702'', v: α703''}  <!<  y626'
//│ ╟── while constraining:  {u: y700'', v: α701''}  <!<  y626'
//│ ╟── while constraining:  {u: y698'', v: α699''}  <!<  y626'
//│ ╟── while constraining:  {u: y696'', v: α697''}  <!<  y626'
//│ ╟── while constraining:  {u: y694'', v: α695''}  <!<  y626'
//│ ╟── while constraining:  {u: y692'', v: α693''}  <!<  y626'
//│ ╟── while constraining:  {u: y690'', v: α691''}  <!<  y626'
//│ ╟── while constraining:  {u: y688'', v: α689''}  <!<  y626'
//│ ╟── while constraining:  {u: y686'', v: α687''}  <!<  y626'
//│ ╟── while constraining:  {u: y684'', v: α685''}  <!<  y626'
//│ ╟── while constraining:  {u: y682'', v: α683''}  <!<  y626'
//│ ╟── while constraining:  {u: y680'', v: α681''}  <!<  y626'
//│ ╟── while constraining:  {u: y678'', v: α679''}  <!<  y626'
//│ ╟── while constraining:  {u: y676'', v: α677''}  <!<  y626'
//│ ╟── while constraining:  {u: y674'', v: α675''}  <!<  y626'
//│ ╟── while constraining:  {u: y672'', v: α673''}  <!<  y626'
//│ ╟── while constraining:  {u: y670'', v: α671''}  <!<  y626'
//│ ╟── while constraining:  {u: y668'', v: α669''}  <!<  y626'
//│ ╟── while constraining:  {u: y666'', v: α667''}  <!<  y626'
//│ ╟── while constraining:  {u: y664'', v: α665''}  <!<  y626'
//│ ╟── while constraining:  {u: y662'', v: α663''}  <!<  y626'
//│ ╟── while constraining:  {u: y660'', v: α661''}  <!<  y626'
//│ ╟── while constraining:  {u: y658'', v: α659''}  <!<  y626'
//│ ╟── while constraining:  {u: y656'', v: α657''}  <!<  y626'
//│ ╟── while constraining:  {u: y654'', v: α655''}  <!<  y626'
//│ ╟── while constraining:  {u: y652'', v: α653''}  <!<  y626'
//│ ╟── while constraining:  {u: y650'', v: α651''}  <!<  y626'
//│ ╟── while constraining:  {u: y648'', v: α649''}  <!<  y626'
//│ ╟── while constraining:  {u: y646'', v: α647''}  <!<  y626'
//│ ╟── while constraining:  {u: y644'', v: α645''}  <!<  y626'
//│ ╟── while constraining:  {u: y642'', v: α643''}  <!<  y626'
//│ ╟── while constraining:  {u: y640'', v: α641''}  <!<  y626'
//│ ╟── while constraining:  {u: y638'', v: α639''}  <!<  y626'
//│ ╟── while constraining:  {u: y636'', v: α637''}  <!<  y626'
//│ ╟── while constraining:  {u: y634'', v: α635''}  <!<  y626'
//│ ╟── while constraining:  {u: y632'', v: α633''}  <!<  y626'
//│ ╟── while constraining:  {u: y630'', v: α631''}  <!<  y626'
//│ ╟── while constraining:  {u: y628'', v: α629''}  <!<  y626'
//│ ╟── while constraining:  {u: y624'', v: α625''}  <!<  y626'
//│ ╙── while constraining:  {u: y624'', v: α625''}  <!<  y624''
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

