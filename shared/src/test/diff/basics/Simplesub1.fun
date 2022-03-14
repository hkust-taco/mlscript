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
//│ ╟── reference of type `true` does not match type `int`
//│ ║  l.+1: 	succ true
//│ ╙──      	     ^^^^
//│ res: error | int

:e
x => succ (not x)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.+1: 	x => succ (not x)
//│ ║        	     ^^^^^^^^^^^^
//│ ╟── application of type `bool` does not match type `int`
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
//│ ╟── integer literal of type `123` does not match type `bool`
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
//│ res: {f: 'a} -> 'a

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
//│ res: (42 -> 'a) -> 'a

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
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: α181
//│ ╟── while constraining α179 <: α181
//│ ╟── while constraining (α181 -> α182) <: (α179 -> α180)
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: (α179 -> α180)
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: α179
//│ ╟── while constraining α177 <: α179
//│ ╟── while constraining (α179 -> α180) <: (α177 -> α178)
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: (α177 -> α178)
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: α177
//│ ╟── while constraining α175 <: α177
//│ ╟── while constraining (α177 -> α178) <: (α175 -> α176)
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: (α175 -> α176)
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: α175
//│ ╟── while constraining α173 <: α175
//│ ╟── while constraining (α175 -> α176) <: (α173 -> α174)
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: (α173 -> α174)
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: α173
//│ ╟── while constraining α168 <: α173
//│ ╟── while constraining (α173 -> α174) <: (α168 -> α169)
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: (α168 -> α169)
//│ ╟── while constraining ∀ 0. (α170' -> α171') <: α168
//│ ╙── while constraining (α168 -> α169) <: (∀ 0. (α170' -> α171') -> α172)
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
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: α220
//│ ╟── while constraining α217 <: α220
//│ ╟── while constraining (α220 -> α222) <: (α217 -> α218)
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: (α217 -> α218)
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: α217
//│ ╟── while constraining α214 <: α217
//│ ╟── while constraining (α217 -> α219) <: (α214 -> α215)
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: (α214 -> α215)
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: α214
//│ ╟── while constraining α211 <: α214
//│ ╟── while constraining (α214 -> α216) <: (α211 -> α212)
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: (α211 -> α212)
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: α211
//│ ╟── while constraining α208 <: α211
//│ ╟── while constraining (α211 -> α213) <: (α208 -> α209)
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: (α208 -> α209)
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: α208
//│ ╟── while constraining α199 <: α208
//│ ╟── while constraining (α208 -> α210) <: (α199 -> α200)
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: (α199 -> α200)
//│ ╟── while constraining ∀ 0. (α202' -> α204') <: α199
//│ ╙── while constraining (α199 -> α201) <: (∀ 0. (α202' -> α204') -> α207)
//│ res: (nothing -> anything & nothing -> anything) -> error

// Z combinator:
:e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d, ?e, ?f, ?g. ?c -> ?g) -> ?h` exceeded recursion depth limit (100)
//│ ║  l.+1: 	(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: α289
//│ ╟── while constraining α284 <: α289
//│ ╟── while constraining (α289 -> α293) <: (α284 -> α285)
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: (α284 -> α285)
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: α284
//│ ╟── while constraining α279 <: α284
//│ ╟── while constraining (α284 -> α288) <: (α279 -> α280)
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: (α279 -> α280)
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: α279
//│ ╟── while constraining α274 <: α279
//│ ╟── while constraining (α279 -> α283) <: (α274 -> α275)
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: (α274 -> α275)
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: α274
//│ ╟── while constraining α269 <: α274
//│ ╟── while constraining (α274 -> α278) <: (α269 -> α270)
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: (α269 -> α270)
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: α269
//│ ╟── while constraining α247 <: α269
//│ ╟── while constraining (α269 -> α273) <: (α247 -> α250)
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: (α247 -> α250)
//│ ╟── while constraining ∀ 0. (α255' -> α262') <: α247
//│ ╙── while constraining (α247 -> α254) <: (∀ 0. (α255' -> α262') -> α268)
//│ res: ((anything -> nothing) -> anything & (anything -> nothing) -> anything) -> error

// Function that takes arbitrarily many arguments:
:e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ ╔══[ERROR] Subtyping constraint of the form `?a -> ?b <: (forall ?c, ?d, ?e, ?f, ?g. ?c -> ?g) -> ?h` exceeded recursion depth limit (100)
//│ ║  l.+1: 	(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: α381
//│ ╟── while constraining α376 <: α381
//│ ╟── while constraining (α381 -> α385) <: (α376 -> α377)
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: (α376 -> α377)
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: α376
//│ ╟── while constraining α371 <: α376
//│ ╟── while constraining (α376 -> α380) <: (α371 -> α372)
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: (α371 -> α372)
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: α371
//│ ╟── while constraining α366 <: α371
//│ ╟── while constraining (α371 -> α375) <: (α366 -> α367)
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: (α366 -> α367)
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: α366
//│ ╟── while constraining α361 <: α366
//│ ╟── while constraining (α366 -> α370) <: (α361 -> α362)
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: (α361 -> α362)
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: α361
//│ ╟── while constraining α339 <: α361
//│ ╟── while constraining (α361 -> α365) <: (α339 -> α342)
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: (α339 -> α342)
//│ ╟── while constraining ∀ 0. (α347' -> α354') <: α339
//│ ╙── while constraining (α339 -> α346) <: (∀ 0. (α347' -> α354') -> α360)
//│ res: error


let rec trutru = g => trutru (g true)
//│ trutru: (true -> 'a as 'a) -> nothing

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
//│ f: ({u: 'a} as 'a) -> nothing


// from https://www.cl.cam.ac.uk/~sd601/mlsub/
let rec recursive_monster = x => { thing: x, self: recursive_monster x }
//│ recursive_monster: 'a -> ({self: 'b, thing: 'a} as 'b)



// --- random --- //


(let rec x = {a: x, b: x}; x)
//│ res: {a: 'a, b: 'a} as 'a

(let rec x = v => {a: x v, b: x v}; x)
//│ res: anything -> ({a: 'a, b: 'a} as 'a)

:e
let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ╔══[ERROR] Subtyping constraint of the form `{u: ?a, v: ?b} <: ?c` exceeded recursion depth limit (100)
//│ ║  l.+1: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ║        	                         ^^^^^^^^^^^^^^^^
//│ ╟── while constraining {u: α774'', v: α775''} <: α576'
//│ ╟── while constraining {u: α772'', v: α773''} <: α576'
//│ ╟── while constraining {u: α770'', v: α771''} <: α576'
//│ ╟── while constraining {u: α768'', v: α769''} <: α576'
//│ ╟── while constraining {u: α766'', v: α767''} <: α576'
//│ ╟── while constraining {u: α764'', v: α765''} <: α576'
//│ ╟── while constraining {u: α762'', v: α763''} <: α576'
//│ ╟── while constraining {u: α760'', v: α761''} <: α576'
//│ ╟── while constraining {u: α758'', v: α759''} <: α576'
//│ ╟── while constraining {u: α756'', v: α757''} <: α576'
//│ ╟── while constraining {u: α754'', v: α755''} <: α576'
//│ ╟── while constraining {u: α752'', v: α753''} <: α576'
//│ ╟── while constraining {u: α750'', v: α751''} <: α576'
//│ ╟── while constraining {u: α748'', v: α749''} <: α576'
//│ ╟── while constraining {u: α746'', v: α747''} <: α576'
//│ ╟── while constraining {u: α744'', v: α745''} <: α576'
//│ ╟── while constraining {u: α742'', v: α743''} <: α576'
//│ ╟── while constraining {u: α740'', v: α741''} <: α576'
//│ ╟── while constraining {u: α738'', v: α739''} <: α576'
//│ ╟── while constraining {u: α736'', v: α737''} <: α576'
//│ ╟── while constraining {u: α734'', v: α735''} <: α576'
//│ ╟── while constraining {u: α732'', v: α733''} <: α576'
//│ ╟── while constraining {u: α730'', v: α731''} <: α576'
//│ ╟── while constraining {u: α728'', v: α729''} <: α576'
//│ ╟── while constraining {u: α726'', v: α727''} <: α576'
//│ ╟── while constraining {u: α724'', v: α725''} <: α576'
//│ ╟── while constraining {u: α722'', v: α723''} <: α576'
//│ ╟── while constraining {u: α720'', v: α721''} <: α576'
//│ ╟── while constraining {u: α718'', v: α719''} <: α576'
//│ ╟── while constraining {u: α716'', v: α717''} <: α576'
//│ ╟── while constraining {u: α714'', v: α715''} <: α576'
//│ ╟── while constraining {u: α712'', v: α713''} <: α576'
//│ ╟── while constraining {u: α710'', v: α711''} <: α576'
//│ ╟── while constraining {u: α708'', v: α709''} <: α576'
//│ ╟── while constraining {u: α706'', v: α707''} <: α576'
//│ ╟── while constraining {u: α704'', v: α705''} <: α576'
//│ ╟── while constraining {u: α702'', v: α703''} <: α576'
//│ ╟── while constraining {u: α700'', v: α701''} <: α576'
//│ ╟── while constraining {u: α698'', v: α699''} <: α576'
//│ ╟── while constraining {u: α696'', v: α697''} <: α576'
//│ ╟── while constraining {u: α694'', v: α695''} <: α576'
//│ ╟── while constraining {u: α692'', v: α693''} <: α576'
//│ ╟── while constraining {u: α690'', v: α691''} <: α576'
//│ ╟── while constraining {u: α688'', v: α689''} <: α576'
//│ ╟── while constraining {u: α686'', v: α687''} <: α576'
//│ ╟── while constraining {u: α684'', v: α685''} <: α576'
//│ ╟── while constraining {u: α682'', v: α683''} <: α576'
//│ ╟── while constraining {u: α680'', v: α681''} <: α576'
//│ ╟── while constraining {u: α678'', v: α679''} <: α576'
//│ ╟── while constraining {u: α676'', v: α677''} <: α576'
//│ ╟── while constraining {u: α674'', v: α675''} <: α576'
//│ ╟── while constraining {u: α672'', v: α673''} <: α576'
//│ ╟── while constraining {u: α670'', v: α671''} <: α576'
//│ ╟── while constraining {u: α668'', v: α669''} <: α576'
//│ ╟── while constraining {u: α666'', v: α667''} <: α576'
//│ ╟── while constraining {u: α664'', v: α665''} <: α576'
//│ ╟── while constraining {u: α662'', v: α663''} <: α576'
//│ ╟── while constraining {u: α660'', v: α661''} <: α576'
//│ ╟── while constraining {u: α658'', v: α659''} <: α576'
//│ ╟── while constraining {u: α656'', v: α657''} <: α576'
//│ ╟── while constraining {u: α654'', v: α655''} <: α576'
//│ ╟── while constraining {u: α652'', v: α653''} <: α576'
//│ ╟── while constraining {u: α650'', v: α651''} <: α576'
//│ ╟── while constraining {u: α648'', v: α649''} <: α576'
//│ ╟── while constraining {u: α646'', v: α647''} <: α576'
//│ ╟── while constraining {u: α644'', v: α645''} <: α576'
//│ ╟── while constraining {u: α642'', v: α643''} <: α576'
//│ ╟── while constraining {u: α640'', v: α641''} <: α576'
//│ ╟── while constraining {u: α638'', v: α639''} <: α576'
//│ ╟── while constraining {u: α636'', v: α637''} <: α576'
//│ ╟── while constraining {u: α634'', v: α635''} <: α576'
//│ ╟── while constraining {u: α632'', v: α633''} <: α576'
//│ ╟── while constraining {u: α630'', v: α631''} <: α576'
//│ ╟── while constraining {u: α628'', v: α629''} <: α576'
//│ ╟── while constraining {u: α626'', v: α627''} <: α576'
//│ ╟── while constraining {u: α624'', v: α625''} <: α576'
//│ ╟── while constraining {u: α622'', v: α623''} <: α576'
//│ ╟── while constraining {u: α620'', v: α621''} <: α576'
//│ ╟── while constraining {u: α618'', v: α619''} <: α576'
//│ ╟── while constraining {u: α616'', v: α617''} <: α576'
//│ ╟── while constraining {u: α614'', v: α615''} <: α576'
//│ ╟── while constraining {u: α612'', v: α613''} <: α576'
//│ ╟── while constraining {u: α610'', v: α611''} <: α576'
//│ ╟── while constraining {u: α608'', v: α609''} <: α576'
//│ ╟── while constraining {u: α606'', v: α607''} <: α576'
//│ ╟── while constraining {u: α604'', v: α605''} <: α576'
//│ ╟── while constraining {u: α602'', v: α603''} <: α576'
//│ ╟── while constraining {u: α600'', v: α601''} <: α576'
//│ ╟── while constraining {u: α598'', v: α599''} <: α576'
//│ ╟── while constraining {u: α596'', v: α597''} <: α576'
//│ ╟── while constraining {u: α594'', v: α595''} <: α576'
//│ ╟── while constraining {u: α592'', v: α593''} <: α576'
//│ ╟── while constraining {u: α590'', v: α591''} <: α576'
//│ ╟── while constraining {u: α588'', v: α589''} <: α576'
//│ ╟── while constraining {u: α586'', v: α587''} <: α576'
//│ ╟── while constraining {u: α584'', v: α585''} <: α576'
//│ ╟── while constraining {u: α582'', v: α583''} <: α576'
//│ ╟── while constraining {u: α580'', v: α581''} <: α576'
//│ ╟── while constraining {u: α578'', v: α579''} <: α576'
//│ ╟── while constraining {u: α574'', v: α575''} <: α576'
//│ ╙── while constraining {u: α574'', v: α575''} <: α574''
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

(let rec x = (y => (y (x x))); x)
//│ res: ('b -> ('a & 'b & 'c) as 'a) -> 'c

next => 0
//│ res: anything -> 0

((x => (x x)) (x => x))
//│ res: 'a -> 'a

(let rec x = (y => (x (y y))); x)
//│ res: ('b -> 'a & 'b as 'a) -> nothing

x => (y => (x (y y)))
//│ res: ('a -> 'b) -> ('c -> 'a & 'c) -> 'b

(let rec x = (let y = (x x); (z => z)); x)
//│ res: 'b -> ('a | 'b) as 'a

(let rec x = (y => (let z = (x x); y)); x)
//│ res: 'b -> ('a | 'b) as 'a

(let rec x = (y => {u: y, v: (x x)}); x)
//│ res: 'b -> ({u: 'a | 'b, v: 'c} as 'c) as 'a

(let rec x = (y => {u: (x x), v: y}); x)
//│ res: 'b -> ({u: 'c, v: 'a | 'b} as 'c) as 'a

(let rec x = (y => (let z = (y x); y)); x)
//│ res: ('a -> anything & 'b) -> 'b as 'a

(x => (let y = (x x.v); 0))
//│ res: ('a -> anything & {v: 'a}) -> 0

let rec x = (let y = (x x); (z => z)); (x (y => y.u))
//│ x: 'b -> ('a | 'b) as 'a
//│ res: ({u: 'a} & 'b) -> (({u: 'a} & 'b) -> (forall 'a, 'd. 'c) | 'a | 'b as 'c) | 'b

