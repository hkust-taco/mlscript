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
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	(x => x x) (x => x x)
//│ ║        	^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ∀ 0. (α224' -> α225')  <:  (α229 -> α230)    PolymorphicType  FunctionType
//│ ╙──  ... looks like:  ∀ 0. (α224' -> α225')  <:  (α224' -> α225')
//│ res: error


x => {l: x x, r: x }
//│ res: ('a -> 'b & 'a) -> {l: 'b, r: 'a}


// From https://github.com/stedolan/mlsub
// Y combinator:
:e // similarly to Omega
(f => (x => f (x x)) (x => f (x x)))
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	(f => (x => f (x x)) (x => f (x x)))
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ∀ 0. (α244' -> α246')  <:  (α253 -> α254)    PolymorphicType  FunctionType
//│ ╙──  ... looks like:  ∀ 0. (α244' -> α246')  <:  (α244' -> α245')
//│ res: ('a -> 'a & 'a -> 'b) -> (error | 'b)

// Z combinator:
:e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ∀ 0. (α276' -> α283')  <:  (α295 -> α296)    PolymorphicType  FunctionType
//│ ╙──  ... looks like:  ∀ 0. (α276' -> α283')  <:  (α276' -> α279')
//│ res: (('a -> 'b) -> ('c -> 'd & 'a -> 'b) & ('c -> 'd) -> 'e) -> (error | 'e)

// Function that takes arbitrarily many arguments:
:e
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ ║        	      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ∀ 0. (α335' -> α342')  <:  (α354 -> α355)    PolymorphicType  FunctionType
//│ ╙──  ... looks like:  ∀ 0. (α335' -> α342')  <:  (α335' -> α338')
//│ res: 'a | error
//│   where
//│     'a :> anything -> 'a


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

:e
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
//│ ╟── while constraining:  {u: y722'', v: α723''}  <!<  y524'
//│ ╟── while constraining:  {u: y720'', v: α721''}  <!<  y524'
//│ ╟── while constraining:  {u: y718'', v: α719''}  <!<  y524'
//│ ╟── while constraining:  {u: y716'', v: α717''}  <!<  y524'
//│ ╟── while constraining:  {u: y714'', v: α715''}  <!<  y524'
//│ ╟── while constraining:  {u: y712'', v: α713''}  <!<  y524'
//│ ╟── while constraining:  {u: y710'', v: α711''}  <!<  y524'
//│ ╟── while constraining:  {u: y708'', v: α709''}  <!<  y524'
//│ ╟── while constraining:  {u: y706'', v: α707''}  <!<  y524'
//│ ╟── while constraining:  {u: y704'', v: α705''}  <!<  y524'
//│ ╟── while constraining:  {u: y702'', v: α703''}  <!<  y524'
//│ ╟── while constraining:  {u: y700'', v: α701''}  <!<  y524'
//│ ╟── while constraining:  {u: y698'', v: α699''}  <!<  y524'
//│ ╟── while constraining:  {u: y696'', v: α697''}  <!<  y524'
//│ ╟── while constraining:  {u: y694'', v: α695''}  <!<  y524'
//│ ╟── while constraining:  {u: y692'', v: α693''}  <!<  y524'
//│ ╟── while constraining:  {u: y690'', v: α691''}  <!<  y524'
//│ ╟── while constraining:  {u: y688'', v: α689''}  <!<  y524'
//│ ╟── while constraining:  {u: y686'', v: α687''}  <!<  y524'
//│ ╟── while constraining:  {u: y684'', v: α685''}  <!<  y524'
//│ ╟── while constraining:  {u: y682'', v: α683''}  <!<  y524'
//│ ╟── while constraining:  {u: y680'', v: α681''}  <!<  y524'
//│ ╟── while constraining:  {u: y678'', v: α679''}  <!<  y524'
//│ ╟── while constraining:  {u: y676'', v: α677''}  <!<  y524'
//│ ╟── while constraining:  {u: y674'', v: α675''}  <!<  y524'
//│ ╟── while constraining:  {u: y672'', v: α673''}  <!<  y524'
//│ ╟── while constraining:  {u: y670'', v: α671''}  <!<  y524'
//│ ╟── while constraining:  {u: y668'', v: α669''}  <!<  y524'
//│ ╟── while constraining:  {u: y666'', v: α667''}  <!<  y524'
//│ ╟── while constraining:  {u: y664'', v: α665''}  <!<  y524'
//│ ╟── while constraining:  {u: y662'', v: α663''}  <!<  y524'
//│ ╟── while constraining:  {u: y660'', v: α661''}  <!<  y524'
//│ ╟── while constraining:  {u: y658'', v: α659''}  <!<  y524'
//│ ╟── while constraining:  {u: y656'', v: α657''}  <!<  y524'
//│ ╟── while constraining:  {u: y654'', v: α655''}  <!<  y524'
//│ ╟── while constraining:  {u: y652'', v: α653''}  <!<  y524'
//│ ╟── while constraining:  {u: y650'', v: α651''}  <!<  y524'
//│ ╟── while constraining:  {u: y648'', v: α649''}  <!<  y524'
//│ ╟── while constraining:  {u: y646'', v: α647''}  <!<  y524'
//│ ╟── while constraining:  {u: y644'', v: α645''}  <!<  y524'
//│ ╟── while constraining:  {u: y642'', v: α643''}  <!<  y524'
//│ ╟── while constraining:  {u: y640'', v: α641''}  <!<  y524'
//│ ╟── while constraining:  {u: y638'', v: α639''}  <!<  y524'
//│ ╟── while constraining:  {u: y636'', v: α637''}  <!<  y524'
//│ ╟── while constraining:  {u: y634'', v: α635''}  <!<  y524'
//│ ╟── while constraining:  {u: y632'', v: α633''}  <!<  y524'
//│ ╟── while constraining:  {u: y630'', v: α631''}  <!<  y524'
//│ ╟── while constraining:  {u: y628'', v: α629''}  <!<  y524'
//│ ╟── while constraining:  {u: y626'', v: α627''}  <!<  y524'
//│ ╟── while constraining:  {u: y624'', v: α625''}  <!<  y524'
//│ ╟── while constraining:  {u: y622'', v: α623''}  <!<  y524'
//│ ╟── while constraining:  {u: y620'', v: α621''}  <!<  y524'
//│ ╟── while constraining:  {u: y618'', v: α619''}  <!<  y524'
//│ ╟── while constraining:  {u: y616'', v: α617''}  <!<  y524'
//│ ╟── while constraining:  {u: y614'', v: α615''}  <!<  y524'
//│ ╟── while constraining:  {u: y612'', v: α613''}  <!<  y524'
//│ ╟── while constraining:  {u: y610'', v: α611''}  <!<  y524'
//│ ╟── while constraining:  {u: y608'', v: α609''}  <!<  y524'
//│ ╟── while constraining:  {u: y606'', v: α607''}  <!<  y524'
//│ ╟── while constraining:  {u: y604'', v: α605''}  <!<  y524'
//│ ╟── while constraining:  {u: y602'', v: α603''}  <!<  y524'
//│ ╟── while constraining:  {u: y600'', v: α601''}  <!<  y524'
//│ ╟── while constraining:  {u: y598'', v: α599''}  <!<  y524'
//│ ╟── while constraining:  {u: y596'', v: α597''}  <!<  y524'
//│ ╟── while constraining:  {u: y594'', v: α595''}  <!<  y524'
//│ ╟── while constraining:  {u: y592'', v: α593''}  <!<  y524'
//│ ╟── while constraining:  {u: y590'', v: α591''}  <!<  y524'
//│ ╟── while constraining:  {u: y588'', v: α589''}  <!<  y524'
//│ ╟── while constraining:  {u: y586'', v: α587''}  <!<  y524'
//│ ╟── while constraining:  {u: y584'', v: α585''}  <!<  y524'
//│ ╟── while constraining:  {u: y582'', v: α583''}  <!<  y524'
//│ ╟── while constraining:  {u: y580'', v: α581''}  <!<  y524'
//│ ╟── while constraining:  {u: y578'', v: α579''}  <!<  y524'
//│ ╟── while constraining:  {u: y576'', v: α577''}  <!<  y524'
//│ ╟── while constraining:  {u: y574'', v: α575''}  <!<  y524'
//│ ╟── while constraining:  {u: y572'', v: α573''}  <!<  y524'
//│ ╟── while constraining:  {u: y570'', v: α571''}  <!<  y524'
//│ ╟── while constraining:  {u: y568'', v: α569''}  <!<  y524'
//│ ╟── while constraining:  {u: y566'', v: α567''}  <!<  y524'
//│ ╟── while constraining:  {u: y564'', v: α565''}  <!<  y524'
//│ ╟── while constraining:  {u: y562'', v: α563''}  <!<  y524'
//│ ╟── while constraining:  {u: y560'', v: α561''}  <!<  y524'
//│ ╟── while constraining:  {u: y558'', v: α559''}  <!<  y524'
//│ ╟── while constraining:  {u: y556'', v: α557''}  <!<  y524'
//│ ╟── while constraining:  {u: y554'', v: α555''}  <!<  y524'
//│ ╟── while constraining:  {u: y552'', v: α553''}  <!<  y524'
//│ ╟── while constraining:  {u: y550'', v: α551''}  <!<  y524'
//│ ╟── while constraining:  {u: y548'', v: α549''}  <!<  y524'
//│ ╟── while constraining:  {u: y546'', v: α547''}  <!<  y524'
//│ ╟── while constraining:  {u: y544'', v: α545''}  <!<  y524'
//│ ╟── while constraining:  {u: y542'', v: α543''}  <!<  y524'
//│ ╟── while constraining:  {u: y540'', v: α541''}  <!<  y524'
//│ ╟── while constraining:  {u: y538'', v: α539''}  <!<  y524'
//│ ╟── while constraining:  {u: y536'', v: α537''}  <!<  y524'
//│ ╟── while constraining:  {u: y534'', v: α535''}  <!<  y524'
//│ ╟── while constraining:  {u: y532'', v: α533''}  <!<  y524'
//│ ╟── while constraining:  {u: y530'', v: α531''}  <!<  y524'
//│ ╟── while constraining:  {u: y528'', v: α529''}  <!<  y524'
//│ ╟── while constraining:  {u: y526'', v: α527''}  <!<  y524'
//│ ╟── while constraining:  {u: y522'', v: α523''}  <!<  y524'
//│ ╙── while constraining:  {u: y522'', v: α523''}  <!<  y522''
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

:e
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

:e
(let rec x = (let y = (x x); (z => z)); x)
//│ res: 'x
//│   where
//│     'x :> 'a -> 'a
//│     'a :> 'x

:e
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

:e
(let rec x = (y => (let z = (y x); y)); x)
//│ res: 'x
//│   where
//│     'x :> 'a -> 'a
//│     'a <: 'x -> anything

:e
(x => (let y = (x x.v); 0))
//│ res: ('v -> anything & {v: 'v}) -> 0

:e
let rec x = (let y = (x x); (z => z)); (x (y => y.u)) // [test:T1]
//│ x: 'x
//│   where
//│     'x :> 'a -> 'a
//│     'a :> 'x
//│ res: 'a
//│   where
//│     'a :> forall 'u. ({u: 'u} & 'a) -> ('u | 'a)

:e
:ns
let rec x = (let y = (x x); (z => z))
//│ x: forall 'x, 'a, 'b. 'x
//│   where
//│     'x :> 'b -> 'b
//│        <: 'b & 'x -> 'a
//│     'b :> 'b -> 'b
//│        <: 'a
//│     'a :> 'b -> 'b

