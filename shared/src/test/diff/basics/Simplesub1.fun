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
//│ ╟── this constraint:  ‹∀ 0. (α224' -> α225')›  <:  α229    PolymorphicType  TypeVariable
//│ ╙──  ... looks like:  ‹∀ 0. (α224' -> α225')›  <:  α224'
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
//│ ╟── this constraint:  ‹∀ 0. {(α244' -> α246') where: α240 <: (α245' -> α246')}›  <:  α253    PolymorphicType  TypeVariable
//│ ╙──  ... looks like:  ‹∀ 0. {(α244' -> α246') where: α240 <: (α245' -> α246')}›  <:  α244'
//│ res: ('a -> 'b & nothing -> 'c & 'c -> 'a) -> (error | 'b)

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

:e
y => (let f = x => y x; {a: f 0, b: f true})
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	y => (let f = x => y x; {a: f 0, b: f true})
//│ ║        	                   ^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α393  <:  (α396 -> α397)    TypeVariable  FunctionType
//│ ╙──  ... looks like:  α393  <:  (α394' -> α395')
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	y => (let f = x => y x; {a: f 0, b: f true})
//│ ║        	                            ^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  0<int,number>  <:  α396    ClassTag  TypeVariable
//│ ╙──  ... looks like:  0<int,number>  <:  α394'
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	y => (let f = x => y x; {a: f 0, b: f true})
//│ ║        	                                    ^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  true<bool>  <:  α396    ClassTag  TypeVariable
//│ ╙──  ... looks like:  true<bool>  <:  α394'
//│ res: anything -> {a: error, b: error}

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
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ║        	                                    ^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  x485'  <:  (y488' -> α489')    TypeVariable  FunctionType
//│ ╙──  ... looks like:  x485'  <:  (y486'' -> α487'')
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of record
//│ ║  l.+1: 	let rec x = (let rec y = {u: y, v: (x y)}; 0); 0
//│ ║        	                         ^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  {u: y486'', v: α487''}  <:  y488'    RecordType  TypeVariable
//│ ╙──  ... looks like:  {u: y486'', v: α487''}  <:  y486''
//│ x: 0
//│ res: 0

:e
(x => (let y = (x x); 0))
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	(x => (let y = (x x); 0))
//│ ║        	                ^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α491  <:  (α491 -> α493)    TypeVariable  FunctionType
//│ ╙──  ... looks like:  α491  <:  (α491 -> α492')
//│ res: anything -> 0

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
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	(let rec x = (let y = (x x); (z => z)); x)
//│ ║        	                       ^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  x542'  <:  (x542' -> α544')    TypeVariable  FunctionType
//│ ╙──  ... looks like:  x542'  <:  (x542' -> α543'')
//│ res: 'a -> 'a

:e
(let rec x = (y => (let z = (x x); y)); x)
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	(let rec x = (y => (let z = (x x); y)); x)
//│ ║        	                             ^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  x550'  <:  (x550' -> α553')    TypeVariable  FunctionType
//│ ╙──  ... looks like:  x550'  <:  (x550' -> α552'')
//│ res: 'a -> 'a

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
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	(let rec x = (y => (let z = (y x); y)); x)
//│ ║        	                             ^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α583'  <:  (x582' -> α585')    TypeVariable  FunctionType
//│ ╙──  ... looks like:  α583'  <:  (x582' -> α584'')
//│ res: 'a -> 'a

:e
(x => (let y = (x x.v); 0))
//│ ╔══[ERROR] Cyclic-looking constraint while typing field selection
//│ ║  l.+1: 	(x => (let y = (x x.v); 0))
//│ ║        	                   ^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α590  <:  {v: v592}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α590  <:  {v: v591'}
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	(x => (let y = (x x.v); 0))
//│ ║        	                ^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α590  <:  (v594 -> α595)    TypeVariable  FunctionType
//│ ╙──  ... looks like:  α590  <:  (v591' -> α593')
//│ res: anything -> 0

:e
let rec x = (let y = (x x); (z => z)); (x (y => y.u)) // [test:T1]
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	let rec x = (let y = (x x); (z => z)); (x (y => y.u)) // [test:T1]
//│ ║        	                      ^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  x597'  <:  (x597' -> α599')    TypeVariable  FunctionType
//│ ╙──  ... looks like:  x597'  <:  (x597' -> α598'')
//│ x: 'a -> 'a
//│ res: {u: 'u} -> 'u

:e
:ns
let rec x = (let y = (x x); (z => z))
//│ ╔══[ERROR] Cyclic-looking constraint while typing application
//│ ║  l.+1: 	let rec x = (let y = (x x); (z => z))
//│ ║        	                      ^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  x615'  <:  (x615' -> α617')    TypeVariable  FunctionType
//│ ╙──  ... looks like:  x615'  <:  (x615' -> α616'')
//│ x: forall 'x, 'a. 'x
//│   where
//│     'x :> 'a -> 'a

