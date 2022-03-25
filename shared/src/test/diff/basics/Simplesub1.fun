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
//│ res: ('a -> ('a & 'b)) -> 'a -> 'b

let twice = f => x => f (f x)
//│ twice: ('a -> ('a & 'b)) -> 'a -> 'b



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


:ds
x => x x
//│ Typed as: (α0 -> α1)
//│  where: α0 <: [[[[([[α0]] -> α1)]]]]
//│ ty[+] (α0 -> α1)
//│ -> Right(DNF((α0 -> α1){}))
//│ DNF[+] DNF((α0 -> α1){})
//│ | ty[-] α0
//│ | | isRecursive TreeMap(α0 -> None, α1 -> None) Some(None)
//│ | | Renewed α0 ~> α2
//│ | | ty[-] [[[[([[α0]] -> α1)]]]]
//│ | | -> Right(DNF(([[α0]] -> α1){}))
//│ | | DNF[-] DNF(([[α0]] -> α1){})
//│ | | ~> α3
//│ | -> Right(DNF(α0))
//│ | DNF[-] DNF(α0)
//│ | ~> α2
//│ | ty[+] α1
//│ | | isRecursive TreeMap() None
//│ | | Consider α1 List() List()
//│ | | isRecursive TreeMap() None
//│ | -> Right(DNF(α1))
//│ | DNF[+] DNF(α1)
//│ | | Renewed α1 ~> α4
//│ | ~> α4
//│ ~> α3
//│ Canon: α3
//│  where: α2 <: α3, α3 :> (α2 -> α4)
//│ analyze[+] α3       HashSet()
//│ | go α3   ()
//│ | | α3 false
//│ | | go (α2 -> α4)   (α3)
//│ | | | analyze[+] (α2 -> α4)       HashSet((α3,true))
//│ | | | | analyze[-] α2       HashSet((α3,true), ((α2 -> α4),true))
//│ | | | | | go α2   ()
//│ | | | | | | α2 false
//│ | | | | | | go α3   (α2)
//│ | | | | | | | α3 false
//│ | | | | | >>>> α2 HashSet(α2, α3) None
//│ | | | | | >>>> α3 HashSet(α2, α3) None
//│ | | | | analyze[+] α4       HashSet((α2,false), (α3,true), ((α2 -> α4),true))
//│ | | | | | go α4   ()
//│ | | | | | | α4 false
//│ | | | | | >>>> α4 HashSet(α4) None
//│ | >>>> α3 HashSet(α3, (α2 -> α4)) None
//│ [occs] -α2 {α2,α3} ; -α3 {α2,α3} ; +α4 {α4} ; +α3 {α3,(α2 -> α4)}
//│ [vars] TreeSet(α2, α3, α4)
//│ [bounds] α2 <: α3, α3 :> (α2 -> α4)
//│ [rec] HashSet(α2, α3)
//│ [!] α4
//│ [v] α2 None Some(HashSet(α2, α3))
//│ [w] α3 Some(HashSet(α2, α3))
//│ [U] α3 := α2
//│ [sub] α3 -> Some(α2), α4 -> None
//│ Renewed α2 ~> α5
//│ Type after simplification: α5
//│  where: α5 :> (α5 -> ⊥) <: α5
//│ recons[+] α5  (TypeVariable)
//│ | recons[+] (α5 -> ⊥)  (FunctionType)
//│ | | recons[-] α5  (TypeVariable)
//│ | | => α6
//│ | | recons[+] ⊥  (ExtrType)
//│ | | => ⊥
//│ | => (α6 -> ⊥)
//│ | recons[-] α5  (TypeVariable)
//│ | => α6
//│ => α6
//│ Recons: α6
//│  where: α6 :> (α6 -> ⊥) <: α6
//│ allVarPols: =α6
//│ res: 'a -> nothing as 'a

res id
//│ res: (('b & 'c) -> 'a as 'a) | 'c


let f = (x => x + 1); {a: f; b: f 2}
//│ f: int -> int
//│ res: {a: int -> int, b: int}

x => x x x
//│ res: ('b -> 'a as 'b) -> 'c as 'a

x => y => x y x
//│ res: ('a -> 'b -> 'c & 'b) -> 'a -> 'c

x => y => x x y
//│ res: 'a -> 'b -> 'c as 'a

(x => x x) (x => x x)
//│ res: nothing


x => {l: x x, r: x }
//│ res: ('a -> 'b as 'a) -> {l: 'b, r: nothing as 'a}


// From https://github.com/stedolan/mlsub
// Y combinator:
(f => (x => f (x x)) (x => f (x x)))
//│ res: ('a -> 'a) -> 'a

// Z combinator:
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v)))
//│ res: (('a -> 'b) -> ('a -> 'b & 'c)) -> 'c

// Function that takes arbitrarily many arguments:
(f => (x => f (v => (x x) v)) (x => f (v => (x x) v))) (f => x => f)
//│ res: anything -> (anything -> 'a as 'a)


let rec trutru = g => trutru (g true)
//│ trutru: (true -> 'a as 'a) -> nothing

i => if ((i i) true) then true else true
//│ res: ('a -> true -> bool as 'a) -> true
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
//│ res: ('a -> anything as 'a) -> 0

(let rec x = (y => (y (x x))); x)
//│ res: ('b -> ('c & 'a) as 'a) -> 'c

next => 0
//│ res: anything -> 0

((x => (x x)) (x => x))
//│ res: (('b & 'c) -> 'a as 'a) | 'c

(let rec x = (y => (x (y y))); x)
//│ res: ('a -> 'a as 'a) -> nothing

x => (y => (x (y y)))
//│ res: ('a -> 'b) -> ('c -> 'a as 'c) -> 'b

(let rec x = (let y = (x x); (z => z)); x)
//│ res: ('b & anything) -> 'a as 'a

(let rec x = (y => (let z = (x x); y)); x)
//│ res: ('b & anything) -> 'a as 'a

(let rec x = (y => {u: y, v: (x x)}); x)
//│ res: 'b -> ({u: 'a, v: 'c} as 'c) as 'a

(let rec x = (y => {u: (x x), v: y}); x)
//│ res: 'b -> ({u: 'c, v: 'a} as 'c) as 'a

(let rec x = (y => (let z = (y x); y)); x)
//│ res: ('a -> anything & 'b) -> 'b as 'a

(x => (let y = (x x.v); 0))
//│ res: ('a -> anything & {v: 'a}) -> 0

let rec x = (let y = (x x); (z => z)); (x (y => y.u)) // [test:T1]
//│ x: ('b & anything) -> 'a as 'a
//│ res: ({u: 'a} & 'b & 'c & anything) -> ('a | ({u: 'a} -> 'a | 'd -> 'd as 'd)) | 'c

