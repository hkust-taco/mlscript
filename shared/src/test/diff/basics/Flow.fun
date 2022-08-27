
:p
data L x
data R x
//│ Parsed: data L x; data R x;
//│ Desugared: class L[x]: {x: x}
//│ Desugared: class R[x]: {x: x}
//│ Desugared: def L: [x] -> x -> L[x]
//│ Desugared: def R: [x] -> x -> R[x]
//│ Defined class L[+x]
//│ Defined class R[+x]
//│ L: 'a -> L['a]
//│ R: 'a -> R['a]

// TODO flow-type
:e
let f x = if x is L y then y else 0
//│ ╔══[ERROR] Unsupported pattern shape:
//│ ║  l.17: 	let f x = if x is L y then y else 0
//│ ╙──      	                  ^^^
//│ ╔══[ERROR] identifier not found: y
//│ ║  l.17: 	let f x = if x is L y then y else 0
//│ ╙──      	                           ^
//│ f: error -> (0 | error)

// TODO
// true and false
// :e
// 1 and 2

