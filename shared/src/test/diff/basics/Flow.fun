
:p
data L x
data R x
//│ Parsed: data L x; data R x;
//│ Desugared: class L[x]: {x: x}
//│ Desugared: class R[x]: {x: x}
//│ Desugared: def L: [x] -> x -> L[x]
//│ AST: Def(false, L, PolyType(List(TypeName(x)),Function(TypeName(x),AppliedType(TypeName(L),List(TypeName(x))))), true)
//│ Desugared: def R: [x] -> x -> R[x]
//│ AST: Def(false, R, PolyType(List(TypeName(x)),Function(TypeName(x),AppliedType(TypeName(R),List(TypeName(x))))), true)
//│ Defined class L[+x]
//│ Defined class R[+x]
//│ L: 'a -> L['a]
//│ R: 'a -> R['a]

// TODO flow-type
:e
let f x = if x is L y then y else 0
//│ ╔══[ERROR] Unsupported pattern shape:
//│ ║  l.19: 	let f x = if x is L y then y else 0
//│ ╙──      	                  ^^^
//│ ╔══[ERROR] identifier not found: y
//│ ║  l.19: 	let f x = if x is L y then y else 0
//│ ╙──      	                           ^
//│ f: error -> (0 | error)

// TODO
// true and false
// :e
// 1 and 2

