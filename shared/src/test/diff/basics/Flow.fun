
data L x
data R x
//│ L: 'a -> {x: 'a}
//│ R: 'a -> {x: 'a}

// TODO flow-type
:e
let f x = if x is L y then y else 0
//│ ╔══[ERROR] identifier not found: y
//│ ║  l.9: 	let f x = if x is L y then y else 0
//│ ╙──     	                           ^
//│ f: L 'a -> error | 0

// TODO
// true and false
// :e
// 1 and 2

