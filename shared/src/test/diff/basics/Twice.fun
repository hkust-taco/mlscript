
let twice f x = f / f x
//│ twice: ('a -> ('a & 'b)) -> 'a -> 'b

twice(x => x + 1)
//│ res: int -> int

twice twice
//│ res: ('a -> ('a & 'b)) -> 'a -> 'b

let f = x => 1, x
//│ f: 'a -> (1, 'a,)

// Note: once we instantiate during constraint solving instead of on variable reference,
//  the following should get the more useful type: 'a -> (1, (1 'a,),)
// Note: but then the pretty-printed type of `twice` should not be simplified to ('a | 'b -> 'a) -> 'b -> 'a
//  because function types would effectively become non-mergeable without losing precsion...
// (I found this example while reading the HN thread: https://news.ycombinator.com/item?id=13783237)
twice f
//│ res: 'a -> 'b
//│   where
//│     'a :> 'b
//│     'b :> (1, 'a,)

// TODO simplify more
// :ds
twice / x => x, x
//│ res: 'a -> 'b
//│   where
//│     'a :> 'b
//│     'b :> ('a, 'a,)

:e
let one = twice (o => o.x) { x: { x: 1 } }
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.34: 	let one = twice (o => o.x) { x: { x: 1 } }
//│ ║        	          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── integer literal of type `1` does not have field 'x'
//│ ║  l.34: 	let one = twice (o => o.x) { x: { x: 1 } }
//│ ║        	                                     ^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.34: 	let one = twice (o => o.x) { x: { x: 1 } }
//│ ╙──      	                       ^^
//│ one: 1 | error | {x: 1}





