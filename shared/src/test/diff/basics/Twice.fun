
let twice f x = f / f x
//│ twice: ('a -> ('a & 'b)) -> 'a -> 'b
// Note: the pretty-printed type of `twice` is simplified (another equivalent simplification is ('a | 'b -> 'a) -> 'b -> 'a);
//    this simplification loses some information in the context of first-class polymorphism
//    because function types effectively become non-mergeable without losing precsion...
// (Also see this HN thread: https://news.ycombinator.com/item?id=13783237)

twice(x => x + 1)
//│ res: int -> int

twice twice
//│ res: ('a -> ('a & 'b)) -> 'a -> 'b

let f = x => 1, x
//│ f: 'a -> (1, 'a,)

// Note: now that we instantiate during constraint solving instead of on variable reference,
//    we get the more useful type: 'a -> (1, (1, 'a,),).
//    Previously, we were getting: 'a -> ((1, 'c | 'b | 'a,) as 'b)
twice f
//│ res: 'a -> (1, (1, 'a,),)

twice / x => x, x
//│ res: 'a -> (('a, 'a,), ('a, 'a,),)

:e
let one = twice (o => o.x) { x: { x: 1 } }
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.28: 	let one = twice (o => o.x) { x: { x: 1 } }
//│ ║        	          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── integer literal of type `1` does not have field 'x'
//│ ║  l.28: 	let one = twice (o => o.x) { x: { x: 1 } }
//│ ║        	                                     ^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.28: 	let one = twice (o => o.x) { x: { x: 1 } }
//│ ╙──      	                       ^^
//│ one: 1 | error | {x: 1}


