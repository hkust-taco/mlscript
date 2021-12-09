
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
//│ res: 'a -> ((1, 'c | 'b | 'a,) as 'b)

twice / x => x, x
//│ res: 'a -> (('c | 'b | 'a, 'c | 'b | 'a,) as 'b)

:e
let one = twice (o => o.x) { x: { x: 1 } }
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.26: 	let one = twice (o => o.x) { x: { x: 1 } }
//│ ║        	          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `1` does not have field 'x'
//│ ║  l.26: 	let one = twice (o => o.x) { x: { x: 1 } }
//│ ║        	                                     ^
//│ ╟── but it flows into record with expected type `{x: ?a}`
//│ ║  l.26: 	let one = twice (o => o.x) { x: { x: 1 } }
//│ ║        	                           ^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.26: 	let one = twice (o => o.x) { x: { x: 1 } }
//│ ║        	                       ^^
//│ ╟── from argument:
//│ ║  l.2: 	let twice f x = f / f x
//│ ╙──     	                    ^^^
//│ one: 1 | error | {x: 1}


