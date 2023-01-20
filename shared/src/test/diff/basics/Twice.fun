
let twice f x = f / f x
//│ twice: ('a -> 'b & 'c -> 'a) -> 'c -> 'b
// Note: the pretty-printed type of `twice` *used to be* simplified to ('a -> ('a & 'b)) -> 'a -> 'b
//    (another equivalent simplification is ('a | 'b -> 'a) -> 'b -> 'a);
//    this simplification lost some information in the context of first-class polymorphism
//    because function types effectively become non-mergeable without losing precsion...
// (Also see this HN thread: https://news.ycombinator.com/item?id=13783237)

twice(x => x + 1)
//│ res: int -> int

twice twice
//│ res: ('a -> 'b & ('c | 'b) -> 'a) -> 'c -> 'b

let f = x => 1, x
//│ f: 'a -> (1, 'a,)

// Note: now that we instantiate during constraint solving instead of on variable reference,
//    we get the more useful type: 'a -> (1, (1, 'a,),).
//    Previously, we were getting: 'a -> ((1, 'c | 'b | 'a,) as 'b)
twice f
//│ res: 'a -> (1, (1, 'a,),)

twice / x => x, x
//│ res: 'a -> (('a, 'a,), ('a, 'a,),)

let one = twice (o => o.x) { x: { x: 1 } }
//│ one: 1


