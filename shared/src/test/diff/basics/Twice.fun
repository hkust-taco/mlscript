
let twice f x = f / f x
//│ twice: ((forall 'a, 'b, 'c. ('c
//│   where
//│     'a <: 'b -> 'c)) -> 'd & 'b -> 'a & 'a) -> 'b -> 'd
// Note: the pretty-printed type of `twice` *used to be* simplified to ('a -> ('a & 'b)) -> 'a -> 'b
//    (another equivalent simplification is ('a | 'b -> 'a) -> 'b -> 'a);
//    this simplification lost some information in the context of first-class polymorphism
//    because function types effectively become non-mergeable without losing precsion...
// (Also see this HN thread: https://news.ycombinator.com/item?id=13783237)

twice(x => x + 1)
//│ res: int -> int

twice twice
//│ res: nothing -> anything -> nothing

let f = x => 1, x
//│ f: 'a -> (1, 'a,)

// Note: now that we instantiate during constraint solving instead of on variable reference,
//    we get the more useful type: 'a -> (1, (1, 'a,),).
//    Previously, we were getting: 'a -> ((1, 'c | 'b | 'a,) as 'b)
twice f
//│ res: 'a -> (1, forall 'b. ('b
//│   where
//│     'c <: 'a -> 'b),)

// TODO simplify more
// :ds
twice / x => x, x
//│ res: 'a -> (forall 'b. ('b
//│   where
//│     'c <: 'a -> 'b), forall 'b. ('b
//│   where
//│     'c <: 'a -> 'b),)

let one = twice (o => o.x) { x: { x: 1 } }
//│ one: 1


