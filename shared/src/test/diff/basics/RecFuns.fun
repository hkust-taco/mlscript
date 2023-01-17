
// From a comment on the Simple-sub blog post:

let rec r a = r
//│ r: 'r
//│   where
//│     'r :> anything -> 'r

let join a b = if true then a else b
//│ join: 'a -> (forall 'b. 'b -> ('a | 'b))

// "Lateral" hash consing
let s = join r r
//│ s: 'r
//│   where
//│     'r :> anything -> 'r

