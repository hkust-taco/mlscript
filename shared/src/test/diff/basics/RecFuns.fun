
// From a comment on the Simple-sub blog post:

let rec r a = r
//│ r: 'a
//│   where
//│     'a :> anything -> 'a

let join a b = if true then a else b
//│ join: 'a -> 'a -> 'a

// "Lateral" hash consing
let s = join r r
//│ s: anything -> ('a | 'b)
//│   where
//│     'b :> anything -> 'b
//│     'a :> anything -> 'a

