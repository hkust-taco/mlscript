
// From a comment on the Simple-sub blog post:

let rec r a = r
//│ r: (anything -> 'a) as 'a

let join a b = if true then a else b
//│ join: 'a -> 'a -> 'a

// TODO lateral hash consing
let s = join r r
//│ s: (anything -> 'a) as 'a | (anything -> 'b) as 'b

