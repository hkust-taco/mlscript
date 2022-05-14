

// :ds
x => x x
//│ res: ('a -> 'b & 'a) -> 'b


// TODO simplifify more
// :ds
(let rec x = (y => (y (x x))); x)
//│ res: 'a -> 'b
//│   where
//│     'a <: 'b -> 'b
//│     'b <: 'a


// :ds
let rec consume = strm => add strm.head (consume strm.tail)
//│ consume: 'a -> int
//│   where
//│     'a <: {head: int, tail: 'a}

