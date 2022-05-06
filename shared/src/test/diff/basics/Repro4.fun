

// :ds
x => x x
//│ res: ('b & 'a) -> 'c as 'a


// TODO-simplif
// :ds
(let rec x = (y => (y (x x))); x)
//│ res: ('b -> ('b & 'a) as 'a) -> 'b


// :ds
let rec consume = strm => add strm.head (consume strm.tail)
//│ consume: ({head: int, tail: 'a} as 'a) -> int

