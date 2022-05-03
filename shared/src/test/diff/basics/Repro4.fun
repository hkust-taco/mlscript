

// :ds
x => x x
//│ res: ('a -> 'b & 'a) -> 'b


// TODO-simplif
// :ds
(let rec x = (y => (y (x x))); x)
//│ res: 'b -> 'c as 'a
//│ 	where
//│ 		'b :> 'a
//│ 		   <: 'c -> ('c & 'b)


// :ds
let rec consume = strm => add strm.head (consume strm.tail)
//│ consume: ({head: int, tail: 'a} as 'a) -> int

