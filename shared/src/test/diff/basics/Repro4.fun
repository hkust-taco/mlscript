
// TODO-simplif
// :ds
(let rec x = (y => (y (x x))); x)
//│ res: ('b -> ('c & 'b) as 'a) -> 'c
//│ 	where
//│ 		'b <: 'a

