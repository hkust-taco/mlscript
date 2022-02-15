
data Left v
data Right v
//│ Defined class Left
//│ Defined class Right
//│ Left: 'a -> Left['a]
//│ Right: 'a -> Right['a]

let Either l r = Left l | Right r // TODO actual type parameters
//│ Either: 'a -> (forall 'b, 'c. 'b -> (Left['c .. 'a | 'c] | Right['b]))

Either 1 2
//│ res: Left['a] | Right['b .. 2 | 'b]

res.v
//│ res: 2

