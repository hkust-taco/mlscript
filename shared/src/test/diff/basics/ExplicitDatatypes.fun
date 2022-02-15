
data Left v
data Right v
//│ Defined class Left
//│ Defined class Right
//│ Left: 'a -> Left['a]
//│ Right: 'a -> Right['a]

let Either l r = Left l | Right r // TODO actual type parameters
//│ Either: 'a -> 'b -> (Left['a] | Right['b])

Either 1 2
//│ res: Left['a .. 1 | 'a] | Right['b .. 2 | 'b]

res.v
//│ res: 1 | 2

