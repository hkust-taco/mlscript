
data Left v
data Right v
//│ Defined class Left[+v]
//│ Defined class Right[+v]
//│ Left: 'a -> Left['a]
//│ Right: 'a -> Right['a]

let Either l r = Left l | Right r // TODO actual type parameters
//│ Either: 'a -> 'b -> (Left['a] | Right['b])

Either 1 2
//│ res: Left[1] | Right[2]

res.v
//│ res: 1 | 2

