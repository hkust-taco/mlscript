
data Left v
data Right v
//│ Defined class Left
//│ Defined class Right
//│ Left: 'a -> (left & {v: 'a})
//│ Right: 'a -> (right & {v: 'a})

let Either l r = Left l | Right r // TODO actual type parameters
//│ Either: 'a -> 'b -> (left & {v: 'a} | right & {v: 'b})

Either 1 2
//│ res: left & {v: 1} | right & {v: 2}

res.v
//│ res: 2 | 1

