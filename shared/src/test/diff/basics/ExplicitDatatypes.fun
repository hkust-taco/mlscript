
data Left v
data Right v
//│ Left: 'a -> {v: 'a}
//│ Right: 'a -> {v: 'a}

let Either l r = Left l | Right r // TODO actual type parameters
//│ Either: 'a -> 'b -> Left 'a | Right 'b


