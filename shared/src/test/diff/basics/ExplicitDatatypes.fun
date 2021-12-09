
data Left v
data Right v
//│ Defined class Left
//│ Defined class Right
//│ Left: 'a -> (left & {Left#v = 'a, v: 'a})
//│ Right: 'a -> (right & {Right#v = 'a, v: 'a})

let Either l r = Left l | Right r // TODO actual type parameters
//│ Either: 'a -> 'b -> (left & {Left#v = 'a, v: 'a} | right & {Right#v = 'b, v: 'b})

Either 1 2
//│ res: left & {Left#v :> 'a <: 1 | 'a, v: 1 | 'a} | right & {Right#v :> 'b <: 2 | 'b, v: 2 | 'b}

res.v
//│ res: 1 | 2

