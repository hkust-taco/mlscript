
data Left v
data Right v
//│ Defined class Left
//│ Defined class Right
//│ Left: 'a -> (left & {v: 'a, Left#v = 'a})
//│ Right: 'a -> (right & {v: 'a, Right#v = 'a})

let Either l r = Left l | Right r // TODO actual type parameters
//│ Either: 'a -> 'b -> (left & {v: 'a, Left#v = 'a} | right & {v: 'b, Right#v = 'b})

Either 1 2
//│ res: left & {v: 'a | 1, Left#v :> 'a | 1 <: 'a} | right & {v: 'b | 2, Right#v :> 'b | 2 <: 'b}

res.v
//│ res: 2 | 1

