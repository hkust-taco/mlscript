
data Left v
data Right v
//│ Left: 'a -> {v: 'a}
//│ Right: 'a -> {v: 'a}

:e // TODO
let Either l r = Left l | Right r // TODO actual type bindings
//│ ╔══[ERROR] unexpected use of: |
//│ ║  l.8: 	let Either l r = Left l | Right r // TODO actual type bindings
//│ ╙──     	                        ^
//│ ╔══[ERROR] identifier not found: |
//│ ║  l.8: 	let Either l r = Left l | Right r // TODO actual type bindings
//│ ╙──     	                        ^
//│ Either: error -> error -> error
