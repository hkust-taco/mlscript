
:p
data type Either L R of
  Left L
  Right R
//│ Parsed: data type ((Either L) R) of (Left L); (Right R);;
//│ Desugared: type Either[L, R] = Left[L, R] | Right[L, R]
//│ Desugared: class Left[L, R]: {L: L}
//│ Desugared: class Right[L, R]: {R: R}
//│ Desugared: def Left: [L, R] -> L -> Left[L, R]
//│ Desugared: def Right: [L, R] -> R -> Right[L, R]
//│ Defined type Either
//│ Defined class Left
//│ Defined class Right
//│ Left: 'a -> left & {L: 'a}
//│ Right: 'a -> right & {R: 'a}

:e
data type Either2 (L: _) (R: _) of
  Left2 L
  Right2 R
//│ ╔══[ERROR] illegal datatype type parameter shape: ((L: _,);)
//│ ║  l.19: 	data type Either2 (L: _) (R: _) of
//│ ╙──      	                  ^^^^^^
//│ ╔══[ERROR] illegal datatype type parameter shape: ((R: _,);)
//│ ║  l.19: 	data type Either2 (L: _) (R: _) of
//│ ╙──      	                         ^^^^^^
//│ ╔══[ERROR] type identifier not found: L
//│ ╙──
//│ ╔══[ERROR] type identifier not found: R
//│ ╙──
//│ Defined type Either2
//│ Defined class Left2
//│ Defined class Right2
//│ Left2: 'a -> left2 & {L: 'a}
//│ Right2: 'a -> right2 & {R: 'a}

let l = Left 1
let r = Right "ok"
let e = if _ then l else r
//│ l: left & {L: 1}
//│ r: right & {R: "ok"}
//│ e: left & {L: 1} | right & {R: "ok"}

:e // TODO
e as Either Int String
//│ ╔══[ERROR] Unsupported pattern shape:
//│ ║  l.46: 	e as Either Int String
//│ ╙──      	     ^^^^^^^^^^^^^^^^^
//│ res: error

// TODO
// e as (_: Either Int String)
// e as (_: Either (L: Int) (R: String))

:e
e as Either
//│ ╔══[ERROR] identifier not found: Either
//│ ║  l.57: 	e as Either
//│ ╙──      	     ^^^^^^
//│ res: error


