
:p
data type Either l r of
  Left l
  Right r
//│ Parsed: data type ((Either l) r) of (Left l); (Right r);;
//│ Desugared: type alias Either[l, r] = Left[l, r] | Right[l, r]
//│ Desugared: class Left[l, r]: {l: l}
//│ Desugared: class Right[l, r]: {r: r}
//│ Desugared: def Left: [l, r] -> l -> Left[l, r]
//│ Desugared: def Right: [l, r] -> r -> Right[l, r]
//│ Defined type alias Either
//│ Defined class Left
//│ Defined class Right
//│ Left: 'a -> (left & {Left#r: 'b, Left#l: 'a, l: 'a})
//│ Right: 'a -> (right & {r: 'a, Right#r: 'a, Right#l: 'b})

:e
data type Either2 (l: _) (r: _) of
  Left2 l
  Right2 r
//│ ╔══[ERROR] illegal datatype type parameter shape: ((l: _,);)
//│ ║  l.19: 	data type Either2 (l: _) (r: _) of
//│ ╙──      	                  ^^^^^^
//│ ╔══[ERROR] illegal datatype type parameter shape: ((r: _,);)
//│ ║  l.19: 	data type Either2 (l: _) (r: _) of
//│ ╙──      	                         ^^^^^^
//│ ╔══[ERROR] type identifier not found: l
//│ ║  l.20: 	  Left2 l
//│ ╙──      	        ^
//│ ╔══[ERROR] type identifier not found: r
//│ ║  l.21: 	  Right2 r
//│ ╙──      	         ^
//│ Defined type alias Either2
//│ Defined class Left2
//│ Defined class Right2
//│ Left2: 'a -> (left2 & {Left2#l: 'a, l: 'a})
//│ Right2: 'a -> (right2 & {r: 'a, Right2#r: 'a})

let l = Left 1
let r = Right "ok"
let e = if _ then l else r
//│ l: left & {Left#r: 'a, Left#l: 'b | 1 .. 'b, l: 'b | 1}
//│ r: right & {r: 'a | "ok", Right#r: 'a | "ok" .. 'a, Right#l: 'b}
//│ e: left & {Left#r: 'a, Left#l: 'b | 1 .. 'b, l: 'b | 1} | right & {r: 'c | "ok", Right#r: 'c | "ok" .. 'c, Right#l: 'd}

:e // TODO
e as Either Int String
//│ ╔══[ERROR] Unsupported pattern shape:
//│ ║  l.48: 	e as Either Int String
//│ ╙──      	     ^^^^^^^^^^^^^^^^^
//│ res: error

// TODO
// e as (_: Either Int String)
// e as (_: Either (L: Int) (R: String))

:e
e as Either
//│ ╔══[ERROR] identifier not found: Either
//│ ║  l.59: 	e as Either
//│ ╙──      	     ^^^^^^
//│ res: error


