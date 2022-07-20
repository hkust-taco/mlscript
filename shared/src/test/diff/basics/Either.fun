
:p
:w
data type Either l r of
  Left l
  Right r
//│ Parsed: data type Either l r of {Left l; Right r};
//│ Desugared: type alias Either[l, r] = Left[l, r] | Right[l, r]
//│ Desugared: class Left[l, r]: {l: l}
//│ Desugared: class Right[l, r]: {r: r}
//│ Desugared: def Left: [l, r] -> l -> Left[l, r]
//│ Desugared: def Right: [l, r] -> r -> Right[l, r]
//│ Defined type alias Either[+l, +r]
//│ Defined class Left[+l, ±r]
//│ Defined class Right[±l, +r]
//│ ╔══[WARNING] Type definition Left has bivariant type parameters:
//│ ║  l.5: 	  Left l
//│ ║       	  ^^^^
//│ ╟── r is irrelevant and may be removed
//│ ║  l.4: 	data type Either l r of
//│ ╙──     	                   ^
//│ ╔══[WARNING] Type definition Right has bivariant type parameters:
//│ ║  l.6: 	  Right r
//│ ║       	  ^^^^^
//│ ╟── l is irrelevant and may be removed
//│ ║  l.4: 	data type Either l r of
//│ ╙──     	                 ^
//│ Left: 'a -> Left['a, ?]
//│ Right: 'a -> Right[?, 'a]

:e
data type Either2 (l: _) (r: _) of
  Left2 l
  Right2 r
//│ ╔══[ERROR] illegal datatype type parameter shape: '(' {l: _,} ')'
//│ ║  l.32: 	data type Either2 (l: _) (r: _) of
//│ ╙──      	                  ^^^^^^
//│ ╔══[ERROR] illegal datatype type parameter shape: '(' {r: _,} ')'
//│ ║  l.32: 	data type Either2 (l: _) (r: _) of
//│ ╙──      	                         ^^^^^^
//│ ╔══[ERROR] type identifier not found: l
//│ ║  l.33: 	  Left2 l
//│ ╙──      	        ^
//│ ╔══[ERROR] type identifier not found: r
//│ ║  l.34: 	  Right2 r
//│ ╙──      	         ^
//│ Defined type alias Either2
//│ Defined class Left2[+l]
//│ Defined class Right2[+r]
//│ Left2: 'a -> Left2['a]
//│ Right2: 'a -> Right2['a]

let l = Left 1
let r = Right "ok"
let e = if _ then l else r
//│ l: Left[1, ?]
//│ r: Right[?, "ok"]
//│ e: Left[1, ?] | Right[?, "ok"]

:e // TODO
e as Either Int String
//│ ╔══[ERROR] Unsupported pattern shape:
//│ ║  l.61: 	e as Either Int String
//│ ╙──      	     ^^^^^^^^^^^^^^^^^
//│ res: error

// TODO
// e as (_: Either Int String)
// e as (_: Either (L: Int) (R: String))

:e
e as Either
//│ ╔══[ERROR] identifier not found: Either
//│ ║  l.72: 	e as Either
//│ ╙──      	     ^^^^^^
//│ res: error


