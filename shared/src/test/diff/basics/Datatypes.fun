
// FIXME
data type Bool of True, False
//│ Bool: True | False
//│ True: anything
//│ False: anything

:e
data type Bool of True & False
//│ ╔══[ERROR] Illegal use of operator: &
//│ ║  l.9: 	data type Bool of True & False
//│ ╙──     	                       ^
//│ Bool: True & False
//│ &: True -> False -> anything

data type Bool of
  True; False
//│ Bool: True | False
//│ True: anything
//│ False: anything

data type Bool of
  True
  False
//│ Bool: True | False
//│ True: anything
//│ False: anything

Bool
True
//│ res: Bool
//│ res: True
:e // FIXME
True as Bool
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.34: 	True as Bool
//│ ║        	^^^^^^^^^^^^
//│ ╟── expression of type `anything` does not match type `False`
//│ ║  l.23: 	  True
//│ ║        	  ^^^^
//│ ╟── but it flows into reference with expected type `Bool`
//│ ║  l.34: 	True as Bool
//│ ║        	^^^^
//│ ╟── Note: constraint arises from data symbol:
//│ ║  l.24: 	  False
//│ ║        	  ^^^^^
//│ ╟── from data type symbol:
//│ ║  l.22: 	data type Bool of
//│ ║        	          ^^^^
//│ ╟── from reference:
//│ ║  l.34: 	True as Bool
//│ ╙──      	        ^^^^
//│ res: Bool

// TODO treat the ending curly-blocks as bodies (not params)?
data type List of
  Nil { T: Nothing }
  Cons head tail { T: head | tail.T }
//│ List: Nil {T: 'a} | Cons 'b 'c {T: 'd}
//│ Nil: {T: 'a & nothing} -> {T: 'a}
//│ Cons: 'a -> 'b & {T: anything} -> {T: 'c & ('a | anything)} -> {T: 'c, head: 'a, tail: 'b}

// TODO also try the one-line version:
// data type List of Nil { T: Nothing }, Cons head tail { T: head | tail.T }


data type List a of // FIXME param type becomes 'anything'
  Nil
  Cons (head: a) (tail: List a) // FIXME type of 'tail'; absence of type "a"
//│ List: anything -> Nil | Cons (head: 'a,) (tail: 'b,)
//│ Nil: anything
//│ Cons: (head: 'a,) -> (tail: 'b,) -> {head: 'a, tail: 'b}

Nil
Cons
Cons 1
Cons 2 Nil // TODO the type repr should be desugared to Cons (head: 1) (tail: Nil)
//│ res: Nil
//│ res: Cons
//│ res: Cons 1
//│ res: Cons 2 Nil

(Cons 3 Nil).head
succ (Cons 3 Nil).head
not (Cons false Nil).head
//│ res: 3
//│ res: int
//│ res: bool

:e
not (Cons 42 Nil).head
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.91: 	not (Cons 42 Nil).head
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `42` does not match type `bool`
//│ ║  l.91: 	not (Cons 42 Nil).head
//│ ║        	          ^^
//│ ╟── but it flows into field selection with expected type `bool`
//│ ║  l.91: 	not (Cons 42 Nil).head
//│ ╙──      	                 ^^^^^
//│ res: bool | error

:e
(Cons 4).head
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.104: 	(Cons 4).head
//│ ║         	        ^^^^^
//│ ╟── expression of type `(tail: ?a,) -> {head: ?b | 4, tail: ?a}` does not have field 'head'
//│ ║  l.69: 	  Cons (head: a) (tail: List a) // FIXME type of 'tail'; absence of type "a"
//│ ║        	  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from applied expression:
//│ ║  l.104: 	(Cons 4).head
//│ ╙──       	 ^^^^
//│ res: error

// FIXME
Cons 1 2
//│ res: Cons 1 2

// TODO Allow method/field defintions in the same file (lose the let?):
:e
let List.head = () // ...
//│ ╔══[ERROR] Unsupported pattern shape
//│ ║  l.122: 	let List.head = () // ...
//│ ╙──       	        ^^^^^
//│ <error>: ()


