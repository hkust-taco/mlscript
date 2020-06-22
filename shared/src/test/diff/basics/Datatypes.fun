
// FIXME
data type Bool of True, False
//│ Bool: True | False
//│ True: {}
//│ False: {}

:e
data type Bool of True & False
//│ ╔══[ERROR] Illegal use of operator: &
//│ ║  l.9: 	data type Bool of True & False
//│ ╙──     	                       ^
//│ Bool: True & False
//│ &: True -> False -> {}

data type Bool of
  True; False
//│ Bool: True | False
//│ True: {}
//│ False: {}

data type Bool of
  True
  False
//│ Bool: True | False
//│ True: {}
//│ False: {}

Bool
True
//│ res: Bool
//│ res: True
:e // FIXME
True as Bool
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.34: 	True as Bool
//│ ║        	^^^^^^^^^^^^
//│ ╟── expression of type `{}` does not match type `False`
//│ ║  l.23: 	  True
//│ ║        	  ^^^^
//│ ╟── but it flows into variable reference of expected type `Bool`
//│ ║  l.34: 	True as Bool
//│ ║        	^^^^
//│ ╟── Note: constraint arises from data symbol:
//│ ║  l.24: 	  False
//│ ║        	  ^^^^^
//│ ╟── from data type symbol:
//│ ║  l.22: 	data type Bool of
//│ ║        	          ^^^^
//│ ╟── from variable reference:
//│ ║  l.34: 	True as Bool
//│ ╙──      	        ^^^^
//│ res: Bool

:e // TODO
data type List of
  Nil { T: Nothing }
  Cons head tail { T: head | tail.T }
//│ ╔══[ERROR] Unsupported pattern shape:
//│ ║  l.57: 	  Nil { T: Nothing }
//│ ╙──      	      ^^^^^^^^^^^^^^
//│ ╔══[ERROR] Unsupported pattern shape:
//│ ║  l.58: 	  Cons head tail { T: head | tail.T }
//│ ╙──      	                 ^^^^^^^^^^^^^^^^^^^^
//│ List: Nil error | Cons 'a 'b error
//│ Nil: error -> {}
//│ Cons: 'a -> 'b -> error -> {head: 'a, tail: 'b}

// TODO also try the one-line version:
// data type List of Nil { T: Nothing }, Cons head tail { T: head | tail.T }


data type List a of // FIXME param type becomes 'anything'
  Nil
  Cons (head: a) (tail: List a) // FIXME type of 'tail'; absence of type "a"
//│ List: anything -> Nil | Cons (head: 'a,) (tail: 'b,)
//│ Nil: {}
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
//│ ║  l.97: 	not (Cons 42 Nil).head
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `42` does not match type `bool`
//│ ║  l.97: 	not (Cons 42 Nil).head
//│ ║        	          ^^
//│ ╟── but it flows into field selection of expected type `bool`
//│ ║  l.97: 	not (Cons 42 Nil).head
//│ ╙──      	                 ^^^^^
//│ res: bool | error

:e
(Cons 4).head
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.110: 	(Cons 4).head
//│ ║         	        ^^^^^
//│ ╟── expression of type `(tail: ?a,) -> {head: ?b | 4, tail: ?a}` does not have field 'head'
//│ ║  l.75: 	  Cons (head: a) (tail: List a) // FIXME type of 'tail'; absence of type "a"
//│ ║        	  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from applied expression:
//│ ║  l.110: 	(Cons 4).head
//│ ╙──       	 ^^^^
//│ res: error

// TODO Allow method/field defintions in the same file (lose the let?):
:e
let List.head = () // ...
//│ ╔══[ERROR] Unsupported pattern shape
//│ ║  l.124: 	let List.head = () // ...
//│ ╙──       	        ^^^^^
//│ <error>: ()


