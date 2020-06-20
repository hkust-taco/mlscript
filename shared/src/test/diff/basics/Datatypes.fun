
// FIXME
data type Bool of True, False
//│ Bool: True | False
//│ True: {}
//│ False: {}

:e
data type Bool of True & False
//│ ╔══[ERROR] unexpected use of: &
//│ ║  l.9: 	data type Bool of True & False
//│ ╙──     	                       ^
//│ Bool: & 'a 'b
//│ &: 'a -> 'b -> {False: 'b, True: 'a}

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

// Bool
True
//│ res: True

:pe // TODO
True as Bool
//│ /!\ Parse error: Expected end-of-input:1:6, found "as Bool" at l.34:6: True as Bool

:e // TODO
data type List of
  Nil { T: Nothing }
  Cons head tail { T: head | tail.T }
//│ ╔══[ERROR] Unsupported parameter shape:
//│ ║  l.39: 	  Nil { T: Nothing }
//│ ╙──      	      ^^^^^^^^^^^^^^
//│ ╔══[ERROR] Unsupported parameter shape:
//│ ║  l.40: 	  Cons head tail { T: head | tail.T }
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
//│ ║  l.79: 	not (Cons 42 Nil).head
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `42` does not match type `bool`
//│ ║  l.79: 	not (Cons 42 Nil).head
//│ ║        	          ^^
//│ ╟── but it flows into field selection of expected type `bool`
//│ ║  l.79: 	not (Cons 42 Nil).head
//│ ╙──      	                 ^^^^^
//│ res: bool | error

:e
(Cons 4).head
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.92: 	(Cons 4).head
//│ ║        	        ^^^^^
//│ ╟── expression of type `(tail: ?a,) -> {head: ?b | 4, tail: ?a}` does not have field 'head'
//│ ║  l.57: 	  Cons (head: a) (tail: List a) // FIXME type of 'tail'; absence of type "a"
//│ ║        	  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from applied expression:
//│ ║  l.92: 	(Cons 4).head
//│ ╙──      	 ^^^^
//│ res: error

// TODO Allow method/field defintions in the same file (lose the let?):
:e
let List.head = () // ...
//│ ╔══[ERROR] Unsupported pattern shape
//│ ║  l.106: 	let List.head = () // ...
//│ ╙──       	        ^^^^^
//│ <error>: ()


