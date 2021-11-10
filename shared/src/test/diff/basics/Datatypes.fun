
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

// FIXME later
:e // FIXME
True as Bool
//│ /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
//│ 	at: scala.Predef$.$qmark$qmark$qmark(Predef.scala:344)
//│ 	at: mlscript.NormalForms$LhsNf.$amp(NormalForms.scala:32)
//│ 	at: mlscript.NormalForms$LhsNf.$amp(NormalForms.scala:45)
//│ 	at: mlscript.NormalForms$Conjunct.$amp(NormalForms.scala:135)
//│ 	at: mlscript.NormalForms$DNF.$anonfun$$amp$8(NormalForms.scala:190)
//│ 	at: scala.collection.immutable.List.flatMap(List.scala:293)
//│ 	at: mlscript.NormalForms$DNF.$amp(NormalForms.scala:190)
//│ 	at: mlscript.NormalForms$DNF.$anonfun$$amp$6(NormalForms.scala:187)
//│ 	at: scala.collection.immutable.List.map(List.scala:246)
//│ 	at: mlscript.NormalForms$DNF.$amp(NormalForms.scala:187)

// TODO treat the ending curly-blocks as bodies (not params)?
data type List of
  Nil { T: Nothing }
  Cons head tail { T: head | tail.T }
//│ List: Nil {T: nothing} | Cons nothing nothing {T: nothing}
//│ Nil: {T: nothing} -> {T: nothing}
//│ Cons: 'a -> {T: anything} & 'b -> {T: 'c} -> {T: 'c, head: 'a, tail: 'b}

// TODO also try the one-line version:
// data type List of Nil { T: Nothing }, Cons head tail { T: head | tail.T }


data type List a of // FIXME param type becomes 'anything'
  Nil
  Cons (head: a) (tail: List a) // FIXME type of 'tail'; absence of type "a"
//│ List: anything -> Nil | Cons (head: nothing,) (tail: nothing,)
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
//│ ║  l.85: 	not (Cons 42 Nil).head
//│ ║        	^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `42` does not match type `bool`
//│ ║  l.85: 	not (Cons 42 Nil).head
//│ ║        	          ^^
//│ ╟── but it flows into field selection with expected type `bool`
//│ ║  l.85: 	not (Cons 42 Nil).head
//│ ╙──      	                 ^^^^^
//│ res: bool | error

:e
(Cons 4).head
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.98: 	(Cons 4).head
//│ ║        	        ^^^^^
//│ ╟── expression of type `(tail: ?a,) -> {head: ?b | 4, tail: ?a}` does not have field 'head'
//│ ║  l.63: 	  Cons (head: a) (tail: List a) // FIXME type of 'tail'; absence of type "a"
//│ ║        	  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from applied expression:
//│ ║  l.98: 	(Cons 4).head
//│ ╙──      	 ^^^^
//│ res: error

// FIXME
Cons 1 2
//│ res: Cons 1 2

// TODO Allow method/field defintions in the same file (lose the let?):
:e
let List.head = () // ...
//│ ╔══[ERROR] Unsupported pattern shape
//│ ║  l.116: 	let List.head = () // ...
//│ ╙──       	        ^^^^^
//│ <error>: ()


