
:p
data type Boolean of Tru, Fals
//│ Parsed: data type Boolean of {Tru; Fals};
//│ Desugared: type alias Boolean = Tru[] | Fals[]
//│ Desugared: class Tru: {}
//│ Desugared: class Fals: {}
//│ Desugared: def Tru: Tru[]
//│ AST: Def(false, Tru, PolyType(List(),AppliedType(TypeName(Tru),List())), true)
//│ Desugared: def Fals: Fals[]
//│ AST: Def(false, Fals, PolyType(List(),AppliedType(TypeName(Fals),List())), true)
//│ Defined type alias Boolean
//│ Defined class Tru
//│ Defined class Fals
//│ Tru: Tru
//│ Fals: Fals

:e
Boolean
//│ ╔══[ERROR] identifier not found: Boolean
//│ ║  l.19: 	Boolean
//│ ╙──      	^^^^^^^
//│ res: error

:p
:e
data type Bool2 of True2 & False2
//│ Parsed: data type Bool2 of {& True2 False2};
//│ Desugared: type alias Bool2 = &[True2, False2]
//│ Desugared: class &[True2, False2]: {False2 <: False2, True2 <: True2}
//│ Desugared: def &: forall True2 False2. (...True2) -> (...False2) -> &[True2, False2]
//│ AST: Def(false, &, PolyType(List(Left(TypeName(True2)), Left(TypeName(False2))),Function(TypeName(True2),Function(TypeName(False2),AppliedType(TypeName(&),List(TypeName(True2), TypeName(False2)))))), true)
//│ ╔══[ERROR] type identifier not found: True2
//│ ║  l.27: 	data type Bool2 of True2 & False2
//│ ╙──      	                   ^^^^^
//│ ╔══[ERROR] type identifier not found: False2
//│ ║  l.27: 	data type Bool2 of True2 & False2
//│ ╙──      	                           ^^^^^^
//│ ╔══[ERROR] Type names must start with a capital letter
//│ ║  l.27: 	data type Bool2 of True2 & False2
//│ ╙──      	                         ^
//│ ╔══[ERROR] Field identifiers must start with a small letter
//│ ║  l.27: 	data type Bool2 of True2 & False2
//│ ╙──      	                           ^^^^^^
//│ ╔══[ERROR] Field identifiers must start with a small letter
//│ ║  l.27: 	data type Bool2 of True2 & False2
//│ ╙──      	                   ^^^^^
//│ Defined type alias Bool2
//│ Defined class &[+True2, +False2]
//│ &: 'a -> 'b -> &['a, 'b]

data type Bool3 of
  True3; False3
//│ Defined type alias Bool3
//│ Defined class True3
//│ Defined class False3
//│ True3: True3
//│ False3: False3

data type Bool4 of
  True4
  False4
//│ Defined type alias Bool4
//│ Defined class True4
//│ Defined class False4
//│ True4: True4
//│ False4: False4

:e
Boolean
//│ ╔══[ERROR] identifier not found: Boolean
//│ ║  l.70: 	Boolean
//│ ╙──      	^^^^^^^
//│ res: error

Tru
//│ res: Tru

:e // TODO support types on RHS of `as`
Tru as Boolean
Tru : Boolean
//│ ╔══[ERROR] identifier not found: Boolean
//│ ║  l.80: 	Tru as Boolean
//│ ╙──      	       ^^^^^^^
//│ res: error
//│ ╔══[ERROR] identifier not found: Boolean
//│ ║  l.81: 	Tru : Boolean
//│ ╙──      	      ^^^^^^^
//│ res: (Tru: error,)

:e // Maybe we shouldn't interpret capitalized identifiers as field names...
Tru : Boolean
//│ ╔══[ERROR] identifier not found: Boolean
//│ ║  l.92: 	Tru : Boolean
//│ ╙──      	      ^^^^^^^
//│ res: (Tru: error,)

:pe
(Tru) : Boolean
//│ /!\ Parse error: Expected end-of-input:1:7, found ": Boolean\n" at l.99:7: (Tru) : Boolean


// TODO treat the ending curly-blocks as bodies (not params)?
// data type List of
//   Nil { T: Nothing }
//   Cons head tail { T: head | tail.T }

// TODO also try the one-line version:
// data type List of Nil { T: Nothing }, Cons head tail { T: head | tail.T }

:p
:w
:e
data type List a of
  Nil
  Cons (head: a) (tail: List a)
//│ Parsed: data type List a of {Nil; Cons '(' {head: a,} ')' '(' {tail: List a,} ')'};
//│ ╔══[ERROR] not a recognized type
//│ ║  l.116: 	  Cons (head: a) (tail: List a)
//│ ╙──       	                        ^^^^^^
//│ Desugared: type alias List[a] = Nil[a] | Cons[a]
//│ Desugared: class Nil[a]: {}
//│ Desugared: class Cons[a]: {head: a, tail: anything}
//│ Desugared: def Nil: forall a. Nil[a]
//│ AST: Def(false, Nil, PolyType(List(Left(TypeName(a))),AppliedType(TypeName(Nil),List(TypeName(a)))), true)
<<<<<<< HEAD
//│ Desugared: def Cons: forall a. (head: a,) -> (tail: List[a],) -> Cons[a]
//│ AST: Def(false, Cons, PolyType(List(Left(TypeName(a))),Function(Tuple(List((Some(head),Field(None,TypeName(a),false)))),Function(Tuple(List((Some(tail),Field(None,AppliedType(TypeName(List),List(TypeName(a))),false)))),AppliedType(TypeName(Cons),List(TypeName(a)))))), true)
||||||| a0084daf
//│ Desugared: def Cons: forall a. (head: a,) -> (tail: List[a],) -> Cons[a]
//│ AST: Def(false, Cons, PolyType(List(Left(TypeName(a))),Function(Tuple(List((Some(head),Field(None,TypeName(a))))),Function(Tuple(List((Some(tail),Field(None,AppliedType(TypeName(List),List(TypeName(a))))))),AppliedType(TypeName(Cons),List(TypeName(a)))))), true)
=======
//│ Desugared: def Cons: forall a. (head: a) -> (tail: anything) -> Cons[a]
//│ AST: Def(false, Cons, PolyType(List(Left(TypeName(a))),Function(Tuple(List((Some(head),Field(None,TypeName(a))))),Function(Tuple(List((Some(tail),Field(None,Top)))),AppliedType(TypeName(Cons),List(TypeName(a)))))), true)
>>>>>>> new-definition-typing
//│ Defined type alias List[+a]
//│ Defined class Nil[±a]
//│ Defined class Cons[+a]
//│ ╔══[WARNING] Type definition Nil has bivariant type parameters:
//│ ║  l.115: 	  Nil
//│ ║         	  ^^^
//│ ╟── a is irrelevant and may be removed
//│ ║  l.114: 	data type List a of
//│ ╙──       	               ^
//│ Nil: Nil[?]
//│ Cons: (head: 'a,) -> (tail: anything,) -> Cons['a]

// TODO interpret as free type variable?
:p
data type Ls of LsA a
//│ Parsed: data type Ls of {LsA a};
//│ Desugared: type alias Ls = LsA[a]
//│ Desugared: class LsA[a]: {a: a}
//│ Desugared: def LsA: forall a. (...a) -> LsA[a]
//│ AST: Def(false, LsA, PolyType(List(Left(TypeName(a))),Function(TypeName(a),AppliedType(TypeName(LsA),List(TypeName(a))))), true)
//│ ╔══[ERROR] type identifier not found: a
//│ ║  l.142: 	data type Ls of LsA a
//│ ╙──       	                    ^
//│ Defined type alias Ls
//│ Defined class LsA[+a]
//│ LsA: 'a -> LsA['a]

:p
:e
data type Ls2 of LsA2 `a
//│ Parsed: data type Ls2 of {LsA2 `a};
//│ Desugared: type alias Ls2 = LsA2[]
//│ Desugared: class LsA2: {`a: 'a}
//│ Desugared: def LsA2: (...'a) -> LsA2[]
//│ AST: Def(false, LsA2, PolyType(List(),Function(a,AppliedType(TypeName(LsA2),List()))), true)
//│ ╔══[ERROR] cannot inherit from a polymorphic type
//│ ║  l.157: 	data type Ls2 of LsA2 `a
//│ ╙──       	                 ^^^^^^^
//│ ╔══[ERROR] type identifier not found: LsA2
//│ ╙──
//│ Defined type alias Ls2
//│ ╔══[ERROR] type identifier not found: LsA2
//│ ╙──
//│ LsA2: anything -> error

Nil
Cons
Cons 1
Cons 2 Nil
Cons 1 (Cons 2 Nil)
//│ res: Nil[?]
//│ res: (head: 'a,) -> (tail: anything,) -> Cons['a]
//│ res: (tail: anything,) -> Cons[1]
//│ res: Cons[2]
//│ res: Cons[1]

(Cons 3 Nil).head
succ (Cons 3 Nil).head
not (Cons false Nil).head
//│ res: 3
//│ res: int
//│ res: bool

:e
not (Cons 42 Nil).head
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.192: 	not (Cons 42 Nil).head
//│ ║         	^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── integer literal of type `42` is not an instance of type `bool`
//│ ║  l.192: 	not (Cons 42 Nil).head
//│ ║         	          ^^
//│ ╟── but it flows into field selection with expected type `bool`
//│ ║  l.192: 	not (Cons 42 Nil).head
//│ ╙──       	                 ^^^^^
//│ res: bool | error

:e
(Cons 4).head
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.205: 	(Cons 4).head
//│ ║         	        ^^^^^
//│ ╟── type `(tail: anything,) -> Cons[?a]` does not have field 'head'
//│ ║  l.114: 	data type List a of
//│ ║         	               ^
//│ ╟── but it flows into receiver with expected type `{head: ?head}`
//│ ║  l.205: 	(Cons 4).head
//│ ╙──       	^^^^^^^^
//│ res: error

// :e
Cons 1 2
//│ res: Cons[1]

// TODO Allow method/field defintions in the same file (lose the let?):
:e
let List.head = () // ...
//│ ╔══[ERROR] Unsupported pattern shape
//│ ║  l.223: 	let List.head = () // ...
//│ ╙──       	        ^^^^^
//│ <error>: ()


