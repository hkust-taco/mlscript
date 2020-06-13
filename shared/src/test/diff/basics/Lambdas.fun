
let a = succ
let x = true
//│ a: int -> int
//│ x: bool

x => add (a x)
//│ res: int -> int -> int

x =>
  add (a x)
//│ res: int -> int -> int

let x =
  x =>
    add (a x)
//│ x: int -> int -> int

let id = v => v
//│ id: 'a -> 'a

f => f f
//│ res: 'a ∧ ('a -> 'b) -> 'b

f => id f id f id
//│ res: 'a ∧ (('b -> 'b) -> 'a -> ('c -> 'c) -> 'd) -> 'd

:pe
let oops = hu(h
//│ /!\ Parse error: Expected end-of-input:1:14, found "(h" at l.29:14: let oops = hu(h

x => x; y => y
//│ res: 'a -> 'a
//│ res: 'a -> 'a

:pe
x => let y = x; y
//│ /!\ Parse error: Expected expression:1:1, found "x => let y" at l.37:1: x => let y = x; y

x => (let y = x; y)
x =>
  let y = x; y
x =>
  let y = x
  y
//│ res: 'a -> 'a
//│ res: 'a -> 'a
//│ res: 'a -> 'a

// TODO
let f x = x + 1
//│ /!!!\ Uncaught error: java.lang.Exception: Internal Error: Not yet supported: pattern (f x)
//│ 	at: funtypes.utils.package$.lastWords(package.scala:113)
//│ 	at: funtypes.Typer.typeStatement(Typer.scala:103)
//│ 	at: funtypes.Typer.typeBlk(Typer.scala:94)
//│ 	at: funtypes.DiffTests.rec$1(DiffTests.scala:86)
//│ 	at: funtypes.DiffTests.$anonfun$new$2(DiffTests.scala:178)
//│ 	at: org.scalatest.OutcomeOf.outcomeOf(OutcomeOf.scala:85)
//│ 	at: org.scalatest.OutcomeOf.outcomeOf$(OutcomeOf.scala:83)
//│ 	at: org.scalatest.OutcomeOf$.outcomeOf(OutcomeOf.scala:104)
//│ 	at: org.scalatest.Transformer.apply(Transformer.scala:22)
//│ 	at: org.scalatest.Transformer.apply(Transformer.scala:20)

// TODO
let f (
  x
  y
) = x + 1
//│ /!!!\ Uncaught error: java.lang.Exception: Internal Error: Not yet supported: pattern (f (x; y;))
//│ 	at: funtypes.utils.package$.lastWords(package.scala:113)
//│ 	at: funtypes.Typer.typeStatement(Typer.scala:103)
//│ 	at: funtypes.Typer.typeBlk(Typer.scala:94)
//│ 	at: funtypes.DiffTests.rec$1(DiffTests.scala:86)
//│ 	at: funtypes.DiffTests.$anonfun$new$2(DiffTests.scala:178)
//│ 	at: org.scalatest.OutcomeOf.outcomeOf(OutcomeOf.scala:85)
//│ 	at: org.scalatest.OutcomeOf.outcomeOf$(OutcomeOf.scala:83)
//│ 	at: org.scalatest.OutcomeOf$.outcomeOf(OutcomeOf.scala:104)
//│ 	at: org.scalatest.Transformer.apply(Transformer.scala:22)
//│ 	at: org.scalatest.Transformer.apply(Transformer.scala:20)
