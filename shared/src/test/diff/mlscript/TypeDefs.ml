
// FIXME
class Test: { x: Int }
//│ /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
//│ 	at: scala.Predef$.$qmark$qmark$qmark(Predef.scala:344)
//│ 	at: funtypes.Typer.typeTopLevel(Typer.scala:129)
//│ 	at: funtypes.Typer.typePgrm(Typer.scala:112)
//│ 	at: funtypes.DiffTests.rec$1(DiffTests.scala:104)
//│ 	at: funtypes.DiffTests.$anonfun$new$2(DiffTests.scala:229)
//│ 	at: org.scalatest.OutcomeOf.outcomeOf(OutcomeOf.scala:85)
//│ 	at: org.scalatest.OutcomeOf.outcomeOf$(OutcomeOf.scala:83)
//│ 	at: org.scalatest.OutcomeOf$.outcomeOf(OutcomeOf.scala:104)
//│ 	at: org.scalatest.Transformer.apply(Transformer.scala:22)
//│ 	at: org.scalatest.Transformer.apply(Transformer.scala:20)

// FIXME
type Test = { x: Int }
//│ /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
//│ 	at: scala.Predef$.$qmark$qmark$qmark(Predef.scala:344)
//│ 	at: funtypes.Typer.typeTopLevel(Typer.scala:129)
//│ 	at: funtypes.Typer.typePgrm(Typer.scala:112)
//│ 	at: funtypes.DiffTests.rec$1(DiffTests.scala:104)
//│ 	at: funtypes.DiffTests.$anonfun$new$2(DiffTests.scala:229)
//│ 	at: org.scalatest.OutcomeOf.outcomeOf(OutcomeOf.scala:85)
//│ 	at: org.scalatest.OutcomeOf.outcomeOf$(OutcomeOf.scala:83)
//│ 	at: org.scalatest.OutcomeOf$.outcomeOf(OutcomeOf.scala:104)
//│ 	at: org.scalatest.Transformer.apply(Transformer.scala:22)
//│ 	at: org.scalatest.Transformer.apply(Transformer.scala:20)

:pe
class Test = { x: Int }
//│ /!\ Parse error: Expected ":":1:12, found "= { x: Int" at l.31:12: class Test = { x: Int }

:pe
type Test: { x: Int }
//│ /!\ Parse error: Expected "=":1:10, found ": { x: Int" at l.35:10: type Test: { x: Int }


