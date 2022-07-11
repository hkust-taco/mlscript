package mlscript.mono

import mlscript.Pgrm
import mlscript.TypingUnit
import mlscript.Term
import mlscript.TypeDef
import mlscript.Def
import mlscript.{NuDecl, NuFunDef, NuTypeDef}
import fastparse.parse
import fastparse.Parsed.{Failure, Success}
import mlscript.MLParser
import mlscript.Origin
import mlscript.PolyType

@main
def main(): Unit =
  val source = """
    def f(x) = x + 1
    def g(x) = f(x) * 2
    g(0)
    g(1)
  """
  val fastParseHelpers = mlscript.FastParseHelpers(source)
  val parserOrigin = mlscript.Origin("test.mls", 1, fastParseHelpers)
  parse(source, p => MLParser(parserOrigin).pgrm(p)) match {
    case failure: Failure => println("Failed.")
    case Success(pgrm, index) =>
      val typingUnit = fromPgrmToTypingUnit(pgrm)
      println("Typing unit = " + PrettyPrinter.show(typingUnit))
      val monomorphized = Monomorph.monomprphize(typingUnit)
      println("Successfully monomorphized the program.")
  }

def fromPgrmToTypingUnit(pgrm: Pgrm): TypingUnit =
  TypingUnit(pgrm.tops.flatMap[Either[Term, NuDecl]] { 
    case term: Term => Some(Left(term))
    case Def(isRec, name, Left(term)) =>
      Some(Right(NuFunDef(name, Nil, Nil, Left(term))))
    case Def(isRec, name, Right(ty)) =>
      Some(Right(NuFunDef(name, Nil, Nil, Right(ty))))
    case tyDef @ TypeDef(kind, name, tyParams, body, mthDecls, mthDefs) =>
      // Translate member functions to functions in the enclosed typing unit.
      val subUnit = TypingUnit(List.from(
        tyDef.mthDecls.iterator.map { mthDecl =>
          Right(NuFunDef(mthDecl.nme, mthDecl.tparams, Nil, Right(PolyType(Nil, mthDecl.rhs.value))))
        }.concat(tyDef.mthDefs.iterator.map { mthDef => 
          Right(NuFunDef(mthDef.nme, mthDef.tparams, Nil, Left(mthDef.rhs.value)))
        })
      ))
      Some(Right(NuTypeDef(kind, name, tyParams, Nil, Nil, subUnit)))
    // Following items are not used in MLscript.
    case mlscript.DataDefn(_) => None
    case mlscript.DatatypeDefn(_, _) => None
    case mlscript.LetS(_, _, _) => None
  })