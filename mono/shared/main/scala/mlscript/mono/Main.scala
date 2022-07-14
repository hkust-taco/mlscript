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
import mlscript.{Lam, Tup, Var}
import collection.mutable.Map as MutMap
import mlscript.Cls
import mlscript.New.apply
import mlscript.Trt

@main
def main(): Unit =
  val source = """
class Box[T]: { inner: T }
  method Map: (T -> 'a) -> Box['a]
  method Map f = Box { inner = f this.inner }
  method Get = this.inner

def inc x = x + 1
def dbl x = x * 2
def app f x = f x

class Stop: {}

Box { inner = 4 * 5 }

def box0 = Box { inner = 0 }
def box1 = box0.Map inc
def box2 = box1.Map dbl
  """
  val fastParseHelpers = mlscript.FastParseHelpers(source)
  val parserOrigin = mlscript.Origin("test.mls", 1, fastParseHelpers)
  parse(source, p => MLParser(parserOrigin).pgrm(p)) match {
    case failure: Failure => println("Failed." + failure.msg)
    case Success(pgrm, index) =>
      val typingUnit = fromPgrmToTypingUnit(pgrm)
      val monomorphized = Monomorph.monomprphize(typingUnit)
      println("Successfully monomorphized the program.")
      println("Specialized type definitions:")
      Monomorph.specializedTypeDefs.foreach { case tyDef =>
        println(PrettyPrinter.show(tyDef))
      }
  }

// This function converts a `Pgrm` to a `TypingUnit`.
def fromPgrmToTypingUnit(pgrm: Pgrm): TypingUnit =
  val nameClassMap = MutMap[String, NuTypeDef]()

  import mlscript.{App, New, TypeName}

  // Replaces class constructor calls to `New(_, _, _)`.
  def go(term: Term): Term =
    term match {
      case App(Var(name), args) if nameClassMap.contains(name) =>
        New(Some((TypeName(name), args)), TypingUnit(Nil))
      case _ => term.map(go)
    }

  TypingUnit(pgrm.tops.flatMap[Either[Term, NuDecl]] { 
    // Just a term
    case term: Term => Some(Left(go(term)))
    // Function definitions
    case Def(isRec, name, Left(term)) =>
      // val (params, body) = extractParameters(term)
      // // FIXME: types in `specParams` are missing.
      // Some(Right(NuFunDef(name, Nil, params.map((_, None)), Left(body))))
      Some(Right(NuFunDef(name, Nil, Nil, Left(term))))
    // Function declarations
    case Def(isRec, name, Right(ty)) =>
      Some(Right(NuFunDef(name, ty.targs, Nil, Right(ty))))
    // Aliases, classes or traits
    case tyDef @ TypeDef(kind, name, tyParams, body, mthDecls, mthDefs) =>
      // Translate member functions to functions in the enclosed typing unit.
      val subUnit = TypingUnit(List.from(
        tyDef.mthDecls.iterator.map { mthDecl =>
          Right(NuFunDef(mthDecl.nme, mthDecl.tparams, Nil, Right(PolyType(Nil, mthDecl.rhs.value))))
        }.concat(tyDef.mthDefs.iterator.map { mthDef => 
          Right(NuFunDef(mthDef.nme, mthDef.tparams, Nil, Left(mthDef.rhs.value)))
        })
      ))
      val nuTyDef = NuTypeDef(kind, name, tyParams, Nil, Nil, subUnit)
      // FIXME: This type is invisible to inner classes.
      if (tyDef.kind == Cls || tyDef.kind == Trt)
        nameClassMap.addOne((name.name, nuTyDef))
      Some(Right(nuTyDef))
    // Following items are (rarely?) used in MLscript.
    case mlscript.DataDefn(_) => None
    case mlscript.DatatypeDefn(_, _) => None
    case mlscript.LetS(_, _, _) => None
  })

// The parser desugars function definitions to curried lambdas.
// `def app f x = <...>` becomese `((f,) => ((x,) => <...>))`.
// This function extracts curried function parameters.
def extractParameters(term: Term): (List[Var], Term) =
  term match
    case Lam(Tup(fields), outerBody) =>
      val (restParams, innerBody) = extractParameters(outerBody)
      val params = fields.map {
        case (_, (param: Var, _)) => param
        case _ => throw MonomorphError("only support `Var` as function parameters")
      }
      (params ++ restParams, innerBody)
    case _ => (Nil, term)
    