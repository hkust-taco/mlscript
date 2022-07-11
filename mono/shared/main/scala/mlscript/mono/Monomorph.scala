package mlscript.mono

import mlscript.{TypingUnit, NuTypeDef, NuFunDef}
import mlscript.TypeName
import mlscript.{App, Asc, Assign, Bind, Blk, Block, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var}
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.ArrayBuffer
import mlscript.Cls

object Monomorph:
  private val debug = RainbowDebug()
  private val funImpls = MutMap[String, ArrayBuffer[NuFunDef]]()
  private val tyImpls = MutMap[String, ArrayBuffer[NuTypeDef]]()
  private val lamTyDefs = MutMap[String, NuTypeDef]()

  def monomprphize(tu: TypingUnit): TypingUnit = debug.trace("MONO", PrettyPrinter.show(tu)) {
    TypingUnit(tu.entities.map {
      case Left(term) => Left(monomorphizeTerm(term))
      case Right(tyDef: NuTypeDef) => Right(monomorphizeTypeDef(tyDef))
      case Right(funDef: NuFunDef) => Right(monomorphizeFunDef(funDef))
    })
  }()

  def monomorphizeTerm(term: Term): Term =
    debug.trace[Term]("TERM", PrettyPrinter.show(term)) {
      term match
        case New(None, body) => throw new MonomorphError("why head is None")
        case New(Some((TypeName(name), term)), body) =>
          // I think `term` should always be a `Tuple`.
          val args = term match
            case Tup(terms) => terms.map { case (_, (term, _)) => term }
            case term: Term => term :: Nil
          specializeNew(name, args, body)
        case Lam(Tup(fields), body) =>
          val params = fields.map {
            case (_, (Var(name), _)) => name
            case _ => throw new MonomorphError("the argument of Lam should be Var")
          }
          // TODO: Capture variables referenced in the lambda body.
          // We should capture: closure variables and referenced type variables.
          val lambdaClassName = s"Lambda$$${lamTyDefs.size}"
          val lambdaClassBody = TypingUnit(Right(NuFunDef(Var("apply"), Nil, Nil, Left(body))) :: Nil)
          val lambdaClassDef = NuTypeDef(Cls, TypeName(lambdaClassName), Nil, Nil, Nil, lambdaClassBody)
          lamTyDefs.addOne((lambdaClassName, lambdaClassDef))
          // Returns a class construction.
          New(Some((TypeName(lambdaClassName), Tup(Nil))), TypingUnit(Nil))
        case Lam(_, _) => throw new MonomorphError("the first argument of Lam should be Tup")
        case term => term.map(monomorphizeTerm)
    }(PrettyPrinter.show)

  def specializeNew(name: String, args: List[Term], body: TypingUnit): New =
    throw new MonomorphError("specializeNew work in progress")

  def monomorphizeTypeDef(tyDef: NuTypeDef): NuTypeDef =
    debug.trace("TDEF", tyDef.kind.str + " " + tyDef.nme.name) {
      tyImpls.addOne((tyDef.nme.name, ArrayBuffer()))
      tyDef
    }()

  def monomorphizeFunDef(funDef: NuFunDef): NuFunDef =
    debug.trace("FDEF", PrettyPrinter.show(funDef)) {
      funImpls.addOne((funDef.nme.name, ArrayBuffer()))
      funDef
    }(PrettyPrinter.show)
