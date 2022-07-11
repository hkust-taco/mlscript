package mlscript.mono

import mlscript.{TypingUnit, NuTypeDef, NuFunDef}
import mlscript.TypeName
import mlscript.{App, Asc, Assign, Bind, Blk, Block, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var}
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.ArrayBuffer

object Monomorph:
  private val debug = RainbowDebug()
  private val funImpls = MutMap[String, ArrayBuffer[NuFunDef]]()
  private val tyImpls = MutMap[String, ArrayBuffer[NuTypeDef]]()

  def monomprphize(tu: TypingUnit): TypingUnit = debug.trace("MONO") {
    TypingUnit(tu.entities.map {
      case Left(term) => Left(monomorphizeTerm(term))
      case Right(tyDef: NuTypeDef) => Right(monomorphizeTypeDef(tyDef))
      case Right(funDef: NuFunDef) => Right(monomorphizeFunDef(funDef))
    })
  }(_ => "MONO")

  def monomorphizeTerm(term: Term): Term = debug.trace[Term]("TERM") {
    term match
      case App(lhs, rhs) => monomorphizeTerm(lhs)
      case Asc(term, ty) => monomorphizeTerm(term)
      case Assign(lhs, rhs) => Assign(lhs, monomorphizeTerm(term))
      case Bind(lhs, rhs) => Bind(monomorphizeTerm(lhs), monomorphizeTerm(rhs))
      case Blk(_) => throw MonomorphError("Blk is not supported")
      case Block(_) => throw MonomorphError("cannot monomorphize `Block`")
      case Bra(rcd, term) => monomorphizeTerm(term)
      case CaseOf(scrutinee, branches) => monomorphizeTerm(scrutinee)
      case Lam(lhs, rhs) => monomorphizeTerm(rhs)
      case Let(isRec, Var(name), rhs, body) => monomorphizeTerm(body)
      case literal: Lit => literal
      case New(None, body) => throw new MonomorphError("why head is None")
      case New(Some((TypeName(name), term)), body) =>
        // I think `term` should always be a `Tuple`.
        val args = term match
          case Tup(terms) => terms.map { case (_, (term, _)) => term }
          case term: Term => term :: Nil
        throw new MonomorphError("work in progress")
      case Rcd(fields) => Rcd(fields.map { case (name, (term, flag)) =>
        (name, (monomorphizeTerm(term), flag))
      })
      case Sel(receiver, fieldName) => monomorphizeTerm(receiver)
      case term@Var(name) => term
      case Subs(array, index) => monomorphizeTerm(array)
      case Tup(fields) => Tup(fields.map { case (name, (term, flag)) =>
        (name, (monomorphizeTerm(term), flag))
      })
      case Test(term, ty) => monomorphizeTerm(term)
      case With(term, fields) => monomorphizeTerm(term)
  }(_ => "MONO")

  def monomorphizeTypeDef(tyDef: NuTypeDef): NuTypeDef = debug.trace("TDEF") {
    tyImpls.addOne((tyDef.nme.name, ArrayBuffer()))
    tyDef
  }(_ => "TDEF")

  def monomorphizeFunDef(funDef: NuFunDef): NuFunDef = debug.trace("FDEF") {
    funImpls.addOne((funDef.nme.name, ArrayBuffer()))
    funDef
  }(_ => "FDEF")
