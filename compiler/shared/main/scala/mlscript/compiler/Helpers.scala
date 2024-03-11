package mlscript
package compiler

import mlscript.compiler.mono.*
import scala.collection.mutable.ArrayBuffer

type NuParameter = (FldFlags, Var, Option[Term])

object Helpers:
  /**
   * Extract parameters for monomorphization from a `Tup`.
   */  
  def extractLamParams(term: Term): Option[List[NuParameter]] = term match
    case Lam(Tup(fields), _) => Some(fields.flatMap {
      case (_, Fld(FldFlags(_, _, _), UnitLit(true))) => None
      case (None, Fld(flags, name: Var)) => Some((flags, name, None))
      case (None, Fld(flags, Bra(_, name: Var))) => Some((flags, name, None))
      case (Some(name: Var), Fld(flags, typename: Term)) => Some((flags, name, Some(typename)))
      case _ => throw MonomorphError(
        s"Encountered unexpected structure when extracting parameters: ${term}"
      )
    })
    case _ => None //FIXME: Silent failure? Improve semantics

  def extractObjParams(term: Term): Iterator[NuParameter] = term match
    case Tup(fields) => fields.iterator.flatMap {
      case (_, Fld(FldFlags(_, _, _), UnitLit(true))) => None
      case (None, Fld(flags, name: Var)) => Some((flags, name, None))
      case (None, Fld(flags, Bra(_, name: Var))) => Some((flags, name, None))
      case (Some(name: Var), Fld(flags, typename: Term)) => Some((flags, name, Some(typename)))
      case _ => throw MonomorphError(s"Encountered unexpected structure when extracting parameters: ${term}")
    }
    case _ => throw MonomorphError(s"Encountered unexpected structure when extracting parameters: ${term}")

  def extractLamBody(term: Term): Term = term match
    case Lam(_, body) => body
    case _ => throw MonomorphError(s"Attempted to extract Lambda Body from ${term}")

  def toTuple(args: List[Term]): Tup =
    Tup(args.map{term => (None, Fld(FldFlags.empty, term))})

  def paramToTuple(args: List[NuParameter]): Tup = 
  Tup(args.map{
    case (flags, name, None) => (None, Fld(flags, name))
    case (flags, name, Some(typename)) => (Some(name), Fld(flags, typename))
  })
  
  /*
  * If term is not a Lambda, turn it into a lambda with a "this" parameter
  * If term is already a Lambda, add a "this" parameter to the front of the parameter list
  */
  def addThisParam(term: Term): Term = term match
    case Lam(Tup(fields), rhs) => Lam(Tup((None, Fld(FldFlags.empty, Var("this")))::fields), rhs)
    case rhs => Lam(Tup((None, Fld(FldFlags.empty, Var("this")))::Nil), rhs)

  // OLD FIXME: Loses tuple information in conversion
  def toFuncArgs(term: Term): IterableOnce[Term] = term match
    // The new parser generates `(undefined, )` when no arguments.
    // Let's do this temporary fix.
    case Tup((_, Fld(FldFlags(_, _, _), UnitLit(true))) :: Nil) => Iterable.empty
    case Tup(fields) => fields.iterator.map(_._2.value)
    case _ => Some(term)
  
  def extractFuncArgs(term: Term): List[Term] = term match
    // The new parser generates `(undefined, )` when no arguments.
    // Let's do this temporary fix.
    case Tup((_, Fld(FldFlags(_, _, _), UnitLit(true))) :: Nil) => ???
    case Tup(fields) => fields.map(_._2.value)
    case _ => throw MonomorphError("Unknown structure in FuncArgs")
  
