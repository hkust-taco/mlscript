package funtypes

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.annotation.tailrec
import funtypes.utils._, shorthands._

/** Inessential methods used to help debugging. */
abstract class TyperHelpers { self: Typer =>
  
  private val noPostTrace: Any => String = _ => ""
  
  protected var indent = 0
  def trace[T](pre: String)(thunk: => T)(post: T => String = noPostTrace): T = {
    println(pre)
    indent += 1
    val res = try thunk finally indent -= 1
    if (post isnt noPostTrace) println(post(res))
    res
  }
  
  def emitDbg(str: String): Unit = scala.Predef.println(str)
  
  // Shadow Predef functions with debugging-flag-enabled ones:
  def println(msg: => Any): Unit = if (dbg) emitDbg(" " * indent + msg)
  
  def dbg_assert(assertion: => Boolean): Unit = if (dbg) scala.Predef.assert(assertion)
  // def dbg_assert(assertion: Boolean): Unit = scala.Predef.assert(assertion)
  
  trait SimpleTypeImpl { self: SimpleType =>
    
    def app(that: SimpleType)(prov: TypeProvenance): SimpleType = this match {
      case AppType(lhs, args) => AppType(lhs, args :+ that)(prov)
      case FunctionType(lhs, rhs) =>
        // Note: we assume that `lhs` has already been constrained to take `args` as arguments
        rhs
      case _ => AppType(this, that :: Nil)(prov)
    }
    def abs(that: SimpleType)(prov: TypeProvenance): SimpleType =
      FunctionType(this, that)(prov)
    
    def widenVar: SimpleType = this match {
      case vt: VarType => vt.sign
      case _ => this
    }
    def widen: SimpleType = this match {
      case vt: VarType => vt.sign
      case pt: PrimType => pt.widenPrim
      case _ => this
    }
    
    def isInjective: Bool = this match {
      case vt: VarType => true // TODO also support non-injective ones!
      case ProxyType(und) => und.isInjective
      case _ => false
    }
    
    def unwrapProxies: SimpleType = this match {
      case ProxyType(und) => und.unwrapProxies
      case _ => this
    }
    
    def children: List[SimpleType] = this match {
      case tv: TypeVariable => tv.lowerBounds ::: tv.upperBounds
      case vt: VarType => vt.sign :: Nil
      case FunctionType(l, r) => l :: r :: Nil
      case ComposedType(_, l, r) => l :: r :: Nil
      case AppType(lhs, args) => lhs :: args
      case RecordType(fs) => fs.map(_._2)
      case TupleType(fs) => fs.map(_._2)
      case NegType(n) => n :: Nil
      case ExtrType(_) => Nil
      case ProxyType(und) => und :: Nil
      case PrimType(_) => Nil
    }
    
    def getVars: Set[TypeVariable] = {
      val res = MutSet.empty[TypeVariable]
      @tailrec def rec(queue: List[SimpleType]): Unit = queue match {
        case (tv: TypeVariable) :: tys =>
          if (res(tv)) rec(tys)
          else { res += tv; rec(tv.children ::: tys) }
        case ty :: tys => rec(ty.children ::: tys)
        case Nil => ()
      }
      rec(this :: Nil)
      SortedSet.from(res)(Ordering.by(_.uid))
    }
    
    def showBounds: String =
      getVars.iterator.filter(tv => (tv.upperBounds ++ tv.lowerBounds).nonEmpty).map(tv =>
        tv.toString
          + (if (tv.lowerBounds.isEmpty) "" else " :> " + tv.lowerBounds.mkString(" | "))
          + (if (tv.upperBounds.isEmpty) "" else " <: " + tv.upperBounds.mkString(" & "))
      ).mkString(", ")
    
    def expPos: Type = (this
      |> (compactType(_, true))
      |> (simplifyType(_, true, removePolarVars = false))
      |> (expandCompactType(_, true))
    )
    def expNeg: Type = (this
      |> (compactType(_, false))
      |> (simplifyType(_, false, removePolarVars = false))
      |> (expandCompactType(_, false))
    )
    
  }
  
}
