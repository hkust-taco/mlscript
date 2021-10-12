package mlscript

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.annotation.tailrec
import mlscript.utils._, shorthands._

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
    
    def | (that: SimpleType, prov: TypeProvenance = noProv, swapped: Bool = false): SimpleType = (this, that) match {
      case (TopType, _) => TopType
      case (BotType, _) => that
      case (_: RecordType, _: PrimType | _: FunctionType) => TopType
      case (_: FunctionType, _: PrimType | _: RecordType) => TopType
      case (RecordType(fs1), RecordType(fs2)) =>
        val fs2m = fs2.toMap
        RecordType(fs1.flatMap { case (k, v) => fs2m.get(k).map(v2 => k -> (v | v2)) })(prov)
      case _ if !swapped => that | (this, prov, swapped = true)
      case (`that`, _) => this
      case (NegType(`that`), _) => TopType
      case _ => ComposedType(true, that, this)(prov)
    }
    def & (that: SimpleType, prov: TypeProvenance = noProv, swapped: Bool = false): SimpleType = (this, that) match {
      case (TopType, _) => that
      case (BotType, _) => BotType
      case (ComposedType(true, l, r), _) => l & that | r & that
      case (_: PrimType, _: FunctionType) => BotType
      case (RecordType(fs1), RecordType(fs2)) =>
        RecordType(mergeSortedMap(fs1, fs2)(_ & _).toList)(prov)
      case _ if !swapped => that & (this, prov, swapped = true)
      case (`that`, _) => this
      case (NegType(`that`), _) => BotType
      case _ => ComposedType(false, that, this)(prov)
    }
    def neg(prov: TypeProvenance = noProv, force: Bool = false): SimpleType = this match {
      case ExtrType(b) => ExtrType(!b)(noProv)
      case ComposedType(true, l, r) => l.neg() & r.neg()
      case ComposedType(false, l, r) if force => l.neg() | r.neg()
      case NegType(n) => n
      // case _: RecordType => BotType // Only valid in positive positions!
        // Because Top<:{x:S}|{y:T}, any record type negation neg{x:S}<:{y:T} for any y=/=x,
        // meaning negated records are basically bottoms.
      case _ => NegType(this)(prov)
    }
    
    // TODO make it the other way around (more efficient)
    def without(names: Set[Str]): SimpleType =
      if (names.isEmpty) this else names.foldLeft(this)(_.without(_))
    
    def without(name: Str): SimpleType = this match {
      case Without(b, ns) => Without(b, ns + name)(this.prov)
      case t @ FunctionType(l, r) => t
      case t @ ComposedType(true, l, r) => l.without(name) | r.without(name)
      case t @ ComposedType(false, l, r) => l.without(name) & r.without(name)
      case a @ AppType(f, as) => ???
      // case t @ RecordType(fs) if fs.forall(_._1 =/= name) => t // ? probably not right
      case t @ RecordType(fs) =>
        // RecordType(fs.filter(nt => nt._1 =/= name))(t.prov)
        // ^ Since we want to be able to transform S\a<:T to S<:T\a in the constraint solver,
        //    interpreting Without as field deletion would be wrong. Instead, Without implements
        //    field _hiding_, which makes a given field irrelevant for a given type, during
        //    later subtyping constraints that will involve the type.
        //    We can still remove fields when these Without types appear in positive positions,
        //    so there will still be opportunity for simplification.
        Without(this, Set.single(name))(noProv)
      case t @ TupleType(fs) => t
      case vt: VarType => ???
      case n @ NegType(nt) if (nt match {
        case _: ComposedType | _: ExtrType | _: NegType => true
        // case c: ComposedType => c.pol
        // case _: ExtrType | _: NegType => true
        case _ => false
      }) => nt.neg(n.prov, force = true).without(name)
      case e @ ExtrType(_) => e // valid?
      case p @ ProxyType(und) => ProxyType(und.without(name))(p.prov)
      case p @ PrimType(_, _) => p
      case _: TypeVariable | _: NegType | _: TypeRef => Without(this, Set.single(name))(noProv)
    }
    def pushPosWithout: SimpleType = this match {
      case Without(b, ns) => b.without(ns) match {
        case rewritten @ Without(b, ns) => b match {
          case t @ RecordType(fs) => // In positive position, this is valid:
            RecordType(fs.filterNot(nt => ns(nt._1)))(t.prov)
          case _: TypeVariable => this
          // case t: NegType => t
          // case NegType(t) => t.without(ns).neg(b.prov)
          // case NegType(_: BaseType | _: RecordType) => b
          // case NegType(Without(b2, ns2)) => b
          
          case NegType(_: BaseType) => b
          
          // case NegType(Without(NegType(b2), ns2)) => b2.without(ns).neg().without(ns2).neg()
          // case NegType(Without(_: BaseType | _: RecordType, ns2)) => b
          // case NegType(Without(_: BaseType | _: RecordType, ns2)) /* if ns.exists(ns2) */ =>
          //   b.without(ns.filterNot(ns2))
          case NegType(Without(b2, ns2)) /* if ns.exists(ns2) */ =>
            b2.without(ns2.filterNot(ns)).neg().without(ns.filterNot(ns2))
          
          // case NegType(Without(b2, ns2)) => b2.without(ns.filterNot(ns2)).neg() // make things work but surely wrong!
          case NegType(Without(NegType(b2), ns2)) => b2.without(ns.filterNot(ns2)).neg().without(ns2).neg()
          
          case NegType(_) => rewritten
          
          // case Without(_: BaseType, ns) => b
          case b: BaseType => b
          case b: TypeRef => b
          
          // case t: NegType => this
          case _ => lastWords(s"$this $rewritten (${this.getClass})")
        }
        case _ => this
      }
      case _ => this
    }
    
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
      case PrimType(_, _) => Nil
      case TypeRef(d, ts) => ts
      case Without(b, ns) => b :: Nil
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
