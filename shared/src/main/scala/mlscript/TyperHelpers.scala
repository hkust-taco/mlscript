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
  def println(msg: => Any): Unit = if (dbg) emitDbg("| " * indent + msg)
  
  def dbg_assert(assertion: => Boolean): Unit = if (dbg) scala.Predef.assert(assertion)
  // def dbg_assert(assertion: Boolean): Unit = scala.Predef.assert(assertion)
  
  
  def recordUnion(fs1: Ls[Var -> SimpleType], fs2: Ls[Var -> SimpleType]): Ls[Var -> SimpleType] = {
    val fs2m = fs2.toMap
    fs1.flatMap { case (k, v) => fs2m.get(k).map(v2 => k -> (v | v2)) }
  }
  
  trait SimpleTypeImpl { self: SimpleType =>
    
    def | (that: SimpleType, prov: TypeProvenance = noProv, swapped: Bool = false): SimpleType = (this, that) match {
      case (TopType, _) => TopType
      case (BotType, _) => that
      
      // These were wrong! During constraint solving it's important to keep them!
      // case (_: RecordType, _: PrimType | _: FunctionType) => TopType
      // case (_: FunctionType, _: PrimType | _: RecordType) => TopType
      
      case (_: RecordType, _: FunctionType) => TopType
      case (RecordType(fs1), RecordType(fs2)) =>
        RecordType(recordUnion(fs1, fs2))(prov)
      case _ if !swapped => that | (this, prov, swapped = true)
      case (`that`, _) => this
      case (NegType(`that`), _) => TopType
      case _ => ComposedType(true, that, this)(prov)
    }
    def & (that: SimpleType, prov: TypeProvenance = noProv, swapped: Bool = false): SimpleType = (this, that) match {
      case (TopType | RecordType(Nil), _) => that
      case (BotType, _) => BotType
      case (ComposedType(true, l, r), _) => l & that | r & that
      case (_: ClassTag, _: FunctionType) => BotType
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
    
    // TODO for composed types and negs, should better first normalize the inequation
    def <:< (that: SimpleType)(implicit cache: MutMap[ST -> ST, Bool] = MutMap.empty): Bool =
    // trace(s"? $this <: $that") {
    (this === that) || ((this, that) match {
      case (RecordType(Nil), _) => TopType <:< that
      case (_, RecordType(Nil)) => this <:< TopType
      case (pt1 @ ClassTag(id1, ps1), pt2 @ ClassTag(id2, ps2)) => (id1 === id2) || pt1.parentsST(id2)
      case (FunctionType(l1, r1), FunctionType(l2, r2)) => l2 <:< l1 && r1 <:< r2
      case (_: FunctionType, _) | (_, _: FunctionType) => false
      case (ComposedType(true, l, r), _) => l <:< that && r <:< that
      case (_, ComposedType(false, l, r)) => that <:< l && that <:< r
      case (ComposedType(false, l, r), _) => l <:< that || r <:< that
      case (_, ComposedType(true, l, r)) => that <:< l || that <:< r
      case (RecordType(fs1), RecordType(fs2)) =>
        fs2.forall(f => fs1.find(_._1 === f._1).exists(_._2 <:< f._2))
      case (_: RecordType, _: ObjectTag) | (_: ObjectTag, _: RecordType) => false
      case (_: TypeVariable, _) | (_, _: TypeVariable)
        if cache.contains(this -> that)
        => cache(this -> that)
      case (tv: TypeVariable, _) =>
        cache(this -> that) = true
        val tmp = tv.upperBounds.exists(_ <:< that)
        cache(this -> that) = tmp
        tmp
      case (_, tv: TypeVariable) =>
        cache(this -> that) = true
        val tmp = tv.lowerBounds.exists(this <:< _)
        cache(this -> that) = tmp
        tmp
      case (ProxyType(und), _) => und <:< that
      case (_, ProxyType(und)) => this <:< und
      case (_, NegType(und)) => (this & und) <:< BotType
      case (NegType(und), _) => TopType <:< (that | und)
      case (_, ExtrType(false)) => true
      case (ExtrType(true), _) => true
      case (_, ExtrType(true)) | (ExtrType(false), _) => false // not sure whether LHS <: Bot (or Top <: RHS)
      case (_: TypeRef, _) | (_, _: TypeRef) =>
        false // TODO try to expand them (this requires populating the cache because of recursive types)
      case (_: Without, _) | (_, _: Without)
        | (_: TupleType, _) | (_, _: TupleType)
        | (_: TraitTag, _) | (_, _: TraitTag)
        => false // don't even try
      case _ => lastWords(s"TODO $this $that ${getClass} ${that.getClass()}")
    })
    // }(r => s"! $r")
    
    // Sometimes, Without types are temporarily pushed to the RHS of constraints,
    // sometimes behind a single negation,
    // just for the time of massaging the constraint through a type variable.
    // So it's important we only push and simplify Without types only in _positive_ position!
    def without(names: Set[Var]): SimpleType = if (names.isEmpty) this else this match {
      case Without(b, ns) => Without(b, ns ++ names)(this.prov)
      case _ => Without(this, names)(noProv)
    }
    def without(name: Var): SimpleType = 
      without(Set.single(name))
    
    def withoutPos(names: Set[Var]): SimpleType = this match {
      case Without(b, ns) => Without(b, ns ++ names)(this.prov)
      case t @ FunctionType(l, r) => t
      case t @ ComposedType(true, l, r) => l.without(names) | r.without(names)
      case t @ ComposedType(false, l, r) => l.without(names) & r.without(names)
      case t @ RecordType(fs) => RecordType(fs.filter(nt => !names(nt._1)))(t.prov)
      case t @ TupleType(fs) => t
      case n @ NegType(_ : ClassTag | _: FunctionType | _: RecordType) => n
      case n @ NegType(nt) if (nt match {
        case _: ComposedType | _: ExtrType | _: NegType => true
        // case c: ComposedType => c.pol
        // case _: ExtrType | _: NegType => true
        case _ => false
      }) => nt.neg(n.prov, force = true).withoutPos(names)
      case e @ ExtrType(_) => e // valid? -> seems we could go both ways, but this way simplifies constraint solving
      // case e @ ExtrType(false) => e
      case p @ ProxyType(und) => ProxyType(und.withoutPos(names))(p.prov)
      case p: ObjectTag => p
      case _: TypeVariable | _: NegType | _: TypeRef => Without(this, names)(noProv)
    }
    def unwrapAll(implicit raise: Raise): SimpleType = unwrapProxies match {
      case tr: TypeRef => tr.expand.unwrapAll
      case u => u
    }
    def negNormPos(f: SimpleType => SimpleType, p: TypeProvenance)(implicit raise: Raise): SimpleType = unwrapAll match {
      case ExtrType(b) => ExtrType(!b)(noProv)
      case ComposedType(true, l, r) => l.negNormPos(f, p) & r.negNormPos(f, p)
      case ComposedType(false, l, r) => l.negNormPos(f, p) | r.negNormPos(f, p)
      case NegType(n) => f(n).withProv(p)
      case tr: TypeRef => tr.expand.negNormPos(f, p)
      case _: RecordType | _: FunctionType => BotType // Only valid in positive positions!
        // Because Top<:{x:S}|{y:T}, any record type negation neg{x:S}<:{y:T} for any y=/=x,
        // meaning negated records are basically bottoms.
      case rw => NegType(f(rw))(p)
    }
    def withProvOf(ty: SimpleType): ProxyType = withProv(ty.prov)
    def withProv(p: TypeProvenance): ProxyType = ProxyType(this)(p)
    def pushPosWithout(implicit raise: Raise): SimpleType = this match {
      case NegType(n) => n.negNormPos(_.pushPosWithout, prov)
      case Without(b, ns) => b.unwrapAll.withoutPos(ns) match {
        case Without(c @ ComposedType(pol, l, r), ns) => ComposedType(pol, l.withoutPos(ns), r.withoutPos(ns))(c.prov)
        case Without(NegType(nt), ns) => nt.negNormPos(_.pushPosWithout, nt.prov).withoutPos(ns) match {
          case rw @ Without(NegType(nt), ns) =>
            nt match {
              case _: TypeVariable | _: ClassTag | _: RecordType => rw
              case _ => lastWords(s"$this  $rw  (${nt.getClass})")
            }
          case rw => rw
        }
        case rw => rw
      }
      case _ => this
    }
    def normalize(pol: Bool): ST = DNF.mk(this, pol = pol).toType
    
    def abs(that: SimpleType)(prov: TypeProvenance): SimpleType =
      FunctionType(this, that)(prov)
    
    def unwrapProxies: SimpleType = this match {
      case ProxyType(und) => und.unwrapProxies
      case _ => this
    }
    
    def children: List[SimpleType] = this match {
      case tv: TypeVariable => tv.lowerBounds ::: tv.upperBounds
      case FunctionType(l, r) => l :: r :: Nil
      case ComposedType(_, l, r) => l :: r :: Nil
      case RecordType(fs) => fs.map(_._2)
      case TupleType(fs) => fs.map(_._2)
      case NegType(n) => n :: Nil
      case ExtrType(_) => Nil
      case ProxyType(und) => und :: Nil
      case _: ObjectTag => Nil
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
      |> (canonicalizeType(_, true))
      |> (simplifyType(_, true, removePolarVars = false))
      |> (expandType(_, true))
    )
    def expNeg: Type = (this
      |> (canonicalizeType(_, false))
      |> (simplifyType(_, false, removePolarVars = false))
      |> (expandType(_, false))
    )
    
  }
  
}
