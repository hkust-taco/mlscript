package mlscript

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._
import mlscript.utils._, shorthands._

trait TypeSimplifier { self: Typer =>
  
  
  // Compact types representation, useful for simplification:
  
  /** Depending on whether it occurs in positive or negative position,
   * this represents either a union or an intersection, respectively,
   * of different type components.  */
  case class CompactType(
    vars: Set[TypeVariable],
    prims: BaseTypes,
    rec: Option[SortedMap[Str, CompactType]],
    tup: Option[List[Opt[Str] -> CompactType]],
    fun: Option[(CompactType, CompactType)])
  extends CompactTypeOrBaseType with CompactTypeOrVariable {
    override def toString = List(vars, prims.underlying,
      rec.map(_.map(fs => fs._1 + ": " + fs._2).mkString("{",", ","}")),
      fun.map(lr => lr._1.toString + " -> " + lr._2),
    ).flatten.mkString("‹", ", ", "›")
  }
  object CompactType {
    val empty: CompactType = CompactType(Set.empty, BaseTypes.empty, None, None, None)
    def merge(pol: Boolean)(lhs: CompactType, rhs: CompactType): CompactType = {
      val rec = mergeOptions(lhs.rec, rhs.rec) { (lhs, rhs) =>
        if (pol) lhs.flatMap { case (k, v) => rhs.get(k).map(k -> merge(pol)(v, _)) }
        else mergeSortedMap(lhs, rhs)(merge(pol)) }
      val tup = mergeOptionsFlat(lhs.tup, rhs.tup) { (lhs, rhs) =>
        if (lhs.size =/= rhs.size) N
        else S(lhs.zip(rhs).map { case ((n0, t0), (n1, t1)) =>
          n0.orElse(n1) -> merge(pol)(t0, t1) // TODO return Nothing if the field names differ?
        })
      }
      val fun = mergeOptions(lhs.fun, rhs.fun){
        case ((l0,r0), (l1,r1)) => (merge(!pol)(l0, l1), merge(pol)(r0, r1)) }
      CompactType(lhs.vars ++ rhs.vars, (lhs.prims ++ rhs.prims)(pol), rec, tup, fun)
    }
  }
  
  sealed abstract class CompactTypeOrBaseType
  
  sealed abstract class CompactBaseType extends CompactTypeOrBaseType with CompactTypeOrVariable {
    def widen: CompactTypeOrBaseType
  }
  case class CompactVarType(vt: VarType, sign: CompactType) extends CompactBaseType {
    def widen: CompactTypeOrBaseType = sign
  }
  case class CompactAppType(lhs: CompactType, args: Ls[CompactType]) extends CompactBaseType {
    def widen: CompactTypeOrBaseType =
      lhs.fun.fold(this: CompactTypeOrBaseType)(_._2) // Q: also try to retrieve it from rec bounds?
  }
  case class CompactPrimType(prim: PrimType) extends CompactBaseType {
    lazy val widen: CompactPrimType = CompactPrimType(prim.widenPrim)
  }
  
  class BaseTypes private(val underlying: Set[CompactBaseType]) {
    def ++ (that: BaseTypes)(pol: Bool): BaseTypes = {
      var cur = underlying
      // println(s"[$pol]++ $this $that")
      if (pol) that.underlying.foreach {
        case prim @ CompactPrimType(PrimType(_: Lit)) =>
          if (!cur.contains(prim.widen)) cur += prim
        case prim @ CompactPrimType(PrimType(_: Var)) =>
          cur = cur.filterNot(_.widen === prim) + prim
        case app @ CompactAppType(lhs, args) =>
          cur = cur.filterNot(_.widen === app) + app // TODO what if widen returns a CompactType?!
        case vt @ CompactVarType(_, sign) =>
          cur = cur.filterNot(_.widen === vt) + vt // TODO what if widen returns a CompactType?!
      } else that.underlying.foreach {
        case prim @ CompactPrimType(PrimType(l0: Lit)) =>
          if (cur.collectFirst {
            case CompactPrimType(PrimType(l1: Lit)) if l1 =/= l0 =>
          }.isDefined)
            // return ... // TODO return Nothing, when we have a repr for it...
            ()
          if (cur.forall(_.widen =/= prim)) cur += prim
        case prim @ CompactPrimType(PrimType(_: Var)) =>
          if (cur.forall(_.widen =/= prim)) cur += prim
        case app @ CompactAppType(lhs, args) =>
          cur = cur.filterNot(app.widen === _) + app // TODO what if widen returns a CompactType?!
        case vt @ CompactVarType(_, sign) =>
          cur = cur.filterNot(vt.widen === _) + vt // TODO what if widen returns a CompactType?!
      }
      // println(s"== $cur")
      new BaseTypes(cur)
    }
    override def equals(that: Any): Boolean = that match {
      case ps: BaseTypes => ps.underlying === underlying
      case _ => false
    }
    override def hashCode: Int = underlying.hashCode
    override def toString: Str = underlying.mkString("{",",","}")
  }
  object BaseTypes {
    val empty: BaseTypes = new BaseTypes(Set.empty)
    def single(prim: PrimType): BaseTypes = new BaseTypes(Set.single(CompactPrimType(prim)))
    def single(app: CompactAppType): BaseTypes = new BaseTypes(Set.single(app))
    def single(vt: CompactVarType): BaseTypes = new BaseTypes(Set.single(vt))
    def apply(pol: Bool)(prims: CompactBaseType*): BaseTypes = (empty ++ new BaseTypes(Set.from(prims)))(pol)
  }
  
  case class CompactTypeScheme(term: CompactType, recVars: Map[TypeVariable, CompactType])
  
  
  // Simplification:
  
  // It is best to convert inferred types into compact types so we merge the bounds of inferred variables
  //   e.g., transform the bounds {x: A}, {x: B; y: C} into {x: A ∧ B; y: C}
  // This will allow for more precise co-occurrence analysis and hash-consing down the line.
  
  /** Convert an inferred SimpleType into the CompactType representation for simplification. */
  def compactType(ty: SimpleType, pol: Bool = true): CompactTypeScheme = {
    import CompactType.{empty, merge}, empty.{copy => ct}
    
    val recursive = MutMap.empty[PolarVariable, TypeVariable]
    var recVars = SortedMap.empty[TypeVariable, CompactType](Ordering by (_.uid))
    
    // `parents` remembers the variables whose bounds are being compacted,
    //    so as to remove spurious cycles such as ?a <: ?b and ?b <: ?a,
    //    which do not correspond to actual recursive types.
    def go(ty: SimpleType, pol: Boolean, parents: Set[TypeVariable])
          (implicit inProcess: Set[(TypeVariable, Boolean)]): CompactType = ty match {
      case p: PrimType => ct(prims = BaseTypes.single(p))
      case TypeRef(td, targs) =>
        ct(prims = BaseTypes single CompactAppType(
          ct(prims = BaseTypes single PrimType(Var(td.nme.name))(noProv)),
          targs.map(go(_, pol, Set.empty)))) // FIXME variance!
      case vt: VarType => ct(prims = BaseTypes.single(CompactVarType(vt, go(vt.sign, pol, parents))))
      case NegType(ty) => // FIXME tmp hack
        val base = ct(prims = BaseTypes single PrimType(Var("~"))(noProv))
        ct(prims = BaseTypes single CompactAppType(base, go(ty, pol, Set.empty) :: Nil))
      case ExtrType(pol) => // FIXME tmp hack
        ct(prims = BaseTypes single PrimType(Var(if (pol) "nothing" else "anything"))(noProv))
      case ProxyType(und) => go(und, pol, parents)
      case FunctionType(l, r) =>
        ct(fun = Some(go(l, !pol, Set.empty) -> go(r, pol, Set.empty)))
      case ComposedType(p, l, r) => // FIXME tmp hack
        val base = ct(prims = BaseTypes single PrimType(Var(if (p) "|" else "&"))(noProv))
        ct(prims = BaseTypes single CompactAppType(base, go(l, pol, parents) :: go(r, pol, parents) :: Nil))
      case Without(b, ns) =>
        val base = ct(prims = BaseTypes single PrimType(Var(ns.map("\\"+_).mkString))(noProv))
        ct(prims = BaseTypes single CompactAppType(base, go(b, pol, parents) :: Nil))
      case a @ AppType(lhs, args) =>
        ct(prims = BaseTypes single CompactAppType(go(lhs, pol, Set.empty), args.map(go(_, pol, Set.empty))))
      case RecordType(fs) =>
        ct(rec = Some(SortedMap from fs.iterator.map(f => f._1 -> go(f._2, pol, Set.empty))))
      case TupleType(fs) =>
        ct(tup = Some(fs.map(f => f._1 -> go(f._2, pol, Set.empty))))
      case tv: TypeVariable =>
        val bounds = if (pol) tv.lowerBounds else tv.upperBounds
        val tv_pol = tv -> pol
        if (inProcess.contains(tv_pol))
          if (parents(tv)) ct() // we have a spurious cycle: ignore the bound
          else ct(vars = Set(recursive.getOrElseUpdate(tv_pol, freshVar(tv.prov)(0))))
        else (inProcess + (tv -> pol)) pipe { implicit inProcess =>
          val bound = bounds.map(b => go(b, pol, parents + tv))
            .foldLeft[CompactType](ct(vars = Set(tv)))(merge(pol))
          recursive.get(tv_pol) match {
            case Some(v) =>
              recVars += v -> bound
              ct(vars = Set(v))
            case None => bound
          }
        }
      }
    
    CompactTypeScheme(go(ty, pol, Set.empty)(Set.empty), recVars)
  }
  
  
  // Idea: if a type var 'a always occurs positively (resp. neg) along with some 'b AND vice versa,
  //      this means that the two are undistinguishable, and they can therefore be unified.
  //    Ex: ('a & 'b) -> ('a, 'b) is the same as 'a -> ('a, 'a)
  //    Ex: ('a & 'b) -> 'b -> ('a, 'b) is NOT the same as 'a -> 'a -> ('a, 'a)
  //      there is no value of 'a that can make 'a -> 'a -> ('a, 'a) <: (a & b) -> b -> (a, b) work
  //      we'd require 'a :> b | a & b <: a & b, which are NOT valid bounds!
  //    Ex: 'a -> 'b -> 'a | 'b is the same as 'a -> 'a -> 'a
  //    Justification: the other var 'b can always be taken to be 'a & 'b (resp. a | b)
  //      without loss of gen. Indeed, on the pos side we'll have 'a <: 'a & 'b and 'b <: 'a & 'b
  //      and on the neg side, we'll always have 'a and 'b together, i.e., 'a & 'b
  
  // Additional idea: remove variables which always occur both positively AND negatively together
  //      with some other type.
  //    This would arise from constraints such as: 'a :> Int <: 'b and 'b <: Int
  //      (contraints which basically say 'a =:= 'b =:= Int)
  //    Ex: 'a ∧ Int -> 'a ∨ Int is the same as Int -> Int
  //    Currently, we only do this for primitive types PrimType.
  //    In principle it could be done for functions and records, too.
  //    Note: conceptually, this idea subsumes the simplification that removes variables occurring
  //        exclusively in positive or negative positions.
  //      Indeed, if 'a never occurs positively, it's like it always occurs both positively AND
  //      negatively along with the type Bot, so we can replace it with Bot.
  
  /** Simplifies a CompactTypeScheme by performing a co-occurrence analysis on the type variables. */
  def simplifyType(cty: CompactTypeScheme, pol: Bool = true, removePolarVars: Bool = true): CompactTypeScheme = {
    
    // State accumulated during the analysis phase:
    var allVars = SortedSet.from(cty.recVars.keysIterator)(Ordering by (-_.uid))
    var recVars = SortedMap.empty[TypeVariable, () => CompactType](Ordering by (_.uid))
    val coOccurrences: MutMap[(Boolean, TypeVariable), MutSet[CompactTypeOrVariable]] = LinkedHashMap.empty
    
    // This will be filled up after the analysis phase, to influence the reconstruction phase:
    val varSubst = MutMap.empty[TypeVariable, Option[TypeVariable]]
    
    // Traverses the type, performing the analysis, and returns a thunk to reconstruct it later:
    def go(ty: CompactType, pol: Boolean): () => CompactType = {
      ty.vars.foreach { tv =>
        allVars += tv
        val newOccs = LinkedHashSet.from[CompactTypeOrVariable](ty.vars.iterator ++ ty.prims.underlying)
        coOccurrences.get(pol -> tv) match {
          case Some(os) => os.filterInPlace(newOccs) // computes the intersection
          case None => coOccurrences(pol -> tv) = newOccs
        }
        cty.recVars.get(tv).foreach { b => // if `tv` is recursive, process its bound `b` too
          if (!recVars.contains(tv)) {
            lazy val goLater: () => CompactType = {
              // Make sure to register `tv` before recursing, to avoid an infinite recursion:
              recVars += tv -> (() => goLater())
              go(b, pol)
            }; goLater
          }; ()
        }
      }
      val prims_ = ty.prims.underlying.iterator.map {
        case cp: CompactPrimType => () => cp
        case CompactVarType(vt, sign) =>
          val sign_ = go(sign, pol)
          () => CompactVarType(vt, sign_())
        case CompactAppType(lhs, args) =>
          val lhs_ = go(lhs, pol)
          val args_ = args.map(go(_, pol))
          () => CompactAppType(lhs_(), args_.map(_()))
      }.toList
      val rec_ = ty.rec.map(_.map(f => f._1 -> go(f._2, pol)))
      val tup_ = ty.tup.map(_.map(f => f._1 -> go(f._2, pol)))
      val fun_ = ty.fun.map(lr => go(lr._1, !pol) -> go(lr._2, pol))
      () => {
        val newVars = ty.vars.flatMap { case tv => varSubst get tv match {
          case Some(Some(tv2)) => tv2 :: Nil
          case Some(None) => Nil
          case None => tv :: Nil
        }}
        CompactType(newVars, BaseTypes(pol)(prims_.map(_()): _*),
          rec_.map(r => r.map(f => f._1 -> f._2())),
          tup_.map(r => r.map(f => f._1 -> f._2())),
          fun_.map(lr => lr._1() -> lr._2()))
      }
    }
    val gone = go(cty.term, pol)
    println(s"[occ] ${coOccurrences}")
    println(s"[rec] ${recVars.keySet}")
    
    // Simplify away those non-recursive variables that only occur in positive or negative positions:
    allVars.foreach { case v0 => if (!recVars.contains(v0)) {
      (coOccurrences.get(true -> v0), coOccurrences.get(false -> v0)) match {
        case (Some(_), None) | (None, Some(_)) =>
          if (removePolarVars) {
            println(s"[!] $v0")
            varSubst += v0 -> None; ()
          } else {
            // The rest of simplifyType expects all remaining non-rec variables to occur both positively and negatively
            coOccurrences.getOrElseUpdate(true -> v0, MutSet(v0))
            coOccurrences.getOrElseUpdate(false -> v0, MutSet(v0))
          }
        case occ => dbg_assert(occ =/= (None, None))
      }
    }}
    // Unify equivalent variables based on polar co-occurrence analysis:
    val pols = true :: false :: Nil
    allVars.foreach { case v => if (!varSubst.contains(v)) {
      println(s"[v] $v ${coOccurrences.get(true -> v)} ${coOccurrences.get(false -> v)}")
      pols.foreach { pol =>
        coOccurrences.get(pol -> v).iterator.flatMap(_.iterator).foreach {
          case w: TypeVariable if !(w is v) && !varSubst.contains(w) && (recVars.contains(v) === recVars.contains(w)) =>
            // Note: We avoid merging rec and non-rec vars, because the non-rec one may not be strictly polar ^
            //       As an example of this, see [test:T1].
            println(s"[w] $w ${coOccurrences.get(pol -> w)}")
            if (coOccurrences.get(pol -> w).forall(_(v))) {
              println(s"[U] $w := $v") // we unify w into v
              varSubst += w -> Some(v)
              // Since w gets unified with v, we need to merge their bounds if they are recursive,
              // and otherwise merge the other co-occurrences of v and w from the other polarity (!pol).
              // For instance,
              //  consider that if we merge v and w in `(v & w) -> v & x -> w -> x`
              //  we get `v -> v & x -> v -> x`
              //  and the old positive co-occ of v, {v,x} should be changed to just {v,x} & {w,v} == {v}!
              recVars.get(w) match {
                case Some(b_w) => // `w` is a recursive variable, so `v` is too (see `recVars.contains` guard above)
                  dbg_assert(!coOccurrences.contains((!pol) -> w)) // recursive types have strict polarity
                  recVars -= w // w is merged into v, so we forget about it
                  val b_v = recVars(v) // `v` is recursive so `recVars(v)` is defined
                  // and record the new recursive bound for v:
                  recVars += v -> (() => CompactType.merge(pol)(b_v(), b_w()))
                case None => // `w` is NOT recursive
                  val wCoOcss = coOccurrences((!pol) -> w)
                  // ^ this must be defined otherwise we'd already have simplified away the non-rec variable
                  coOccurrences((!pol) -> v).filterInPlace(t => t === v || wCoOcss(t))
                  // ^ `w` is not recursive, so `v` is not either, and the same reasoning applies
              }
            }; ()
          case atom: CompactPrimType if (coOccurrences.get(!pol -> v).exists(_(atom))) =>
            varSubst += v -> None; ()
          case _ =>
        }
      }
    }}
    println(s"[sub] ${varSubst.map(k => k._1.toString + " -> " + k._2).mkString(", ")}")
    
    CompactTypeScheme(gone(), recVars.view.mapValues(_()).toMap)
  }
  
  /** Expands a CompactTypeScheme into a Type while performing hash-consing
   * to tie recursive type knots a bit tighter, when possible. */
  def expandCompactType(cty: CompactTypeScheme, pol: Bool = true): Type = {
    def go(ty: CompactTypeOrVariable, pol: Boolean)
          (implicit inProcess: Map[(CompactTypeOrVariable, Boolean), () => TypeVar]): Type = {
      inProcess.get(ty -> pol) match { // Note: we use pat-mat instead of `foreach` to avoid non-local return
        case Some(t) =>
          val res = t()
          println(s"REC[$pol] $ty -> $res")
          return res
        case None => ()
      }
      var isRecursive = false
      lazy val v = {
        isRecursive = true
        (ty match {
          case tv: TypeVariable => tv
          case _ => new TypeVariable(0, Nil, Nil)(noProv)
        }).asTypeVar
      }
      val res = inProcess + (ty -> pol -> (() => v)) pipe { implicit inProcess =>
        ty match {
          case tv: TypeVariable => cty.recVars.get(tv).fold(tv.asTypeVar: Type)(go(_, pol))
          case CompactType(vars, prims, rec, tup, fun) =>
            val (extr, mrg) = if (pol) (Bot, Union) else (Top, Inter)
            (vars.iterator.map(go(_, pol)).toList
              ::: prims.underlying.iterator.map {
                case CompactPrimType(PrimType(id)) => Primitive(id.idStr)
                case CompactAppType(lhs @ CompactType(vs, cs, r, t, f), targs) =>
                  (cs.underlying.toList, vs.size) match {
                    case (CompactPrimType(PrimType(Var(id))) :: Nil, 0) if id.head.isLetter && targs.nonEmpty =>
                      AppliedType(Primitive(id), targs.map(go(_, pol)))
                    case _ =>
                      targs.map(go(_, pol)).foldLeft(go(lhs, pol))(Applied(_, _))
                  }
                case CompactVarType(vt, sign) => Primitive(vt.vi.v.name) // FIXME do sthg else for higher levels?
              }.toList
              ::: rec.map(fs => Record(fs.toList.map(f => f._1 -> go(f._2, pol)))).toList
              ::: tup.map(fs => Tuple(fs.toList.map(f => f._1 -> go(f._2, pol)))).toList
              ::: fun.map(lr => Function(go(lr._1, !pol), go(lr._2, pol))).toList
            ).reduceOption(mrg).getOrElse(extr)
        }
      }
      if (isRecursive) Recursive(v, res) else res
    }
    go(cty.term, pol)(Map.empty)
  }
  
  
}
