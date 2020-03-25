package simplesub

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._
import scala.annotation.tailrec

abstract class TyperHelpers { self: Typer =>
  
  
  // Helper methods:
  
  trait SimpleTypeImpl { self: SimpleType =>
    def freshenAbove(lim: Int)(implicit lvl: Int): SimpleType = {
      val freshened = MutMap.empty[TypeVariable, TypeVariable]
      def freshen(ty: SimpleType): SimpleType = ty match {
        case tv: TypeVariable =>
          if (tv.level > lim) freshened.get(tv) match {
            case Some(tv) => tv
            case None =>
              val v = freshVar
              freshened += tv -> v
              // v.lowerBounds = tv.lowerBounds.mapConserve(freshen)
              // v.upperBounds = tv.upperBounds.mapConserve(freshen)
              //  ^ the above are more efficient, but they lead to a different order
              //    of fresh variable creations, which leads to some types not being
              //    simplified the same when put into the RHS of a let binding...
              v.lowerBounds = tv.lowerBounds.reverse.map(freshen).reverse
              v.upperBounds = tv.upperBounds.reverse.map(freshen).reverse
              v
          } else tv
        case FunctionType(l, r) => FunctionType(freshen(l), freshen(r))
        case RecordType(fs) => RecordType(fs.map(ft => ft._1 -> freshen(ft._2)))
        case PrimType(_) => ty
      }
      freshen(this)
    }
    def children: List[SimpleType] = this match {
      case tv: TypeVariable => tv.lowerBounds ::: tv.upperBounds
      case FunctionType(l, r) => l :: r :: Nil
      case RecordType(fs) => fs.map(_._2)
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
    def show: String = expandPosType(this, simplify = false).show
    def showBounds: String =
      getVars.iterator.filter(tv => (tv.upperBounds ++ tv.lowerBounds).nonEmpty).map(tv =>
        tv.toString
          + (if (tv.lowerBounds.isEmpty) "" else " :> " + tv.lowerBounds.mkString(" | "))
          + (if (tv.upperBounds.isEmpty) "" else " <: " + tv.upperBounds.mkString(" & "))
      ).mkString(", ")
  }
  
  
  // Conversion into proper immutable Type representations:
  
  def expandType(tv: SimpleType, simplify: Boolean): Type = {
    val polarities = MutMap.empty[TypeVar, Option[Boolean]]
    def go(ts: SimpleType, polarity: Boolean)(inProcess: Set[(TypeVariable, Boolean)]): Type = ts match {
      case tv: TypeVariable =>
        val uv = tv.asTypeVar
        val newPol = Some(polarity)
        val oldPol = polarities.getOrElseUpdate(uv, newPol)
        if (oldPol =/= newPol) polarities(uv) = None
        if (inProcess(tv -> polarity)) uv
        else {
          val bounds = if (polarity) tv.lowerBounds else tv.upperBounds
          val boundTypes = bounds.map(go(_, polarity)(inProcess + (tv -> polarity)))
          val isRecursive = boundTypes.exists(_.typeVars(uv))
          val v: Type = if (isRecursive) if (polarity) Bot else Top else uv
          val body = boundTypes.foldLeft(v)(if (polarity) Union else Inter)
          if (isRecursive) Recursive(uv, body) else body
        }
      case FunctionType(l, r) => Function(go(l, !polarity)(inProcess), go(r, polarity)(inProcess))
      case RecordType(fs) => Record(fs.map(nt => nt._1 -> go(nt._2, polarity)(inProcess)))
      case PrimType(n) => Primitive(n)
    }
    val ty = go(tv, true)(Set.empty)
    def doSimplify(ty: Type): Type = ty match {
      case uv: TypeVar => polarities.get(uv) match {
        case Some(Some(true)) => Bot
        case Some(Some(false)) => Top
        case _ => ty
      }
      case _ => ty.map(doSimplify)
    }
    if (simplify) doSimplify(ty) else ty
  }
  
  def expandPosType(tv: SimpleType, simplify: Boolean): Pos.Type = {
    
    // First, solidify the record types present in the upper bounds:
    //   e.g., transform {x: A}, {x: B; y: C} into {x: A ∧ B; y: C}
    // This is merely done to generate cleaner recursive types in some cases;
    //    without it, the term "let rec c = fun s -> add s.head (c s.tail)"
    //    gets inferred type:
    //      {head: Int, tail: {head: Int} ∧ 'a} as 'a -> Int
    //    instead of the cleaner:
    //      {head: Int, tail: 'a} as 'a -> Int
    tv.getVars.foreach { v =>
      val ubs = v.upperBounds
      val (recs, rest) = ubs.partitionMap {
        case RecordType(fields) => Left(fields)
        case t => Right(t)
      }
      recs.reduceOption { (fs0, fs1) =>
        mergeMap(fs0.toMap, fs1.toMap)((t0, t1) => new TypeVariable(0, Nil, t0 :: t1 :: Nil)).toList
      }.foreach { rec =>
        v.upperBounds = RecordType(rec) :: rest
      }
    }
    
    val polarities = MutMap.empty[TypeVariable, Option[Polarity]]
    
    def go(ts: SimpleType, pol: Polarity)(implicit inProcess: Map[(SimpleType, Polarity), () => TypeVar])
        : Set[TypeVariable] => pol.Type
        = {
      import pol.empty.{copy => mk}
      
      inProcess.get(ts -> pol) match {
        case Some(t) => return _ => mk(atoms = Set(t()))
        case None => ()
      }
      var isRecursive = false
      lazy val uv = {
        isRecursive = true
        (ts match {
          case tv: TypeVariable => tv
          case _ => new TypeVariable(0, Nil, Nil)
        }).asTypeVar
      }
      inProcess + (ts -> pol -> (() => uv)) pipe { implicit inProcess =>
        ts match {
          case tv: TypeVariable =>
            val newPol = Some(pol)
            val oldPol = polarities.getOrElseUpdate(tv, newPol)
            if (oldPol =/= newPol) polarities(tv) = None
            val bounds = if (pol === Pos) tv.lowerBounds else tv.upperBounds
            val boundsRec = bounds.map(go(_, pol))
            ctx => {
              val boundsRes = boundsRec.map(_(ctx))
              boundsRes.foldLeft(
                if (isRecursive) mk(rec = Some(uv))
                else if (ctx(tv)) mk(atoms = Set(uv)) else mk()
              )(pol.merge(_, _))
            }
          case FunctionType(l, r) =>
            val l2 = go(l, !pol)
            val r2 = go(r, pol)
            ctx => mk(fun = Some(l2(ctx) -> r2(ctx)), rec = Option.when(isRecursive)(uv))
          case RecordType(fs) =>
            val fs2 = fs.map(nt => nt._1 -> go(nt._2, pol))
            ctx => mk(fields = Some(fs2.iterator.map(nt => nt._1 -> nt._2(ctx)).toMap),
                      rec = Option.when(isRecursive)(uv))
          case PrimType(n) => _ => assert(!isRecursive); mk(atoms = Set(Primitive(n)))
        }
      }
    }
    go(tv, Pos)(Map.empty)(
      polarities.iterator.filter(!simplify || _._2.isEmpty).map(_._1).toSet)
  }
  // Note: we do not do co-occurrence analysis here in type expansion, but later in the PosType,
  //    since many co-occurrences appear only after we have normalized the type!
  
  
  
  // It is best to convert inferred types into compact types so we merge the bounds of inferred variables
  //   e.g., transform the bounds {x: A}, {x: B; y: C} into {x: A ∧ B; y: C}
  // This will allow for more precise co-occurrence analysis and hash-consing down the line.
  def compactType(ty: SimpleType): CompactTypeScheme = {
    import CompactType.{empty, merge}, empty.{copy => ct}
    
    ty.getVars.foreach(_.recursiveFlag = false)
    var recVars = SortedMap.empty[TypeVariable, CompactType](Ordering by (_.uid))
    
    // `parents` remembers the variables whose bounds are being compacted,
    // so as to remove spurious cycles such as ?a <: ?b and ?b <: ?a,
    // which do not correspond to actual recursive types.
    def go(ty: SimpleType, pol: Boolean, parents: Set[TypeVariable])
        (implicit inProcess: Set[(TypeVariable, Boolean)]): CompactType = {
      ty match {
        case p: PrimType => ct(prims = Set(p))
        case FunctionType(l, r) =>
          ct(fun = Some(go(l, !pol, Set.empty) -> go(r, pol, Set.empty)))
        case RecordType(fs) =>
          ct(rec = Some(SortedMap from fs.iterator.map(f => f._1 -> go(f._2, pol, Set.empty))))
        case tv: TypeVariable =>
          val bounds = if (pol) tv.lowerBounds else tv.upperBounds
          val res = ct(vars = Set(tv))
          if (inProcess(tv -> pol))
            if (parents(tv)) ct() // we have a spurious cycle: ignore the bound
            else { tv.recursiveFlag = true; res }
          else (inProcess + (tv -> pol)) pipe { implicit inProcess =>
            if (tv.recursiveFlag) return res
            val bound = bounds.map(b => go(b, pol, parents + tv))
              .reduceOption(merge(pol)).getOrElse(empty)
            if (tv.recursiveFlag) {
              if (!recVars.contains(tv)) recVars += tv -> bound
              res
            } else merge(pol)(bound, res)
          }
      }
    }
    
    CompactTypeScheme(go(ty, true, Set.empty)(Set.empty), recVars)
  }
  
  
  /** Simplifies a CompactTypeScheme by performing a co-occurrence analysis on the type variables. */
  def simplifyType(cty: CompactTypeScheme): CompactTypeScheme = {
    
    // State accumulated during the analysis phase:
    var allVars = SortedSet.from(cty.recVars.keysIterator)(Ordering by (-_.uid))
    var recVars = SortedMap.empty[TypeVariable, () => CompactType](Ordering by (_.uid))
    val coOccurrences: MutMap[(Boolean, TypeVariable), MutSet[SimpleType]] = LinkedHashMap.empty
    
    // This will be filled up after the analysis phase, to influence the reconstruction phase:
    val varSubst = MutMap.empty[TypeVariable, Option[TypeVariable]]
    
    // Traverses the type, performing the analysis, and returns a thunk to reconstruct it later:
    def go(ty: CompactType, pol: Boolean): () => CompactType = {
      ty.vars.foreach { tv =>
        allVars += tv
        val newOccs = LinkedHashSet.from(ty.vars.iterator ++ ty.prims)
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
      val rec_ = ty.rec.map(_.map(f => f._1 -> go(f._2, pol)))
      val fun_ = ty.fun.map(lr => go(lr._1, !pol) -> go(lr._2, pol))
      () => {
        val newVars = ty.vars.flatMap { case tv => varSubst get tv match {
          case Some(Some(tv2)) => tv2 :: Nil
          case Some(None) => Nil
          case None => tv :: Nil
        }}
        CompactType(newVars, ty.prims,
          rec_.map(r => r.map(f => f._1 -> f._2())),
          fun_.map(lr => lr._1() -> lr._2()))
      }
    }
    val gone = go(cty.term, true)
    println(s"[occ] ${coOccurrences}")
    println(s"[rec] ${recVars}")
    
    // Simplify away those non-recursive variables that only occur in positive or negative positions:
    allVars.foreach { case v0 => if (!recVars.contains(v0)) {
      (coOccurrences.get(true -> v0), coOccurrences.get(false -> v0)) match {
        case (Some(_), None) | (None, Some(_)) =>
          println(s"[!] $v0")
          varSubst += v0 -> None; ()
        case occ => assert(occ =/= (None, None))
      }
    }}
    // Unify equivalent variables based on polar co-occurrence analysis:
    val pols = true :: false :: Nil
    allVars.foreach { case v => if (!varSubst.contains(v)) {
      println(s"[v] $v ${coOccurrences.get(true -> v)} ${coOccurrences.get(false -> v)}")
      pols.foreach { pol =>
        coOccurrences.get(pol -> v).iterator.flatMap(_.iterator).foreach {
          case w: TypeVariable if !(w is v) && !varSubst.contains(w) =>
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
                case Some(b_w) => // `w` is a recursive type variable, with bound `b`
                  assert(!coOccurrences.contains((!pol) -> w)) // recursive types have strict polarity
                  recVars -= w // w is merged into v, so we forget about it
                  val b_v = recVars.get(v).getOrElse(() => CompactType.empty)
                  // and record the new recursive bound for v:
                  recVars += v -> (() => CompactType.merge(pol)(b_v(), b_w()))
                case None => // `w` is NOT recursive
                  val wCoOcss = coOccurrences((!pol) -> w)
                  // ^ this must be defined otherwise we'd already have simplified away the non-rec variable
                  coOccurrences((!pol) -> v).filterInPlace(t => t === v || wCoOcss(t))
                  // ^ since `w` is not recursive but co-occurs with `v`, then `v` must not be recursive either!
              }
            }; ()
          case atom: PrimType if (coOccurrences.get(!pol -> v).exists(_(atom))) =>
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
  def expandCompactType(cty: CompactTypeScheme): Type = {
    def go(ty: CompactTypeOrVariable, pol: Boolean)
        (implicit inProcess: Map[(CompactTypeOrVariable, Boolean), () => TypeVar]): Type =
    {
      inProcess.get(ty -> pol) match {
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
          case _ => new TypeVariable(0, Nil, Nil)
        }).asTypeVar
      }
      val res = inProcess + (ty -> pol -> (() => v)) pipe { implicit inProcess =>
        ty match {
          case tv: TypeVariable =>
            cty.recVars.get(tv) match {
              case Some(b) => go(b, pol)
              case _ => tv.asTypeVar
            }
          case CompactType(vars, prims, rec, fun) =>
            val (extr, mrg) = if (pol) (Bot, Union) else (Top, Inter)
            (vars.iterator.map(go(_, pol)).toList
              ::: prims.iterator.map(p => Primitive(p.name)).toList
              ::: rec.map(fs => Record(fs.toList.map(f => f._1 -> go(f._2, pol)))).toList
              ::: fun.map(lr => Function(go(lr._1, !pol), go(lr._2, pol))).toList
            ).reduceOption(mrg).getOrElse(extr)
        }
      }
      if (isRecursive) Recursive(v, res) else res
    }
    go(cty.term, true)(Map.empty)
  }
  
  
}
