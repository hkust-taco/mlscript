package simplesub

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._
import scala.annotation.tailrec

abstract class TyperHelpers { self: Typer =>
  
  
  // Helper methods
  
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
  
  
  // Conversion into proper immutable type representations
  
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
        mergeMaps(fs0.toMap, fs1.toMap)((t0, t1) => new TypeVariable(0, Nil, t0 :: t1 :: Nil)).toList
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
  
  
}
