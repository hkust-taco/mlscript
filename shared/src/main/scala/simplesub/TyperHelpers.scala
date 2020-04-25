package simplesub

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}

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
    
    def show: String = expandType(this).show
    
  }
  
  
  // Conversion into proper immutable Type representations:
  
  /** Convert an inferred SimpleType into the immutable Type representation. */
  def expandType(sty: SimpleType): Type = {
    def go(ts: SimpleType, polarity: Boolean)(inProcess: Set[(TypeVariable, Boolean)]): Type = ts match {
      case tv: TypeVariable =>
        val v = tv.asTypeVar
        if (inProcess(tv -> polarity)) v
        else {
          val bounds = if (polarity) tv.lowerBounds else tv.upperBounds
          val boundTypes = bounds.map(go(_, polarity)(inProcess + (tv -> polarity)))
          val isRecursive = boundTypes.exists(_.typeVars(v))
          val mrg = if (polarity) Union else Inter
          if (isRecursive) Recursive(v,
            boundTypes.reduceOption(mrg).getOrElse(if (polarity) Bot else Top))
          else boundTypes.foldLeft[Type](v)(mrg)
        }
      case FunctionType(l, r) => Function(go(l, !polarity)(inProcess), go(r, polarity)(inProcess))
      case RecordType(fs) => Record(fs.map(nt => nt._1 -> go(nt._2, polarity)(inProcess)))
      case PrimType(n) => Primitive(n)
    }
    go(sty, true)(Set.empty)
  }
  
  
}
