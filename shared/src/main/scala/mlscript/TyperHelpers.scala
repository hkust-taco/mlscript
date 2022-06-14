package mlscript

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.annotation.tailrec
import mlscript.utils._, shorthands._

/** Inessential methods used to help debugging. */
abstract class TyperHelpers { Typer: Typer =>
  
  protected var constrainCalls = 0
  protected var annoyingCalls = 0
  protected var subtypingCalls = 0
  protected var constructedTypes = 0
  def stats: (Int, Int, Int, Int) =
    (constrainCalls, annoyingCalls, subtypingCalls, constructedTypes)
  def resetStats(): Unit = {
    constrainCalls = 0
    annoyingCalls  = 0
    subtypingCalls = 0
    constructedTypes = 0
  }
  
  private val noPostTrace: Any => String = _ => ""
  
  protected var indent = 0
  def trace[T](pre: => String)(thunk: => T)(post: T => String = noPostTrace): T = {
    println(pre)
    indent += 1
    val res = try thunk finally indent -= 1
    if (post isnt noPostTrace) println(post(res))
    res
  }
  
  def emitDbg(str: String): Unit = scala.Predef.println(str)
  
  // Shadow Predef functions with debugging-flag-enabled ones:
  
  def println(msg: => Any): Unit = if (dbg) emitDbg("| " * indent + msg)
  
  /** A more advanced println version to show where things are printed from. */
  // def println(msg: => Any)(implicit file: sourcecode.FileName, line: sourcecode.Line): Unit =
  //   if (dbg) {
  //     emitDbg((if (showPrintPrefix) {
  //       val prefix = s"[${file.value}:${line.value}]"
  //       prefix + " " * (30 - prefix.length)
  //     } else "") + "| " * indent + msg)
  //   }
  // val showPrintPrefix =
  //   // false
  //   true
  
  def dbg_assert(assertion: => Boolean): Unit = if (dbg) scala.Predef.assert(assertion)
  // def dbg_assert(assertion: Boolean): Unit = scala.Predef.assert(assertion)
  
  
  def printPol(pol: Opt[Bool]): Str = pol match {
    case S(true) => "+"
    case S(false) => "-"
    case N => "="
  }
  
  def recordIntersection(fs1: Ls[Var -> FieldType], fs2: Ls[Var -> FieldType]): Ls[Var -> FieldType] =
    mergeMap(fs1, fs2)(_ && _).toList
  
  def recordUnion(fs1: Ls[Var -> FieldType], fs2: Ls[Var -> FieldType]): Ls[Var -> FieldType] = {
    val fs2m = fs2.toMap
    fs1.flatMap { case (k, v) => fs2m.get(k).map(v2 => k -> (v || v2)) }
  }

  def subst(ts: PolymorphicType, map: Map[SimpleType, SimpleType]): PolymorphicType = 
    PolymorphicType(ts.level, subst(ts.body, map))

  def subst(st: SimpleType, map: Map[SimpleType, SimpleType], substInMap: Bool = false)
        (implicit cache: MutMap[TypeVariable, SimpleType] = MutMap.empty): SimpleType =
            // trace(s"subst($st)") {
    map.get(st) match {
      case S(res) => if (substInMap) subst(res, map, substInMap) else res
      case N =>
        st match {
          case tv: TypeVariable if tv.lowerBounds.isEmpty && tv.upperBounds.isEmpty =>
            cache += tv -> tv
            tv
          case tv: TypeVariable => cache.getOrElse(tv, {
            val v = freshVar(tv.prov, tv.nameHint)(tv.level)
            cache += tv -> v
            v.lowerBounds = tv.lowerBounds.map(subst(_, map, substInMap))
            v.upperBounds = tv.upperBounds.map(subst(_, map, substInMap))
            v
          })
          case _ => st.map(subst(_, map, substInMap))
        }
    }
    // }(r => s"= $r")
  
  /** Substitutes only at the syntactic level, without updating type variables nor traversing their bounds. */
  def substSyntax(st: SimpleType)(map: PartialFunction[SimpleType, SimpleType]): SimpleType =
    // trace(s"substSyntax $st") {
      map.applyOrElse[ST, ST](st, _.map(substSyntax(_)(map)))
    // }(r => s"=> $r")
  
  def tupleIntersection(fs1: Ls[Opt[Var] -> FieldType], fs2: Ls[Opt[Var] -> FieldType]): Ls[Opt[Var] -> FieldType] = {
    require(fs1.size === fs2.size)
    (fs1 lazyZip fs2).map {
      case ((S(n1), t1), (S(n2), t2)) if n1 =/= n2 => (N, t1 && t2)
      case ((no1, t1), (no2, t2)) => (no1 orElse no2, t1 && t2)
    }
  }
  def tupleUnion(fs1: Ls[Opt[Var] -> FieldType], fs2: Ls[Opt[Var] -> FieldType]): Ls[Opt[Var] -> FieldType] = {
    require(fs1.size === fs2.size)
    (fs1 lazyZip fs2).map {
      case ((S(n1), t1), (S(n2), t2)) => (Option.when(n1 === n2)(n1), t1 || t2)
      case ((no1, t1), (no2, t2)) => (N, t1 || t2)
    }
  }
  
  def factorize(cs: Ls[Conjunct], sort: Bool): Ls[ST] = {
    val factors = MutMap.empty[Factorizable, Int]
    cs.foreach { c =>
      c.vars.foreach { v =>
        factors(v) = factors.getOrElse(v, 0) + 1
      }
      c.nvars.foreach { v =>
        val nv = NegVar(v)
        factors(nv) = factors.getOrElse(nv, 0) + 1
      }
      c.lnf match {
        case LhsTop => ()
        case LhsRefined(_, ttags, _, _) =>
          ttags.foreach { ttg =>
            factors(ttg) = factors.getOrElse(ttg, 0) + 1
          }
      }
      c.rnf match {
        case RhsBot | _: RhsField => ()
        case RhsBases(ps, _, _) =>
          ps.foreach {
            case ttg: TraitTag =>
              val nt = NegTrait(ttg)
              factors(nt) = factors.getOrElse(nt, 0) + 1
            case _ => ()
          }
      }
    }
    factors.maxByOption(_._2) match {
      // case S((fact, n)) =>  // Very strangely, this seems to improve some StressTrait tests slightly...
      case S((fact, n)) if n > 1 =>
        val (factored, rest) = fact match {
          case v: TV =>
            cs.partitionMap(c => if (c.vars(v)) L(c) else R(c))
          case NegVar(v) =>
            cs.partitionMap(c => if (c.nvars(v)) L(c) else R(c))
          case ttg: TraitTag =>
            cs.partitionMap(c => if (c.lnf.hasTag(ttg)) L(c) else R(c))
          case NegTrait(ttg) =>
            cs.partitionMap(c => if (c.rnf.hasTag(ttg)) L(c) else R(c))
        }
        (fact & factorize(factored.map(_ - fact), sort).reduce(_ | _)) :: (
          if (factors.sizeCompare(1) > 0 && factors.exists(f => (f._1 isnt fact) && f._2 > 1))
            factorize(rest, sort)
          else rest.map(_.toType(sort))
        )
      case _ =>
        cs.map(_.toType(sort))
    }
  }
  
  private def cleanupUnion(tys: Ls[ST])(implicit ctx: Ctx): Ls[ST] = {
    var res: Ls[ST] = Nil
    tys.reverseIterator.foreach { ty =>
      if (!res.exists(ty <:< _)) res ::= ty
    }
    res
  }
  def factorize(ctx: Ctx)(ty: ST): ST = {
    cleanupUnion(ty.components(true))(ctx) match {
      case Nil => BotType
      case ty :: Nil => ty
      case cs => factorizeImpl(cs.map(_.components(false)))
    }
  }
  def factorizeImpl(cs: Ls[Ls[ST]]): ST = trace(s"factorize? ${cs.map(_.mkString(" & ")).mkString(" | ")}") {
    def rebuild(cs: Ls[Ls[ST]]): ST =
      cs.iterator.map(_.foldLeft(TopType: ST)(_ & _)).foldLeft(BotType: ST)(_ | _)
    if (cs.sizeCompare(1) <= 0) return rebuild(cs)
    val factors = MutMap.empty[Factorizable, Int]
    cs.foreach { c =>
      c.foreach {
        case tv: TV =>
          factors(tv) = factors.getOrElse(tv, 0) + 1
        case tt: TraitTag =>
          factors(tt) = factors.getOrElse(tt, 0) + 1
        case nv: NegVar =>
          factors(nv) = factors.getOrElse(nv, 0) + 1
        case nt: NegTrait =>
          factors(nt) = factors.getOrElse(nt, 0) + 1
        case _ =>
      }
    }
    println(s"Factors ${factors.mkString(", ")}")
    factors.maxByOption(_._2) match {
      // case S((fact, n)) =>
      case S((fact, n)) if n > 1 =>
        val (factored, rest) =
          cs.partitionMap(c => if (c.contains(fact)) L(c) else R(c))
        println(s"Factor $fact -> ${factored.mkString(", ")}")
        assert(factored.size === n, factored -> n)
        val factoredFactored = fact & factorizeImpl(factored.map(_.filterNot(_ === fact)))
        val restFactored =
          if (factors.sizeCompare(1) > 0 && factors.exists(f => (f._1 isnt fact) && f._2 > 1))
            factorizeImpl(rest)
          else rebuild(rest)
        restFactored | factoredFactored
      case _ => rebuild(cs)
    }
  }(r => s"yes: $r")
  
  
  def mapPol(rt: RecordType, pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType): RecordType =
    RecordType(rt.fields.mapValues(_.update(f(pol.map(!_), _), f(pol, _))))(rt.prov)
  
  def mapPol(bt: BaseType, pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType): BaseType = bt match {
    case FunctionType(lhs, rhs) => FunctionType(f(pol.map(!_), lhs), f(pol, rhs))(bt.prov)
    case TupleType(fields) => TupleType(fields.mapValues(_.update(f(pol.map(!_), _), f(pol, _))))(bt.prov)
    case ArrayType(inner) => ArrayType(inner.update(f(pol.map(!_), _), f(pol, _)))(bt.prov)
    case sp @SpliceType(elems) => sp.updateElems(f(pol, _), f(pol.map(!_), _), f(pol, _))
    case wt @ Without(b: ComposedType, ns @ empty()) => Without(b.map(f(pol, _)), ns)(wt.prov) // FIXME very hacky
    case Without(base, names) => Without(f(pol, base), names)(bt.prov)
    case _: ClassTag => bt
  }
  
  
  
  trait SimpleTypeImpl { self: SimpleType =>
    
    def showProvOver(enabled: Bool)(str: Str): Str =
      if (enabled) str + prov.toString
      else str
    
    // Note: we implement hashCode and equals manually because:
    //  1. On one hand, we want a ProvType to compare equal to its underlying type,
    //      which is necessary for recursive types to associate type provenances to
    //      their recursive uses without making the constraint solver diverge; and
    //  2. Additionally, caching hashCode should have performace benefits
    //      — though I'm not sure whether it's best as a `lazy val` or a `val`.
    override lazy val hashCode: Int = this match {
      case tv: TypeVariable => tv.uid
      case ProvType(und) => und.hashCode
      case p: Product => scala.runtime.ScalaRunTime._hashCode(p)
    }
    override def equals(that: Any): Bool = 
        // trace(s"$this == $that") {
        this match {
      case ProvType(und) => (und: Any) === that
      case tv1: TV => that match {
        case tv2: Typer#TV => tv1.uid === tv2.uid
        case ProvType(und) => this === und
        case _ => false
      }
      case p1: Product => that match {
        case that: ST => that match {
          case ProvType(und) => this === und
          case tv: TV => false
          case p2: Product =>
            p1.canEqual(p2) && p1.productArity === p2.productArity && {
              val it1 = p1.productIterator
              val it2 = p2.productIterator
              while(it1.hasNext && it2.hasNext) {
                if (it1.next() =/= it2.next()) return false
              }
              return !it1.hasNext && !it2.hasNext
            }
        }
        case _ => false
      }
    }
    // }(r => s"= $r")
    
    def map(f: SimpleType => SimpleType): SimpleType = this match {
      case TypeBounds(lb, ub) => TypeBounds(f(lb), f(ub))(prov)
      case FunctionType(lhs, rhs) => FunctionType(f(lhs), f(rhs))(prov)
      case RecordType(fields) => RecordType(fields.mapValues(_.update(f, f)))(prov)
      case TupleType(fields) => TupleType(fields.mapValues(_.update(f, f)))(prov)
      case sp @ SpliceType(fs) => sp.updateElems(f, f, f)
      case ArrayType(inner) => ArrayType(inner.update(f, f))(prov)
      case ComposedType(pol, lhs, rhs) => ComposedType(pol, f(lhs), f(rhs))(prov)
      case NegType(negated) => NegType(f(negated))(prov)
      case Without(base, names) => Without(f(base), names)(prov)
      case ProvType(underlying) => ProvType(f(underlying))(prov)
      case WithType(bse, rcd) => WithType(f(bse), RecordType(rcd.fields.mapValues(_.update(f, f)))(rcd.prov))(prov)
      case ProxyType(underlying) => f(underlying) // TODO different?
      case TypeRef(defn, targs) => TypeRef(defn, targs.map(f(_)))(prov)
      case _: TypeVariable | _: ObjectTag | _: ExtrType => this
    }
    def mapPol(pol: Opt[Bool], smart: Bool = false)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): SimpleType = this match {
      case TypeBounds(lb, ub) if smart && pol.isDefined =>
        if (pol.getOrElse(die)) f(S(true), ub) else f(S(false), lb)
      case TypeBounds(lb, ub) => TypeBounds(f(S(false), lb), f(S(true), ub))(prov)
      case rt: RecordType => Typer.mapPol(rt, pol, smart)(f)
      case Without(base, names) if smart => f(pol, base).without(names)
      case bt: BaseType => Typer.mapPol(bt, pol, smart)(f)
      case ComposedType(kind, lhs, rhs) if smart =>
        if (kind) f(pol, lhs) | f(pol, rhs)
        else f(pol, lhs) & f(pol, rhs)
      case ComposedType(kind, lhs, rhs) => ComposedType(kind, f(pol, lhs), f(pol, rhs))(prov)
      case NegType(negated) if smart => f(pol.map(!_), negated).neg(prov)
      case NegType(negated) => NegType(f(pol.map(!_), negated))(prov)
      case ProvType(underlying) => ProvType(f(pol, underlying))(prov)
      case WithType(bse, rcd) => WithType(f(pol, bse), RecordType(rcd.fields.mapValues(_.update(f(pol.map(!_), _), f(pol, _))))(rcd.prov))(prov)
      case ProxyType(underlying) => f(pol, underlying) // TODO different?
      case tr @ TypeRef(defn, targs) => TypeRef(defn, tr.mapTargs(pol)(f))(prov)
      case _: TypeVariable | _: ObjectTag | _: ExtrType => this
    }
    
    def toUpper(prov: TypeProvenance): FieldType = FieldType(None, this)(prov)
    def toLower(prov: TypeProvenance): FieldType = FieldType(Some(this), TopType)(prov)
    
    def | (that: SimpleType, prov: TypeProvenance = noProv, swapped: Bool = false): SimpleType = (this, that) match {
      case (TopType, _) => TopType
      case (BotType, _) => that
      
      // These were wrong! During constraint solving it's important to keep them!
      // case (_: RecordType, _: PrimType | _: FunctionType) => TopType
      // case (_: FunctionType, _: PrimType | _: RecordType) => TopType
      
      case (_: RecordType, _: FunctionType) => TopType
      case (RecordType(fs1), RecordType(fs2)) =>
        RecordType(recordUnion(fs1, fs2))(prov)
      case (t0 @ TupleType(fs0), t1 @ TupleType(fs1))
        // If the sizes are different, to merge these we'd have to return
        //  the awkward `t0.toArray & t0.toRecord | t1.toArray & t1.toRecord`
      if fs0.sizeCompare(fs1) === 0 =>
        TupleType(tupleUnion(fs0, fs1))(t0.prov)
      case _ if !swapped => that | (this, prov, swapped = true)
      case (`that`, _) => this
      case (NegType(`that`), _) => TopType
      case _ => ComposedType(true, that, this)(prov)
    }
    def & (that: SimpleType, prov: TypeProvenance = noProv, swapped: Bool = false): SimpleType =
        (this, that) match {
      case (TopType | RecordType(Nil), _) => that
      case (BotType, _) => BotType
      // Unnecessary and can complicate constraint solving quite a lot:
      // case (ComposedType(true, l, r), _) => l & that | r & that
      case (_: ClassTag, _: FunctionType) => BotType
      case (FunctionType(l1, r1), FunctionType(l2, r2)) =>
        FunctionType(l1 | l2, r1 & r2)(prov)
      case (RecordType(fs1), RecordType(fs2)) =>
        RecordType(mergeSortedMap(fs1, fs2)(_ && _).toList)(prov)
      case (t0 @ TupleType(fs0), t1 @ TupleType(fs1)) =>
        if (fs0.sizeCompare(fs1) =/= 0) BotType
        else TupleType(tupleIntersection(fs0, fs1))(t0.prov)
      case (TypeBounds(l0, u0), TypeBounds(l1, u1)) =>
        TypeBounds(l0 | l1, u0 & u1)(prov)
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
    
    def >:< (that: SimpleType)(implicit ctx: Ctx): Bool =
      (this is that) || this <:< that && that <:< this
    
    // TODO for composed types and negs, should better first normalize the inequation
    def <:< (that: SimpleType)(implicit ctx: Ctx, cache: MutMap[ST -> ST, Bool] = MutMap.empty): Bool =
    {
    // trace(s"? $this <: $that") {
    // trace(s"? $this <: $that   assuming:  ${
    //     cache.iterator.map(kv => "" + kv._1._1 + (if (kv._2) " <: " else " <? ") + kv._1._2).mkString(" ; ")}") {
      subtypingCalls += 1
      def assume[R](k: MutMap[ST -> ST, Bool] => R): R = k(cache.map(kv => kv._1 -> true))
      (this === that) || ((this, that) match {
        case (RecordType(Nil), _) => TopType <:< that
        case (_, RecordType(Nil)) => this <:< TopType
        case (pt1 @ ClassTag(id1, ps1), pt2 @ ClassTag(id2, ps2)) => (id1 === id2) || pt1.parentsST(id2)
        case (TypeBounds(lb, ub), _) => ub <:< that
        case (_, TypeBounds(lb, ub)) => this <:< lb
        case (FunctionType(l1, r1), FunctionType(l2, r2)) => assume { implicit cache =>
          l2 <:< l1 && r1 <:< r2 
        }
        case (ComposedType(true, l, r), _) => l <:< that && r <:< that
        case (_, ComposedType(false, l, r)) => this <:< l && this <:< r
        case (ComposedType(false, l, r), _) => l <:< that || r <:< that
        case (_, ComposedType(true, l, r)) => this <:< l || this <:< r
        case (RecordType(fs1), RecordType(fs2)) => assume { implicit cache =>
          fs2.forall(f => fs1.find(_._1 === f._1).exists(_._2 <:< f._2))
        }
        case (_: TypeVariable, _) | (_, _: TypeVariable)
          if cache.contains(this -> that)
          => cache(this -> that)
        case (tv: TypeVariable, _) =>
          cache(this -> that) = false
          val tmp = tv.upperBounds.exists(_ <:< that)
          if (tmp) cache(this -> that) = true
          tmp
        case (_, tv: TypeVariable) =>
          cache(this -> that) = false
          val tmp = tv.lowerBounds.exists(this <:< _)
          if (tmp) cache(this -> that) = true
          tmp
        case (ProxyType(und), _) => und <:< that
        case (_, ProxyType(und)) => this <:< und
        case (_, NegType(und)) => (this & und) <:< BotType
        case (NegType(und), _) => TopType <:< (that | und)
        case (_, ExtrType(false)) => true
        case (ExtrType(true), _) => true
        case (_, ExtrType(true)) | (ExtrType(false), _) => false // not sure whether LHS <: Bot (or Top <: RHS)
        case (tr: TypeRef, _)
          if (primitiveTypes contains tr.defn.name) && !tr.defn.name.isCapitalized => tr.expand <:< that
        case (_, tr: TypeRef)
          if (primitiveTypes contains tr.defn.name) && !tr.defn.name.isCapitalized => this <:< tr.expand
        case (tr: TypeRef, _) =>
          ctx.tyDefs.get(tr.defn.name) match {
            case S(td) if td.kind is Cls => clsNameToNomTag(td)(noProv, ctx) <:< that
            case _ => false
          }
        case (_, _: TypeRef) =>
          false // TODO try to expand them (this requires populating the cache because of recursive types)
        case (_: Without, _) | (_, _: Without)
          | (_: ArrayBase, _) | (_, _: ArrayBase)
          | (_: TraitTag, _) | (_, _: TraitTag)
          => false // don't even try
        case (_: FunctionType, _) | (_, _: FunctionType) => false
        case (_: RecordType, _: ObjectTag) | (_: ObjectTag, _: RecordType) => false
        // case _ => lastWords(s"TODO $this $that ${getClass} ${that.getClass()}")
      })
    // }(r => s"! $r")
    }
    
    def isTop: Bool = (TopType <:< this)(Ctx.empty)
    def isBot: Bool = (this <:< BotType)(Ctx.empty)
    
    // * Sometimes, Without types are temporarily pushed to the RHS of constraints,
    // *  sometimes behind a single negation,
    // *  just for the time of massaging the constraint through a type variable.
    // * So it's important we only push and simplify Without types only in _positive_ position!
    def without(names: SortedSet[Var]): SimpleType = if (names.isEmpty) this else this match {
      case Without(b, ns) => Without(b, ns ++ names)(this.prov)
      case _ => Without(this, names)(noProv)
    }
    def without(name: Var): SimpleType = 
      without(SortedSet.single(name))
    
    def withoutPos(names: SortedSet[Var]): SimpleType = if (names.isEmpty) this else this match {
      case Without(b, ns) => Without(b, ns ++ names)(this.prov)
      case t @ FunctionType(l, r) => t
      case t @ ComposedType(true, l, r) => l.without(names) | r.without(names)
      case t @ ComposedType(false, l, r) => l.without(names) & r.without(names)
      case t @ RecordType(fs) => RecordType(fs.filter(nt => !names(nt._1)))(t.prov)
      case t @ TupleType(fs) =>
        val relevantNames = names.filter(n =>
          n.name.startsWith("_")
            && {
              val t = n.name.tail
              t.forall(_.isDigit) && {
                val n = t.toInt
                1 <= n && n <= fs.length
              }
            })
        if (relevantNames.isEmpty) t
        else {
          val rcd = t.toRecord
          rcd.copy(fields = rcd.fields.filterNot(_._1 |> relevantNames))(rcd.prov)
        }
      case t @ ArrayType(ar) => t
      case t @ SpliceType(fs) => ???  // TODO
      case n @ NegType(_ : ClassTag | _: FunctionType | _: RecordType) => n
      case n @ NegType(nt) if (nt match {
        case _: ComposedType | _: ExtrType | _: NegType => true
        // case c: ComposedType => c.pol
        // case _: ExtrType | _: NegType => true
        case _ => false
      }) => nt.neg(n.prov, force = true).withoutPos(names)
      case e @ ExtrType(_) => e // valid? -> seems we could go both ways, but this way simplifies constraint solving
      // case e @ ExtrType(false) => e
      case p @ ProvType(und) => ProvType(und.withoutPos(names))(p.prov)
      case p @ ProxyType(und) => und.withoutPos(names)
      case p: ObjectTag => p
      case TypeBounds(lo, hi) => hi.withoutPos(names)
      case _: TypeVariable | _: NegType | _: TypeRef => Without(this, names)(noProv)
    }
    def unwrapAll(implicit ctx: Ctx): SimpleType = unwrapProxies match {
      case tr: TypeRef => tr.expand.unwrapAll
      case u => u
    }
    def negNormPos(f: SimpleType => SimpleType, p: TypeProvenance)
          (implicit ctx: Ctx, ptr: PreserveTypeRefs): SimpleType = (if (preserveTypeRefs) this else unwrapAll) match {
      case ExtrType(b) => ExtrType(!b)(noProv)
      case ComposedType(true, l, r) => l.negNormPos(f, p) & r.negNormPos(f, p)
      case ComposedType(false, l, r) => l.negNormPos(f, p) | r.negNormPos(f, p)
      case NegType(n) => f(n).withProv(p)
      case tr: TypeRef if !preserveTypeRefs => tr.expand.negNormPos(f, p)
      case _: RecordType | _: FunctionType => BotType // Only valid in positive positions!
        // Because Top<:{x:S}|{y:T}, any record type negation neg{x:S}<:{y:T} for any y=/=x,
        // meaning negated records are basically bottoms.
      case rw => NegType(f(rw))(p)
    }
    def withProvOf(ty: SimpleType): ST = withProv(ty.prov)
    def withProv(p: TypeProvenance): ST = mkProxy(this, p)
    def pushPosWithout(implicit ctx: Ctx, ptr: PreserveTypeRefs): SimpleType = this match {
      case NegType(n) => n.negNormPos(_.pushPosWithout, prov)
      case Without(b, ns) => if (ns.isEmpty) b.pushPosWithout else (if (preserveTypeRefs) b.unwrapProxies else b.unwrapAll).withoutPos(ns) match {
        case Without(c @ ComposedType(pol, l, r), ns) => ComposedType(pol, l.withoutPos(ns), r.withoutPos(ns))(c.prov)
        case Without(NegType(nt), ns) => nt.negNormPos(_.pushPosWithout, nt.prov).withoutPos(ns) match {
          case rw @ Without(NegType(nt), ns) =>
            nt match {
              case _: TypeVariable | _: ClassTag | _: RecordType => rw
              case _ => if (preserveTypeRefs) rw else lastWords(s"$this  $rw  (${nt.getClass})")
            }
          case rw => rw
        }
        case rw => rw
      }
      case _ => this
    }
    def normalize(pol: Bool)(implicit ctx: Ctx): ST = DNF.mk(this, pol = pol).toType()
    
    def abs(that: SimpleType)(prov: TypeProvenance): SimpleType =
      FunctionType(this, that)(prov)
    
    def unwrapProxies: SimpleType = this match {
      case ProxyType(und) => und.unwrapProxies
      case _ => this
    }
    def unwrapProvs: SimpleType = this match {
      case ProvType(und) => und.unwrapProvs
      case _ => this
    }
    
    def components(union: Bool): Ls[ST] = this match {
      case ExtrType(`union`) => Nil
      case ComposedType(`union`, l, r) => l.components(union) ::: r.components(union)
      case NegType(tv: TypeVariable) if !union => NegVar(tv) :: Nil
      case NegType(tt: TraitTag) if !union => NegTrait(tt) :: Nil
      case ProvType(und) => und.components(union)
      case _ => this :: Nil
    }
    
    def childrenPol(pol: Opt[Bool])(implicit ctx: Ctx): List[Opt[Bool] -> SimpleType] = {
      def childrenPolField(fld: FieldType): List[Opt[Bool] -> SimpleType] =
        fld.lb.map(pol.map(!_) -> _).toList ::: pol -> fld.ub :: Nil
      this match {
        case tv: TypeVariable =>
          (if (pol =/= S(false)) tv.lowerBounds.map(S(true) -> _) else Nil) :::
          (if (pol =/= S(true)) tv.upperBounds.map(S(false) -> _) else Nil)
        case FunctionType(l, r) => pol.map(!_) -> l :: pol -> r :: Nil
        case ComposedType(_, l, r) => pol -> l :: pol -> r :: Nil
        case RecordType(fs) => fs.unzip._2.flatMap(childrenPolField)
        case TupleType(fs) => fs.unzip._2.flatMap(childrenPolField)
        case ArrayType(fld) => childrenPolField(fld)
        case SpliceType(elems) => elems flatMap {case L(l) => pol -> l :: Nil case R(r) => childrenPolField(r)}
        case NegType(n) => pol.map(!_) -> n :: Nil
        case ExtrType(_) => Nil
        case ProxyType(und) => pol -> und :: Nil
        case _: ObjectTag => Nil
        case tr: TypeRef => tr.mapTargs(pol)(_ -> _)
        case Without(b, ns) => pol -> b :: Nil
        case TypeBounds(lb, ub) => S(false) -> lb :: S(true) -> ub :: Nil
    }}
    
    def getVarsPol(pol: Opt[Bool])(implicit ctx: Ctx): SortedMap[TypeVariable, Opt[Bool]] = {
      val res = MutMap.empty[TypeVariable, Opt[Bool]]
      @tailrec
      def rec(queue: List[Opt[Bool] -> SimpleType]): Unit =
          // trace(s"getVarsPol ${queue.iterator.map(e => s"${printPol(e._1)}${e._2}").mkString(", ")}") {
          queue match {
        case (tvp, tv: TypeVariable) :: tys =>
          res.get(tv) match {
            case S(N) => rec(tys)
            case S(p) if p === tvp => rec(tys)
            case S(S(p)) =>
              assert(!tvp.contains(p))
              // println(s"$tv -> =")
              res += tv -> N
              rec(tv.childrenPol(tvp) ::: tys)
            case N =>
              res += tv -> tvp
              // println(s"$tv -> ${printPol(tvp)}")
              rec(tv.childrenPol(tvp) ::: tys)
          }
        case (typ, ty) :: tys => rec(ty.childrenPol(typ) ::: tys)
        case Nil => ()
      }
      // }()
      rec(pol -> this :: Nil)
      SortedMap.from(res)(Ordering.by(_.uid))
    }
    
    def children(includeBounds: Bool): List[SimpleType] = this match {
      case tv: TypeVariable => if (includeBounds) tv.lowerBounds ::: tv.upperBounds else Nil
      case FunctionType(l, r) => l :: r :: Nil
      case ComposedType(_, l, r) => l :: r :: Nil
      case RecordType(fs) => fs.flatMap(f => f._2.lb.toList ::: f._2.ub :: Nil)
      case TupleType(fs) => fs.flatMap(f => f._2.lb.toList ::: f._2.ub :: Nil)
      case ArrayType(inner) => inner.lb.toList ++ (inner.ub :: Nil)
      case NegType(n) => n :: Nil
      case ExtrType(_) => Nil
      case ProxyType(und) => und :: Nil
      case _: ObjectTag => Nil
      case TypeRef(d, ts) => ts
      case Without(b, ns) => b :: Nil
      case TypeBounds(lb, ub) => lb :: ub :: Nil
      case SpliceType(fs) => fs.flatMap{ case L(l) => l :: Nil case R(r) => r.lb.toList ::: r.ub :: Nil}
    }
    
    def getVars: SortedSet[TypeVariable] = {
      val res = MutSet.empty[TypeVariable]
      @tailrec def rec(queue: List[SimpleType]): Unit = queue match {
        case (tv: TypeVariable) :: tys =>
          if (res(tv)) rec(tys)
          else { res += tv; rec(tv.children(includeBounds = true) ::: tys) }
        case ty :: tys => rec(ty.children(includeBounds = true) ::: tys)
        case Nil => ()
      }
      rec(this :: Nil)
      SortedSet.from(res)(Ordering.by(_.uid))
    }
    
    def showBounds: String =
      getVars.iterator.filter(tv => (tv.upperBounds ++ tv.lowerBounds).nonEmpty).map(tv =>
        "\n\t\t" + tv.toString
          + (if (tv.lowerBounds.isEmpty) "" else " :> " + tv.lowerBounds.mkString(" | "))
          + (if (tv.upperBounds.isEmpty) "" else " <: " + tv.upperBounds.mkString(" & "))
      ).mkString
    
    def expPos(implicit ctx: Ctx): Type = exp(S(true), this)
    def expNeg(implicit ctx: Ctx): Type = exp(S(false), this)
    def exp(pol: Opt[Bool], ty: ST)(implicit ctx: Ctx): Type = (
      ty
      // |> (_.normalize(false))
      // |> (simplifyType(_, pol, removePolarVars = false, inlineBounds = false))
      // |> (shallowCopy)
      |> (subst(_, Map.empty)) // * Make a copy of the type and its TV graph – although we won't show the TV bounds, we still care about the bounds as they affect class type reconstruction in normalizeTypes_!
      |> (normalizeTypes_!(_, pol)(ctx))
      |> (expandType(_, stopAtTyVars = true))
    )
    
  }
  
  
  def shallowCopy(st: ST)(implicit cache: MutMap[TV, TV] = MutMap.empty): ST = st match {
    case tv: TV => cache.getOrElseUpdate(tv, freshVar(tv.prov, tv.nameHint, Nil, Nil)(tv.level))
    case _ => st.map(shallowCopy)
  }
  
  def merge(pol: Bool, ts: Ls[ST]): ST =
    if (pol) ts.foldLeft(BotType: ST)(_ | _)
    else ts.foldLeft(TopType: ST)(_ & _)
  
  
  class Traverser(implicit ctx: Ctx) {
    def apply(pol: Opt[Bool])(st: ST): Unit = st match {
      case tv: TypeVariable =>
        if (pol =/= S(false)) tv.lowerBounds.foreach(apply(S(true)))
        if (pol =/= S(true)) tv.upperBounds.foreach(apply(S(false)))
      case FunctionType(l, r) => apply(pol.map(!_))(l); apply(pol)(r)
      case ComposedType(_, l, r) => apply(pol)(l); apply(pol)(r)
      case RecordType(fs) => fs.unzip._2.foreach(applyField(pol))
      case TupleType(fs) => fs.unzip._2.foreach(applyField(pol))
      case ArrayType(fld) => applyField(pol)(fld)
      case SpliceType(elems) => elems foreach {case L(l) => apply(pol)(l) case R(r) => applyField(pol)(r)}
      case NegType(n) => apply(pol.map(!_))(n)
      case ExtrType(_) => ()
      case ProxyType(und) => apply(pol)(und)
      case _: ObjectTag => ()
      case tr: TypeRef => tr.mapTargs(pol)(apply(_)(_)); ()
      case Without(b, ns) => apply(pol)(b)
      case TypeBounds(lb, ub) => apply(S(false))(lb); apply(S(true))(ub)
    }
    def applyField(pol: Opt[Bool])(fld: FieldType): Unit = {
      fld.lb.foreach(apply(pol.map(!_)))
      apply(pol)(fld.ub)
    }
  }
  object Traverser {
    trait InvariantFields extends Traverser {
      override def applyField(pol: Opt[Bool])(fld: FieldType): Unit =
        if (fld.lb.exists(_ === fld.ub)) apply(N)(fld.ub)
        else super.applyField(pol)(fld)
    }
  }
  
  
}
