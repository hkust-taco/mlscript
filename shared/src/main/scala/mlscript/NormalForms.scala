package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import SortedSet.{empty => ssEmp}, SortedMap.{empty => smEmp}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class NormalForms extends TyperDatatypes { self: Typer =>
  
  type ExpandTupleFields >: Bool
  type PreserveTypeRefs >: Bool
  
  def preserveTypeRefs(implicit ptr: PreserveTypeRefs): Bool = ptr === true
  def expandTupleFields(implicit etf: ExpandTupleFields): Bool = etf === true
  
  
  private def mergeTypeRefs(pol: Bool, trs1: SortedMap[TN, TR], trs2: SortedMap[TN, TR])(implicit ctx: Ctx): SortedMap[TN, TR] =
    mergeSortedMap(trs1, trs2) { (tr1, tr2) =>
      assert(tr1.defn === tr2.defn)
      assert(tr1.targs.size === tr2.targs.size)
      TypeRef(tr1.defn, (tr1.targs lazyZip tr2.targs).map((ta1, ta2) => 
          if (pol) TypeBounds.mk(ta1 & ta2, ta1 | ta2) else TypeBounds.mk(ta1 | ta2, ta1 & ta2)
        ))(noProv)
    }
  
  
  sealed abstract class LhsNf {
    def toTypes: Ls[SimpleType] = toType() :: Nil
    def toType(sort: Bool = false): SimpleType =
      if (sort) mkType(true) else underlying
    private def mkType(sort: Bool): SimpleType = this match {
      case LhsRefined(bo, ts, r, trs) =>
        val sr = if (sort) r.sorted else r
        val bo2 = bo.filter {
          case ClassTag(id, parents) => !trs.contains(TypeName(id.idStr.capitalize))
          case _ => true
        }
        val trsBase = trs.valuesIterator.foldRight(bo2.fold[ST](sr)(_ & sr))(_ & _)
        (if (sort) ts.toArray.sorted else ts.toArray).foldLeft(trsBase)(_ & _)
      case LhsTop => TopType
    }
    lazy val underlying: SimpleType = mkType(false)
    def level: Int = underlying.level
    def hasTag(ttg: TraitTag): Bool = this match {
      case LhsRefined(bo, ts, r, trs) => ts(ttg)
      case LhsTop => false
    }
    def size: Int = this match {
      case LhsRefined(bo, ts, r, trs) => bo.size + ts.size + r.fields.size + trs.size
      case LhsTop => 0
    }
    def & (that: BaseTypeOrTag)(implicit etf: ExpandTupleFields): Opt[LhsNf] = (this, that) match {
      case (LhsTop, that: TupleType) => S(LhsRefined(S(that), ssEmp, if (expandTupleFields) that.toRecord else RecordType.empty, smEmp))
      case (LhsTop, that: BaseType) => S(LhsRefined(S(that), ssEmp, RecordType.empty, smEmp))
      case (LhsTop, that: TraitTag) => S(LhsRefined(N, SortedSet.single(that), RecordType.empty, smEmp))
      case (LhsRefined(b1, ts, r1, trs), that: TraitTag) => S(LhsRefined(b1, ts + that, r1, trs))
      case (LhsRefined(b1, ts, r1, trs), that: BaseType) =>
        var r1Final = r1
        ((b1, that) match {
          case (S(p0 @ ClassTag(pt0, ps0)), p1 @ ClassTag(pt1, ps1)) =>
            // println(s"!GLB! $this $that ${p0.glb(p1)}")
            p0.glb(p1)
          case (S(FunctionType(l0, r0)), FunctionType(l1, r1)) =>
            S(FunctionType(l0 | l1, r0 & r1)(noProv/*TODO*/))
          case (S(TupleType(fs0)), tup @ TupleType(fs1)) if fs0.size === fs1.size =>
            if (expandTupleFields)
              r1Final = RecordType(mergeSortedMap(r1Final.fields, tup.toRecord.fields)(_ && _).toList)(noProv)
            S(TupleType(tupleIntersection(fs0, fs1))(noProv))
          case (S(ArrayType(ar)), tup @ TupleType(fs)) =>
            if (expandTupleFields)
              r1Final = RecordType(mergeSortedMap(r1Final.fields, tup.toRecord.fields)(_ && _).toList)(noProv)
            S(TupleType(fs.map { ty =>
              ty._1 -> (ar && ty._2)
            })(noProv))
          case (S(TupleType(fs)), ArrayType(ar)) =>
            S(TupleType(fs.map { ty =>
              ty._1 -> (ty._2 && ar)
            })(noProv))
          case (S(ArrayType(i1)), ArrayType(i2)) =>
            // Array[p] & Array[q] => Array[p & q]
            S(ArrayType(i1 && i2)(noProv))
            
          case (S(w1 @ Without(b1, ns1)), w2 @ Without(b2, ns2)) if ns1 === ns2 =>
            S(Without(b1 & b2, ns1)(w1.prov & w2.prov))
          // The following cases are quite hacky... if we find two incompatible Without types,
          //  just make a new dummy Without type to merge them.
          // The workaround is due to the fact that unlike other types, we can't fully
          //  reduce Without types away, so they are "unduly" treated as `BaseType`s.
          // This will be fixed whe we support proper TV bounds for homomorphic type computations
          case (S(b), w: Without) => S(Without(b & w, ssEmp)(noProv))
          case (S(w: Without), b) => S(Without(w & b, ssEmp)(noProv))
            
          case (S(_), _) => N
          case (N, tup: TupleType) =>
            if (expandTupleFields)
              r1Final = RecordType(mergeSortedMap(r1Final.fields, tup.toRecord.fields)(_ && _).toList)(noProv)
            S(that)
          case (N, _) => S(that)
        }) map { b => LhsRefined(S(b), ts, r1Final, trs) }
    }
    def & (that: RecordType): LhsNf = this match {
      case LhsTop => LhsRefined(N, ssEmp, that, smEmp)
      case LhsRefined(b1, ts, r1, trs) =>
        LhsRefined(b1, ts,
          RecordType(recordIntersection(r1.fields, that.fields))(noProv/*TODO*/), trs)
    }
    def & (that: TypeRef)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[LhsNf] = this match {
      case LhsTop => S(LhsRefined(N, ssEmp, RecordType.empty, SortedMap.single(that.defn -> that)))
      case LhsRefined(b, ts, rt, trs) =>
        val trs2 = trs + (that.defn -> trs.get(that.defn).fold(that) { other =>
          assert(that.targs.sizeCompare(other.targs) === 0)
          TypeRef(that.defn, that.targs.lazyZip(other.targs).map{
            case (ta1, ta2) => TypeBounds.mk(ta1 | ta2, ta1 & ta2)
          }.toList)(that.prov)
        })
        val res = LhsRefined(b, ts, rt, trs2)
        that.mkTag.fold(S(res): Opt[LhsNf])(res & _)
    }
    def & (that: LhsNf)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[LhsNf] = (this, that) match {
      case (_, LhsTop) => S(this)
      case (LhsTop, _) => S(that)
      case (_, LhsRefined(bo, ts, rt, trs)) =>
        ts.iterator.foldLeft(
          trs.valuesIterator.foldLeft((bo.fold(some(this & rt))(this & rt & _)))(_.getOrElse(return N) & _)
        )(_.getOrElse(return N) & _)
    }
    def <:< (that: LhsNf): Bool = (this, that) match {
      case (_, LhsTop) => true
      case (LhsTop, _) => false
      case (LhsRefined(b1, ts1, rt1, trs1), LhsRefined(b2, ts2, rt2, trs2)) =>
        implicit val ctx: Ctx = Ctx.empty
        b2.forall(b2 => b1.exists(_ <:< b2)) &&
          ts2.forall(ts1) && rt1 <:< rt2 &&
          trs2.valuesIterator.forall(tr2 => trs1.valuesIterator.exists(_ <:< tr2))
    }
    def isTop: Bool = isInstanceOf[LhsTop.type]
  }
  case class LhsRefined(base: Opt[BaseType], ttags: SortedSet[TraitTag], reft: RecordType, trefs: SortedMap[TypeName, TypeRef]) extends LhsNf {
    // assert(!trefs.exists(primitiveTypes contains _._1.name))
    override def toString: Str = s"${base.getOrElse("")}${reft}${
      (ttags.iterator ++ trefs.valuesIterator).map("∧"+_).mkString}"
  }
  case object LhsTop extends LhsNf {
    override def toString: Str = "⊤"
  }
  
  
  sealed abstract class RhsNf {
    def toTypes: Ls[SimpleType] = toType() :: Nil
    def toType(sort: Bool = false): SimpleType =
      if (sort) mkType(true) else underlying
    private def mkType(sort: Bool): SimpleType = this match {
      case RhsField(n, t) => RecordType(n -> t :: Nil)(noProv) // FIXME prov
      case RhsBases(ps, bf, trs) =>
        val sr = bf.fold(BotType: ST)(_.fold(identity, _.toType(sort)))
        val trsBase = trs.valuesIterator.foldRight(sr)(_ | _)
        (if (sort) ps.sorted else ps).foldLeft(trsBase)(_ | _)
      case RhsBot => BotType
    }
    lazy val underlying: SimpleType = mkType(false)
    def level: Int = underlying.level
    def hasTag(ttg: TraitTag): Bool = this match {
      case RhsBases(ts, _, trs) => ts.contains(ttg)
      case RhsBot | _: RhsField => false
    }
    def | (that: TypeRef)(implicit ctx: Ctx): Opt[RhsNf] = this match {
      case RhsBot => S(RhsBases(Nil, N, SortedMap.single(that.defn -> that)))
      case RhsField(name, ty) => this | name -> ty
      case RhsBases(prims, bf, trs) =>
        val trs2 = trs + (that.defn -> trs.get(that.defn).fold(that) { other =>
          assert(that.targs.sizeCompare(other.targs) === 0)
          TypeRef(that.defn, that.targs.lazyZip(other.targs).map{
            case (ta1, ta2) => TypeBounds.mk(ta1 & ta2, ta1 | ta2)
          }.toList)(that.prov)
        })
        S(RhsBases(prims, bf, trs2))
    }
    def | (that: RhsNf)(implicit ctx: Ctx): Opt[RhsNf] = that match {
      case RhsBases(prims, bf, trs) =>
        val thisWithTrs = trs.valuesIterator.foldLeft(this)(_ | _ getOrElse (return N))
        val tmp = prims.foldLeft(thisWithTrs)(_ | _ getOrElse (return N))
        S(bf.fold(tmp)(_.fold(tmp | _ getOrElse (return N),
          tmp | _.name_ty getOrElse (return N))))
      case RhsField(name, ty) => this | name -> ty
      case RhsBot => S(this)
    }
    def tryMergeInter(that: RhsNf)(implicit ctx: Ctx): Opt[RhsNf] = (this, that) match {
      case (RhsBot, _) | (_, RhsBot) => S(RhsBot)
      case (RhsField(name1, ty1), RhsField(name2, ty2)) if name1 === name2 => S(RhsField(name1, ty1 && ty2))
      case (RhsBases(prims1, S(R(r1)), trs1), RhsBases(prims2, S(R(r2)), trs2))
        if prims1 === prims2 && trs1 === trs2 && r1.name === r2.name
        => S(RhsBases(prims1, S(R(RhsField(r1.name, r1.ty && r2.ty))), trs1))
      case (RhsBases(prims1, bf1, trs1), RhsBases(prims2, bf2, trs2))
        if prims1 === prims2 && bf1 === bf2 && trs1.keySet === trs2.keySet
        => // * eg for merging `~Foo[S] & ~Foo[T]`:
          S(RhsBases(prims1, bf1, mergeTypeRefs(false, trs1, trs2)))
      case (RhsBases(prims1, bf1, trs1), RhsBases(prims2, bf2, trs2)) =>
        N // TODO could do some more merging here – for the possible base types
      case _ => N
    }
    // TODO use inheritance hierarchy to better merge these
    def | (that: BaseTypeOrTag): Opt[RhsNf] = (this, that) match {
      case (RhsBot, p: ObjectTag) => S(RhsBases(p::Nil,N,smEmp))
      case (RhsBot, that: MiscBaseType) => S(RhsBases(Nil,S(L(that)),smEmp))
      case (RhsBases(ps, bf, trs), p: ClassTag) =>
        S(RhsBases(if (ps.contains(p)) ps else p :: ps , bf, trs))
      case (RhsBases(ps, N, trs), that: MiscBaseType) => S(RhsBases(ps, S(L(that)), trs))
      case (RhsBases(ps, S(L(t1@TupleType(fs1))), trs), t2@TupleType(fs2)) =>
        if (fs1.size =/= fs2.size) 
          RhsBases(ps, S(L(t1.toArray)), trs) | t2.toArray // upcast tuples of different sizes to array
        else S(RhsBases(ps, S(L(TupleType(fs1.lazyZip(fs2).map {
          case ((S(n1), ty1), (S(n2), ty2)) => (if (n1 === n2) S(n1) else N, ty1 || ty2)
          case ((n1o, ty1), (n2o, ty2)) => (n1o orElse n2o, ty1 || ty2)
        })(noProv))), trs))
      case (RhsBases(ps, S(L(ArrayType(_))), trs), t@TupleType(_)) => this | t.toArray
      case (RhsBases(ps, S(L(t@TupleType(_))), trs), ar@ArrayType(_)) => RhsBases(ps, S(L(t.toArray)), trs) | ar
      case (RhsBases(ps, S(L(ArrayType(ar1))), trs), ArrayType(ar2)) => 
        S(RhsBases(ps, S(L(ArrayType(ar1 || ar2)(noProv))), trs))
      case (RhsBases(_, S(L(_: Without)), _), _) | (_, _: Without) => die // Without should be handled elsewhere
      case (RhsBases(ps, S(L(bt)), trs), _) if (that === bt) => S(this)
      case (RhsBases(ps, S(L(FunctionType(l0, r0))), trs), FunctionType(l1, r1)) =>
        S(RhsBases(ps, S(L(FunctionType(l0 & l1, r0 | r1)(noProv))), trs))
      case (RhsBases(ps, bf, trs), tt: TraitTag) =>
        S(RhsBases(if (ps.contains(tt)) ps else tt :: ps, bf, trs))
      case (f @ RhsField(_, _), p: ObjectTag) => S(RhsBases(p::Nil, S(R(f)), smEmp))
      case (f @ RhsField(_, _), _: FunctionType | _: ArrayBase) =>
        // S(RhsBases(Nil, S(that), S(f)))
        N // can't merge a record and a function or a tuple -> it's the same as Top
        // NOTE: in the future, if we do actually register fields in named tuples
        //  (so their fields is not pure compiler fiction,
        //    as it is currently and in TypeScript arrays),
        //  we will want to revisit this...
      case
          (RhsBases(_, S(L(_: FunctionType)), _), _: ArrayBase)
        | (RhsBases(_, S(L(_: ArrayBase)), _), _: FunctionType)
        | (RhsBases(_, S(R(_)), _), _: FunctionType | _: ArrayBase)
        => N
      case (RhsBases(_, Some(Left(SpliceType(_))), _), _) | (_, _: SpliceType) => ??? // TODO
    }
    def | (that: (Var, FieldType)): Opt[RhsNf] = this match {
      case RhsBot => S(RhsField(that._1, that._2))
      case RhsField(n1, t1) if n1 === that._1 => S(RhsField(n1, t1 || that._2))
      case RhsBases(p, N, trs) => S(RhsBases(p, S(R(RhsField(that._1, that._2))), trs))
      case RhsBases(p, S(R(RhsField(n1, t1))), trs) if n1 === that._1 =>
        S(RhsBases(p, S(R(RhsField(n1, t1 || that._2))), trs))
      case _: RhsField | _: RhsBases => N
    }
    def <:< (that: RhsNf): Bool = (this.toType() <:< that.toType())(Ctx.empty) // TODO less inefficient! (uncached calls to toType)
    def isBot: Bool = isInstanceOf[RhsBot.type]
  }
  case class RhsField(name: Var, ty: FieldType) extends RhsNf {
    def name_ty: Var -> FieldType = name -> ty
    override def toString: Str = s"{$name:$ty}"
  }
  case class RhsBases(tags: Ls[ObjectTag], rest: Opt[MiscBaseType \/ RhsField], trefs: SortedMap[TypeName, TypeRef]) extends RhsNf {
    override def toString: Str =
      s"${tags.mkString("|")}${rest.fold("")("|" + _.fold(""+_, ""+_))}${trefs.valuesIterator.map("|"+_).mkString}"
  }
  case object RhsBot extends RhsNf {
    override def toString: Str = "⊥"
  }
  
  
  case class Conjunct(lnf: LhsNf, vars: SortedSet[TypeVariable], rnf: RhsNf, nvars: SortedSet[TypeVariable]) extends Ordered[Conjunct] {
    def compare(that: Conjunct): Int = this.toString compare that.toString // TODO less inefficient!!
    def toType(sort: Bool = false): SimpleType =
      toTypeWith(_.toType(sort), _.toType(sort), sort)
    def toTypeWith(f: LhsNf => SimpleType, g: RhsNf => SimpleType, sort: Bool = false): SimpleType =
      ((if (sort) vars.toArray.sorted.iterator else vars.iterator) ++ Iterator(g(rnf).neg())
        ++ (if (sort) nvars.toArray.sorted.iterator else nvars).map(_.neg())).foldLeft(f(lnf))(_ & _)
    lazy val level: Int = (vars.iterator ++ nvars).map(_.level).++(Iterator(lnf.level, rnf.level)).max
    def - (fact: Factorizable): Conjunct = fact match {
      case tv: TV => Conjunct(lnf, vars - tv, rnf, nvars)
      case NegVar(tv) => Conjunct(lnf, vars, rnf, nvars - tv)
      case tt: TraitTag => lnf match {
        case LhsRefined(b, tts, rft, trs) =>
          if (tts(tt)) copy(lnf = LhsRefined(b, tts - tt, rft, trs)) else this
        case LhsTop => this
      }
      case NegTrait(tt) => rnf match {
        case RhsBases(tts, r, trs) => copy(rnf = RhsBases(tts.filterNot(_ === tt), r, trs))
        case RhsBot | _: RhsField => this
      }
    }
    def <:< (that: Conjunct): Bool =
      // trace(s"?? $this <:< $that") {
      that.vars.forall(vars) &&
        lnf <:< that.lnf &&
        that.rnf <:< rnf &&
        that.nvars.forall(nvars)
      // }(r => s"!! $r")
    def & (that: Conjunct)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[Conjunct] =
      // trace(s"?? $this & $that ${lnf & that.lnf} ${rnf | that.rnf}") {
      if ((lnf.toType() <:< that.rnf.toType())(Ctx.empty)) N // TODO support <:< on any Nf? // TODO less inefficient! (uncached calls to toType)
      else S(Conjunct.mk(lnf & that.lnf getOrElse (return N), vars | that.vars
        , rnf | that.rnf getOrElse (return N)
        , nvars | that.nvars))
      // }(r => s"!! $r")
    def neg: Disjunct = Disjunct(rnf, nvars, lnf, vars)
    /** `tryMergeUnion` tries to compute the union of two conjuncts as a conjunct,
      * failing if this merging cannot be done without losing information.
      * This ends up simplifying away things like:
      *   {x: int} | {y: int} ~> anything
      *   (A -> B) | {x: C}   ~> anything  */
    def tryMergeUnion(that: Conjunct)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[Conjunct] = (this, that) match {
      case _ if this <:< that => S(that)
      case _ if that <:< this => S(this)
      case (Conjunct(LhsTop, vs1, r1, nvs1), Conjunct(LhsTop, vs2, r2, nvs2))
        if vs1 === vs2 && nvs1 === nvs2
      =>
        S(Conjunct(LhsTop, vs1, r1 tryMergeInter r2 getOrElse (return N), nvs1))
        // * Conceptually, `tryMergeInter` could return None either because the ThsNfs cannot be merged
        // *  or because merging them would return bottom... but conjuncts cannot represent bottom.
      case (Conjunct(LhsRefined(bse1, ts1, rcd1, trs1), vs1, r1, nvs1)
          , Conjunct(LhsRefined(bse2, ts2, rcd2, trs2), vs2, r2, nvs2))
        if bse1 === bse2 && ts1 === ts2 && vs1 === vs2 && r1 === r2 && nvs1 === nvs2
        && trs1.keySet === trs2.keySet
      =>
        val trs = mergeTypeRefs(true, trs1, trs2)
        val rcd = RecordType(recordUnion(rcd1.fields, rcd2.fields))(noProv)
        S(Conjunct(LhsRefined(bse1, ts1, rcd, trs), vs1, r1, nvs1))
      case (Conjunct(LhsRefined(bse1, ts1, rcd1, trs1), vs1, r1, nvs1)
          , Conjunct(LhsRefined(bse2, ts2, rcd2, trs2), vs2, r2, nvs2))
        if ts1 === ts2 && vs1 === vs2 && r1 === r2 && nvs1 === nvs2
        && trs1 === trs2 // TODO!!
      =>
        val ts = ts1
        
        val rcdU = RecordType(recordUnion(
          if (expandTupleFields) rcd1.fields
            else bse1.map(_.toRecord.fields).fold(rcd1.fields)(recordIntersection(rcd1.fields, _)),
          if (expandTupleFields) rcd2.fields
            else bse2.map(_.toRecord.fields).fold(rcd2.fields)(recordIntersection(rcd2.fields, _)),
        ))(noProv)
        
        // Example:
        //    Why is it sound to merge (A -> B) & {R} | (C -> D) & {S}
        //    into ((A & C) -> (B | D)) & ({R} | {S}) ?
        //  Because the former can be distributed to
        //    (A -> B | C -> D) & (A -> B | {S}) & ({R} | C -> D) & ({R} | {S})
        //    == ((A & C) -> (B | D)) & Top & Top & ({R} | {S})
        (bse1, bse2) match {
          case (S(FunctionType(l1, r1)), S(FunctionType(l2, r2))) => // TODO Q: records ok here?!
            S(Conjunct(
              LhsRefined(S(FunctionType(l1 & l2, r1 | r2)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (S(tup1 @ TupleType(fs1)), S(tup2 @ TupleType(fs2))) => // TODO Q: records ok here?!
            if (fs1.size =/= fs2.size) S(Conjunct(
              LhsRefined(S(ArrayType(tup1.inner || tup2.inner)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
            else S(Conjunct(
              LhsRefined(S(TupleType(tupleUnion(fs1, fs2))(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (S(tup @ TupleType(fs)), S(ArrayType(ar))) =>
            S(Conjunct(LhsRefined(S(ArrayType(tup.inner || ar)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (S(ArrayType(ar)), S(tup @ TupleType(fs))) =>
            S(Conjunct(
              LhsRefined(S(ArrayType(tup.inner || ar)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (S(ArrayType(ar1)), S(ArrayType(ar2))) =>
            S(Conjunct(LhsRefined(S(ArrayType(ar1 || ar2)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (N, N)
            | (S(_: FunctionType), S(_: ArrayBase)) | (S(_: ArrayBase), S(_: FunctionType))
          =>
            S(Conjunct(LhsRefined(N, ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case _ => N
        }
        case _ => N
      }
    override def toString: Str =
      (Iterator(lnf).filter(_ =/= LhsTop) ++ vars
        ++ (Iterator(rnf).filter(_ =/= RhsBot) ++ nvars).map("~("+_+")")).mkString("∧")
  }
  
  object Conjunct {
    def of(tvs: SortedSet[TypeVariable]): Conjunct = Conjunct(LhsTop, tvs, RhsBot, ssEmp)
    def mk(lnf: LhsNf, vars: SortedSet[TypeVariable], rnf: RhsNf, nvars: SortedSet[TypeVariable])(implicit etf: ExpandTupleFields): Conjunct = {
      Conjunct(lnf, vars, rnf match {
        case RhsField(name, ty) => RhsField(name, ty)
        case RhsBases(prims, bf, trs) =>
          RhsBases(prims.filter(lnf & _ pipe (_.isDefined)), bf.filter {
            case L(b) => lnf & b pipe (_.isDefined)
            case R(r) => true
          }, trs)
        case RhsBot => RhsBot
      }, nvars)
    }
  }
  
  
  case class Disjunct(rnf: RhsNf, vars: SortedSet[TypeVariable], lnf: LhsNf, nvars: SortedSet[TypeVariable]) {
    def neg: Conjunct = Conjunct(lnf, nvars, rnf, vars)
    def | (that: Disjunct)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[Disjunct] =
      S(Disjunct(rnf | that.rnf getOrElse (return N), vars | that.vars,
        lnf & that.lnf getOrElse (return N), nvars | that.nvars))
    override def toString: Str =
      (Iterator(rnf).filter(_ =/= RhsBot) ++ vars
        ++ (Iterator(lnf).filter(_ =/= LhsTop) ++ nvars).map("~"+_)).mkString("∨")
  }
  
  object Disjunct {
    def of(tvs: SortedSet[TypeVariable]): Disjunct = Disjunct(RhsBot, tvs, LhsTop, ssEmp)
  }
  
  
  case class DNF(cs: Ls[Conjunct]) {
    def isBot: Bool = cs.isEmpty
    def toType(sort: Bool = false): SimpleType = (if (sort) cs.sorted else cs) match {
      case Nil => BotType
      case t :: ts => t.toType(sort) | DNF(ts).toType(sort)
    }
    def level: Int = cs.maxByOption(_.level).fold(0)(_.level)
    def & (that: DNF)(implicit ctx: Ctx, etf: ExpandTupleFields): DNF =
      that.cs.map(this & _).foldLeft(DNF.extr(false))(_ | _)
    def | (that: DNF)(implicit ctx: Ctx, etf: ExpandTupleFields): DNF = that.cs.foldLeft(this)(_ | _)
    def & (that: Conjunct)(implicit ctx: Ctx, etf: ExpandTupleFields): DNF =
      DNF(cs.flatMap(_ & that)) // TODO may need further simplif afterward
    def | (that: Conjunct)(implicit ctx: Ctx, etf: ExpandTupleFields): DNF = {
      def go(cs: Ls[Conjunct], acc: Ls[Conjunct], toMerge: Conjunct): Ls[Conjunct] = 
        // trace(s"go?? $cs $acc M $toMerge") {
        cs match {
        case c :: cs =>
          if (c <:< toMerge) acc.reverse ::: toMerge :: cs
          else if (toMerge <:< c) acc.reverse ::: c :: cs
          else c.tryMergeUnion(toMerge) match {
            case Some(value) => acc.reverse ::: value :: cs
            case None => go(cs, c :: acc, toMerge)
          }
        case Nil => (toMerge :: acc).reverse
      }
      // }(r => s"go!! $r")
      DNF(go(cs, Nil, that))
    }
    override def toString: Str = s"DNF(${cs.mkString(" | ")})"
  }
  
  object DNF {
    def of(lnf: LhsNf): DNF = DNF(Conjunct(lnf, ssEmp, RhsBot, ssEmp) :: Nil)
    def of(bt: BaseType)(implicit etf: ExpandTupleFields): DNF = DNF.of(LhsRefined(S(bt), ssEmp, if (expandTupleFields) bt.toRecord else RecordType.empty, smEmp))
    def of(tt: TraitTag): DNF = DNF.of(LhsRefined(N, SortedSet.single(tt), RecordType.empty, smEmp))
    def of(rcd: RecordType): DNF = DNF.of(LhsRefined(N, ssEmp, rcd, smEmp))
    def of(tvs: SortedSet[TypeVariable]): DNF = DNF(Conjunct.of(tvs) :: Nil)
    def extr(pol: Bool): DNF = if (pol) of(LhsTop) else DNF(Nil)
    def merge(pol: Bool)(l: DNF, r: DNF)(implicit ctx: Ctx, etf: ExpandTupleFields): DNF = if (pol) l | r else l & r
    
    def mkDeep(ty: SimpleType, pol: Bool)
          (implicit ctx: Ctx, ptr: PreserveTypeRefs = false, etf: ExpandTupleFields = true): DNF = {
      mk(mkDeepST(ty, pol), pol)
    }
    def mkDeepST(ty: SimpleType, pol: Bool)
          (implicit ctx: Ctx, ptr: PreserveTypeRefs = false, etf: ExpandTupleFields = true): ST = ty match {
      case ProvType(und) =>
        mkDeepST(und, pol).withProv(ty.prov)
      case TypeBounds(lb, ub) => mkDeepST(if (pol) ub else lb, pol).withProv(ty.prov)
      case _ =>
        val dnf = mk(ty, pol)
        def go(polo: Opt[Bool], st: ST): ST = polo match {
          case _ if st === ty => ty.mapPol(polo)(go)
          case S(pol) => mkDeepST(st, pol)(ctx, ptr = true, etf = false)
          case N => TypeBounds.mk(
            mkDeepST(st, false)(ctx, ptr = true, etf = false),
            mkDeepST(st, false)(ctx, ptr = true, etf = false))
        }
        dnf.toType().mapPol(S(pol))(go)
    }
    
    def mk(ty: SimpleType, pol: Bool)(implicit ctx: Ctx, ptr: PreserveTypeRefs = false, etf: ExpandTupleFields = true): DNF =
        // trace(s"DNF[$pol,$ptr,$etf](${ty})") {
        (if (pol) ty.pushPosWithout else ty) match {
      case bt: BaseType => of(bt)
      case bt: TraitTag => of(bt)
      case rt @ RecordType(fs) => of(rt)
      case ExtrType(pol) => extr(!pol)
      case ty @ ComposedType(p, l, r) => merge(p)(mk(l, pol), mk(r, pol))
      case NegType(und) => DNF(CNF.mk(und, !pol).ds.map(_.neg))
      case tv: TypeVariable => of(SortedSet.single(tv))
      case ProxyType(underlying) => mk(underlying, pol)
      case tr @ TypeRef(defn, targs) =>
        // * TODO later: when proper TypeRef-based simplif. is implemented, can remove this special case
        if (preserveTypeRefs && !primitiveTypes.contains(defn.name)) {
          of(LhsRefined(tr.mkTag, ssEmp, RecordType.empty, SortedMap(defn -> tr)))
        } else mk(tr.expand, pol)
      case TypeBounds(lb, ub) => mk(if (pol) ub else lb, pol)
    }
    // }(r => s"= $r")
  }
  
  
  case class CNF(ds: Ls[Disjunct]) {
    def & (that: CNF): CNF = that.ds.foldLeft(this)(_ & _)
    def | (that: CNF)(implicit ctx: Ctx, etf: ExpandTupleFields): CNF = that.ds.map(this | _).foldLeft(CNF.extr(false))(_ & _)
    def & (that: Disjunct): CNF =
      // TODO try to merge it with the others if possible
      CNF(that :: ds)
    def | (that: Disjunct)(implicit ctx: Ctx, etf: ExpandTupleFields): CNF = CNF(ds.flatMap(_ | that))
    override def toString: Str = s"CNF(${ds.mkString(" & ")})"
  }
  
  object CNF {
    def of(rnf: RhsNf): CNF = CNF(Disjunct(rnf, ssEmp, LhsTop, ssEmp) :: Nil)
    def of(bt: BaseType): CNF =
      CNF.of(RhsBot | bt getOrElse (return CNF.extr(true)))
    def of(tvs: SortedSet[TypeVariable]): CNF = CNF(Disjunct.of(tvs) :: Nil)
    def of(rcd: RecordType): CNF = CNF(rcd.fields.iterator.map(f =>
      Disjunct(RhsField(f._1, f._2), ssEmp, LhsTop, ssEmp)).toList)
    def extr(pol: Bool): CNF = if (pol) CNF(Nil) else of(RhsBot)
    def merge(pol: Bool)(l: CNF, r: CNF)(implicit ctx: Ctx, etf: ExpandTupleFields): CNF = if (pol) l | r else l & r
    def mk(ty: SimpleType, pol: Bool)(implicit ctx: Ctx, ptr: PreserveTypeRefs, etf: ExpandTupleFields): CNF =
      // trace(s"?CNF $ty") {
      ty match {
        case bt: BaseType => of(bt)
        case tt: TraitTag => of(RhsBases(tt :: Nil, N, smEmp))
        case rt @ RecordType(fs) => of(rt)
        case ExtrType(pol) => extr(!pol)
        case ty @ ComposedType(p, l, r) => merge(p)(mk(l, pol), mk(r, pol))
        case NegType(und) => CNF(DNF.mk(und, !pol).cs.map(_.neg))
        case tv: TypeVariable => of(SortedSet.single(tv))
        case ProxyType(underlying) => mk(underlying, pol)
        case tr @ TypeRef(defn, targs) =>
          if (preserveTypeRefs && !primitiveTypes.contains(defn.name)) {
            CNF(Disjunct(RhsBases(Nil, N, SortedMap.single(defn -> tr)), ssEmp, LhsTop, ssEmp) :: Nil)
          } else mk(tr.expand, pol)
        case TypeBounds(lb, ub) => mk(if (pol) ub else lb, pol)
      }
      // }(r => s"!CNF $r")
  }
  
  
}
