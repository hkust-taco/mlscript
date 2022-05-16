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
  
  sealed abstract class LhsNf {
    def toTypes: Ls[SimpleType] = toType() :: Nil
    def toType(sort: Bool = false): SimpleType =
      if (sort) mkType(true) else underlying
    private def mkType(sort: Bool): SimpleType = this match {
      case LhsRefined(bo, ts, r, trs) =>
        val sr = if (sort) r.sorted else r
        // (trs.valuesIterator ++ ts.toArray.sorted).foldLeft(bo.fold[ST](sr)(_ & sr))(_ & _)
        val trsBase = trs.valuesIterator.foldRight(bo.fold[ST](sr)(_ & sr))(_ & _)
        (if (sort) ts.toArray.sorted else ts.toArray).foldLeft(trsBase)(_ & _)
        // ts.toArray.sorted.foldLeft(trs.valuesIterator.foldLeft(bo.fold[ST](sr)(_ & sr))(_ & _))(_ & _)
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
          // // RecordType(mergeMap(r1.fields, that.fields)(_ & _).toList)(noProv/*TODO*/), trs)
          // RecordType(mergeMap(r1.fields, that.fields)(_ && _).toList)(noProv/*TODO*/))
          RecordType(recordIntersection(r1.fields, that.fields))(noProv/*TODO*/), trs)
    }
    def & (that: TypeRef): Opt[LhsNf] = this match {
      case LhsTop => S(LhsRefined(N, ssEmp, RecordType.empty, SortedMap.single(that.defn -> that)))
      case LhsRefined(b, ts, rt, trs) =>
        val trs2 = trs + (that.defn -> trs.get(that.defn).fold(that) { other =>
          assert(that.targs.sizeCompare(other.targs) === 0)
          TypeRef(that.defn, that.targs.lazyZip(other.targs).map{
            case (ta1, ta2) => TypeBounds.mk2(ta1 | ta2, ta1 & ta2)
          }.toList)(that.prov)
        })
        S(LhsRefined(b, ts, rt, trs2))
    }
    def & (that: LhsNf)(implicit etf: ExpandTupleFields): Opt[LhsNf] = (this, that) match {
      case (_, LhsTop) => S(this)
      case (LhsTop, _) => S(that)
      case (_, LhsRefined(bo, ts, rt, trs)) =>
        ts.iterator.foldLeft(
          trs.valuesIterator.foldLeft((bo.fold(some(this & rt))(this & rt & _)))(_.getOrElse(return N) & _)
        )(_.getOrElse(return N) & _)
      // case (_, LhsRefined(S(b), ts, rt, trs)) =>
      //   // (ts.iterator ++ trs.valuesIterator).foldLeft(this & rt & b)(_.getOrElse(return N) & _)
      //   ts.iterator.foldLeft(
      //     trs.valuesIterator.foldLeft(this & rt & b)(_.getOrElse(return N) & _)
      //   )(_.getOrElse(return N) & _)
      // case (_, LhsRefined(N, ts, rt, trs)) =>
      //   S(ts.foldLeft(this & rt)(_ & _ getOrElse (return N)))
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
    // def size: Int = this match {
    //   case RhsBases(ts, r, trs) => ts.size + 1 + ???
    //   case _: RhsField => 1
    //   case RhsBot => 0
    // }
    def | (that: TypeRef): Opt[RhsNf] = this match {
    // def | (that: TypeRef): RhsNf = this match {
      case RhsBot => S(RhsBases(Nil, N, SortedMap.single(that.defn -> that)))
      case RhsField(name, ty) => this | name -> ty
      case RhsBases(prims, bf, trs) =>
        val trs2 = trs + (that.defn -> trs.get(that.defn).fold(that) { other =>
          assert(that.targs.sizeCompare(other.targs) === 0)
          TypeRef(that.defn, that.targs.lazyZip(other.targs).map{
            case (ta1, ta2) => TypeBounds.mk2(ta1 & ta2, ta1 | ta2)
          }.toList)(that.prov)
        })
        S(RhsBases(prims, bf, trs2))
    }
    def | (that: RhsNf): Opt[RhsNf] = that match {
      case RhsBases(prims, bf, trs) =>
        // val thisWithTrs = this match {
        //   case RhsBases(tags, rest, trefs) => 
        // }
        val thisWithTrs = trs.valuesIterator.foldLeft(this)(_ | _ getOrElse (return N))
        // println(s"thisWithTrs $thisWithTrs")
        // val thisWithTrs = trs.valuesIterator.foldLeft(this)(_ | _)
        val tmp = prims.foldLeft(thisWithTrs)(_ | _ getOrElse (return N))
        S(bf.fold(tmp)(_.fold(tmp | _ getOrElse (return N),
          tmp | _.name_ty getOrElse (return N))))
      case RhsField(name, ty) => this | name -> ty
      case RhsBot => S(this)
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
  case class RhsField(name: Var, ty: FieldType) extends RhsNf
    { def name_ty: Var -> FieldType = name -> ty }
  case class RhsBases(tags: Ls[ObjectTag], rest: Opt[MiscBaseType \/ RhsField], trefs: SortedMap[TypeName, TypeRef]) extends RhsNf {
    // override def toString: Str = s"${tags.mkString("|")}|$rest"
    override def toString: Str = s"${tags.mkString("|")}${rest.fold("")("|" + _)}${trefs.valuesIterator.map("|"+_).mkString}"
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
    // lazy val interSize: Int = vars.size + nvars.size + lnf.size + rnf.size
    def <:< (that: Conjunct): Bool =
      // trace(s"?? $this <:< $that") {
      that.vars.forall(vars) &&
        lnf <:< that.lnf &&
        that.rnf <:< rnf &&
        that.nvars.forall(nvars)
      // }(r => s"!! $r")
    def & (that: Conjunct)(implicit etf: ExpandTupleFields): Opt[Conjunct] =
      // trace(s"?? $this & $that ${lnf & that.lnf} ${rnf | that.rnf}") {
      if ((lnf.toType() <:< that.rnf.toType())(Ctx.empty)) N // TODO support <:< on any Nf? // TODO less inefficient! (uncached calls to toType)
      else S(Conjunct.mk(lnf & that.lnf getOrElse (return N), vars | that.vars
        , rnf | that.rnf getOrElse (return N)
        , nvars | that.nvars))
      // }(r => s"!! $r")
    def neg: Disjunct = Disjunct(rnf, nvars, lnf, vars)
    /** `tryMerge` tries to compute the union of two conjuncts as a conjunct,
      * failing if this merging cannot be done without losing information.
      * This ends up simplifying away things like:
      *   {x: int} | {y: int} ~> anything
      *   (A -> B) | {x: C}   ~> anything  */
    def tryMerge(that: Conjunct)(implicit etf: ExpandTupleFields): Opt[Conjunct] = (this, that) match {
      case (Conjunct(LhsRefined(bse1, ts1, rcd1, trs1), vs1, r1, nvs1)
          , Conjunct(LhsRefined(bse2, ts2, rcd2, trs2), vs2, r2, nvs2))
        if bse1 === bse2 && ts1 === ts2 && vs1 === vs2 && r1 === r2 && nvs1 === nvs2
        && trs1.keySet === trs2.keySet
      =>
        val trs = mergeSortedMap(trs1, trs2) { (tr1, tr2) =>
          assert(tr1.defn === tr2.defn)
          assert(tr1.targs.size === tr2.targs.size)
          TypeRef(tr1.defn, (tr1.targs lazyZip tr2.targs).map((ta1, ta2) => 
            TypeBounds.mk2(ta1 | ta2, ta1 & ta2)))(noProv)
        }
        val rcd = RecordType(recordUnion(rcd1.fields, rcd2.fields))(noProv)
        S(Conjunct(LhsRefined(bse1, ts1, rcd, trs), vs1, r1, nvs1))
      case (Conjunct(LhsRefined(bse1, ts1, rcd1, trs1), vs1, r1, nvs1)
          , Conjunct(LhsRefined(bse2, ts2, rcd2, trs2), vs2, r2, nvs2))
        if vs1 === vs2 && r1 === r2 && nvs1 === nvs2 && ts1 === ts2
        && trs1 === trs2 // TODO!!
      =>
        val ts = ts1
        // val rcdU_ = recordUnion(rcd1.fields, rcd2.fields)
        // val rcdU = RecordType(
        //   if (expandTupleFields) rcdU_
        //   else bse1.fold(bse2.map(_.toRecord.fields).fold(rcdU_)(recordUnion(rcdU_, _))) { b1 =>
        //     val u = recordUnion(rcdU_, b1.toRecord.fields)
        //     bse2.map(_.toRecord.fields).fold(u)(recordUnion(u, _))
        //   }
        // )(noProv)
        
        // println(">>>>>>>"+expandTupleFields, rcd1, rcd2, rcdU_, rcdU)
        // println(">>>>>>>", bse1.map(_.toRecord), bse2.map(_.toRecord))
        // println(">>>>>>>", bse1.fold(bse2.map(_.toRecord.fields).fold(rcdU_)(recordUnion(rcdU_, _))) { b1 =>
        //     val u = recordUnion(rcdU_, b1.toRecord.fields)
        //     println(rcdU_, u)
        //     bse2.map(_.toRecord.fields).fold(u)(recordUnion(u, _))
        //   })
        val rcdU = RecordType(recordUnion(
          if (expandTupleFields) rcd1.fields else bse1.map(_.toRecord.fields).fold(rcd1.fields)(recordIntersection(rcd1.fields, _)),
          if (expandTupleFields) rcd2.fields else bse2.map(_.toRecord.fields).fold(rcd2.fields)(recordIntersection(rcd2.fields, _)),
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
              // LhsRefined(S(ArrayType(tup1.inner | tup2.inner)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
              // LhsRefined(S(ArrayType(tup1.inner || tup2.inner)(noProv)), ts, rcdU), vs1, RhsBot, nvs1))
              LhsRefined(S(ArrayType(tup1.inner || tup2.inner)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
            else S(Conjunct(
              LhsRefined(S(TupleType(tupleUnion(fs1, fs2))(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (S(tup @ TupleType(fs)), S(ArrayType(ar))) =>
            S(Conjunct(
              // LhsRefined(S(ArrayType(tup.inner || ar)(noProv)), ts, rcdU), vs1, RhsBot, nvs1))
              // LhsRefined(S(ArrayType(tup.inner | ar)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
              LhsRefined(S(ArrayType(tup.inner || ar)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          // case (S(ArrayType(ar)), S(tup @ TupleType(fs))) =>
          //   S(Conjunct(
          //     LhsRefined(S(ArrayType(tup.inner || ar)(noProv)), ts, rcdU), vs1, RhsBot, nvs1))
          // case (S(ArrayType(ar)), S(tup @ TupleType(fs))) =>
          //   S(Conjunct(
          //     LhsRefined(S(ArrayType(tup.inner | ar)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (S(ArrayType(ar)), S(tup @ TupleType(fs))) =>
            S(Conjunct(
              LhsRefined(S(ArrayType(tup.inner || ar)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          // case (S(ArrayType(ar1)), S(ArrayType(ar2))) =>
          //   S(Conjunct(LhsRefined(S(ArrayType(ar1 | ar2)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          // case (S(ArrayType(ar1)), S(ArrayType(ar2))) =>
          //   S(Conjunct(LhsRefined(S(ArrayType(ar1 || ar2)(noProv)), ts, rcdU), vs1, RhsBot, nvs1))
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
        ++ (Iterator(rnf).filter(_ =/= RhsBot) ++ nvars).map("~"+_)).mkString("∧")
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
    def | (that: Disjunct)(implicit etf: ExpandTupleFields): Opt[Disjunct] =
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
    def & (that: DNF)(implicit etf: ExpandTupleFields): DNF =
      that.cs.map(this & _).foldLeft(DNF.extr(false))(_ | _)
    def | (that: DNF)(implicit etf: ExpandTupleFields): DNF = that.cs.foldLeft(this)(_ | _)
    def & (that: Conjunct)(implicit etf: ExpandTupleFields): DNF =
      DNF(cs.flatMap(_ & that)) // TODO may need further simplif afterward
    def | (that: Conjunct)(implicit etf: ExpandTupleFields): DNF = {
      def go(cs: Ls[Conjunct], acc: Ls[Conjunct], toMerge: Conjunct): Ls[Conjunct] = 
        // trace(s"go?? $cs $acc M $toMerge") {
        cs match {
        case c :: cs =>
          if (c <:< toMerge) acc.reverse ::: toMerge :: cs
          else if (toMerge <:< c) acc.reverse ::: c :: cs
          else c.tryMerge(toMerge) match {
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
    def merge(pol: Bool)(l: DNF, r: DNF)(implicit etf: ExpandTupleFields): DNF = if (pol) l | r else l & r
    def mk(ty: SimpleType, pol: Bool)(implicit ctx: Ctx, ptr: PreserveTypeRefs = false, etf: ExpandTupleFields = true): DNF =
      mkWith(ty, pol, (_, st) => st)
    def mkWith(ty: SimpleType, pol: Bool, f: (Opt[Bool], ST) => ST)(implicit ctx: Ctx, ptr: PreserveTypeRefs = false, etf: ExpandTupleFields = true): DNF =
        // trace(s"DNF[$pol,$ptr,$etf](${ty})") {
        (if (pol) ty.pushPosWithout else ty) match {
      case bt: BaseType => of(mapPol(bt, S(pol), smart = false)(f))
      case bt: TraitTag => of(bt)
      // case rt @ RecordType(fs) => of(rt.mapPol(S(pol))(f).asInstanceOf[RecordType])
      case rt @ RecordType(fs) => of(mapPol(rt, S(pol), smart = false)(f))
      case ExtrType(pol) => extr(!pol)
      case ty @ ComposedType(p, l, r) => merge(p)(mkWith(l, pol, f), mkWith(r, pol, f))
      case NegType(und) => DNF(CNF.mkWith(und, !pol, f).ds.map(_.neg))
      case tv: TypeVariable => of(SortedSet.single(tv))
      case ProxyType(underlying) => mkWith(underlying, pol, f)
      case tr @ TypeRef(defn, targs) =>
        // * TODO later: when proper TypeRef-based simplif. is implemented, can remove this special case
        if (preserveTypeRefs && !primitiveTypes.contains(defn.name)) {
          val base = ctx.tyDefs.get(defn.name) match {
            case S(td @ TypeDef(Cls, _, _, _, _, _, _, _, _)) => S(clsNameToNomTag(td)(noProv, ctx))
            case _ => N
          }
          val tr2 = TypeRef(defn, targs.map(st => f(N, st)))(tr.prov)
          of(LhsRefined(base, ssEmp, RecordType.empty, SortedMap(defn -> tr)))
        } else mkWith(tr.expand, pol, f)
      case TypeBounds(lb, ub) => mkWith(if (pol) ub else lb, pol, f)
    }
    // }(r => s"= $r")
    
    // // TODO inline logic
    // def mk(ty: SimpleType, pol: Opt[Bool])(implicit ctx: Ctx, ptr: PreserveTypeRefs, etf: ExpandTupleFields): Either[(DNF, DNF), DNF] = {
    //   // implicit val preserveTypeRefs: Bool = true
    //   pol match {
    //     case S(true) => R(mk(ty, true))
    //     case S(false) => R(mk(ty, false))
    //     case N =>
    //       // TODO less inefficient! don't recompute
    //       val dnf1 = mk(ty, true)
    //       // if (dnf1.cs.exists(_.vars.nonEmpty))
    //       val dnf2 = mk(ty, false)
    //       if (dnf1.cs.forall(_.vars.isEmpty) && dnf1 === dnf2) R(dnf1)
    //       else L(dnf1 -> dnf2)
    //   }
    // }
  }
  
  
  case class CNF(ds: Ls[Disjunct]) {
    def & (that: CNF): CNF = that.ds.foldLeft(this)(_ & _)
    def | (that: CNF)(implicit etf: ExpandTupleFields): CNF = that.ds.map(this | _).foldLeft(CNF.extr(false))(_ & _)
    def & (that: Disjunct): CNF =
      // TODO try to merge it with the others if possible
      CNF(that :: ds)
    def | (that: Disjunct)(implicit etf: ExpandTupleFields): CNF = CNF(ds.flatMap(_ | that))
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
    def merge(pol: Bool)(l: CNF, r: CNF)(implicit etf: ExpandTupleFields): CNF = if (pol) l | r else l & r
    def mk(ty: SimpleType, pol: Bool)(implicit ctx: Ctx, ptr: PreserveTypeRefs, etf: ExpandTupleFields): CNF = mkWith(ty, pol, (_, st) => st)
    def mkWith(ty: SimpleType, pol: Bool, f: (Opt[Bool], ST) => ST)(implicit ctx: Ctx, ptr: PreserveTypeRefs, etf: ExpandTupleFields): CNF =
      // trace(s"?CNF $ty") {
      ty match {
        case bt: BaseType => of(mapPol(bt, S(pol), smart = false)(f))
        case tt: TraitTag => of(RhsBases(tt :: Nil, N, smEmp))
        // case rt @ RecordType(fs) => of(rt)
        case rt @ RecordType(fs) => of(mapPol(rt, S(pol), smart = false)(f))
        case ExtrType(pol) => extr(!pol)
        case ty @ ComposedType(p, l, r) => merge(p)(mkWith(l, pol, f), mkWith(r, pol, f))
        case NegType(und) => CNF(DNF.mkWith(und, !pol, f).cs.map(_.neg))
        case tv: TypeVariable => of(SortedSet.single(tv))
        case ProxyType(underlying) => mkWith(underlying, pol, f)
        // case tr @ TypeRef(defn, targs) => mkWith(tr.expand, pol) // TODO try to keep them?
        case tr @ TypeRef(defn, targs) =>
          if (preserveTypeRefs && !primitiveTypes.contains(defn.name)) {
            val tr2 = TypeRef(defn, targs.map(st => f(N, st)))(tr.prov)
            CNF(Disjunct(RhsBases(Nil, N, SortedMap.single(defn -> tr2)), ssEmp, LhsTop, ssEmp) :: Nil)
          } else mkWith(tr.expand, pol, f)
        case TypeBounds(lb, ub) => mkWith(if (pol) ub else lb, pol, f)
      }
      // }(r => s"!CNF $r")
  }
  
  
}
