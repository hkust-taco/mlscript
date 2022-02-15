package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class NormalForms extends TyperDatatypes { self: Typer =>
  
  
  sealed abstract class LhsNf {
    def toTypes: Ls[SimpleType] = toType() :: Nil
    def toType(sort: Bool = false): SimpleType =
      if (sort) mkType(true) else underlying
    private def mkType(sort: Bool): SimpleType = this match {
      case LhsRefined(bo, ts, r) =>
        val sr = if (sort) r.sorted else r
        ts.toArray.sorted.foldLeft(bo.fold[ST](sr)(_ & sr))(_ & _)
      case LhsTop => TopType
    }
    lazy val underlying: SimpleType = mkType(false)
    def level: Int = underlying.level
    def hasTag(ttg: TraitTag): Bool = this match {
      case LhsRefined(bo, ts, r) => ts(ttg)
      case LhsTop => false
    }
    def size: Int = this match {
      case LhsRefined(bo, ts, r) => bo.size + ts.size + r.fields.size
      case LhsTop => 0
    }
    def & (that: BaseTypeOrTag): Opt[LhsNf] = (this, that) match {
      case (LhsTop, that: TupleType) => S(LhsRefined(S(that), SortedSet.empty, that.toRecord))
      case (LhsTop, that: BaseType) => S(LhsRefined(S(that), SortedSet.empty, RecordType(Nil)(noProv)))
      case (LhsTop, that: TraitTag) => S(LhsRefined(N, SortedSet.single(that), RecordType(Nil)(noProv)))
      case (LhsRefined(b1, ts, r1), that: TraitTag) => S(LhsRefined(b1, ts + that, r1))
      case (LhsRefined(b1, ts, r1), that: BaseType) =>
        var r1Final = r1
        ((b1, that) match {
          case (S(p0 @ ClassTag(pt0, ps0)), p1 @ ClassTag(pt1, ps1)) =>
            // println(s"!GLB! $this $that ${p0.glb(p1)}")
            p0.glb(p1)
          case (S(FunctionType(l0, r0)), FunctionType(l1, r1)) =>
            S(FunctionType(l0 | l1, r0 & r1)(noProv/*TODO*/))
          case (S(TupleType(fs0)), tup @ TupleType(fs1)) if fs0.size === fs1.size =>
            r1Final = RecordType(mergeSortedMap(r1Final.fields, tup.toRecord.fields)(_ && _).toList)(noProv)
            S(TupleType(tupleIntersection(fs0, fs1))(noProv))
          case (S(ArrayType(ar)), tup @ TupleType(fs)) =>
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
            // This case is quite hacky... if we find two incompatible Without types,
            //  just make a new dummy Without type to merge them.
            // The workaround is due to the fact that unlike other types, we can't fully
            //  reduce Without types away, so they are "unduly" treated as `BaseType`s.
            S(Without(b1 & b2, ns1)(w1.prov & w2.prov))
          case (S(b), w: Without) => S(Without(b & w, SortedSet.empty)(noProv))
          case (S(w: Without), b) => S(Without(w & b, SortedSet.empty)(noProv))
          case (S(_), _) => N
          case (N, tup: TupleType) =>
            r1Final = RecordType(mergeSortedMap(r1Final.fields, tup.toRecord.fields)(_ && _).toList)(noProv)
            S(that)
          case (N, _) => S(that)
        }) map { b => LhsRefined(S(b), ts, r1Final) }
    }
    def & (that: RecordType): LhsNf = this match {
      case LhsTop => LhsRefined(N, SortedSet.empty, that)
      case LhsRefined(b1, ts, r1) =>
        LhsRefined(b1, ts,
          RecordType(mergeMap(r1.fields, that.fields)(_ && _).toList)(noProv/*TODO*/))
    }
    def & (that: LhsNf): Opt[LhsNf] = (this, that) match {
      case (_, LhsTop) => S(this)
      case (LhsTop, _) => S(that)
      case (_, LhsRefined(S(b), ts, rt)) =>
        ts.foldLeft(this & rt & b)(_.getOrElse(return N) & _)
      case (_, LhsRefined(N, ts, rt)) => S(ts.foldLeft(this & rt)(_ & _ getOrElse (return N)))
    }
    def <:< (that: LhsNf): Bool = (this, that) match {
      case (_, LhsTop) => true
      case (LhsTop, _) => false
      case (LhsRefined(b1, ts1, rt1), LhsRefined(b2, ts2, rt2)) =>
        implicit val ctx: Ctx = Ctx.empty
        b2.forall(b2 => b1.exists(_ <:< b2)) && ts2.forall(ts1) && rt1 <:< rt2
    }
    def isTop: Bool = isInstanceOf[LhsTop.type]
  }
  case class LhsRefined(base: Opt[BaseType], ttags: SortedSet[TraitTag], reft: RecordType) extends LhsNf {
    override def toString: Str = s"${base.getOrElse("")}${reft}${ttags.iterator.map("∧"+_).mkString}"
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
      case RhsBases(ps, bf) =>
        (if (sort) ps.sorted else ps).foldLeft(bf.fold(BotType: ST)(_.fold(identity, _.toType(sort))))(_ | _)
      case RhsBot => BotType
    }
    lazy val underlying: SimpleType = mkType(false)
    def level: Int = underlying.level
    def hasTag(ttg: TraitTag): Bool = this match {
      case RhsBases(ts, _) => ts.contains(ttg)
      case RhsBot | _: RhsField => false
    }
    def size: Int = this match {
      case RhsBases(ts, r) => ts.size + 1
      case _: RhsField => 1
      case RhsBot => 0
    }
    def | (that: RhsNf): Opt[RhsNf] = that match {
      case RhsBases(prims, bf) =>
        val tmp = prims.foldLeft(this)(_ | _ getOrElse (return N))
        S(bf.fold(tmp)(_.fold(tmp | _ getOrElse (return N),
          tmp | _.name_ty getOrElse (return N))))
      case RhsField(name, ty) => this | name -> ty
      case RhsBot => S(this)
    }
    // TODO use inheritance hierarchy to better merge these
    def | (that: BaseTypeOrTag): Opt[RhsNf] = (this, that) match {
      case (RhsBot, p: ObjectTag) => S(RhsBases(p::Nil,N))
      case (RhsBot, that: MiscBaseType) => S(RhsBases(Nil,S(L(that))))
      case (RhsBases(ps, bf), p: ClassTag) =>
        S(RhsBases(if (ps.contains(p)) ps else p :: ps , bf))
      case (RhsBases(ps, N), that: MiscBaseType) => S(RhsBases(ps, S(L(that))))
      case (RhsBases(ps, S(L(t1@TupleType(fs1)))), t2@TupleType(fs2)) =>
        if (fs1.size =/= fs2.size) 
          RhsBases(ps, S(L(t1.toArray))) | t2.toArray // upcast tuples of different sizes to array
        else S(RhsBases(ps, S(L(TupleType(fs1.lazyZip(fs2).map {
          case ((S(n1), ty1), (S(n2), ty2)) => (if (n1 === n2) S(n1) else N, ty1 || ty2)
          case ((n1o, ty1), (n2o, ty2)) => (n1o orElse n2o, ty1 || ty2)
        })(noProv)))))
      case (RhsBases(ps, S(L(ArrayType(_)))), t@TupleType(_)) => this | t.toArray
      case (RhsBases(ps, S(L(t@TupleType(_)))), ar@ArrayType(_)) => RhsBases(ps, S(L(t.toArray))) | ar
      case (RhsBases(ps, S(L(ArrayType(ar1)))), ArrayType(ar2)) => 
        S(RhsBases(ps, S(L(ArrayType(ar1 || ar2)(noProv)))))
      case (RhsBases(_, S(L(_: Without))), _) | (_, _: Without) => die // Without should be handled elsewhere
      case (RhsBases(ps, S(L(bt))), _) if (that === bt) => S(this)
      case (RhsBases(ps, S(L(FunctionType(l0, r0)))), FunctionType(l1, r1)) =>
        S(RhsBases(ps, S(L(FunctionType(l0 & l1, r0 | r1)(noProv)))))
      case (RhsBases(ps, bf), tt: TraitTag) =>
        S(RhsBases(if (ps.contains(tt)) ps else tt :: ps, bf))
      case (f @ RhsField(_, _), p: ObjectTag) => S(RhsBases(p::Nil, S(R(f))))
      case (f @ RhsField(_, _), _: FunctionType | _: ArrayBase) =>
        // S(RhsBases(Nil, S(that), S(f)))
        N // can't merge a record and a function or a tuple -> it's the same as Top
        // NOTE: in the future, if we do actually register fields in named tuples
        //  (so their fields is not pure compiler fiction,
        //    as it is currently and in TypeScript arrays),
        //  we will want to revisit this...
      case
          (RhsBases(_, S(L(_: FunctionType))), _: ArrayBase)
        | (RhsBases(_, S(L(_: ArrayBase))), _: FunctionType)
        | (RhsBases(_, S(R(_))), _: FunctionType | _: ArrayBase)
        => N
    }
    def | (that: (Var, FieldType)): Opt[RhsNf] = this match {
      case RhsBot => S(RhsField(that._1, that._2))
      case RhsField(n1, t1) if n1 === that._1 => S(RhsField(n1, t1 || that._2))
      case RhsBases(p, N) => S(RhsBases(p, S(R(RhsField(that._1, that._2)))))
      case RhsBases(p, S(R(RhsField(n1, t1)))) if n1 === that._1 =>
        S(RhsBases(p, S(R(RhsField(n1, t1 || that._2)))))
      case _: RhsField | _: RhsBases => N
    }
    def <:< (that: RhsNf): Bool = (this.toType() <:< that.toType())(Ctx.empty) // TODO less inefficient! (uncached calls to toType)
    def isBot: Bool = isInstanceOf[RhsBot.type]
  }
  case class RhsField(name: Var, ty: FieldType) extends RhsNf
    { def name_ty: Var -> FieldType = name -> ty }
  case class RhsBases(tags: Ls[ObjectTag], rest: Opt[MiscBaseType \/ RhsField]) extends RhsNf {
    override def toString: Str = s"${tags.mkString("|")}|$rest"
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
        case LhsRefined(b, tts, rft) =>
          if (tts(tt)) copy(lnf = LhsRefined(b, tts - tt, rft)) else this
        case LhsTop => this
      }
      case NegTrait(tt) => rnf match {
        case RhsBases(tts, r) => copy(rnf = RhsBases(tts.filterNot(_ === tt), r))
        case RhsBot | _: RhsField => this
      }
    }
    lazy val interSize: Int = vars.size + nvars.size + lnf.size + rnf.size
    def <:< (that: Conjunct): Bool =
      // trace(s"?? $this <:< $that") {
      that.vars.forall(vars) &&
        lnf <:< that.lnf &&
        that.rnf <:< rnf &&
        that.nvars.forall(nvars)
      // }(r => s"!! $r")
    def & (that: Conjunct): Opt[Conjunct] =
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
    def tryMerge(that: Conjunct): Opt[Conjunct] = (this, that) match {
      case (Conjunct(LhsRefined(bse1, ts1, rcd1), vs1, r1, nvs1)
          , Conjunct(LhsRefined(bse2, ts2, rcd2), vs2, r2, nvs2))
        if vs1 === vs2 && r1 === r2 && nvs1 === nvs2 && ts1 === ts2
      =>
        val ts = ts1
        val rcdU = RecordType(recordUnion(rcd1.fields, rcd2.fields))(noProv)
        // Example:
        //    Why is it sound to merge (A -> B) & {R} | (C -> D) & {S}
        //    into ((A & C) -> (B | D)) & ({R} | {S}) ?
        //  Because the former can be distributed to
        //    (A -> B | C -> D) & (A -> B | {S}) & ({R} | C -> D) & ({R} | {S})
        //    == ((A & C) -> (B | D)) & Top & Top & ({R} | {S})
        (bse1, bse2) match {
          case (S(FunctionType(l1, r1)), S(FunctionType(l2, r2))) => // TODO Q: records ok here?!
            S(Conjunct(
              LhsRefined(S(FunctionType(l1 & l2, r1 | r2)(noProv)), ts, rcdU), vs1, RhsBot, nvs1))
          case (S(tup1 @ TupleType(fs1)), S(tup2 @ TupleType(fs2))) => // TODO Q: records ok here?!
            if (fs1.size =/= fs2.size) S(Conjunct(
              LhsRefined(S(ArrayType(tup1.inner || tup2.inner)(noProv)), ts, rcdU), vs1, RhsBot, nvs1))
            else S(Conjunct(
              LhsRefined(S(TupleType(tupleUnion(fs1, fs2))(noProv)), ts, rcdU), vs1, RhsBot, nvs1))
          case (S(tup @ TupleType(fs)), S(ArrayType(ar))) =>
            S(Conjunct(
              LhsRefined(S(ArrayType(tup.inner || ar)(noProv)), ts, rcdU), vs1, RhsBot, nvs1))
          case (S(ArrayType(ar)), S(tup @ TupleType(fs))) =>
            S(Conjunct(
              LhsRefined(S(ArrayType(tup.inner || ar)(noProv)), ts, rcdU), vs1, RhsBot, nvs1))
          case (S(ArrayType(ar1)), S(ArrayType(ar2))) =>
            S(Conjunct(LhsRefined(S(ArrayType(ar1 || ar2)(noProv)), ts, rcdU), vs1, RhsBot, nvs1))
          case (N, N)
            | (S(_: FunctionType), S(_: ArrayBase)) | (S(_: ArrayBase), S(_: FunctionType))
          =>
            S(Conjunct(LhsRefined(N, ts, rcdU), vs1, RhsBot, nvs1))
          case _ => N
        }
        case _ => N
      }
    override def toString: Str =
      (Iterator(lnf).filter(_ =/= LhsTop) ++ vars
        ++ (Iterator(rnf).filter(_ =/= RhsBot) ++ nvars).map("~"+_)).mkString("∧")
  }
  
  object Conjunct {
    def of(tvs: SortedSet[TypeVariable]): Conjunct = Conjunct(LhsTop, tvs, RhsBot, SortedSet.empty)
    def mk(lnf: LhsNf, vars: SortedSet[TypeVariable], rnf: RhsNf, nvars: SortedSet[TypeVariable]): Conjunct = {
      Conjunct(lnf, vars, rnf match {
        case RhsField(name, ty) => RhsField(name, ty)
        case RhsBases(prims, bf) =>
          RhsBases(prims.filter(lnf & _ pipe (_.isDefined)), bf.filter {
            case L(b) => lnf & b pipe (_.isDefined)
            case R(r) => true
          })
        case RhsBot => RhsBot
      }, nvars)
    }
  }
  
  
  case class Disjunct(rnf: RhsNf, vars: SortedSet[TypeVariable], lnf: LhsNf, nvars: SortedSet[TypeVariable]) {
    def neg: Conjunct = Conjunct(lnf, nvars, rnf, vars)
    def | (that: Disjunct): Opt[Disjunct] =
      S(Disjunct(rnf | that.rnf getOrElse (return N), vars | that.vars,
        lnf & that.lnf getOrElse (return N), nvars | that.nvars))
    override def toString: Str =
      (Iterator(rnf).filter(_ =/= RhsBot) ++ vars
        ++ (Iterator(lnf).filter(_ =/= LhsTop) ++ nvars).map("~"+_)).mkString("∨")
  }
  
  object Disjunct {
    def of(tvs: SortedSet[TypeVariable]): Disjunct = Disjunct(RhsBot, tvs, LhsTop, SortedSet.empty)
  }
  
  
  case class DNF(cs: Ls[Conjunct]) {
    def isBot: Bool = cs.isEmpty
    def toType(sort: Bool = false): SimpleType = cs.sorted match {
      case Nil => BotType
      case t :: ts => t.toType(sort) | DNF(ts).toType(sort)
    }
    def level: Int = cs.maxByOption(_.level).fold(0)(_.level)
    def & (that: DNF): DNF =
      that.cs.map(this & _).foldLeft(DNF.extr(false))(_ | _)
    def | (that: DNF): DNF = that.cs.foldLeft(this)(_ | _)
    def & (that: Conjunct): DNF =
      DNF(cs.flatMap(_ & that)) // TODO may need further simplif afterward
    def | (that: Conjunct): DNF = {
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
    def of(lnf: LhsNf): DNF = DNF(Conjunct(lnf, SortedSet.empty, RhsBot, SortedSet.empty) :: Nil)
    def of(bt: BaseType): DNF = DNF.of(LhsRefined(S(bt), SortedSet.empty, bt.toRecord))
    def of(tt: TraitTag): DNF = DNF.of(LhsRefined(N, SortedSet.single(tt), RecordType.empty))
    def of(rcd: RecordType): DNF = DNF.of(LhsRefined(N, SortedSet.empty, rcd))
    def of(tvs: SortedSet[TypeVariable]): DNF = DNF(Conjunct.of(tvs) :: Nil)
    def extr(pol: Bool): DNF = if (pol) of(LhsTop) else DNF(Nil)
    def merge(pol: Bool)(l: DNF, r: DNF): DNF = if (pol) l | r else l & r
    def mk(ty: SimpleType, pol: Bool)(implicit ctx: Ctx): DNF = (if (pol) ty.pushPosWithout else ty) match {
      case bt: BaseType => of(bt)
      case bt: TraitTag => of(bt)
      case rt @ RecordType(fs) => of(rt)
      case ExtrType(pol) => extr(!pol)
      case ty @ ComposedType(p, l, r) => merge(p)(mk(l, pol), mk(r, pol))
      case NegType(und) => DNF(CNF.mk(und, !pol).ds.map(_.neg))
      case tv: TypeVariable => of(SortedSet.single(tv))
      case ProxyType(underlying) => mk(underlying, pol)
      case tr @ TypeRef(defn, targs) => mk(tr.expand, pol) // TODO try to keep them?
      case TypeBounds(lb, ub) => mk(if (pol) ub else lb, pol)
    }
  }
  
  
  case class CNF(ds: Ls[Disjunct]) {
    def & (that: CNF): CNF = that.ds.foldLeft(this)(_ & _)
    def | (that: CNF): CNF = that.ds.map(this | _).foldLeft(CNF.extr(false))(_ & _)
    def & (that: Disjunct): CNF =
      // TODO try to merge it with the others if possible
      CNF(that :: ds)
    def | (that: Disjunct): CNF = CNF(ds.flatMap(_ | that))
    override def toString: Str = s"CNF(${ds.mkString(" & ")})"
  }
  
  object CNF {
    def of(rnf: RhsNf): CNF = CNF(Disjunct(rnf, SortedSet.empty, LhsTop, SortedSet.empty) :: Nil)
    def of(bt: BaseType): CNF =
      CNF.of(RhsBot | bt getOrElse (return CNF.extr(true)))
    def of(tvs: SortedSet[TypeVariable]): CNF = CNF(Disjunct.of(tvs) :: Nil)
    def of(rcd: RecordType): CNF = CNF(rcd.fields.iterator.map(f =>
      Disjunct(RhsField(f._1, f._2), SortedSet.empty, LhsTop, SortedSet.empty)).toList)
    def extr(pol: Bool): CNF = if (pol) CNF(Nil) else of(RhsBot)
    def merge(pol: Bool)(l: CNF, r: CNF): CNF = if (pol) l | r else l & r
    def mk(ty: SimpleType, pol: Bool)(implicit ctx: Ctx): CNF =
      // trace(s"?C $ty") {
      ty match {
        case bt: BaseType => of(bt)
        case tt: TraitTag => of(RhsBases(tt :: Nil, N))
        case rt @ RecordType(fs) => of(rt)
        case ExtrType(pol) => extr(!pol)
        case ty @ ComposedType(p, l, r) => merge(p)(mk(l, pol), mk(r, pol))
        case NegType(und) => CNF(DNF.mk(und, !pol).cs.map(_.neg))
        case tv: TypeVariable => of(SortedSet.single(tv))
        case ProxyType(underlying) => mk(underlying, pol)
        case tr @ TypeRef(defn, targs) => mk(tr.expand, pol) // TODO try to keep them?
        case TypeBounds(lb, ub) => mk(if (pol) ub else lb, pol)
      }
      // }(r => s"!C $r")
  }
  
  
}
