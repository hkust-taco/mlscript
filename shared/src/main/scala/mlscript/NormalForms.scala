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
    def toTypes: Ls[SimpleType] = toType :: Nil
    def toType: SimpleType = this match {
      case LhsRefined(bo, ts, r) => ts.foldLeft(bo.fold[ST](r)(_ & r))(_ & _)
      case LhsTop => TopType
    }
    def & (that: BaseTypeOrTag): Opt[LhsNf] = (this, that) match {
      case (LhsTop, that: BaseType) => S(LhsRefined(S(that), Set.empty, RecordType(Nil)(noProv)))
      case (LhsTop, that: TraitTag) => S(LhsRefined(N, Set.single(that), RecordType(Nil)(noProv)))
      case (LhsRefined(b1, ts, r1), that: TraitTag) => S(LhsRefined(b1, ts + that, r1))
      case (LhsRefined(b1, ts, r1), that: BaseType) =>
        ((b1, that) match {
          case (S(p0 @ ClassTag(pt0, ps0)), p1 @ ClassTag(pt1, ps1)) =>
            println(s"!GLB! $this $that ${p0.glb(p1)}")
            p0.glb(p1)
          case (S(FunctionType(l0, r0)), FunctionType(l1, r1)) =>
            S(FunctionType(l0 | l1, r0 & r1)(noProv/*TODO*/))
          case (S(TupleType(fs0)), TupleType(fs1)) => ???
          case (S(_), _) => N
          case (N, _) => S(that)
        }) map { b => LhsRefined(S(b), ts, r1) }
    }
    def & (that: RecordType): LhsNf = this match {
      case LhsTop => LhsRefined(N, Set.empty, that)
      case LhsRefined(b1, ts, r1) =>
        LhsRefined(b1, ts,
          RecordType(mergeMap(r1.fields, that.fields)(_ & _).toList)(noProv/*TODO*/))
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
        b2.forall(b2 => b1.exists(_ <:< b2)) && ts2.forall(ts1) && rt1 <:< rt2
    }
  }
  case class LhsRefined(base: Opt[BaseType], ttags: Set[TraitTag], reft: RecordType) extends LhsNf {
    override def toString: Str = s"${base.getOrElse("")}${reft}"
  }
  case object LhsTop extends LhsNf {
    override def toString: Str = "⊤"
  }
  
  
  sealed abstract class RhsNf {
    def toTypes: Ls[SimpleType] = toType :: Nil
    def toType: SimpleType = this match {
      case RhsField(n, t) => RecordType(n -> t :: Nil)(noProv) // FIXME prov
      case RhsBases(ps, bf) =>
        ps.foldLeft(bf.fold(BotType:ST)(_.fold(identity, _.toType)))(_ | _)
      case RhsBot => BotType
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
      case (RhsBases(ps, S(L(TupleType(fs1)))), TupleType(fs2)) =>
        // err("TODO handle tuples", prov.loco)
        println("TODO handle tuples")
        N
        // TODO uncomment:
        /* 
        if (fs1.size =/= fs2.size) N
        else S(RhsBases(ps, S(L(TupleType(fs1.lazyZip(fs2).map {
          case ((S(n1), ty1), (S(n2), ty2)) => (if (n1 === n2) S(n1) else N, ty1 | ty2)
          case ((n1o, ty1), (n2o, ty2)) => (n1o orElse n2o, ty1 | ty2)
        })(noProv)))))
        */
      case (RhsBases(_, S(L(_: Without))), _) | (_, _: Without) => die // Without should be handled elsewhere
      case (RhsBases(ps, S(L(bt))), _) if (that === bt) => S(this)
      case (RhsBases(ps, S(L(FunctionType(l0, r0)))), FunctionType(l1, r1)) =>
        S(RhsBases(ps, S(L(FunctionType(l0 & l1, r0 | r1)(noProv)))))
      case (RhsBases(ps, bf), tt: TraitTag) =>
        S(RhsBases(if (ps.contains(tt)) ps else tt :: ps, bf))
      case (RhsBases(_, _), _) => // FIXME should properly consider possible base types here...
        println(s"TODO ?! $this $that")
        // ???
        N
      case (f @ RhsField(_, _), p: ObjectTag) => S(RhsBases(p::Nil, S(R(f))))
      case (f @ RhsField(_, _), _: FunctionType | _: TupleType) =>
          // S(RhsBases(Nil, S(that), S(f)))
          N // can't merge a record and a function or a tuple -> it's the same as Top
          // NOTE: in the future, if we do actually register fields in named tuples
          //  (so their fields is not pure compiler fiction,
          //    as it is currently and in TypeScript arrays),
          //  we will want to revisit this...
    }
    def | (that: (Var, SimpleType)): Opt[RhsNf] = this match {
      case RhsBot => S(RhsField(that._1, that._2))
      case RhsField(n1, t1) if n1 === that._1 => S(RhsField(n1, t1 | that._2))
      case RhsBases(p, N) => S(RhsBases(p, S(R(RhsField(that._1, that._2)))))
      case RhsBases(p, S(R(RhsField(n1, t1)))) if n1 === that._1 =>
        S(RhsBases(p, S(R(RhsField(n1, t1 | that._2)))))
      case _: RhsField | _: RhsBases => N
    }
    def <:< (that: RhsNf): Bool = this.toType <:< that.toType
  }
  case class RhsField(name: Var, ty: SimpleType) extends RhsNf
    { def name_ty: Var -> ST = name -> ty }
  case class RhsBases(tags: Ls[ObjectTag], rest: Opt[MiscBaseType \/ RhsField]) extends RhsNf {
    override def toString: Str = s"${tags.mkString("|")}|$rest"
  }
  case object RhsBot extends RhsNf {
    override def toString: Str = "⊥"
  }
  
  
  case class Conjunct(lnf: LhsNf, vars: Set[TypeVariable], rnf: RhsNf, nvars: Set[TypeVariable]) {
    def toType: SimpleType =
      (vars.iterator ++ Iterator(rnf.toType.neg()) ++ nvars.map(_.neg())).foldLeft(lnf.toType)(_ & _)
    def <:< (that: Conjunct): Bool =
      // trace(s"?? $this <:< $that") {
      that.vars.forall(vars) &&
        lnf <:< that.lnf &&
        that.rnf <:< rnf &&
        that.nvars.forall(nvars)
      // }(r => s"!! $r")
    def & (that: Conjunct): Opt[Conjunct] =
      // trace(s"?? $this & $that ${lnf & that.lnf} ${rnf | that.rnf}") {
      if (lnf.toType <:< that.rnf.toType) N // TODO support <:< on any Nf?
      else S(Conjunct.mk(lnf & that.lnf getOrElse (return N), vars | that.vars
        , rnf | that.rnf getOrElse (return N)
        , nvars | that.nvars))
      // }(r => s"!! $r")
    def neg: Disjunct = Disjunct(rnf, nvars, lnf, vars)
    def tryMerge(that: Conjunct): Opt[Conjunct] = (this, that) match {
      case (Conjunct(LhsRefined(bse1, ts1, rcd1), vs1, r1, nvs1)
          , Conjunct(LhsRefined(bse2, ts2, rcd2), vs2, r2, nvs2))
        if vs1 === vs2 && r1 === r2 && nvs1 === nvs2
      => (bse1, bse2) match {
        case (S(FunctionType(l1, r1)), S(FunctionType(l2, r2))) => // TODO Q: records ok here?!
          S(Conjunct(LhsRefined(S(FunctionType(l1 & l2, r1 | r2)(noProv)), ts1 & ts2, // FIXME or should it be `&& ts1 === ts2` above?
            RecordType(recordUnion(rcd1.fields, rcd2.fields))(noProv)), vs1, RhsBot, nvs1))
        case (N, N) =>
          S(Conjunct(LhsRefined(N, ts1 & ts2, RecordType(recordUnion(rcd1.fields, rcd2.fields))(noProv)), vs1, RhsBot, nvs1))
        case _ => N
      }
      case _ => N
    }
    override def toString: Str =
      (Iterator(lnf).filter(_ =/= LhsTop) ++ vars
        ++ (Iterator(rnf).filter(_ =/= RhsBot) ++ nvars).map("~"+_)).mkString("∧")
  }
  
  object Conjunct {
    def of(tvs: Set[TypeVariable]): Conjunct = Conjunct(LhsTop, tvs, RhsBot, Set.empty)
    def mk(lnf: LhsNf, vars: Set[TypeVariable], rnf: RhsNf, nvars: Set[TypeVariable]): Conjunct = {
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
  
  
  case class Disjunct(rnf: RhsNf, vars: Set[TypeVariable], lnf: LhsNf, nvars: Set[TypeVariable]) {
    def neg: Conjunct = Conjunct(lnf, nvars, rnf, vars)
    def | (that: Disjunct): Opt[Disjunct] =
      S(Disjunct(rnf | that.rnf getOrElse (return N), vars | that.vars,
        lnf & that.lnf getOrElse (return N), nvars | that.nvars))
    override def toString: Str =
      (Iterator(rnf).filter(_ =/= RhsBot) ++ vars
        ++ (Iterator(lnf).filter(_ =/= LhsTop) ++ nvars).map("~"+_)).mkString("∨")
  }
  
  object Disjunct {
    def of(tvs: Set[TypeVariable]): Disjunct = Disjunct(RhsBot, tvs, LhsTop, Set.empty)
  }
  
  
  case class DNF(cs: Ls[Conjunct]) {
    def isBot: Bool = cs.isEmpty
    def toType: SimpleType = cs match {
      case Nil => BotType
      case t :: ts => t.toType | DNF(ts).toType
    }
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
          else 
          // TODO always rm fun/rcd and rcd/rcd here?
          c.tryMerge(toMerge) match {
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
    def of(lnf: LhsNf): DNF = DNF(Conjunct(lnf, Set.empty, RhsBot, Set.empty) :: Nil)
    def of(bt: BaseType): DNF = DNF.of(LhsRefined(S(bt), Set.empty, RecordType.empty))
    def of(tt: TraitTag): DNF = DNF.of(LhsRefined(N, Set.single(tt), RecordType.empty))
    def of(rcd: RecordType): DNF = DNF.of(LhsRefined(N, Set.empty, rcd))
    def of(tvs: Set[TypeVariable]): DNF = DNF(Conjunct.of(tvs) :: Nil)
    def extr(pol: Bool): DNF = if (pol) of(LhsTop) else DNF(Nil)
    def merge(pol: Bool)(l: DNF, r: DNF): DNF = if (pol) l | r else l & r
    def mk(ty: SimpleType, pol: Bool): DNF = (if (pol) ty.pushPosWithout(_ => ()) else ty) match {
      case bt: BaseType => of(bt)
      case bt: TraitTag => of(bt)
      case rt @ RecordType(fs) => of(rt)
      case ExtrType(pol) => extr(!pol)
      case ty @ ComposedType(p, l, r) => merge(p)(mk(l, pol), mk(r, pol))
      case NegType(und) => DNF(CNF.mk(und, !pol).ds.map(_.neg))
      case tv: TypeVariable => of(Set.single(tv))
      case ProxyType(underlying) => mk(underlying, pol)
      case tr @ TypeRef(defn, targs) => mk(tr.expand(_ => ()), pol) // TODO try to keep them?
    }
  }
  
  
  case class CNF(ds: Ls[Disjunct]) {
    def & (that: CNF): CNF =
      that.ds.map(this & _).foldLeft(CNF.extr(false))(_ | _)
    def | (that: CNF): CNF = that.ds.foldLeft(this)(_ | _)
    def & (that: Disjunct): CNF =
      // TODO try to merge it with the others if possible
      CNF(that :: ds)
    def | (that: Disjunct): CNF = CNF(ds.flatMap(_ | that))
    override def toString: Str = s"CNF(${ds.mkString(" & ")})"
  }
  
  object CNF {
    def of(rnf: RhsNf): CNF = CNF(Disjunct(rnf, Set.empty, LhsTop, Set.empty) :: Nil)
    def of(bt: BaseType): CNF =
      CNF.of(RhsBot | bt getOrElse (return CNF.extr(true)))
    def of(tvs: Set[TypeVariable]): CNF = CNF(Disjunct.of(tvs) :: Nil)
    def of(rcd: RecordType): CNF = rcd.fields.iterator.map(f =>
      Disjunct(RhsField(f._1, f._2), Set.empty, LhsTop, Set.empty)).foldLeft(of(RhsBot))(_ | _)
    def extr(pol: Bool): CNF = if (pol) CNF(Nil) else of(RhsBot)
    def merge(pol: Bool)(l: CNF, r: CNF): CNF = if (pol) l | r else l & r
    def mk(ty: SimpleType, pol: Bool): CNF = ty match {
      case bt: BaseType => of(bt)
      case tt: TraitTag => of(RhsBases(tt :: Nil, N))
      case rt @ RecordType(fs) => of(rt)
      case ExtrType(pol) => extr(!pol)
      case ty @ ComposedType(p, l, r) => merge(p)(mk(l, pol), mk(r, pol))
      case NegType(und) => CNF(DNF.mk(und, !pol).cs.map(_.neg))
      case tv: TypeVariable => of(Set.single(tv))
      case ProxyType(underlying) => mk(underlying, pol)
      case tr @ TypeRef(defn, targs) => mk(tr.expand(_ => ()), pol) // TODO try to keep them?
    }
  }
  
  
}
