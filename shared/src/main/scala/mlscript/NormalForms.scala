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
      case LhsRefined(N, r) => r
      case LhsRefined(S(b), RecordType(Nil)) => b
      case LhsRefined(S(b), r) => b & r
      case LhsTop => TopType
    }
    def & (that: BaseType): Opt[LhsNf] = (this, that) match {
      case (LhsTop, _) => S(LhsRefined(S(that), RecordType(Nil)(noProv)))
      case (LhsRefined(b1, r1), _) =>
        ((b1, that) match {
          case (S(p0 @ PrimType(pt0, ps0)), p1 @ PrimType(pt1, ps1)) =>
            println(s"!GLB! ${p0.glb(p1)}")
            p0.glb(p1)
          case (S(FunctionType(l0, r0)), FunctionType(l1, r1)) => S(FunctionType(l0 | l1, r0 & r1)(noProv/*TODO*/))
          case (S(AppType(l0, as0)), AppType(l1, as1)) => ???
          case (S(TupleType(fs0)), TupleType(fs1)) => ???
          case (S(VarType(_, _, _)), VarType(_, _, _)) => ???
          case (S(_), _) => N
          case (N, _) => S(that)
        }) map { b => LhsRefined(S(b), r1) }
    }
    def & (that: RecordType): LhsNf = this match {
      case LhsTop => LhsRefined(N, that)
      case LhsRefined(b1, r1) =>
        LhsRefined(b1, RecordType(mergeMap(r1.fields, that.fields)(_ & _).toList)(noProv/*TODO*/))
    }
    def & (that: LhsNf): Opt[LhsNf] = (this, that) match {
      case (_, LhsTop) => S(this)
      case (LhsTop, _) => S(that)
      case (_, LhsRefined(S(b), rt)) => this & rt & b
      case (_, LhsRefined(N, rt)) => S(this & rt)
    }
    def <:< (that: LhsNf): Bool = (this, that) match {
      case (_, LhsTop) => true
      case (LhsTop, _) => false
      case (LhsRefined(b1, rt1), LhsRefined(b2, rt2)) =>
        b2.forall(b2 => b1.exists(_ <:< b2)) && rt1 <:< rt2
    }
  }
  case class LhsRefined(base: Opt[BaseType], reft: RecordType) extends LhsNf {
    override def toString: Str = s"${base.getOrElse("")}${reft}"
  }
  case object LhsTop extends LhsNf
  
  
  sealed abstract class RhsNf {
    def toTypes: Ls[SimpleType] = toType :: Nil
    def toType: SimpleType = this match {
      case RhsField(n, t) => RecordType(n -> t :: Nil)(noProv) // FIXME prov
      case RhsBases(ps, b, f) => ps.foldLeft(b.getOrElse(BotType) | f.fold(BotType:SimpleType)(_.toType))(_ | _)
      case RhsBot => BotType
    }
    def | (that: RhsNf): Opt[RhsNf] = that match {
      case RhsBases(prims, bty, f) =>
        val tmp = prims.foldLeft(this)(_ | _ getOrElse (return N))
        val tmp2 = bty.fold(tmp)(tmp | _ getOrElse (return N))
        f.fold(some(tmp2))(tmp2 | _)
      case RhsField(name, ty) => this | name -> ty
      case RhsBot => S(this)
    }
    // TODO use inheritance hierarchy to better merge these
    def | (that: BaseType): Opt[RhsNf] = (this, that) match {
      case (RhsBot, p: PrimType) => S(RhsBases(p::Nil,N,N))
      case (RhsBot, _) => S(RhsBases(Nil,S(that),N))
      case (RhsBases(ps, b, f), p: PrimType) =>
        S(RhsBases(if (ps.contains(p)) ps else p :: ps , b, f))
      case (RhsBases(ps, N, f), _) => S(RhsBases(ps, S(that), f))
      case (RhsBases(ps, S(bt), f), _) if bt === that => S(this)
      case (RhsBases(_, S(TupleType(_)), f), TupleType(_)) =>
        // ??? // TODO
        // err("TODO handle tuples", prov.loco)
        println("TODO handle tuples")
        N
      case (RhsBases(_, _, _), _) => // FIXME should properly consider possible base types here...
        println(s"TODO ?! $this $that")
        // ???
        N
      case (f @ RhsField(_, _), p: PrimType) => S(RhsBases(p::Nil, N, S(f)))
      case (f @ RhsField(_, _), _) =>
          // S(RhsBases(Nil, S(that), S(f)))
          N // can't merge a record and a function -> it's the same as Top
    }
    def | (that: (Str, SimpleType)): Opt[RhsNf] = this match {
      case RhsBot => S(RhsField(that._1, that._2))
      case RhsField(n1, t1) if n1 === that._1 => S(RhsField(n1, t1 | that._2))
      case RhsBases(p, b, N) => S(RhsBases(p, b, S(RhsField(that._1, that._2))))
      case RhsBases(p, b, S(RhsField(n1, t1))) if n1 === that._1 => S(RhsBases(p, b, S(RhsField(n1, t1 | that._2))))
      case _: RhsField | _: RhsBases => N
    }
    def <:< (that: RhsNf): Bool = this.toType <:< that.toType
  }
  case class RhsField(name: Str, ty: SimpleType) extends RhsNf
  case class RhsBases(prims: Ls[PrimType], bty: Opt[BaseType], f: Opt[RhsField]) extends RhsNf {
    require(!bty.exists(_.isInstanceOf[PrimType]), this)
    require(bty.isEmpty || f.isEmpty, this)
    // TODO improve type: should make (bty, f) an either...
    override def toString: Str = s"${prims.mkString("|")}|$bty|$f"
  }
  case object RhsBot extends RhsNf
  
  
  
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
      case (Conjunct(LhsRefined(bse1, rcd1), vs1, r1, nvs1), Conjunct(LhsRefined(bse2, rcd2), vs2, r2, nvs2))
        if vs1 === vs2 && r1 === r2 && nvs1 === nvs2
      => (bse1, bse2) match {
        case (S(FunctionType(l1, r1)), S(FunctionType(l2, r2))) => // TODO Q: records ok here?!
          S(Conjunct(LhsRefined(S(FunctionType(l1 & l2, r1 | r2)(noProv)), RecordType(recordUnion(rcd1.fields, rcd2.fields))(noProv)), vs1, RhsBot, nvs1))
        case (N, N) =>
          S(Conjunct(LhsRefined(N, RecordType(recordUnion(rcd1.fields, rcd2.fields))(noProv)), vs1, RhsBot, nvs1))
        case _ => N
      }
      case _ => N
    }
  }
  object Conjunct {
    def of(tvs: Set[TypeVariable]): Conjunct = Conjunct(LhsTop, tvs, RhsBot, Set.empty)
    def mk(lnf: LhsNf, vars: Set[TypeVariable], rnf: RhsNf, nvars: Set[TypeVariable]): Conjunct = {
      Conjunct(lnf, vars, rnf match {
        case RhsField(name, ty) => RhsField(name, ty)
        case RhsBases(prims, bty, f) =>
          RhsBases(prims.filter(lnf & _ pipe (_.isDefined)), bty.filter(lnf & _ pipe (_.isDefined)), f)
        case RhsBot => RhsBot
      }, nvars)
    }
  }
  case class Disjunct(rnf: RhsNf, vars: Set[TypeVariable], lnf: LhsNf, nvars: Set[TypeVariable]) {
    def neg: Conjunct = Conjunct(lnf, nvars, rnf, vars)
    def | (that: Disjunct): Opt[Disjunct] =
      S(Disjunct(rnf | that.rnf getOrElse (return N), vars | that.vars,
        lnf & that.lnf getOrElse (return N), nvars | that.nvars))
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
  }
  object DNF {
    def of(lnf: LhsNf): DNF = DNF(Conjunct(lnf, Set.empty, RhsBot, Set.empty) :: Nil)
    def of(bt: BaseType): DNF = DNF.of(LhsRefined(S(bt), RecordType.empty))
    def of(rcd: RecordType): DNF = DNF.of(LhsRefined(N, rcd))
    def of(tvs: Set[TypeVariable]): DNF = DNF(Conjunct.of(tvs) :: Nil)
    def extr(pol: Bool): DNF = if (pol) of(LhsTop) else DNF(Nil)
    def merge(pol: Bool)(l: DNF, r: DNF): DNF = if (pol) l | r else l & r
    def mk(ty: SimpleType, pol: Bool): DNF = (if (pol) ty.pushPosWithout(_ => ()) else ty) match {
      case bt: BaseType => of(bt)
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
