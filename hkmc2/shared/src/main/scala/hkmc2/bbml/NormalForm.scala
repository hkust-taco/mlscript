package hkmc2
package bbml

import scala.annotation.tailrec

import semantics.*
import Message.MessageContext
import mlscript.utils.*, shorthands.*

// TODO: refactor! this file looks horrible!
object NormalForm:
  final case class NormalClassType(cls: ClassSymbol, targs: List[(Disj, Disj)]) {
    override def toString(): String = if targs.isEmpty then s"${cls.nme}" else s"${cls.nme}[${targs.map{
      case (in, out) => s"in $in out $out"
    }.mkString(", ")}]"
    def toType: Type = Type.ClassType(cls, targs.map {
      case (in, out) => Wildcard(in.toType, out.toType)
    })
    lazy val lvl: Int = targs.map {
      case (in, out) => in.lvl.max(out.lvl)
    }.maxOption.getOrElse(0)
  }
  final case class NormalFunType(args: List[Disj], ret: Disj, eff: Disj) {
    override def toString(): String = s"(${args.mkString(", ")}) ->{${eff}} ${ret}"
    def toType: Type = Type.FunType(args.map(_.toType), ret.toType, eff.toType)
    lazy val lvl: Int = (ret :: eff :: args).map(_.lvl).max
  }

  enum Disj: // * D ::=
    case Bot // * ⊥ |
    case Con(conj: Conj) // * C |
    case DC(disj: Disj, conj: Conj) // * D \/ C
    override def toString(): String = this match {
      case Bot => "⊥"
      case Con(conj) => conj.toString()
      case DC(disj, conj) => s"$disj ∨ $conj"
    }
    def toType: Type = this match
      case Bot => Type.Bot
      case Con(conj) => conj.toType
      case DC(disj, conj) => Type.ComposedType(disj.toType, conj.toType, true)
    lazy val lvl: Int = this match
      case Bot => 0
      case Con(conj) => conj.lvl
      case DC(disj, conj) => disj.lvl.max(conj.lvl)

  type SkolemSet = Set[Uid[Type.InfVar]]

  enum Conj: // * C ::=
    case INU(i: Inter, u: Union) // * I /\ ~U |
    case CVar(conj: Conj, v: Type.InfVar) // * C /\ a |
    case CNVar(conj: Conj, v: Type.InfVar) // * C /\ ~a
    // * None -> not found, or Some(pol)
    def has(t: Type.InfVar): Option[Bool] = this match
      case CVar(conj, v) =>
        Option.when(t.uid == v.uid)(true) orElse conj.has(t)
      case CNVar(conj, v) =>
        Option.when(t.uid == v.uid)(false) orElse conj.has(t)
      case _ => None
    def merge(form: Either[Inter, Union]): Option[Conj] = this match
      case CVar(conj, v) => conj.merge(form).map(CVar(_, v))
      case CNVar(conj, v) => conj.merge(form).map(CNVar(_, v))
      case INU(i, u) => form match
        case Left(inter) => i.merge(inter).map(INU(_, u))
        case Right(union) => Some(INU(i, u.merge(union)))
    override def toString(): String = this match {
      case CNVar(conj, v) => s"($conj) ∧ (¬$v)"
      case CVar(conj, v) => s"($conj) ∧ ($v)"
      case INU(i, u) => s"($i) ∧ (¬($u))"
    }
    def toType: Type = this match
      case INU(i, u) => Type.ComposedType(i.toType, Type.NegType(u.toType), false)
      case CVar(conj, v) => Type.ComposedType(conj.toType, v, false)
      case CNVar(conj, v) => Type.ComposedType(conj.toType, Type.NegType(v), false)
    lazy val lvl: Int = this match
      case INU(i, u) => i.lvl.max(u.lvl)
      case CVar(conj, v) => v.lvl.max(conj.lvl)
      case CNVar(conj, v) => v.lvl.max(conj.lvl)
    def sort(using skolems: SkolemSet): Conj =
      @tailrec
      def rec(conj: Conj, prev: Ls[(Type.InfVar, Bool)]): (Ls[(Type.InfVar, Bool)], INU) = conj match // * tv -> pos/neg
        case inu: INU => (prev, inu)
        case CVar(conj, v) => rec(conj, (v, true) :: prev)
        case CNVar(conj, v) => rec(conj, (v, false) :: prev)
      val (vs, tail) = rec(this, Nil)
      vs.sortWith {
        case ((v1, _), (v2, _)) => skolems(v1.uid) || (!skolems(v2.uid) && v1.lvl < v2.lvl)
      }.foldLeft[Conj](tail)((res, p) => if p._2 then CVar(res, p._1) else CNVar(res, p._1))

  enum Inter: // * I ::=
    case Top // * ⊤ |
    case Fun(fun: NormalFunType) // * D ->{D} D |
    case Cls(cls: NormalClassType) // * Cls[in D out D]
    def merge(it: Inter): Option[Inter] = (this, it) match
      case (Top, i) => Some(i)
      case (i, Top) => Some(i)
      case (Fun(NormalFunType(a1, r1, e1)), Fun(NormalFunType(a2, r2, e2))) =>
        Some(Fun(NormalFunType(a1.zip(a2).map {
          case (a1, a2) => union(a1, a2)
        }, inter(r1, r2), inter(e1, e2))))
      case (Cls(NormalClassType(cls1, targs1)), Cls(NormalClassType(cls2, targs2))) if cls1.uid == cls2.uid =>
        Some(Cls(NormalClassType(cls1, targs1.zip(targs2).map {
          case ((in1, out1), (in2, out2)) => (union(in1, in2), inter(out1, out2))
        })))
      case _ => None
    override def toString(): String = this match
      case Top => "⊤"
      case Fun(f) => f.toString()
      case Cls(c) => c.toString()
    def toType: Type = this match
      case Top => Type.Top
      case Fun(f) => f.toType
      case Cls(c) => c.toType
    lazy val lvl: Int = this match
      case Top => 0
      case Fun(f) => f.lvl
      case Cls(c) => c.lvl
    
  enum Union: // * U ::=
    case Bot // * ⊥ |
    case Fun(fun: NormalFunType) // * D ->{D} D |
    case Uni(lhs: Union, rhs: NormalClassType) // * U \/ Cls[in D out D]
    def merge(un: Union): Union = (this, un) match
      case (Bot, u) => u
      case (u, Bot) => u
      case (Fun(NormalFunType(a1, r1, e1)), Fun(NormalFunType(a2, r2, e2))) =>
        Fun(NormalFunType(a1.zip(a2).map {
          case (a1, a2) => inter(a1, a2)
        }, union(r1, r2), union(e1, e2)))
      case (Uni(u1, cls), f: Fun) => Uni(u1.merge(f), cls)
      case (f: Fun, Uni(u2, cls)) => Uni(u2.merge(f), cls)
      case (Uni(u1, c1 @ NormalClassType(cls1, targs1)), Uni(u2, c2 @ NormalClassType(cls2, targs2))) =>
        val u = u1.merge(u2)
        if cls1.uid == cls2.uid then Uni(u, NormalClassType(cls1, targs1.zip(targs2).map {
          case ((in1, out1), (in2, out2)) => (inter(in1, in2), union(out1, out2))
        }))
        else Uni(Uni(u, c1), c2)
    override def toString(): String = this match
      case Bot => "⊥"
      case Fun(f) => f.toString()
      case Uni(lhs, rhs) => s"$lhs ∨ $rhs"
    def toType: Type = this match
      case Bot => Type.Bot
      case Fun(f) => f.toType
      case Uni(lhs, rhs) => Type.ComposedType(lhs.toType, rhs.toType, true)
    lazy val lvl: Int = this match
      case Bot => 0
      case Fun(f) => f.lvl
      case Uni(lhs, rhs) => lhs.lvl.max(rhs.lvl)

  private lazy val topConj = Conj.INU(Inter.Top, Union.Bot)

  @tailrec
  private def inter(lhs: Conj, rhs: Conj): Disj = rhs match
    case Conj.CVar(conj, v) => lhs.has(v) match
      case Some(true) => inter(lhs, conj)
      case Some(false) => Disj.Bot
      case None => inter(Conj.CVar(lhs, v), rhs)
    case Conj.CNVar(conj, v) => lhs.has(v) match
      case Some(true) => Disj.Bot
      case Some(false) => inter(lhs, conj)
      case None => inter(Conj.CNVar(lhs, v), rhs)
    case Conj.INU(i, u) =>
      lhs.merge(Left(i)) match
        case Some(conj) => conj.merge(Right(u)) match
          case Some(res) => Disj.Con(res)
          case _ => Disj.Bot
        case _ => Disj.Bot

  private def inter(lhs: Disj, rhs: Disj): Disj = (lhs, rhs) match
    case (_, Disj.Bot) => Disj.Bot
    case (Disj.Bot, _) => Disj.Bot
    case (Disj.Con(c1), Disj.Con(c2)) => inter(c1, c2)
    case (Disj.DC(d1, c1), disj @ Disj.Con(c2)) => union(inter(d1, disj), inter(c1, c2))
    case (disj @ Disj.Con(c1), Disj.DC(d2, c2)) => union(inter(disj, d2), inter(c1, c2))
    case (Disj.DC(d1, c1), disj: Disj.DC) => union(inter(d1, disj), inter(Disj.Con(c1), disj))

  @tailrec
  private def union(lhs: Disj, rhs: Disj): Disj = rhs match
    case Disj.Bot => lhs
    case Disj.Con(conj) => Disj.DC(lhs, conj)
    case Disj.DC(disj, conj) => union(Disj.DC(lhs, conj), disj)

  private def neg(ty: Type)(using raise: Raise): Disj = ty match
    case Type.Top => Disj.Bot
    case Type.Bot => Disj.Con(topConj)
    case v: Type.InfVar => Disj.Con(Conj.CNVar(topConj, v))
    case Type.ClassType(cls, targs) =>
      Disj.Con(Conj.INU(Inter.Top, Union.Uni(Union.Bot, NormalClassType(cls, targs.map {
        case Wildcard(in, out) => (dnf(in), dnf(out))
        case ty: Type =>
          val res = dnf(ty)
          (res, res)
      }))))
    case Type.FunType(args, ret, eff) =>
      Disj.Con(Conj.INU(Inter.Top, Union.Fun(NormalFunType(
        args.map(dnf), dnf(ret), dnf(eff)
      ))))
    case Type.ComposedType(lhs, rhs, pol) =>
      if pol then inter(neg(lhs), neg(rhs)) else union(neg(lhs), neg(rhs))
    case Type.NegType(ty) => dnf(ty)
    case _: Type.PolymorphicType =>
      raise(ErrorReport(msg"Polymorphic type is not allowed." -> N :: Nil))
      Disj.Bot

  def dnf(ty: Type)(using raise: Raise): Disj = ty match
    case Type.Top => Disj.Con(topConj)
    case Type.Bot => Disj.Bot
    case v: Type.InfVar => Disj.Con(Conj.CVar(topConj, v))
    case Type.ClassType(cls, targs) =>
      Disj.Con(Conj.INU(Inter.Cls(NormalClassType(cls, targs.map {
        case Wildcard(in, out) => (dnf(in), dnf(out))
        case ty: Type =>
          val res = dnf(ty)
          (res, res)
      })), Union.Bot))
    case Type.FunType(args, ret, eff) =>
      Disj.Con(Conj.INU(Inter.Fun(NormalFunType(
        args.map(dnf), dnf(ret), dnf(eff)
      )), Union.Bot))
    case Type.ComposedType(lhs, rhs, pol) =>
      if pol then union(dnf(lhs), dnf(rhs)) else inter(dnf(lhs), dnf(rhs))
    case Type.NegType(ty) => neg(ty)
    case _: Type.PolymorphicType =>
      raise(ErrorReport(msg"Polymorphic type is not allowed." -> N :: Nil))
      Disj.Bot
