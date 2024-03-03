package mlscript
package compiler
package polydef

import mlscript.utils.*, shorthands.*
import scala.collection.mutable

type TypeVar
type NormalPathElem
type StarPathElem
type PathElemType = NormalPathElem | StarPathElem
type ExprId = Uid[Expr]
type TypeVarId = Uid[TypeVar]
type Cnstr = ProdStrat -> ConsStrat
type ProdStrat = Strat[ProdStratEnum]
type ConsStrat = Strat[ConsStratEnum]

enum PathElemPol {
  case In
  case Out
  lazy val neg = this match
    case In => Out
    case Out => In
  lazy val pp = this match
    case In => "+"
    case Out => "-"
  def canCancel(other: PathElemPol) = (this, other) match
    case (In, Out) | (Out, In) => true
    case _ => false
}
enum PathElem[+T <: PathElemType] {
  case Normal(r: Var)(val pol: PathElemPol = PathElemPol.In) extends PathElem[NormalPathElem]
  case Star(elms: List[PathElem[NormalPathElem]]) extends PathElem[StarPathElem]

  def neg: PathElem[T] = this match
    case n: Normal => n.copy()(pol = n.pol.neg)
    case s: Star => s.copy(elms = s.elms.map(_.neg))
  def rev: PathElem[T] = this match
    case n: Normal => n
    case s: Star => s.copy(elms = s.elms.reverse)
//   def pp(using config: PrettyPrintConfig): Str = this match
//     case n@Normal(r@Var(Ident(_, Var(nme), uid))) =>
//       (if config.showPolarity then n.pol.pp else "")
//       + nme
//       + (if config.showIuid then s":$uid" else "")
//       + (if config.showRefEuid then s"^${r.uid}" else "")
//     case Star(elms) => s"{${elms.map(_.pp).mkString(" · ")}}*"
  def canCancel[V <: PathElemType](other: PathElem[V]): Boolean = (this, other) match
    case (n: Normal, o: Normal) => (n == o) && (n.pol.canCancel(o.pol))
    case _ => ???
}
case class Path(p: Ls[PathElem[PathElemType]]) {
  lazy val neg = this.copy(p = p.map(_.neg))
  lazy val rev = this.copy(p = p.map(_.rev).reverse)
  lazy val last = this.p.last.asInstanceOf[PathElem.Normal]
  // merge two consecutive identical stars during concatenation if we have stars
  def ::: (other: Path) = Path(other.p ::: p)
//   def pp(using config: PrettyPrintConfig): Str = if !config.pathAsIdent
//     then s"[${p.map(_.pp).mkString(" · ")}]"
//     else p.map(_.pp(using InitPpConfig.showRefEuidOn)).mkString("_")

  lazy val annihilated: Path =
    def anni(i: Ls[PathElem[PathElemType]], o: Ls[PathElem[PathElemType]]): Path = (i, o) match
      case (Nil, Nil) => Path(Nil)
      case (h :: t, Nil) => anni(t, h :: Nil)
      case (h :: t, h2 :: t2) => if h.canCancel(h2) then anni(t, t2) else anni(t, h :: h2 :: t2)
      case (Nil, r) => Path(r.reverse)
    anni(this.p, Nil)

  def splitted: Path -> Path = {
    var prod: Ls[PathElem[PathElemType]] = Nil
    var cons: Ls[PathElem[PathElemType]] = Nil
    p foreach {
      case n: PathElem.Normal => n.pol match
        case PathElemPol.Out => prod = (n :: prod)
        case PathElemPol.In => cons = (n :: cons)
      case n: PathElem.Star => ???
    }
    Path(prod) -> Path(cons.reverse)
  }

//   def reachable(callsInfo: (mutable.Set[Var], mutable.Map[Ident, Set[Var]])): Boolean = {
//     p match {
//       case Nil => true
//       case PathElem.Normal(ref) :: t => {
//         val headCheck: Boolean = callsInfo._1.contains(ref)
//         val nextCalls: Option[Set[Var]] = callsInfo._2.get(ref.id)
//         (headCheck, nextCalls) match {
//           case (true, Some(next)) => Path(t).reachable((next.to(mutable.Set), callsInfo._2))
//           case _ => false
//         }
//       }
//       case _ => ???
//     }
//   }
}
object Path {
  lazy val empty = Path(Nil)
}
case class Strat[+T <: (ProdStratEnum | ConsStratEnum)](val s: T)(val path: Path) {
  def updatePath(newPath: Path): Strat[T] = this.copy()(path = newPath)
  def addPath(newPath: Path): Strat[T] = this.updatePath(newPath ::: this.path)
  //def pp(using config: PrettyPrintConfig): Str = if config.showPath then s"(${path.pp}: ${s.pp})" else s.pp
  lazy val negPath = this.copy()(path = path.neg)
//   lazy val asInPath: Option[Path] = this.s match {
//     case pv: ProdStratEnum.ProdVar => pv.asInPath
//     case cv: ConsStratEnum.ConsVar => cv.asInPath
//     case _ => None
//   }
//   lazy val asOutPath: Option[Path] = this.s match {
//     case pv: ProdStratEnum.ProdVar => pv.asOutPath
//     case cv: ConsStratEnum.ConsVar => cv.asOutPath
//     case _ => None
//   }
}
trait ToStrat[+T <: (ProdStratEnum | ConsStratEnum)] { self: T =>
  def toStrat(p: Path = Path(Nil)): Strat[T] = Strat(this)(p)
  //def pp(using config: PrettyPrintConfig): Str
}
trait TypevarWithBoundary(val boundary: Option[Var]) { this: (ProdStratEnum.ProdVar | ConsStratEnum.ConsVar) =>
//   lazy val asInPath: Option[Path] = this.boundary.map(_.toPath(PathElemPol.In))
//   lazy val asOutPath: Option[Path] = this.boundary.map(_.toPath(PathElemPol.Out))
//   def printBoundary(config: PrettyPrintConfig) = boundary.map {
//     case r@Var(Ident(_, Var(nme), uid)) =>
//       (if config.showIuid then s"_${uid}" else "") +
//       (if config.showRefEuid then s"^${r.uid}" else "")
//   }.getOrElse("")
}
trait MkCtorTrait { this: ProdStratEnum.MkCtor =>
  override def equals(x: Any): Boolean = x match {
    case r: ProdStratEnum.MkCtor => this.ctor == r.ctor && this.args == r.args && this.euid == r.euid
    case _ => false
  }
  override lazy val hashCode: Int = (this.ctor, this.args, this.euid).hashCode()
}
trait DestructTrait { this: ConsStratEnum.Destruct =>
  override def equals(x: Any): Boolean = x match {
    case r: ConsStratEnum.Destruct => this.destrs == r.destrs && this.euid == r.euid
    case _ => false
  }
  override lazy val hashCode: Int = (this.destrs, this.euid).hashCode()
}
enum ProdStratEnum extends ToStrat[ProdStratEnum] {
  case NoProd() extends ProdStratEnum with ToStrat[NoProd]
  case MkCtor(ctor: Var, args: Ls[ProdStrat]) extends ProdStratEnum
    with ToStrat[MkCtor]
    with MkCtorTrait
  case Sum(ctors: Ls[Strat[MkCtor]]) extends ProdStratEnum with ToStrat[Sum]
  case ProdFun(lhs: ConsStrat, rhs: ProdStrat) extends ProdStratEnum with ToStrat[ProdFun]
  case ProdVar(uid: TypeVarId, name: String)(boundary: Option[Var] = None)
    extends ProdStratEnum
    with ToStrat[ProdVar]
    with TypevarWithBoundary(boundary)
  case DeadCodeProd() extends ProdStratEnum with ToStrat[DeadCodeProd]

//   def pp(using config: PrettyPrintConfig): Str = this match
//     case NoProd() => "NoProd"
//     case MkCtor(ctor, args) if args.length > 0 => s"${ctor.name}(${args.map(_.pp).mkString(", ")})"
//     case MkCtor(ctor, _) => ctor.name
//     case Sum(ls) => s"Sum[${ls.map(_.pp).mkString(", ")}]"
//     case ProdFun(l, r) => s"${l.pp} => ${r.pp}"
//     case pv@ProdVar(uid, n) =>
//       (if config.showVuid then s"$uid" else "") +
//       s"'$n" +
//       (if config.showVboundary then pv.printBoundary else "")
//     case DeadCodeProd() => "DeadCodeProd"

  def representsDeadCode(using d: Deforest, cache: Set[TypeVarId] = Set()): Boolean = {
    if !(d.exprs.isDefinedAt(this.euid)) then
      false
    else
      this match {
        case p: (MkCtor | NoProd | Sum | ProdFun) => !d.isNotDead.contains(p)
        case v: ProdVar =>
          if cache(v.uid) then
            true
          else
            d.upperBounds(v.uid).forall { case (_, s) => s.s match {
              case ConsStratEnum.DeadCodeCons() => true
              case ConsStratEnum.ConsVar(uid, name) => ProdVar(uid, name)().representsDeadCode(using d, cache + v.uid)
              case _ => false
            }}
        case DeadCodeProd() => lastWords("deadcodeprod cannot associate with an expr")
      }
  }

}
enum ConsStratEnum extends ToStrat[ConsStratEnum] {
  case NoCons() extends ConsStratEnum with ToStrat[NoCons]
  case Destruct(destrs: Ls[Destructor]) extends ConsStratEnum
    with ToStrat[Destruct]
    with DestructTrait
  case ConsFun(lhs: ProdStrat, rhs: ConsStrat) extends ConsStratEnum with ToStrat[ConsFun]
  case ConsVar(uid: TypeVarId, name: String)(boundary: Option[Var] = None)
    extends ConsStratEnum
    with ToStrat[ConsVar]
    with TypevarWithBoundary(boundary)
  case DeadCodeCons() extends ConsStratEnum with ToStrat[DeadCodeCons]

//   def pp(using config: PrettyPrintConfig): Str = this match
//     case NoCons() => "NoCons"
//     case DeadCodeCons() => "DeadCodeCons"
//     case Destruct(x) => s"Destruct(${x.map(_.pp).mkString(", ")})"
//     case ConsFun(l, r) => s"${l.pp} => ${r.pp}"
//     case cv@ConsVar(uid, n) =>
//       (if config.showVuid then s"$uid" else "") +
//       s"'$n" +
//       (if config.showVboundary then cv.printBoundary else "")
}
import ProdStratEnum.*, ConsStratEnum.*
case class Destructor(ctor: Var, argCons: Ls[Strat[ConsVar]]) {
//   def pp(using config: PrettyPrintConfig): Str =
//     if argCons.length > 0 then s"${ctor.name}(${argCons.map(_.pp).mkString(", ")})" else ctor.name
}
object ProdStratEnum {
  def prodBool = Sum(
    MkCtor(Var("True"), Nil).toStrat() :: MkCtor(Var("False"), Nil).toStrat() :: Nil
  )
  def prodInt = MkCtor(Var("Int"), Nil)
  def prodFloat = MkCtor(Var("Float"), Nil)
  def prodChar = MkCtor(Var("Char"), Nil)
  def prodString(using d: Deforest, euid: ExprId): ProdStratEnum = {
    // val v = d.freshVar("_lh_string")
    // val nil = MkCtor(Var("LH_N"), Nil)
    // val cons = MkCtor(Var("LH_C"), prodChar.toStrat() :: v._1.toStrat() :: Nil)
    // d.constrain(nil.toStrat(), v._2.toStrat())
    // d.constrain(cons.toStrat(), v._2.toStrat())
    NoProd()
  }
  def prodString(s: Str): MkCtor = s.headOption match {
    case Some(_) => MkCtor(Var("LH_C"), prodChar.toStrat() :: prodString(s.tail).toStrat() :: Nil)
    case None => MkCtor(Var("LH_N"), Nil)
  }
  def prodIntBinOp(using id: ExprId, d: Deforest) = ProdFun(
    consInt.toStrat(),
    ProdFun(consInt.toStrat(), prodInt.toStrat()).toStrat()
  )
  def prodFloatBinOp(using id: ExprId, d: Deforest) = ProdFun(
    consFloat.toStrat(),
    ProdFun(consFloat.toStrat(), prodFloat.toStrat()).toStrat()
  )
  def prodFloatUnaryOp(using id: ExprId, d: Deforest) = ProdFun(
    consFloat.toStrat(), prodFloat.toStrat()
  )
  def prodIntEq(using id: ExprId, d: Deforest) = ProdFun(
    consInt.toStrat(),
    ProdFun(consInt.toStrat(), prodBool.toStrat()).toStrat()
  )
  def prodBoolBinOp(using id: ExprId, d: Deforest) = ProdFun(
    consBool.toStrat(),
    ProdFun(consBool.toStrat(), prodBool.toStrat()).toStrat()
  )
  def prodBoolUnaryOp(using id: ExprId, d: Deforest) = ProdFun(
    consBool.toStrat(),
    prodBool.toStrat()
  )
}
object ConsStratEnum {
  def consBool = Destruct(
    Destructor(Var("True"), Nil) :: Destructor(Var("False"), Nil) :: Nil
  )
  def consInt = Destruct(Destructor(Var("Int"), Nil) :: Nil)
  def consFloat = Destruct(Destructor(Var("Float"), Nil) :: Nil)
  def consChar = Destruct(Destructor(Var("Char"), Nil) :: Nil)
}

case class Ctx(bindings: Map[Ident, Strat[ProdVar]]) {
  def apply(id: Ident): Strat[ProdVar] =
    bindings.getOrElse(id, lastWords(s"binding not found: " + id))
  def + (b: Ident -> Strat[ProdVar]): Ctx =
    copy(bindings = bindings + b)
  def ++ (bs: Iterable[Ident -> Strat[ProdVar]]): Ctx =
    copy(bindings = bindings ++ bs)
}
object Ctx {
  def empty = Ctx(Map.empty)
}


class Polydef {
    val exprMap: mutable.Map[TermId, Term] = mutable.Map.empty

    def apply(p: TypingUnit): Unit = ???
}