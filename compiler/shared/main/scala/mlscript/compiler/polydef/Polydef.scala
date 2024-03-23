package mlscript
package compiler
package polydef

import mlscript.utils.*, shorthands.*
import scala.collection.mutable

type TypeVar
type NormalPathElem
type StarPathElem
type PathElemType = NormalPathElem | StarPathElem
type TermId = Uid[Term]
type TypeVarId = Uid[TypeVar]
type Cnstr = ProdStrat -> ConsStrat
type ProdStrat = Strat[ProdStratEnum]
type ConsStrat = Strat[ConsStratEnum]


case class Ident(isDef: Bool, tree: Var, uid: Uid[Ident]) {
  //def pp(using config: PrettyPrintConfig): Str = s"${tree.name}${if config.showIuid then s"${toSuperscript(uid.toString)}" else ""}"
  //def copyToNewDeforest(using newd: Deforest): Ident = newd.nextIdent(isDef, tree)
}

case class PrettyPrintConfig(
  multiline: Boolean,
  showEuid: Boolean,
  showIuid: Boolean,
  showRefEuid: Boolean,
  showVuid: Boolean,
  showPolarity: Boolean,
  showVboundary: Boolean,
  showPath: Boolean,
  pathAsIdent: Boolean,
) {
  lazy val multilineOn = copy(multiline = true)
  lazy val showEuidOn = copy(showEuid = true)
  lazy val showIuidOn = copy(showIuid = true)
  lazy val showRefEuidOn = copy(showRefEuid = true)
  lazy val showVuidOn = copy(showVuid = true)
  lazy val showPolarityOn = copy(showPolarity = true)
  lazy val showVboundaryOn = copy(showVboundary = true)
  lazy val showPathOn = copy(showPath = true)
  lazy val pathAsIdentOn = copy(pathAsIdent = true)
}
object InitPpConfig extends PrettyPrintConfig(false, false, false, false, false, false, false, false, false)


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
enum ProdStratEnum(using val euid: TermId) extends ToStrat[ProdStratEnum] {
  case NoProd()(using TermId) extends ProdStratEnum with ToStrat[NoProd]
  case MkCtor(ctor: Var, args: Ls[ProdStrat])(using TermId) extends ProdStratEnum
    with ToStrat[MkCtor]
    with MkCtorTrait
  case Sum(ctors: Ls[Strat[MkCtor]])(using TermId) extends ProdStratEnum with ToStrat[Sum]
  case ProdFun(lhs: ConsStrat, rhs: ProdStrat)(using TermId) extends ProdStratEnum with ToStrat[ProdFun]
  case ProdVar(uid: TypeVarId, name: String)(boundary: Option[Var] = None)(using TermId)
    extends ProdStratEnum
    with ToStrat[ProdVar]
    with TypevarWithBoundary(boundary)
  case DeadCodeProd()(using TermId) extends ProdStratEnum with ToStrat[DeadCodeProd]

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

  // def representsDeadCode(using pd: Polydef, cache: Set[TypeVarId] = Set()): Boolean = {
  //   if !(pd.exprs.isDefinedAt(this.euid)) then
  //     false
  //   else
  //     this match {
  //       case p: (MkCtor | NoProd | Sum | ProdFun) => !pd.isNotDead.contains(p)
  //       case v: ProdVar =>
  //         if cache(v.uid) then
  //           true
  //         else
  //           pd.upperBounds(v.uid).forall { case (_, s) => s.s match {
  //             case ConsStratEnum.DeadCodeCons() => true
  //             case ConsStratEnum.ConsVar(uid, name) => ProdVar(uid, name)().representsDeadCode(using d, cache + v.uid)
  //             case _ => false
  //           }}
  //       case DeadCodeProd() => lastWords("deadcodeprod cannot associate with an expr")
  //     }
  // }

}
enum ConsStratEnum(using val euid: TermId) extends ToStrat[ConsStratEnum] {
  case NoCons()(using TermId) extends ConsStratEnum with ToStrat[NoCons]
  case Destruct(destrs: Ls[Destructor])(using TermId) extends ConsStratEnum
    with ToStrat[Destruct]
    with DestructTrait
  case ConsFun(lhs: ProdStrat, rhs: ConsStrat)(using TermId) extends ConsStratEnum with ToStrat[ConsFun]
  case ConsVar(uid: TypeVarId, name: String)(boundary: Option[Var] = None)(using TermId)
    extends ConsStratEnum
    with ToStrat[ConsVar]
    with TypevarWithBoundary(boundary)
  case DeadCodeCons()(using TermId) extends ConsStratEnum with ToStrat[DeadCodeCons]

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
  def prodBool(using TermId) = Sum(
    MkCtor(Var("True"), Nil).toStrat() :: MkCtor(Var("False"), Nil).toStrat() :: Nil
  )
  def prodInt(using TermId) = MkCtor(Var("Int"), Nil)
  def prodFloat(using TermId) = MkCtor(Var("Float"), Nil)
  def prodChar(using TermId) = MkCtor(Var("Char"), Nil)
  def prodString(using pd: Polydef, euid: TermId): ProdStratEnum = {
    // val v = pd.freshVar("_lh_string")
    // val nil = MkCtor(Var("LH_N"), Nil)
    // val cons = MkCtor(Var("LH_C"), prodChar.toStrat() :: v._1.toStrat() :: Nil)
    // pd.constrain(nil.toStrat(), v._2.toStrat())
    // pd.constrain(cons.toStrat(), v._2.toStrat())
    NoProd()(using euid)
  }
  def prodString(s: Str)(using TermId): MkCtor = s.headOption match {
    case Some(_) => MkCtor(Var("LH_C"), prodChar.toStrat() :: prodString(s.tail).toStrat() :: Nil)
    case None => MkCtor(Var("LH_N"), Nil)
  }
  def prodIntBinOp(using id: TermId, pd: Polydef) = ProdFun(
    consInt(using pd.noExprId).toStrat(),
    ProdFun(consInt(using pd.noExprId).toStrat(), prodInt(using pd.noExprId).toStrat())(using pd.noExprId).toStrat()
  )
  def prodFloatBinOp(using id: TermId, pd: Polydef) = ProdFun(
    consFloat(using pd.noExprId).toStrat(),
    ProdFun(consFloat(using pd.noExprId).toStrat(), prodFloat(using pd.noExprId).toStrat())(using pd.noExprId).toStrat()
  )
  def prodFloatUnaryOp(using id: TermId, pd: Polydef) = ProdFun(
    consFloat(using pd.noExprId).toStrat(), prodFloat(using pd.noExprId).toStrat()
  )
  def prodIntEq(using id: TermId, pd: Polydef) = ProdFun(
    consInt(using pd.noExprId).toStrat(),
    ProdFun(consInt(using pd.noExprId).toStrat(), prodBool(using pd.noExprId).toStrat())(using pd.noExprId).toStrat()
  )
  def prodBoolBinOp(using id: TermId, pd: Polydef) = ProdFun(
    consBool(using pd.noExprId).toStrat(),
    ProdFun(consBool(using pd.noExprId).toStrat(), prodBool(using pd.noExprId).toStrat())(using pd.noExprId).toStrat()
  )
  def prodBoolUnaryOp(using id: TermId, pd: Polydef) = ProdFun(
    consBool(using pd.noExprId).toStrat(),
    prodBool(using pd.noExprId).toStrat()
  )
}
object ConsStratEnum {
  def consBool(using TermId) = Destruct(
    Destructor(Var("True"), Nil) :: Destructor(Var("False"), Nil) :: Nil
  )
  def consInt(using TermId) = Destruct(Destructor(Var("Int"), Nil) :: Nil)
  def consFloat(using TermId) = Destruct(Destructor(Var("Float"), Nil) :: Nil)
  def consChar(using TermId) = Destruct(Destructor(Var("Char"), Nil) :: Nil)
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
  
  extension (t: Term) {
    def uid = termMap.getOrElse(t, {
      val id = euid.nextUid
      termMap.addOne((t, euid.nextUid))
      id
    })
  }

  var log: Str => Unit = (s) => ()
  var constraints: Ls[Cnstr] = Nil
  val termMap = mutable.Map.empty[Term, TermId]
  val varsName = mutable.Map.empty[TypeVarId, Str]
  val vuid = Uid.TypeVar.State()
  val iuid = Uid.Ident.State()
  val euid = Uid.Term.State()
  val noExprId = euid.nextUid
  def nextIdent(isDef: Bool, name: Var): Ident = Ident(isDef, name, iuid.nextUid(name.name))

  def freshVar(n: String)(using TermId): ((ProdStratEnum & ToStrat[ProdVar] & TypevarWithBoundary), (ConsStratEnum & ToStrat[ConsVar] & TypevarWithBoundary)) =
    val vid = vuid.nextUid
    val pv = ProdVar(vid, n)()
    val cv = ConsVar(vid, n)()
    varsName += vid -> n
    log(s"fresh var '$n")
    (pv, cv)
  //def freshVar(n: Ident)(using TermId): ((ProdStratEnum & ToStrat[ProdVar] & TypevarWithBoundary), (ConsStratEnum & ToStrat[ConsVar] & TypevarWithBoundary)) =
  //  freshVar(n.pp(using InitPpConfig.showIuidOn))

  def apply(p: TypingUnit): Ls[Ident -> ProdStrat] = 
    if constraints.nonEmpty then return Nil
    // TODO: Collect Defs?
    val vars: Map[Ident, Strat[ProdVar]] = Map() //p.rawEntities.collect { 
      // case L(ProgDef(id, body)) =>
      //   id -> freshVar(id.pp(using InitPpConfig))(using noExprId)._1.toStrat()
    //}.toMap

    val ctx = Ctx.empty ++ vars
    p.rawEntities.map {
      case ty: NuTypeDef => {
        val calls = mutable.Set.empty[Var]
        val p = process(Blk(ty.body.rawEntities), true)(using ctx, calls, Map.empty)
        val id = nextIdent(true, ty.nameVar)
        val v = vars(id).s
        constrain(p, ConsVar(v.uid, v.name)()(using noExprId).toStrat())
        callsInfo._2.addOne(id -> calls.toSet)
      }
      case t: Term => {
        val calls = mutable.Set.empty[Var]
        val topLevelProd = process(t, true)(using ctx, calls, Map.empty)
        constrain(topLevelProd, NoCons()(using noExprId).toStrat())
        callsInfo._1.addAll(calls)
      }
    }
    vars.toList

  val tailPosExprIds = mutable.Set.empty[TermId]
  val callsInfo = (mutable.Set.empty[Var], mutable.Map.empty[Ident, Set[Var]])
  val ctorExprToType = mutable.Map.empty[TermId, MkCtor]
  val dtorExprToType = mutable.Map.empty[TermId, Destruct]
  val exprToProdType = mutable.Map.empty[TermId, ProdStrat]

  def process(e: Term, isTail: Boolean)(using ctx: Ctx, calls: mutable.Set[Var], varCtx: Map[String, Ident]): ProdStrat = 
    if isTail then tailPosExprIds += e.uid else ()
    val res: ProdStratEnum = e match
      case IntLit(_) => prodInt(using noExprId)
      case DecLit(_) => prodFloat(using noExprId) // floating point numbers as integers type
      case StrLit(_) => ???
      case r @ Var(id) => if varCtx(id).isDef then {
        calls.add(r)
        ctx(varCtx(id)).s.copy()(Some(r))(using e.uid)
      } else ctx(varCtx(id)).s.copy()(None)(using e.uid)
    //   case Call(f, a) =>
    //     val fp = process(f, false)
    //     val ap = process(a, false)
    //     val sv = freshVar(s"${e.uid}_callres")(using e.uid)
    //     constrain(fp, ConsFun(ap, sv._2.toStrat())(using noExprId).toStrat())
    //     sv._1
    //   case ce@Ctor(name, args) =>
    //     val ctorType = MkCtor(name, args.map(a => process(a, false)))(using e.uid)
    //     this.ctorExprToType += ce.uid -> ctorType.asInstanceOf[MkCtor]
    //     ctorType
    //   case me@Match(scrut, arms) =>
    //     val sp = process(scrut, false)
    //     val (detrs, bodies) = arms.map { (v, as, e) =>
    //       if v.name.isCapitalized then { // normal pattern
    //         val as_tys = as.map(a => a -> freshVar(a)(using noExprId))
    //         val ep = process(e, true && isTail)(using ctx ++ as_tys.map(v => v._1 -> v._2._1.toStrat()))
    //         (Destructor(v, as_tys.map(a_ty => a_ty._2._2.toStrat())), ep)
    //       } else if v.name == "_" then { // id pattern or wildcard pattern ("_", id :: Nil (or Nil), armBodyExpr)
    //         val newIdCtx = as.headOption.map { newId =>
    //           val idVar = freshVar(newId)(using noExprId)
    //           (newId -> idVar._1.toStrat(), idVar._2.toStrat())
    //         }
    //         val ep = process(e, true && isTail)(using ctx ++ newIdCtx.map(_._1))
    //         (Destructor(v, newIdCtx.map(_._2).toList), ep)
    //       } else if v.name.toIntOption.isDefined then { // int literal pattern: ("3", Nil, armBodyExpr)
    //         val ep = process(e, true && isTail)
    //         (Destructor(Var("Int"), Nil), ep)
    //       } else if v.name.matches("'.'") then {
    //         val ep = process(e, true && isTail)
    //         (Destructor(Var("Char"), Nil), ep)
    //       } else { lastWords(s"unreachable: unknown kind of match arm: ${v.name}") }
    //     }.unzip
    //     val dtorType = Destruct(detrs)(using e.uid).toStrat()
    //     constrain(sp, dtorType)
    //     val res = freshVar(s"${e.uid}_matchres")(using e.uid)
    //     bodies.foreach(constrain(_, res._2.toStrat()))
    //     // register from expr to type
    //     this.dtorExprToType += me.uid -> dtorType.s
    //     res._1
    //   case Function(param, body) =>
    //     val sv = freshVar(param)(using noExprId)
    //     ProdFun(sv._2.toStrat(),
    //       process(body, false)(using ctx + (param -> sv._1.toStrat()))
    //     )(using e.uid)
    //   case IfThenElse(scrut, thenn, elze) =>
    //     constrain(process(scrut, false), consBool(using noExprId).toStrat())
    //     val res = freshVar(s"${e.uid}_ifres")(using e.uid)
    //     constrain(process(thenn, true && isTail), res._2.toStrat())
    //     constrain(process(elze, true && isTail), res._2.toStrat())
    //     res._1
    //   case LetIn(id, rhs, body) =>
    //     val v = freshVar(id)(using noExprId)
    //     constrain(process(rhs, false)(using ctx + (id -> v._1.toStrat())), v._2.toStrat())
    //     process(body, true && isTail)(using ctx + (id -> v._1.toStrat())).s
    //   case LetGroup(defs, body) =>
    //     assert(defs.nonEmpty)
    //     val vs = defs.keys.map(k => k -> freshVar(k)(using noExprId)).toMap
    //     given newCtx: Ctx = ctx ++ vs.mapValues(_._1.toStrat()).toMap
    //     defs.foreach { case (id, rhs) =>
    //       val t = process(rhs, false)(using newCtx)
    //       constrain(t, vs(id)._2.toStrat())
    //     }
    //     process(body, true && isTail)(using newCtx).s
    //   case Sequence(fst, snd) =>
    //     process(fst, false)
    //     process(snd, true && isTail).s

    res.toStrat()
    //registerExprToType(e, res.toStrat())

  def constrain(prod: ProdStrat, cons: ConsStrat): Unit = {
    (prod.s, cons.s) match
      // case (NoProd(), _) | (_, NoCons()) => ()
      case (p, c) => constraints ::= (prod, cons)
  }
}