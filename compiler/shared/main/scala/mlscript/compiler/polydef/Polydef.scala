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

def toSuperscript(i: String) = i.map {
  case '0' => '⁰'; case '1' => '¹'; case '2' => '²'
  case '3' => '³'; case '4' => '⁴'; case '5' => '⁵'
  case '6' => '⁶'; case '7' => '⁷'; case '8' => '⁸'
  case '9' => '⁹'; case c => c
}

case class Ident(isDef: Bool, tree: Var, uid: Uid[Ident]) {
  def pp(using config: PrettyPrintConfig): Str = s"${tree.name}${if config.showIuid then s"${toSuperscript(uid.toString)}" else ""}"
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
}
object Path {
  lazy val empty = Path(Nil)
}
case class Strat[+T <: (ProdStratEnum | ConsStratEnum)](val s: T)(val path: Path) {
  def updatePath(newPath: Path): Strat[T] = this.copy()(path = newPath)
  def addPath(newPath: Path): Strat[T] = this.updatePath(newPath ::: this.path)
  lazy val negPath = this.copy()(path = path.neg)
}
trait ToStrat[+T <: (ProdStratEnum | ConsStratEnum)] { self: T =>
  def toStrat(p: Path = Path(Nil)): Strat[T] = Strat(this)(p)
  //def pp(using config: PrettyPrintConfig): Str
}
trait TypevarWithBoundary(val boundary: Option[Var]) { this: (ProdStratEnum.ProdVar | ConsStratEnum.ConsVar) => ()
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
  case ProdTup(fields: Ls[ProdStrat])(using TermId) extends ProdStratEnum with ToStrat[ProdTup]
  case DeadCodeProd()(using TermId) extends ProdStratEnum with ToStrat[DeadCodeProd]
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
  case ConsTup(fields: Ls[ConsStrat])(using TermId) extends ConsStratEnum with ToStrat[ConsTup]
  case DeadCodeCons()(using TermId) extends ConsStratEnum with ToStrat[DeadCodeCons]
}
import ProdStratEnum.*, ConsStratEnum.*
case class Destructor(ctor: Var, argCons: Ls[Strat[ConsVar]]) {
}
object ProdStratEnum {
  def prodBool(using TermId) = Sum(
    MkCtor(Var("True"), Nil).toStrat() :: MkCtor(Var("False"), Nil).toStrat() :: Nil
  )
  def prodInt(using TermId) = MkCtor(Var("Int"), Nil)
  def prodFloat(using TermId) = MkCtor(Var("Float"), Nil)
  def prodChar(using TermId) = MkCtor(Var("Char"), Nil)
  def prodString(using pd: Polydef, euid: TermId): ProdStratEnum = {
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
  
  extension (t: Statement) {
    def uid = termMap.getOrElse(t, {
      val id = euid.nextUid
      termMap.addOne((t, euid.nextUid))
      id
    })
  }

  var log: Str => Unit = (s) => ()
  var constraints: Ls[Cnstr] = Nil
  val termMap = mutable.Map.empty[Statement, TermId]
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
  def freshVar(n: Ident)(using TermId): ((ProdStratEnum & ToStrat[ProdVar] & TypevarWithBoundary), (ConsStratEnum & ToStrat[ConsVar] & TypevarWithBoundary)) =
   freshVar(n.pp(using InitPpConfig.showIuidOn))

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
        val p = process(Blk(ty.body.rawEntities))(using ctx, calls, Map.empty)
        val id = nextIdent(true, ty.nameVar)
        val v = vars(id).s
        constrain(p, ConsVar(v.uid, v.name)()(using noExprId).toStrat())
        callsInfo._2.addOne(id -> calls.toSet)
      }
      case t: Term => {
        val calls = mutable.Set.empty[Var]
        val topLevelProd = process(t)(using ctx, calls, Map.empty)
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

  def process(e: Statement)(using ctx: Ctx, calls: mutable.Set[Var], varCtx: Map[String, Ident]): ProdStrat = 
    val res: ProdStratEnum = e match
      case IntLit(_) => prodInt(using noExprId)
      case DecLit(_) => prodFloat(using noExprId) // floating point numbers as integers type
      case StrLit(_) => ???
      case r @ Var(id) => if varCtx(id).isDef then {
        calls.add(r)
        ctx(varCtx(id)).s.copy()(Some(r))(using e.uid)
      } else ctx(varCtx(id)).s.copy()(None)(using e.uid)
      case App(func, arg) => 
        val funcRes = process(func)
        val argRes = process(arg)
        val sv = freshVar(s"${e.uid}_callres")(using e.uid)
        constrain(funcRes, ConsFun(argRes, sv._2.toStrat())(using noExprId).toStrat())
        sv._1
      case Lam(t @ Tup(args), body) =>
        val mapping = args.map{
          case (None, Fld(_, v: Var)) =>
            val argId = nextIdent(false, v)
            (argId, freshVar(s"${e.uid}_${v.name}")(using noExprId))
          case _ => ??? // Unsupported
        }
        ProdFun(ConsTup(mapping.map(_._2._2.toStrat()))(using t.uid).toStrat(),
          process(body)(using ctx ++ mapping.map((i, s) => (i, s._1.toStrat()))))(using e.uid)
      case If(IfThen(scrut, thenn), S(elze)) =>
        constrain(process(scrut), consBool(using noExprId).toStrat())
        val res = freshVar(s"${e.uid}_ifres")(using e.uid)
        constrain(process(thenn), res._2.toStrat())
        constrain(process(elze), res._2.toStrat())
        res._1
      case If(_) => ??? // Desugar first (resolved by pretyper OR moving post-process point)
      //case Blk(stmts) => 
      // val results = stmts.map(process)

    res.toStrat()
    //registerExprToType(e, res.toStrat())

  def constrain(prod: ProdStrat, cons: ConsStrat): Unit = {
    (prod.s, cons.s) match
      // case (NoProd(), _) | (_, NoCons()) => ()
      case (p, c) => constraints ::= (prod, cons)
  }
}