package mlscript
package compiler
package polydef

import mlscript.utils.*, shorthands.*
import scala.collection.mutable
import java.util.IdentityHashMap
import scala.collection.JavaConverters._

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
  lazy val asInPath: Option[Path] = this.s match {
    case pv: ProdStratEnum.ProdVar => pv.asInPath
    case cv: ConsStratEnum.ConsVar => cv.asInPath
    case _ => None
  }
  lazy val asOutPath: Option[Path] = this.s match {
    case pv: ProdStratEnum.ProdVar => pv.asOutPath
    case cv: ConsStratEnum.ConsVar => cv.asOutPath
    case _ => None
  }
}
trait ToStrat[+T <: (ProdStratEnum | ConsStratEnum)] { self: T =>
  def toStrat(p: Path = Path(Nil)): Strat[T] = Strat(this)(p)
  //def pp(using config: PrettyPrintConfig): Str
}
extension (v: Var) {
  def toPath(pol: PathElemPol = PathElemPol.In): Path = Path(PathElem.Normal(v)(pol) :: Nil)
}
trait TypevarWithBoundary(val boundary: Option[Var]) { this: (ProdStratEnum.ProdVar | ConsStratEnum.ConsVar) => 
  lazy val asInPath: Option[Path] = this.boundary.map(_.toPath(PathElemPol.In))
  lazy val asOutPath: Option[Path] = this.boundary.map(_.toPath(PathElemPol.Out))
}
trait MkCtorTrait { this: ProdStratEnum.MkCtor =>
  // override def equals(x: Any): Boolean = x match {
  //   case r: ProdStratEnum.MkCtor => this.ctor == r.ctor && this.args == r.args && this.euid == r.euid
  //   case _ => false
  // }
  override lazy val hashCode: Int = (this.ctor, this.fields, this.euid).hashCode()
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
  case MkCtor(ctor: Var, fields: Ls[Var -> ProdStrat])(using TermId) extends ProdStratEnum
    with ToStrat[MkCtor]
    with MkCtorTrait
  case ProdObj(ctor: Option[Var], fields: Ls[Var -> ProdStrat])(using TermId) extends ProdStratEnum
    with ToStrat[ProdObj]
  case ProdPrim(name: String)(using TermId) extends ProdStratEnum with ToStrat[ProdPrim]
  case Sum(ctors: Ls[Strat[MkCtor]])(using TermId) extends ProdStratEnum with ToStrat[Sum]
  case ProdFun(lhs: ConsStrat, rhs: ProdStrat)(using TermId) extends ProdStratEnum with ToStrat[ProdFun]
  case ProdVar(uid: TypeVarId, name: String)(boundary: Option[Var] = None)(using TermId)
    extends ProdStratEnum
    with ToStrat[ProdVar]
    with TypevarWithBoundary(boundary)
  case ProdTup(fields: Ls[ProdStrat])(using TermId) extends ProdStratEnum with ToStrat[ProdTup]
}
enum ConsStratEnum(using val euid: TermId) extends ToStrat[ConsStratEnum] {
  case NoCons()(using TermId) extends ConsStratEnum with ToStrat[NoCons]
  case Destruct(destrs: Ls[Destructor])(using TermId) extends ConsStratEnum
    with ToStrat[Destruct]
    with DestructTrait
  case ConsObj(name: Option[Var], fields: Ls[Var -> ConsStrat])(using TermId) extends ConsStratEnum with ToStrat[ConsObj]
  case ConsPrim(name: String)(using TermId) extends ConsStratEnum with ToStrat[ConsPrim]
  case ConsFun(lhs: ProdStrat, rhs: ConsStrat)(using TermId) extends ConsStratEnum with ToStrat[ConsFun]
  case ConsVar(uid: TypeVarId, name: String)(boundary: Option[Var] = None)(using TermId)
    extends ConsStratEnum
    with ToStrat[ConsVar]
    with TypevarWithBoundary(boundary)
  case ConsTup(fields: Ls[ConsStrat])(using TermId) extends ConsStratEnum with ToStrat[ConsTup]
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
  // def prodString(s: Str)(using TermId): MkCtor = s.headOption match {
  //   case Some(_) => MkCtor(Var("LH_C"), prodChar.toStrat() :: prodString(s.tail).toStrat() :: Nil)
  //   case None => MkCtor(Var("LH_N"), Nil)
  // }
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

class Polydef(debug: Debug) {
  
  extension (t: Term) {
    def uid = termMap.getOrElse(t, {
      val id = euid.nextUid
      termMap.addOne((t, euid.nextUid))
      id
    })
  }

  var log: Str => Unit = (s) => ()
  var constraints: Ls[Cnstr] = Nil
  val termMap = new IdentityHashMap[Term, TermId]().asScala
  val varsName = mutable.Map.empty[TypeVarId, Str]
  val vuid = Uid.TypeVar.State()
  val euid = Uid.Term.State()
  val noExprId = euid.nextUid

  def freshVar(n: String)(using TermId): ((ProdStratEnum & ToStrat[ProdVar] & TypevarWithBoundary), (ConsStratEnum & ToStrat[ConsVar] & TypevarWithBoundary)) =
    val vid = vuid.nextUid
    val pv = ProdVar(vid, n)()
    val cv = ConsVar(vid, n)()
    varsName += vid -> n
    log(s"fresh var '$n")
    (pv, cv)
  def freshVar(n: Var)(using TermId): ((ProdStratEnum & ToStrat[ProdVar] & TypevarWithBoundary), (ConsStratEnum & ToStrat[ConsVar] & TypevarWithBoundary)) =
   freshVar(n.name)

  def apply(p: TypingUnit, additionalCtx: Map[Var, Strat[ProdVar]] = Map()): Ls[Var -> ProdStrat] = 
    // if constraints.nonEmpty then return Nil
    val vars: Map[Var, Strat[ProdVar]] = p.rawEntities.collect { 
      case fun: NuFunDef =>
        fun.nme -> freshVar(fun.name)(using noExprId)._1.toStrat()
    }.toMap
    val constructors: Map[Var, Strat[ProdObj]] = p.rawEntities.collect { 
      case ty: NuTypeDef =>
        val bodyStrats = apply(ty.body) // TODO: Add additional ctx for class arguments
        ty.nameVar -> ProdObj(Some(ty.nameVar), bodyStrats)(using noExprId).toStrat()
    }.toMap
    val ctx = vars
    p.rawEntities.map {
      case f: NuFunDef => {
        val p = process(f.rhs match 
          case Left(value) => value
          case Right(value) => ???)(using ctx, constructors)
        val v = vars(f.nme).s
        constrain(p, ConsVar(v.uid, v.name)()(using noExprId).toStrat())
      }
      case t: Term => {
        val topLevelProd = process(t)(using ctx, constructors)
        constrain(topLevelProd, NoCons()(using noExprId).toStrat())
      }
      case other => {
        debug.writeLine(s"Skipping ${other}")
      }
    }
    vars.toList

  val ctorExprToType = mutable.Map.empty[TermId, MkCtor]
  val dtorExprToType = mutable.Map.empty[TermId, Destruct]
  val exprToProdType = mutable.Map.empty[TermId, ProdStrat]

  def process(t: Term)(using ctx: Map[Var, Strat[ProdVar]], constructors: Map[Var, Strat[ProdObj]]): ProdStrat = 
    val res: ProdStratEnum = t match
      case IntLit(_) => ProdPrim("Int")(using t.uid)
      case DecLit(_) => ??? // floating point numbers as integers type
      case StrLit(_) => ???
      case r @ Var(id) if constructors.contains(r) =>
        constructors(r).s
      case r @ Var(id) =>// if varCtx(id).isDef then {
        ctx(r).s.copy()(Some(r))(using t.uid)
      //} else ctx(r).s.copy()(None)(using t.uid)
      case App(func, arg) => 
        val funcRes = process(func)
        val argRes = process(arg)
        funcRes.s match 
          case ProdObj(ctor, fields) => 
            // TODO: Handle object args i.e. class X(num: Int)
            funcRes.s
          case fun: ProdFun =>
            val sv = freshVar(s"${t.uid}_callres")(using t.uid)
            constrain(funcRes, ConsFun(argRes, sv._2.toStrat())(using noExprId).toStrat())
            sv._1
      case Lam(t @ Tup(args), body) =>
        val mapping = args.map{
          case (None, Fld(_, v: Var)) =>
            (v, freshVar(s"${t.uid}_${v.name}")(using noExprId))
          case _ => ??? // Unsupported
        }
        ProdFun(ConsTup(mapping.map(_._2._2.toStrat()))(using t.uid).toStrat(),
          process(body)(using ctx ++ mapping.map((i, s) => (i, s._1.toStrat()))))(using t.uid)
      case If(IfThen(scrut, thenn), S(elze)) =>
        constrain(process(scrut), consBool(using noExprId).toStrat())
        val res = freshVar(s"${t.uid}_ifres")(using t.uid)
        constrain(process(thenn), res._2.toStrat())
        constrain(process(elze), res._2.toStrat())
        res._1
      case If(_) => ??? // Desugar first (resolved by pretyper OR moving post-process point)
      case Tup(fields) =>
        val mapping = fields.map{
          case (None, Fld(_, fieldTerm: Term)) =>
            process(fieldTerm)
          case _ => ??? // Unsupported
        }
        ProdTup(mapping)(using t.uid)
      case Sel(receiver, fieldName) =>
        val selRes = freshVar(s"${t.uid}_selres")(using t.uid)
        constrain(process(receiver), ConsObj(None, List(fieldName -> selRes._2.toStrat()))(using noExprId).toStrat())
        selRes._1
      case Bra(true, t) =>
        process(t).s
      case Rcd(fields) =>
        ProdObj(None, fields.map{
          case (v, Fld(_, t)) => (v -> process(t))
        })(using t.uid)
      //case Blk(stmts) => 
      // val results = stmts.map(process)

    registerTermToType(t, res.toStrat())
  
  val constraintCache = mutable.Set.empty[(ProdStrat, ConsStrat)]
  val upperBounds = mutable.Map.empty[TypeVarId, Ls[(Path, ConsStrat)]].withDefaultValue(Nil)
  val lowerBounds = mutable.Map.empty[TypeVarId, Ls[(Path, ProdStrat)]].withDefaultValue(Nil)

  def constrain(prod: ProdStrat, cons: ConsStrat): Unit = {
    debug.writeLine(s"constraining ${prod} -> ${cons}")
    if (constraintCache.contains(prod -> cons)) return ()
    
    (prod.s, cons.s) match
        case (ProdPrim(n), NoCons()) =>
          ()
        case (ProdVar(v, pn), ConsVar(w, cn))
          if v === w => ()
        case (pv@ProdVar(v, _), _) =>
          cons.s match {
            // Check for important cases here
            case _ => ()
          }
          upperBounds += v -> ((pv.asOutPath.getOrElse(Path.empty) ::: prod.path.rev, cons) :: upperBounds(v))
          lowerBounds(v).foreach((lb_path, lb_strat) => constrain(
            lb_strat.addPath(lb_path), cons.addPath(prod.path.rev).addPath(pv.asOutPath.getOrElse(Path.empty))
          ))
        case (_, cv@ConsVar(v, _)) =>
          prod.s match {
            // Check for important cases here
            case _ => ()
          }
          lowerBounds += v -> ((cv.asInPath.getOrElse(Path.empty) ::: cons.path.rev, prod) :: lowerBounds(v))
          upperBounds(v).foreach((ub_path, ub_strat) => constrain(
            prod.addPath(cons.path.rev).addPath(cv.asInPath.getOrElse(Path.empty)), ub_strat.addPath(ub_path)
          ))
        case (ProdFun(lhs1, rhs1), ConsFun(lhs2, rhs2)) =>
          constrain(lhs2.addPath(cons.path.neg), lhs1.addPath(prod.path.neg))
          constrain(rhs1.addPath(prod.path), rhs2.addPath(cons.path))
        case (ProdTup(fields1), ConsTup(fields2)) =>
          (fields1 zip fields2).map((p, c) =>
            constrain(p, c)
          )
        case (ProdObj(nme1, fields1), ConsObj(nme2, fields2)) =>
          nme2 match 
            case Some(name) if name != nme1 => ???
            case _ => ()
          fields2.map((key, res2) => {
            fields1.find(_._1 == key) match 
              case None => ???
              case Some((_, res1)) => constrain(res1, res2)
          })
  }

  private def registerTermToType(t: Term, s: ProdStrat) = {
    exprToProdType.get(t.uid) match {
      case None => {
        exprToProdType += t.uid -> s
        s
      }
      case Some(value) =>
        lastWords(s"${t} registered two prod strategies:\n already has ${value}, but got ${s}")
    }
  }
}