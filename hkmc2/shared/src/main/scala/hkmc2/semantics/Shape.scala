package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.document.*
import hkmc2.document.Document.*


sealed trait Shape extends ShapeLike:
  def describe: Str
  def shwDbg(using DebugPrinter): Str = this match
    // case ds: DefnShape => s"DefnShape(${ds.defn.describe} ${ds.defn.sym.showDbg})"
    case ds: DefnShape => ds.defn.sym.showDbg
    case as: AppShape => s"AppShape(${as.receiver.shwDbg}, ${as.args.showDbg})"
    case ms: MarkedShape => s"MarkedShape(${ms.sh.shwDbg}, ${ms.mark.showDbg})"
    case ns: SymShape => s"SymShape(${ns.sym.showDbg})"
    case ns: NewShape => s"NewShape(${ns.cls.showDbg}, ${ns.argss.map(_.showDbg).mkString(", ")})"
    case is: IntroShape => s"IntroShape(${is.trm.showDbg})"

sealed trait NonMarkedShape extends TermShape
sealed trait NonAppTermShape extends NonMarkedShape

// type Mark = Opt[AnyDefinitionSymbol] -> Bool
// case class Mark(sym: Opt[AnyDefinitionSymbol], entry: Bool)
// sealed abstract class Marks
// case class MoreMarks(sym: Opt[AnyDefinitionSymbol], entry: Bool, rest: Marks) extends Marks
// case object NoMark extends Marks
sealed abstract class Marks:
  def showDbg(using DebugPrinter): Str = this match
    case EntryMark(sym, id, rest) => s"↘⟨${sym.showDbg}⟩${id.fold("")("%⟨"+_.showDbg+"⟩")}${rest.showDbg}"
    case ExitMark(sym, id, rest) => s"↗⟨${sym.showDbg}⟩${id.fold("")("%⟨"+_.showDbg+"⟩")}${rest.showDbg}"
    case NoMarks => "ϵ"
type SomeMarks = EntryMark | ExitMark
case class EntryMark(sym: AnyDefinitionSymbol, id: Opt[FlowSymbol], rest: Marks) extends Marks
sealed abstract class ExitMarks extends Marks
case class ExitMark(sym: AnyDefinitionSymbol, id: Opt[FlowSymbol], rest: ExitMarks) extends ExitMarks
case object NoMarks extends ExitMarks

sealed trait ShapeLike:
  def exit(revMarkss: Ls[Marks])(using TL): TermShape | NoShape
  def exit(marks: Marks)(using TL): TermShape | NoShape
  def enter(revMarkss: Ls[Marks])(using TL): TermShape | NoShape
  def enter(marks: Marks)(using TL): TermShape | NoShape
  def shwDbg(using DebugPrinter): Str

case object NoShape extends ShapeLike:
  def exit(revMarkss: Ls[Marks])(using TL): TermShape | NoShape = NoShape
  def exit(marks: Marks)(using TL): TermShape | NoShape = NoShape
  def enter(revMarkss: Ls[Marks])(using TL): TermShape | NoShape = NoShape
  def enter(marks: Marks)(using TL): TermShape | NoShape = NoShape
  def shwDbg(using DebugPrinter): Str = toString

type NoShape = NoShape.type

object Marked:
  def unapply(sh: TermShape): S[(NonMarkedShape, Marks)] =
    sh match
    case sh: NonMarkedShape => S((sh, NoMarks))
    case MarkedShape(sh, mark) => S((sh, mark))
end Marked

case class MarkedShape(sh: NonMarkedShape, mark: SomeMarks) extends TermShape:
  lazy val members: Map[Str, MemberInfo] =
    // sh.members.view.mapValues(m => MarkedShape.exit(m, mark)).toMap
    // sh.members // FIXME: add marks to tuple result
    sh.members.mapValues(_.mapSecond(_ ::: mark :: Nil)).toMap
    // sh.members.mapValues(_.mapSecond(mark :: _)).toMap
  def describe: Str = sh.describe
  def toLoc: Opt[Loc] = sh.toLoc
object MarkedShape:
  def enter(sh: TermShape, sym: AnyDefinitionSymbol, id: Opt[FlowSymbol])(using TL): MarkedShape =
    sh match
    case sh: NonMarkedShape => MarkedShape(sh, EntryMark(sym, id, NoMarks))
    case MarkedShape(sh, marks) =>
      // marks match
      // case marks: EntryMark => MarkedShape(sh, EntryMark(sym, id, marks))
      // case ExitMark(sym2, id2, rest) =>
      //   require(sym2 is sym)
      //   id2 match
      //   case S(`id`) => MarkedShape(sh, marks)
      //   if id2 is id then
      //     rest match
      //     case NoMarks => sh
      //     case rest: ExitMark => MarkedShape(sh, rest)
      //   else
      //     MarkedShape(sh, EntryMark(sym, id, marks))
      //   // MarkedShape(sh, EntryMark(sym, marks))
      //   ???
      MarkedShape(sh, EntryMark(sym, id, marks))
  def exit(sh: TermShape, sym: AnyDefinitionSymbol, id: Opt[FlowSymbol])(using TL): TermShape | NoShape =
  tl.trace[TermShape | NoShape](s".exit MarkedShape (${sh.shwDbg}, ${sym.showDbg}, ${id.fold("")(_.showDbg)})", res => s"= ${res.shwDbg}"):
    tl.log(s"${sym.getClass} ${sym match
      case sym: TermSymbol => sym.owner.map(_.showDbg)
      case _ => "?"
    }")
    sh match
    case sh: NonMarkedShape => MarkedShape(sh, ExitMark(sym, id, NoMarks))
    case MarkedShape(sh, marks) =>
      marks match
      case marks: ExitMark => MarkedShape(sh, ExitMark(sym, id, marks))
      case EntryMark(sym2, id2, rest) =>
        require(sym2 is sym, s"Expected symbol ${sym.showDbg} but got ${sym2.showDbg}")
        // tl.log(s"!? ${id} vs ${id2}")
        // // id2 match
        // (id,id2) match
        // // case S(`id`) | N =>
        // // case `id` | N =>
        // case (N, _) | (_, N) | (S(_), S(_)) if id === id2 =>
        //   rest match
        //   case NoMarks => sh
        //   case rest: SomeMarks => MarkedShape(sh, rest)
        // // case S(id2) =>
        // case _ =>
        //   // MarkedShape(sh, ExitMark(sym, id, marks))
        //   NoShape
        // // MarkedShape(sh, EntryMark(sym, marks))
        // // ???
        if id.forall(i1 => id2.forall(i2 => i1 is i2)) then
          rest match
          case NoMarks => sh
          case rest: SomeMarks => MarkedShape(sh, rest)
        else NoShape
end MarkedShape

sealed trait TermShape extends Shape:
  def members: Map[Str, MemberInfo]
  
  def extendsCls(cls: ClassLikeDef): Bool = false
  
  lazy val applicationHead: (NonAppTermShape, Ls[Marks]) = this match
    // case ds: DefnShape => ds
    // case as: AppShape => as.receiver.applicationHead
    case as: AppShape => as.receiver.applicationHead
    case ns: NewShape => ns.receiver.applicationHead
    case na: NonAppTermShape => (na, Nil)
    case MarkedShape(sh, mark) => sh.applicationHead.mapSecond(mark :: _)
  lazy val unappliedParams: Ls[(ParamList, Ls[Marks])] = this match
    case ds: DefnShape => ds.defn match
      case defn: TermDefinition => defn.params.map(_ -> Nil)
      case defn: ClassDef =>
        // println(defn.ctorSym)
        // if defn.ctorSym.isDefined then
        if defn.paramsOpt.isDefined then // whether the class can receive direct applications
          (defn.paramsOpt.toList ::: defn.auxParams).map(_ -> Nil)
        else Nil
      case _ => Nil
    case as: AppShape => as.receiver.unappliedParams.drop(1)
    case ns: NewShape => ns.receiver.unappliedParams.drop(ns.argss.length)
    case MarkedShape(sh, mark) => sh.unappliedParams.map(p => p._1 -> (mark :: p._2))
    case is: IntroShape =>
      is.trm match
      case Term.Lam(params, body) => (params -> Nil) :: 
        // body.unappliedParams
        Nil
      case _ => Nil
    case _ => Nil
  
  def exit(marks: Marks)(using TL): TermShape | NoShape =
  tl.trace[TermShape | NoShape](s".exit $shwDbg (${marks.showDbg})", res => s"= ${res.shwDbg}"):
    marks match
    case NoMarks => this
    // case EntryMark(sym, id, rest) =>
    //   MarkedShape.enter(this, sym, id).exit(rest)
    // case ExitMark(sym, id, rest) =>
    //   MarkedShape.exit(this, sym, id).exit(rest)
    case EntryMark(sym, id, rest) =>
      exit(rest) match
      case NoShape =>  NoShape
      case ex: TermShape => MarkedShape.enter(ex, sym, id)
    case ExitMark(sym, id, rest) =>
      exit(rest) match
      case NoShape =>  NoShape
      case ex: TermShape => MarkedShape.exit(ex, sym, id)
  
  def exit(revMarkss: Ls[Marks])(using TL): TermShape | NoShape = revMarkss match
    case Nil => this
    case mark :: rest =>
      exit(mark).exit(rest)
  
  def enter(marks: Marks)(using tl: TL): TermShape | NoShape =
  tl.trace[TermShape | NoShape](s".enter $shwDbg (${marks.showDbg})", res => s"= ${res.shwDbg}"):
    marks match
    case NoMarks => this
    case EntryMark(sym, id, rest) =>
      // MarkedShape.enter(this, sym, id).enter(rest)
      // ???
      // MarkedShape.exit(this, sym, id) match
      // case NoShape => this // TODO: should this be an error?
      // case sh: TermShape => sh.enter(rest)
      MarkedShape.exit(this, sym, id).enter(rest)
    case ExitMark(sym, id, rest) =>
      // MarkedShape.exit(this, sym, id) match
      // case NoShape => this // TODO: should this be an error?
      // case sh => sh.enter(rest)
      MarkedShape.enter(this, sym, id).enter(rest)
    // marks match
    // case NoMarks => this
    // case marks: SomeMarks =>
    //   this match
    //   case sh: NonMarkedShape => MarkedShape(sh, marks)
    //   case MarkedShape(sh, mark) =>
    //     ???
  
  def enter(revMarkss: Ls[Marks])(using TL): TermShape | NoShape = revMarkss match
    case Nil => this
    case mark :: rest =>
      enter(mark).enter(rest)
  
  def isSaturated: Bool = unappliedParams.isEmpty
  def toLoc: Opt[Loc]
  
end TermShape

// sealed trait TermShape:
//   def describe: Str = this match
//     case app: AppShape => s"application of ${app.lhs.describe} to ${app.args.describe}"
//     case sel: SelShape => s"selection of ${sel.nme.name} from ${sel.receiver.describe}"
//     case sym: SymShape => s"symbol ${sym.sym.describe}"

type MemberInfo = (BlockMemberSymbol, Ls[Marks])

class ErrShape(val err: ErrorReport) extends NonAppTermShape:
  def describe: Str = s"error: ${err.mainMsg}"
  def members: Map[Str, MemberInfo] = Map.empty
  def toLoc: Opt[Loc] = N

class AppShape(val receiver: TermShape, val args: Term, val src: Term.App)(using DebugPrinter) extends NonMarkedShape:
  lazy val members: Map[Str, MemberInfo] =
    // An unsaturated term definition is just a concrete function shape
    if !isSaturated then Map.empty
    else
      applicationHead match
      case (ds: DefnShape, mss) =>
        // TODO: handle `mss`
        
        // ds.members
        // ds.defn match
        // case td: TermDefinition => td.sym match
        //   case cs: ClassCtorSymbol =>
        //     val cd = cs.associatedCls.defn.get
        //     cd.ext.fold(Map.empty)(_.members) ++ cd.body.members
        //   case _ => ??? // TODO: add softRequire on ction – should not be possible
        // case cd: ClassDef => cd.ext.fold(Map.empty)(_.members) ++ cd.body.members
        ds.defn match
        case cd: ClassDef => ds.ext.fold(Map.empty)(_.members).mapValues(_.mapSecond(_ ::: mss)).toMap ++
          cd.body.members.mapValues(_ -> mss).toMap
        case td: TermDefinition =>
          ds.ext.fold(Map.empty)(_.members).mapValues(_.mapSecond(_ ::: mss)).toMap
      case _ => Map.empty
  def describe: Str =
    // s"application of ${receiver.describe}"
    s"instance of ${applicationHead._1.describe}"
  def toLoc: Opt[Loc] = src.toLoc
  override def toString: String = s"AppShape($receiver, ${args.showDbg})"
  // def target: Opt[AppTarget]

abstract class NewShape(val receiver: TermShape, val cls: ClassLikeSymbol, val argss: Ls[Term], val src: Term.New)(using DebugPrinter) extends NonMarkedShape:
  def describe: Str =
    // s"instantiation of ${receiver.describe}"
    s"instance of ${cls.defn.get.describeRef}"
  override def toString: String = s"NewNewShape(${cls.showDbg}, $argss)"
  def toLoc: Opt[Loc] = src.toLoc

class SymShape(val sym: BlockMemberSymbol, val resSym: FlowSymbol, val markss: Ls[Marks]) extends Shape:
  def describe: Str = s"${sym.describe} symbol '${sym.nme}'"
  override def toString: String = s"SymShape($sym)"
  def exit(revMarkss: Ls[Marks])(using TL): TermShape | NoShape = ???
  def exit(marks: Marks)(using TL): TermShape | NoShape = ???
  def enter(revMarkss: Ls[Marks])(using TL): TermShape | NoShape = ???
  def enter(marks: Marks)(using TL): TermShape | NoShape = ???

/* 
class ThisShape(val defn: Definition) extends NonAppTermShape:
  def describe: Str = s"Self-reference to ${defn.bsym.describe} '${defn.bsym.nme}'"
  override def toString: String = s"ThisShape(${defn.describe})"
  def members: Map[Str, MemberInfo] = ???
*/

// TODO: make it not a TermShape?
class BaseShape(val defn: ClassLikeDef, val ext: Opt[TermShape]) extends NonAppTermShape:
  def describe: Str = s"${defn.describe}"
  lazy val members: Map[Str, MemberInfo] =
    ext.fold(Map.empty)(_.members) ++ defn.body.members.mapValues(_ -> Nil).toMap
  def toLoc: Opt[Loc] = defn.toLoc

class DefnShape(val defn: Definition, val ext: Opt[TermShape]) extends NonAppTermShape:
  override def extendsCls(cls: ClassLikeDef): Bool =
    clsDef.contains(cls) || ext.exists(_.extendsCls(cls))
  lazy val clsDef = defn match
    case defn: ClassLikeDef => S(defn)
    case defn: TermDefinition =>
      defn.tsym match
      case ts: ClassCtorSymbol => S(ts.associatedCls.defn.get)
      case _ => N
    case _ => N
  // def describe: Str = s"${defn.describe}"
  def describe: Str =
    // s"${defn.bsym.describe} '${defn.bsym.nme}'"
    // s"${defn.describe}"
    // s"${defn.bsym.asCls.fold("")(_.defn.get.kind.desc+" ")}'${defn.bsym.nme}'"
    s"${defn match
      case defn: TypeLikeDef => defn.kind.desc + " "
      case defn: TermDefinition =>
        defn.tsym match
        case _: ClassCtorSymbol => "class constructor "
        case s => s.k.desc + " "
      case _ => ""
    }'${defn.bsym.nme}'"
  // override def toString: String = s"DefnShape(${defn.describe} ${defn.bsym.nme})"
  override def toString: String = s"DefnShape(${defn.describe})"
  lazy val members: Map[Str, MemberInfo] =
    // println((ext, ext.map(_.members)))
    // ext.fold(Map.empty)(_.members) ++ defn.match
    defn match
    case defn: ModuleOrObjectDef =>
      // println(defn.ext.map(_.cls.members))
      ext.fold(Map.empty)(_.members) ++ defn.body.members.mapValues(_ -> Nil).toMap
    case defn: TermDefinition => ???
    case _ => Map.empty
  def toLoc: Opt[Loc] = defn.sym.toLoc

/* 
class RefinedShape(val base: TermShape, val refinements: Ls[Str -> Term]) extends NonAppTermShape:
  def describe: Str = base.describe
  lazy val members: Map[Str, MemberInfo] =
    base.members ++ refinements.iterator.map: (nme, trm) =>
      // nme -> BlockMemberSymbol(nme, trm)
      ???
*/
type IntroTerm = Term.Lit | Term.UnitVal | Term.Tup | Term.Lam | Term.Rcd //| Term.New
class IntroShape(val trm: IntroTerm) extends NonAppTermShape:
  def describe: Str = trm.describe
  lazy val members: Map[Str, MemberInfo] = trm match
    case tup: Term.Tup =>
      // tup.fields.iterator.map:
      ???
    case lam: Term.Lam => Map.empty // TODO: methods on lambdas
    case rcd: Term.Rcd =>
      // rcd.stats.iterator.collect:
      // TODO: handler RcdField, RcdSpread
      ???
    // case newTerm: Term.New =>
    //   Map.empty // TODO
  def toLoc: Opt[Loc] = trm.toLoc
  override def toString: Str = s"IntroShape(${trm})"

sealed trait LitShape extends NonAppTermShape:
  self: Term.Lit =>
  def members: Map[Str, MemberInfo] = Map.empty // TODO: methods on literals, e.g. string methods


type ShapePublisher = Publisher[Shape]
type ShapeHost = Host[Shape]


