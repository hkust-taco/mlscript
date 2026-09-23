package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.document.*
import hkmc2.document.Document.*
import scala.collection.mutable


sealed trait Shape extends ShapeLike:
  def describe: Str
  /** Origin of the value or symbol described by this shape, independently of its use site. */
  def toLoc: Opt[Loc]
  def shwDbg(using DebugPrinter): Str = this match
    // case ds: DefnShape => s"DefnShape(${ds.defn.describe} ${ds.defn.sym.showDbg})"
    case ds: DefnShape => ds.defn.sym.showDbg
    case as: AppShape => s"AppShape(${as.receiver.shwDbg}, ${as.args.showDbg})"
    case ms: MarkedShape => s"MarkedShape(${ms.sh.shwDbg}, ${ms.mark.showDbg})"
    case ns: SymShape => s"SymShape(${ns.sym.showDbg})"
    case ns: NewShape => s"NewShape(${ns.cls.showDbg}, ${ns.argss.map(_.showDbg).mkString(", ")})"
    case is: IntroShape => s"IntroShape(${is.trm.showDbg})"
    case us: UnknownValueShape => s"UnknownValueShape(${us.source.showDbg})"
    case ts: TupleShape => s"TupleShape(${ts.source.showDbg})"
    case rs: RecordShape => s"RecordShape(${rs.source.showDbg})"
    case bs: BaseShape => s"BaseShape(${bs.defn.sym.showDbg})"
    case es: ErrShape => es.describe

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
  protected def getMemberImpl(name: Str): Opt[MemberInfo] =
    sh.getMember(name).map(_.mapSecond(_ ::: mark :: Nil))
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
  // Cache both hits and misses per shape, without materializing all inherited members.
  private val membersCache = mutable.Map.empty[Str, Opt[MemberInfo]]
  final def getMember(name: Str): Opt[MemberInfo] =
    membersCache.getOrElseUpdate(name, getMemberImpl(name))
  protected def getMemberImpl(name: Str): Opt[MemberInfo]
  
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
  
end TermShape

// sealed trait TermShape:
//   def describe: Str = this match
//     case app: AppShape => s"application of ${app.lhs.describe} to ${app.args.describe}"
//     case sel: SelShape => s"selection of ${sel.nme.name} from ${sel.receiver.describe}"
//     case sym: SymShape => s"symbol ${sym.sym.describe}"

// Record properties carry their value term as well as their symbol, avoiding
// mutable definition state on TermSymbol for these non-overloaded members.
type MemberInfo = (BlockMemberSymbol | RecordMember, Ls[Marks])

extension (symbol: BlockMemberSymbol | TermSymbol)
  def describeMember: Str = symbol match
    case symbol: BlockMemberSymbol => symbol.describe
    case symbol: TermSymbol => symbol.describeKind

extension (member: BlockMemberSymbol | RecordMember)
  def memberSymbol: BlockMemberSymbol | TermSymbol = member match
    case symbol: BlockMemberSymbol => symbol
    case member: RecordMember => member.field.sym

class ErrShape(val err: ErrorReport) extends NonAppTermShape:
  def describe: Str = s"error: ${err.mainMsg}"
  protected def getMemberImpl(name: Str): Opt[MemberInfo] = N
  def toLoc: Opt[Loc] = N

class AppShape(val receiver: TermShape, val args: Term, val src: Term.App)(using DebugPrinter) extends NonMarkedShape:
  protected def getMemberImpl(name: Str): Opt[MemberInfo] =
    // An unsaturated term definition is just a concrete function shape
    if !isSaturated then N
    else
      applicationHead match
      case (ds: DefnShape, mss) =>
        ds.getInstanceMember(name).map(_.mapSecond(_ ::: mss))
      case _ => N
  def describe: Str =
    // s"application of ${receiver.describe}"
    s"instance of ${applicationHead._1.describe}"
  def toLoc: Opt[Loc] = src.toLoc
  override def toString: String = s"AppShape($receiver, ${args.showDbg})"
  // def target: Opt[AppTarget]

class NewShape(val receiver: TermShape, val cls: ClassLikeSymbol, clsMarks: Ls[Marks], val argss: Ls[Term], val src: Term.New)(using DebugPrinter) extends NonMarkedShape:
  protected def getMemberImpl(name: Str): Opt[MemberInfo] =
    receiver match
      case ds: DefnShape => ds.getInstanceMember(name).map(_.mapSecond(_ ::: clsMarks))
      case _ => N
  def describe: Str =
    // s"instantiation of ${receiver.describe}"
    s"instance of ${cls.defn.get.describeRef}"
  override def toString: String = s"NewNewShape(${cls.showDbg}, $argss)"
  def toLoc: Opt[Loc] = src.toLoc

class SymShape(val sym: BlockMemberSymbol, val resSym: FlowSymbol, val markss: Ls[Marks]) extends Shape:
  def describe: Str = s"${sym.describe} symbol '${sym.nme}'"
  def toLoc: Opt[Loc] = sym.toLoc
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
  override def extendsCls(cls: ClassLikeDef): Bool =
    (defn is cls) || ext.exists(_.applicationHead._1.extendsCls(cls))
  def describe: Str = s"${defn.describe}"
  protected def getMemberImpl(name: Str): Opt[MemberInfo] =
    defn.body.members.get(name).map(_ -> Nil).orElse(ext.flatMap(_.getMember(name)))
  def toLoc: Opt[Loc] = defn.toLoc

class DefnShape(val defn: Definition, val ext: Opt[TermShape]) extends NonAppTermShape:
  /** Instance lookup is shared by constructor calls and explicit `new`.
    * Inherited members retain their marks before the caller adds its captures. */
  def getInstanceMember(name: Str): Opt[MemberInfo] = defn match
    case cd: ClassDef =>
      cd.body.members.get(name).map(_ -> Nil).orElse(ext.flatMap(_.getMember(name)))
    case _: TermDefinition => ext.flatMap(_.getMember(name))
    case _ => N
  override def extendsCls(cls: ClassLikeDef): Bool =
    clsDef.contains(cls) || ext.exists(_.applicationHead._1.extendsCls(cls))
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
      case defn: ClassDef => return defn.kind.desc + " value"
      case defn: TypeLikeDef => defn.kind.desc + " "
      case defn: TermDefinition =>
        defn.tsym match
        case _: ClassCtorSymbol => "class constructor "
        case s => s.k.desc + " "
    }'${defn.bsym.nme}'"
  // override def toString: String = s"DefnShape(${defn.describe} ${defn.bsym.nme})"
  override def toString: String = s"DefnShape(${defn.describe})"
  protected def getMemberImpl(name: Str): Opt[MemberInfo] =
    defn match
    case defn: ModuleOrObjectDef =>
      defn.body.members.get(name).map(_ -> Nil).orElse(ext.flatMap(_.getMember(name)))
    case defn: TermDefinition => ???
    case _ => N
  def toLoc: Opt[Loc] = defn.sym.toLoc

/* 
class RefinedShape(val base: TermShape, val refinements: Ls[Str -> Term]) extends NonAppTermShape:
  def describe: Str = base.describe
  lazy val members: Map[Str, MemberInfo] =
    base.members ++ refinements.iterator.map: (nme, trm) =>
      // nme -> BlockMemberSymbol(nme, trm)
      ???
*/
/** A tuple candidate selects a value shape for each spread. Ordinary fields stay
  * lazy. Recursive spreads can have unknown length; retain the known fields around
  * them instead of discarding either those fields or the unresolved possibilities.
  */
final case class TupleShape(source: Term, elements: Ls[TupleShape.Element]) extends NonAppTermShape:
  lazy val segments: Ls[TupleShape.Segment] = elements.flatMap:
    case segment: TupleShape.Segment => segment :: Nil
    case TupleShape.Rest(_, segments) => segments
    case TupleShape.Spread(shape, marks) => shape.segments.map:
      case TupleShape.Field(field, inner) => TupleShape.Field(field, inner ::: marks :: Nil)
      case TupleShape.Unknown(shape, inner) => TupleShape.Unknown(shape, inner ::: marks :: Nil)
  /** Does this candidate already depend on the given producer in the given context?
    * `source` identifies the producer by syntax-node identity; `marks` distinguish
    * its spread contexts. Inspect the selected dependency tree, not flattened
    * segments, since flattening would erase the evidence of recursive production.
    * Rest views retain that evidence even when they consume the relevant fields.
    *
    * The tuple listener uses this to widen repeated dependencies: for a producer
    * like `[n, ...growing(n - 1)]`, repeatedly prefixing its own candidates would
    * otherwise create unboundedly many shapes. This is an approximation, not a
    * proof of runtime recursion: contexts have only the precision of their marks.
    */
  def containsSpread(source: Term, marks: Marks): Bool = elements.exists:
    case _: TupleShape.Segment => false
    case TupleShape.Rest(shape, _) => shape.containsSpread(source, marks)
    case TupleShape.Spread(shape, inner) =>
      ((shape.source is source) && inner == marks) || shape.containsSpread(source, marks)
  def describe: Str = "tuple literal"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: Str): Opt[MemberInfo] = ??? // Structural tuple members are not implemented yet.

/** The element of an opaque or widened spread can be any value. Keep this
  * alternative in the flow graph so other, known arguments cannot silently make
  * an unresolved member selection appear to have a unique static target.
  */
final case class UnknownValueShape(source: Term) extends NonAppTermShape:
  def describe: Str = "value of unknown shape"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: Str): Opt[MemberInfo] = N

object TupleShape:
  sealed trait Element
  sealed trait Segment extends Element
  final case class Field(field: Fld, marks: Ls[Marks]) extends Segment
  /** An arbitrary number of arbitrary values. Use this for opaque layouts and
    * recursive widening, never for a spread whose shape has not arrived yet.
    * The `source` field is used for user-facing diagnostic purposes. */  
  final case class Unknown(source: Term, marks: Ls[Marks]) extends Segment
  final case class Spread(shape: TupleShape, marks: Marks) extends Element
  def unknown(source: Term): TupleShape = TupleShape(source, Unknown(source, Nil) :: Nil)
  /** Retain the original candidate as well as the selected residual segments:
    * flattening away the parent would hide recursive producer dependencies from
    * containsSpread, allowing recursion through rest slicing to evade widening. */
  final case class Rest(shape: TupleShape, segments: Ls[Segment]) extends Element


/** A property selected from one record candidate. Mutable records expose a
  * stable property identity, but their initializer is not a sound value shape.
  */
final case class RecordMember(field: RcdField, mutable: Bool)

/** Keep spread candidates and their contexts rather than flattening away their
  * provenance. Lookup follows runtime's last-write-wins order. Unknown entries
  * are barriers: an opaque spread or computed key can overwrite earlier fields.
  */
final case class RecordShape(source: Term.Rcd, elements: Ls[RecordShape.Element]) extends NonAppTermShape:
  def describe: Str = "record literal"
  def toLoc: Opt[Loc] = source.toLoc
  private def lookup(name: Str): Either[Unit, Opt[(RecordMember, Ls[Marks])]] =
    def loop(rest: Ls[RecordShape.Element]): Either[Unit, Opt[(RecordMember, Ls[Marks])]] = rest match
      case Nil => Right(N)
      case RecordShape.Field(field) :: rest => field.field match
        case Term.Lit(Tree.StrLit(key)) =>
          if key == name then Right(S(RecordMember(field, source.mut) -> Nil)) else loop(rest)
        case _ => Left(())
      case RecordShape.Unknown :: _ => Left(())
      case RecordShape.Spread(shape, marks) :: rest => shape.lookup(name) match
        case Left(_) => Left(())
        case Right(N) => loop(rest)
        case Right(S((member, inner))) =>
          Right(S(member.copy(mutable = member.mutable || source.mut) -> (inner ::: marks :: Nil)))
    loop(elements.reverse)
  def hasUnknownMember(name: Str): Bool = lookup(name).isLeft
  protected def getMemberImpl(name: Str): Opt[MemberInfo] = lookup(name).toOption.flatten
  def containsSpread(record: Term.Rcd, marks: Marks): Bool = elements.exists:
    case RecordShape.Spread(shape, inner) =>
      ((shape.source is record) && inner == marks) || shape.containsSpread(record, marks)
    case _ => false

object RecordShape:
  enum Element:
    case Field(field: RcdField)
    case Spread(shape: RecordShape, marks: Marks)
    case Unknown
  export Element.*


type IntroTerm = Term.Lit | Term.UnitVal | Term.Lam //| Term.New
class IntroShape(val trm: IntroTerm) extends NonAppTermShape:
  def describe: Str = trm.describe
  protected def getMemberImpl(name: Str): Opt[MemberInfo] = trm match
    case _: Term.Lit | _: Term.UnitVal => N // TODO: methods on literals
    case lam: Term.Lam => N // TODO: methods on lambdas
    // case newTerm: Term.New =>
    //   Map.empty // TODO
  def toLoc: Opt[Loc] = trm.toLoc
  override def toString: Str = s"IntroShape(${trm})"

sealed trait LitShape extends NonAppTermShape:
  self: Term.Lit =>
  protected def getMemberImpl(name: Str): Opt[MemberInfo] = N // TODO: methods on literals, e.g. string methods


type ShapePublisher = Publisher[Shape]
type ShapeHost = Host[Shape]


