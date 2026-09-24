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
    case _: DynShape => "DynShape"
    case us: UnknownValueShape => s"UnknownValueShape(${us.source.showDbg})"
    case ts: TupleShape => s"TupleShape(${ts.source.showDbg})"
    case rs: RecordShape => s"RecordShape(${rs.source.showDbg})"
    case bs: BaseShape => s"BaseShape(${bs.defn.sym.showDbg})"
    case es: ErrShape => es.describe

sealed trait NonMarkedShape extends TermShape
sealed trait NonAppTermShape extends NonMarkedShape

/** A lexical resolution boundary, independent of a definition's term/type interpretation.
  * A class and its companion constructor enter the same instance scope. Keeping their
  * symbol identities distinct is still necessary for overload selection and lowering.
  */
final case class ResolutionBoundary private (symbol: AnyDefinitionSymbol):
  def showDbg(using DebugPrinter): Str = symbol.showDbg
  override def toString: Str = symbol.toString
object ResolutionBoundary:
  def apply(symbol: AnyDefinitionSymbol): ResolutionBoundary =
    new ResolutionBoundary(symbol match
      case ctor: ClassCtorSymbol => ctor.associatedCls
      case symbol => symbol)

/** A reduced lexical path: entries followed by exits, stored outermost first.
  * Exiting cancels the leading entry when their sites agree (an absent site is
  * a capture, compatible with any activation). Entering never cancels an exit:
  * that pair records an inner value's provenance until a consumer accesses it.
  * Each direction traverses distinct lexical scopes, so recursive calls cannot
  * lengthen a normalized path indefinitely. Violations are asserted, not widened.
  */
sealed abstract class Marks:
  def showDbg(using DebugPrinter): Str = this match
    case EntryMark(boundary, id, rest) => s"↘⟨${boundary.showDbg}⟩${id.fold("")("%⟨"+_.showDbg+"⟩")}${rest.showDbg}"
    case ExitMark(boundary, id, rest) => s"↗⟨${boundary.showDbg}⟩${id.fold("")("%⟨"+_.showDbg+"⟩")}${rest.showDbg}"
    case NoMarks => "ϵ"
  @scala.annotation.tailrec
  final def hasEntry(boundary: ResolutionBoundary): Bool = this match
    case EntryMark(b, _, rest) => b == boundary || rest.hasEntry(boundary)
    case _ => false

type SomeMarks = EntryMark | ExitMark
case class EntryMark(boundary: ResolutionBoundary, id: Opt[FlowSymbol], rest: Marks) extends Marks:
  // Consecutive entries descend lexical scopes; consecutive exits ascend them.
  // Repeating a scope in either direction indicates a missing capture/exit, not
  // another recursive activation to retain or silently truncate.
  assert(!rest.hasEntry(boundary), "Repeated entry into the same lexical resolution scope")
sealed abstract class ExitMarks extends Marks:
  @scala.annotation.tailrec
  final def hasExit(boundary: ResolutionBoundary): Bool = this match
    case ExitMark(b, _, rest) => b == boundary || rest.hasExit(boundary)
    case NoMarks => false
case class ExitMark(boundary: ResolutionBoundary, id: Opt[FlowSymbol], rest: ExitMarks) extends ExitMarks:
  assert(!rest.hasExit(boundary), "Repeated exit from the same lexical resolution scope")
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
  protected def getMemberImpl(name: Str): MemberLookup =
    sh.getMember(name).withMarks(mark :: Nil)
  override def isInstanceOfClass(cls: ClassLikeDef): Bool = sh.isInstanceOfClass(cls)
  def describe: Str = sh.describe
  def toLoc: Opt[Loc] = sh.toLoc
object MarkedShape:
  def enter(sh: TermShape, boundary: ResolutionBoundary, id: Opt[FlowSymbol])(using TL): MarkedShape =
    sh match
    case sh: NonMarkedShape => MarkedShape(sh, EntryMark(boundary, id, NoMarks))
    case MarkedShape(sh, marks) => MarkedShape(sh, EntryMark(boundary, id, marks))
  def exit(sh: TermShape, boundary: ResolutionBoundary, id: Opt[FlowSymbol])(using TL): TermShape | NoShape =
  tl.trace[TermShape | NoShape](s".exit MarkedShape (${sh.shwDbg}, ${boundary.showDbg}, ${id.fold("")(_.showDbg)})", res => s"= ${res.shwDbg}"):
    sh match
    case sh: NonMarkedShape => MarkedShape(sh, ExitMark(boundary, id, NoMarks))
    case MarkedShape(sh, marks) =>
      marks match
      case marks: ExitMark => MarkedShape(sh, ExitMark(boundary, id, marks))
      case EntryMark(entered, id2, rest) =>
        assert(entered == boundary, "Entry and exit cross different lexical resolution scopes")
        if id.forall(i1 => id2.forall(i2 => i1 is i2)) then
          rest match
          case NoMarks => sh
          case rest: SomeMarks => MarkedShape(sh, rest)
        else NoShape
end MarkedShape

sealed trait TermShape extends Shape:
  // Cache all lookup outcomes per shape, without materializing all inherited members.
  private val membersCache = mutable.Map.empty[Str, MemberLookup]
  final def getMember(name: Str): MemberLookup =
    membersCache.getOrElseUpdate(name, getMemberImpl(name))
  protected def getMemberImpl(name: Str): MemberLookup
  
  /** Whether this value is an instance of the nominal class. A saturated class
    * value (e.g. a class without parameters) is still not an instance. */
  def isInstanceOfClass(cls: ClassLikeDef): Bool = false
  
  // Context fragments run from the callable definition to its consumer, just as
  // MemberLookup.withMarks does. Wrapping an applied shape appends its context.
  lazy val applicationHead: (NonAppTermShape, Ls[Marks]) = this match
    // case ds: DefnShape => ds
    // case as: AppShape => as.receiver.applicationHead
    case as: AppShape => as.receiver.applicationHead
    case ns: NewShape => (ns.receiver, ns.clsMarks)
    case na: NonAppTermShape => (na, Nil)
    case MarkedShape(sh, mark) => sh.applicationHead.mapSecond(_ ::: mark :: Nil)
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
    case ns: NewShape => ns.receiver.unappliedParams.drop(ns.argss.length).map:
      case (ps, marks) => ps -> (marks ::: ns.clsMarks)
    case MarkedShape(sh, mark) => sh.unappliedParams.map(p => p._1 -> (p._2 ::: mark :: Nil))
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
      // Fragments describe travel from the definition out to its consumer.
      // Passing an argument back in must undo that composition in reverse order.
      enter(rest).enter(mark)
  
  def isSaturated: Bool = unappliedParams.isEmpty
  
end TermShape

// sealed trait TermShape:
//   def describe: Str = this match
//     case app: AppShape => s"application of ${app.lhs.describe} to ${app.args.describe}"
//     case sel: SelShape => s"selection of ${sel.nme.name} from ${sel.receiver.describe}"
//     case sym: SymShape => s"symbol ${sym.sym.describe}"

/** Missing means definitely absent; Unknown must not be treated as a miss when
  * searching wildcard opens, since it can introduce an additional candidate. */
enum MemberLookup:
  case Found(member: BlockMemberSymbol | RecordMember, marks: Ls[Marks])
  case Dynamic(marks: Ls[Marks])
  case Missing
  case Unknown(reason: MemberLookup.Uncertainty, loc: Opt[Loc])
  
  def withMarks(marks: Ls[Marks]): MemberLookup = this match
    case Found(member, inner) => Found(member, inner ::: marks)
    case Dynamic(inner) => Dynamic(inner ::: marks)
    case _ => this

object MemberLookup:
  enum Uncertainty:
    case ValueShape, RecordOverwrite
  
  /** Own members take precedence over inherited ones, including unknown spreads. */
  def inClass(defn: ClassLikeDef, ext: Opt[TermShape], name: Str): MemberLookup =
    defn.body.members.get(name) match
      case S(member) => Found(member, Nil)
      case N => ext.fold[MemberLookup](Missing)(_.getMember(name))

extension (member: BlockMemberSymbol | RecordMember)
  def memberSymbol: BlockMemberSymbol = member match
    case symbol: BlockMemberSymbol => symbol
    case member: RecordMember => member.field.sym

class ErrShape(val err: ErrorReport) extends NonAppTermShape:
  def describe: Str = s"error: ${err.mainMsg}"
  protected def getMemberImpl(name: Str): MemberLookup = MemberLookup.Missing
  def toLoc: Opt[Loc] = N

class AppShape(val receiver: TermShape, val args: Term, val src: Term.App)(using DebugPrinter) extends NonMarkedShape:
  protected def getMemberImpl(name: Str): MemberLookup =
    // An unsaturated term definition is just a concrete function shape
    if !isSaturated then MemberLookup.Missing
    else
      applicationHead match
      case (ds: DefnShape, mss) =>
        ds.getInstanceMember(name).withMarks(mss)
      case _ => MemberLookup.Missing
  override def isInstanceOfClass(cls: ClassLikeDef): Bool =
    isSaturated && (applicationHead._1 match
      case ds: DefnShape => ds.classExtends(cls)
      case _ => false)
  def describe: Str =
    // s"application of ${receiver.describe}"
    s"instance of ${applicationHead._1.describe}"
  def toLoc: Opt[Loc] = src.toLoc
  override def toString: String = s"AppShape($receiver, ${args.showDbg})"
  // def target: Opt[AppTarget]

class NewShape(val receiver: DefnShape, val cls: ClassLikeSymbol, val clsMarks: Ls[Marks], val argss: Ls[Term], val src: Term.New)(using DebugPrinter) extends NonMarkedShape:
  protected def getMemberImpl(name: Str): MemberLookup =
    if isSaturated then receiver.getInstanceMember(name).withMarks(clsMarks)
    else MemberLookup.Missing
  override def isInstanceOfClass(cls: ClassLikeDef): Bool =
    isSaturated && receiver.classExtends(cls)
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
  override def isInstanceOfClass(cls: ClassLikeDef): Bool =
    (defn is cls) || ext.exists(_.isInstanceOfClass(cls))
  def describe: Str = s"${defn.describe}"
  protected def getMemberImpl(name: Str): MemberLookup =
    MemberLookup.inClass(defn, ext, name)
  def toLoc: Opt[Loc] = defn.toLoc

class DefnShape(val defn: Definition, val ext: Opt[TermShape]) extends NonAppTermShape:
  /** Instance lookup is shared by constructor calls and explicit `new`.
    * Inherited members retain their marks before the caller adds its captures. */
  def getInstanceMember(name: Str): MemberLookup = defn match
    case cd: ClassDef => MemberLookup.inClass(cd, ext, name)
    case _: TermDefinition => ext.fold[MemberLookup](MemberLookup.Missing)(_.getMember(name))
    case _ => MemberLookup.Missing
  /** Nominal ancestry of this definition, independent of whether its value is an instance. */
  def classExtends(cls: ClassLikeDef): Bool =
    clsDef.contains(cls) || ext.exists(_.isInstanceOfClass(cls))
  override def isInstanceOfClass(cls: ClassLikeDef): Bool = defn match
    case _: ModuleOrObjectDef => classExtends(cls)
    case _ => false
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
  protected def getMemberImpl(name: Str): MemberLookup =
    defn match
    case defn: ModuleOrObjectDef =>
      MemberLookup.inClass(defn, ext, name)
    case defn: TermDefinition => ???
    case _ => MemberLookup.Missing
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
      case TupleShape.Unknown(source, inner, value) => TupleShape.Unknown(source, inner ::: marks :: Nil, value)
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
  protected def getMemberImpl(name: Str): MemberLookup = ??? // Structural tuple members are not implemented yet.

/** Values whose members and call results are deliberately checked only at runtime.
  * Unlike UnknownValueShape, this authorizes dynamic operations; it is introduced
  * by JavaScript interop and explicit `dyn` types, not by failed inference.
  */
final case class DynShape() extends NonAppTermShape:
  def describe: Str = "dynamic value"
  def toLoc: Opt[Loc] = N
  protected def getMemberImpl(name: Str): MemberLookup = MemberLookup.Dynamic(Nil)

/** The element of an opaque or widened spread can be any value. Keep this
  * alternative in the flow graph so other, known arguments cannot silently make
  * an unresolved member selection appear to have a unique static target.
  */
final case class UnknownValueShape(source: Term) extends NonAppTermShape:
  def describe: Str = "value of unknown shape"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: Str): MemberLookup =
    MemberLookup.Unknown(MemberLookup.Uncertainty.ValueShape, toLoc)

object TupleShape:
  sealed trait Element
  sealed trait Segment extends Element
  final case class Field(field: Fld, marks: Ls[Marks]) extends Segment
  /** An arbitrary number of arbitrary values. Use this for opaque layouts and
    * recursive widening, never for a spread whose shape has not arrived yet.
    * `value` distinguishes dynamically typed JS elements from values whose
    * shape was lost through widening; `source` supplies diagnostic locations. */
  final case class Unknown(source: Term, marks: Ls[Marks], value: NonMarkedShape) extends Segment
  final case class Spread(shape: TupleShape, marks: Marks) extends Element
  def unknown(source: Term): TupleShape = TupleShape(source, Unknown(source, Nil, UnknownValueShape(source)) :: Nil)
  /** Retain the original candidate as well as the selected residual segments:
    * flattening away the parent would hide recursive producer dependencies from
    * containsSpread, allowing recursion through rest slicing to evade widening. */
  final case class Rest(shape: TupleShape, segments: Ls[Segment]) extends Element


/** A field found by record member lookup. Spreading r into `mut {...r}` reuses
  * its field symbols, but writes can change the copied values even if r is immutable.
  * Store mutability on this lookup result: the mutable copy's initializer no longer
  * determines its value shape, while reads from an immutable r can still use it.
  */
final case class RecordMember(field: RcdField, mutable: Bool)

/** Keep spread candidates and their contexts rather than flattening away their
  * provenance. Lookup follows runtime's last-write-wins order. Unknown entries
  * are barriers: an opaque spread or computed key can overwrite earlier fields.
  */
final case class RecordShape(source: Term.Rcd, elements: Ls[RecordShape.Element]) extends NonAppTermShape:
  def describe: Str = "record literal"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: Str): MemberLookup =
    import MemberLookup.*
    def unknown = Unknown(Uncertainty.RecordOverwrite, toLoc)
    def loop(rest: Ls[RecordShape.Element]): MemberLookup = rest match
      case Nil => Missing
      case RecordShape.Field(field) :: rest => field.field match
        case Term.Lit(Tree.StrLit(key)) =>
          if key == name then Found(RecordMember(field, source.mut), Nil) else loop(rest)
        case _ => unknown
      case RecordShape.Unknown :: _ => unknown
      case RecordShape.Dynamic(marks) :: _ => Dynamic(marks)
      case RecordShape.Spread(shape, marks) :: rest => shape.getMember(name) match
        case Dynamic(inner) => Dynamic(inner ::: marks :: Nil)
        case Unknown(_, _) => unknown
        case Missing => loop(rest)
        case Found(member: RecordMember, inner) =>
          Found(member.copy(mutable = member.mutable || source.mut), inner ::: marks :: Nil)
        case Found(_: BlockMemberSymbol, _) =>
          // Record spreads recursively look up RecordShapes, which only create RecordMembers.
          lastWords("Record lookup returned a nominal member")
    loop(elements.reverse)
  def containsSpread(record: Term.Rcd, marks: Marks): Bool = elements.exists:
    case RecordShape.Spread(shape, inner) =>
      ((shape.source is record) && inner == marks) || shape.containsSpread(record, marks)
    case _ => false

object RecordShape:
  enum Element:
    case Field(field: RcdField)
    case Spread(shape: RecordShape, marks: Marks)
    case Unknown
    case Dynamic(marks: Ls[Marks])
  export Element.*


type IntroTerm = Term.Lit | Term.UnitVal | Term.Lam //| Term.New
class IntroShape(val trm: IntroTerm) extends NonAppTermShape:
  def describe: Str = trm.describe
  protected def getMemberImpl(name: Str): MemberLookup = trm match
    case _: Term.Lit | _: Term.UnitVal => MemberLookup.Missing // TODO: methods on literals
    case lam: Term.Lam => MemberLookup.Missing // TODO: methods on lambdas
    // case newTerm: Term.New =>
    //   Map.empty // TODO
  def toLoc: Opt[Loc] = trm.toLoc
  override def toString: Str = s"IntroShape(${trm})"

sealed trait LitShape extends NonAppTermShape:
  self: Term.Lit =>
  protected def getMemberImpl(name: Str): MemberLookup = MemberLookup.Missing // TODO: methods on literals, e.g. string methods


type ShapePublisher = Publisher[Shape]
type ShapeHost = Host[Shape]


