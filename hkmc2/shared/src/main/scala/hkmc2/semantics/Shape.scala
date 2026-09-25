package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.Message.MessageContext
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
    case rs: RecordTypeShape => s"RecordTypeShape(${rs.source.showDbg})"
    case ts: InstanceShape => s"InstanceShape(${ts.tpe.resolution.source.showDbg})"
    case ts: NominalInstanceView => s"NominalInstanceView(${ts.defn.sym.showDbg})"
    case ts: OpaqueTypeShape => s"OpaqueTypeShape(${ts.source.showDbg})"
    case ts: CallableTypeShape => s"CallableTypeShape(${ts.source.showDbg})"
    case view: ContextualShape => s"ContextualShape(${view.source.shwDbg})"
    case specialized: SpecializedShape => s"SpecializedShape(${specialized.declaration.shwDbg})"
    case rigid: RigidTypeShape => s"RigidTypeShape(${rigid.parameter.showDbg})"
    case flow: ActivatedShape => s"ActivatedShape(${flow.value.shwDbg})"
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

// Scanning each new tail makes chain construction quadratic in its depth.
// Keep the checks enabled so missing scope transfers fail at their source instead
// of allowing repeated boundaries to accumulate in contextual reference keys.
private val checkMarkPaths = true

/** A reduced lexical path: entries followed by exits, most recent crossing first.
  * Exiting cancels the leading entry when their sites agree (an absent site is
  * a capture, compatible with any activation). Entering never cancels an exit:
  * that pair records an inner value's provenance until a consumer accesses it.
  * Each direction traverses distinct lexical scopes, so recursive calls cannot
  * lengthen a normalized path indefinitely. Debug assertions check this invariant
  * without widening paths.
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
  if checkMarkPaths then
    assert(!rest.hasEntry(boundary), "Repeated entry into the same lexical resolution scope")
sealed abstract class ExitMarks extends Marks:
  @scala.annotation.tailrec
  final def hasExit(boundary: ResolutionBoundary): Bool = this match
    case ExitMark(b, _, rest) => b == boundary || rest.hasExit(boundary)
    case NoMarks => false
case class ExitMark(boundary: ResolutionBoundary, id: Opt[FlowSymbol], rest: ExitMarks) extends ExitMarks:
  if checkMarkPaths then
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
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    sh.getMemberThrough(name, mark)
  override def isInstanceOfClass(cls: ClassLikeDef)(using NewResolverState): Bool = sh.isInstanceOfClass(cls)
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
        assert(entered == boundary, s"Entry and exit cross different lexical resolution scopes: ${entered.showDbg} vs ${boundary.showDbg} for ${sh.shwDbg}")
        if id.forall(i1 => id2.forall(i2 => i1 is i2)) then
          rest match
          case NoMarks => sh
          case rest: SomeMarks => MarkedShape(sh, rest)
        else NoShape
end MarkedShape

sealed trait TermShape extends Shape:
  // Cache all lookup outcomes per shape, without materializing all inherited members.
  final def getMember(name: Str)(using state: NewResolverState): MemberLookup =
    state.membersCache.getOrElseUpdate((new Identity[TermShape](this), name), getMemberImpl(name))
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup
  /** Lookup on this shape as reached through the receiver path `receiver`.
    * Shapes whose members are declared by a nominal class override this to
    * locate the member at the class's definition (see NewResolver.nominalMember);
    * other members are transported through the whole path.
    */
  def getMemberThrough(name: Str, receiver: Marks)(using NewResolverState): MemberLookup = receiver match
    case NoMarks => getMember(name)
    case receiver: SomeMarks => getMember(name).withMarks(receiver :: Nil)
  
  /** Whether this value is an instance of the nominal class. A saturated class
    * value (e.g. a class without parameters) is still not an instance. */
  def isInstanceOfClass(cls: ClassLikeDef)(using NewResolverState): Bool = false
  
  // Cache the head independently: following receivers does not need to construct
  // or unpack a (head, marks) pair at every intermediate shape.
  private lazy val applicationHeadShape: NonAppTermShape = this match
    case as: AppShape => as.receiver.applicationHeadShape
    case ns: NewShape => ns.receiver
    case na: NonAppTermShape => na
    case MarkedShape(sh, _) => (sh: TermShape).applicationHeadShape
  // Public contexts run from the callable definition to its consumer, as in
  // MemberLookup.withMarks. Build the reverse privately so each wrapper prepends
  // in constant time; materialize the forward view only when a consumer needs it.
  private lazy val reversedApplicationMarks: Ls[Marks] = this match
    case as: AppShape => as.receiver.reversedApplicationMarks
    case ns: NewShape => ns.clsMarks.reverse
    case _: NonAppTermShape => Nil
    case MarkedShape(sh, mark) => mark :: (sh: TermShape).reversedApplicationMarks
  private lazy val applicationMarks: Ls[Marks] = this match
    case as: AppShape => as.receiver.applicationMarks
    case ns: NewShape => ns.clsMarks
    case _ => reversedApplicationMarks.reverse
  lazy val applicationHead: (NonAppTermShape, Ls[Marks]) = this match
    case as: AppShape => as.receiver.applicationHead
    case _ => (applicationHeadShape, applicationMarks)
  // All remaining parameter lists belong to the same callable and carry its
  // context. Keep the lists separate until the public view needs their pairs.
  private lazy val unappliedParamLists: Ls[ParamList] = this match
    case specialized: SpecializedShape => (specialized.declaration: TermShape).unappliedParamLists
    case ds: DefnShape => ds.defn match
      case defn: TermDefinition => defn.params
      case defn: ClassDef =>
        if defn.paramsOpt.isDefined then // whether the class can receive direct applications
          defn.paramsOpt.toList ::: defn.auxParams
        else Nil
      case _ => Nil
    case as: AppShape => as.receiver.unappliedParamLists.drop(1)
    case ns: NewShape => (ns.receiver: TermShape).unappliedParamLists.drop(ns.argss.length)
    case MarkedShape(sh, _) => (sh: TermShape).unappliedParamLists
    case is: IntroShape =>
      is.trm match
      case Term.Lam(params, _) => params :: Nil
      case _ => Nil
    case _ => Nil
  lazy val unappliedParams: Ls[(ParamList, Ls[Marks])] = this match
    // Applying arguments removes a list without changing the context; retain
    // sharing of the already paired tail when this public view is requested.
    case as: AppShape => as.receiver.unappliedParams.drop(1)
    case _ => unappliedParamLists.map(_ -> applicationMarks)
  
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
  
  def isSaturated: Bool = unappliedParamLists.isEmpty
  
end TermShape

// sealed trait TermShape:
//   def describe: Str = this match
//     case app: AppShape => s"application of ${app.lhs.describe} to ${app.args.describe}"
//     case sel: SelShape => s"selection of ${sel.nme.name} from ${sel.receiver.describe}"
//     case sym: SymShape => s"symbol ${sym.sym.describe}"

/** Missing means definitely absent; Unknown must not be treated as a miss when
  * searching wildcard opens, since it can introduce an additional candidate. */
enum MemberLookup:
  case Contextual(source: MemberLookup, instances: Map[VarSymbol, TypeParameterInstance])
  case Found(member: BlockMemberSymbol | RecordMember, marks: Ls[Marks])
  // Declared members expose signatures only. Their marks transport dependent
  // type arguments; they never authorize reading an implementation's value flow.
  case Declared(member: BlockMemberSymbol, bindings: Map[VarSymbol, DeclaredType], marks: Ls[Marks], annotation: Opt[Term], positive: Bool)
  case Indexed(field: TupleShape.Fixed, marks: Ls[Marks])
  case Dynamic(marks: Ls[Marks])
  case Missing
  case Unknown(reason: MemberLookup.Uncertainty, provenance: ShapeProvenance)
  
  def withMarks(marks: Ls[Marks]): MemberLookup = this match
    case Contextual(source, instances) => Contextual(source.withMarks(marks), instances)
    case Found(member, inner) => Found(member, inner ::: marks)
    case Declared(member, bindings, inner, annotation, positive) => Declared(member, bindings, inner ::: marks, annotation, positive)
    case Indexed(field, inner) => Indexed(field, inner ::: marks)
    case Dynamic(inner) => Dynamic(inner ::: marks)
    case _ => this

  /** The receiver's annotation remains the diagnostic origin when lookup visits a parent. */
  def withAnnotation(annotation: Opt[Term]): MemberLookup = this match
    case Contextual(source, instances) => Contextual(source.withAnnotation(annotation), instances)
    case Declared(member, bindings, marks, _, positive) => Declared(member, bindings, marks, annotation, positive)
    case _ => this

  def instantiate(instances: Map[VarSymbol, TypeParameterInstance]): MemberLookup =
    if instances.isEmpty then this else this match
      case Contextual(source, previous) => Contextual(source, instances ++ previous)
      case Missing | Unknown(_, _) | Dynamic(_) => this
      case _ => Contextual(this, instances)

object MemberLookup:
  enum Uncertainty:
    case ValueShape, RecordOverwrite
  
  /** Own members take precedence over inherited ones, including unknown spreads. */
  def inClass(defn: ClassLikeDef, ext: Opt[TermShape], name: Str)(using NewResolverState): MemberLookup =
    defn.body.members.get(name) match
      case S(member) => Found(member, Nil)
      case N => ext.fold[MemberLookup](Missing)(_.getMember(name))

extension (member: BlockMemberSymbol | RecordMember)
  def memberSymbol: BlockMemberSymbol = member match
    case symbol: BlockMemberSymbol => symbol
    case member: RecordMember => member.field.sym

class ErrShape(val err: ErrorReport) extends NonAppTermShape:
  def describe: Str = s"error: ${err.mainMsg}"
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup = MemberLookup.Missing
  def toLoc: Opt[Loc] = N

class AppShape(val receiver: TermShape, val args: Term, val src: Term.App)(using DebugPrinter) extends NonMarkedShape:
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    // An unsaturated term definition is just a concrete function shape
    if !isSaturated then MemberLookup.Missing
    else
      applicationHead match
      case (ds: DefnShape, mss) =>
        ds.getInstanceMember(name).withMarks(mss)
      case _ => MemberLookup.Missing
  override def isInstanceOfClass(cls: ClassLikeDef)(using NewResolverState): Bool =
    isSaturated && (applicationHead._1 match
      case ds: DefnShape => ds.classExtends(cls)
      case _ => false)
  def describe: Str =
    // s"application of ${receiver.describe}"
    s"instance of ${applicationHead._1.describe}"
  def toLoc: Opt[Loc] = src.toLoc
  override def toString: String = s"AppShape($receiver, ${args.showDbg})"
  // def target: Opt[AppTarget]

class NewShape(val receiver: DefnShape, val cls: ClassLikeSymbol, val clsMarks: Ls[Marks], val argss: Ls[Term], val src: Term.New,
    val supplied: Opt[Ls[DeclaredType]])(using DebugPrinter) extends NonMarkedShape:
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    if isSaturated then receiver.getInstanceMember(name).withMarks(clsMarks)
    else MemberLookup.Missing
  override def isInstanceOfClass(cls: ClassLikeDef)(using NewResolverState): Bool =
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

/** The symbolic counterpart of ContextualShape: retain the value's substitution
  * until overload selection produces a term shape. This does not consume a scheme.
  */
final class ContextualSymShape(val source: SymShape, val instances: Map[VarSymbol, TypeParameterInstance])
extends SymShape(source.sym, source.resSym, source.markss)

/** The symbolic counterpart of ActivatedShape. `listen` unwraps this event and
  * invokes the receiver in `instances`; `source` can independently retain the
  * value's substitution in a ContextualSymShape.
  */
final class ActivatedSymShape(val source: SymShape, val instances: Map[VarSymbol, TypeParameterInstance])
extends SymShape(source.sym, source.resSym, source.markss)

/** Keep a declared receiver's boundary while consumers choose between the term,
  * type, and constructor interpretations of the same overload set.
  */
final class DeclaredSymShape(symbol: BlockMemberSymbol, site: FlowSymbol, marks: Ls[Marks],
    val bindings: Map[VarSymbol, DeclaredType], val annotation: Opt[Term], val positive: Bool) extends SymShape(symbol, site, marks)

/* 
class ThisShape(val defn: Definition) extends NonAppTermShape:
  def describe: Str = s"Self-reference to ${defn.bsym.describe} '${defn.bsym.nme}'"
  override def toString: String = s"ThisShape(${defn.describe})"
  def members: Map[Str, MemberInfo] = ???
*/

// TODO: make it not a TermShape?
class BaseShape(val defn: ClassLikeDef, val ext: Opt[TermShape]) extends NonAppTermShape:
  override def isInstanceOfClass(cls: ClassLikeDef)(using NewResolverState): Bool =
    (defn is cls) || ext.exists(_.isInstanceOfClass(cls))
  def describe: Str = s"${defn.describe}"
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    MemberLookup.inClass(defn, ext, name)
  def toLoc: Opt[Loc] = defn.toLoc

/** A structural annotation exposes only its declared fields. Their symbols belong
  * to the annotation, not to whichever record happens to be passed by a caller.
  */
final case class RecordTypeShape(source: Term.Rcd, fields: Ls[(RcdField, TypeResolution)],
    bindings: Map[VarSymbol, DeclaredType], positive: Bool) extends NonAppTermShape:
  def describe: Str = "record type"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    fields.reverseIterator.collectFirst {
      case (field, _) if field.sym.nme == name => MemberLookup.Declared(field.sym, bindings, Nil, S(source), positive)
    }.getOrElse(MemberLookup.Missing)

/** An instance described by a type, in either position of a constraint. Keep the
  * type reference intact during transport: expanding it to its current positive
  * candidates would lose negative uses of generic arguments and compound types.
  * Operations obtain concrete member/call views through listenInstanceViews.
  */
final case class InstanceShape(tpe: DeclaredType) extends NonAppTermShape:
  def describe: Str = "value with a declared type"
  def toLoc: Opt[Loc] = tpe.resolution.source.toLoc
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    lastWords("Instance member lookup requires interpreting its type first")

/** A deferred value view: interpret references in the shared `source` using
  * `instances`, a flat map from original binders to canonical parameter instances.
  * This does not consume the source's own generic scheme. For example, a returned
  * inner[B] can capture outer's A while leaving B available for a later call.
  * `instantiateShape` composes views instead of nesting them; already captured
  * entries take precedence. Aggregates and declared types can store this view
  * directly rather than using a ContextualShape wrapper.
  * Unlike ActivatedShape.instances, this map belongs to the value, not its receiver.
  * See doc/new-resolution-type-value-flow.md, "Value views, consumed schemes, and activation events".
  */
final case class ContextualShape(source: NonMarkedShape, instances: Map[VarSymbol, TypeParameterInstance]) extends NonAppTermShape:
  require(!source.isInstanceOf[ContextualShape], "Compose shape views rather than nesting them")
  def describe: Str = source.describe
  def toLoc: Opt[Loc] = source.toLoc
  override def isInstanceOfClass(cls: ClassLikeDef)(using NewResolverState): Bool = source.isInstanceOfClass(cls)
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup = source.getMember(name).instantiate(instances)
  override def getMemberThrough(name: Str, receiver: Marks)(using NewResolverState): MemberLookup =
    source.getMemberThrough(name, receiver).instantiate(instances)

/** Explicit type application, such as f[Int], has consumed this declaration's
  * scheme before any term argument list need be applied. `arguments` retains the
  * supplied caller type references; `instances` retains the chosen binder group
  * and lexical captures. `callableParts` tells `appShape` to reuse that group even
  * through stored aliases, rather than instantiate the declaration again.
  * A ContextualShape alone does not record scheme consumption. Complete annotated
  * CallableTypeShape views record consumption by substituting and clearing `scheme`.
  */
final case class SpecializedShape(declaration: DefnShape, arguments: Ls[DeclaredType],
    instances: Map[VarSymbol, TypeParameterInstance]) extends NonAppTermShape:
  def describe: Str = declaration.describe
  def toLoc: Opt[Loc] = declaration.toLoc
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup = declaration.getMember(name).instantiate(instances)

/** An inference-event envelope, not a value interface. `publishActivated` saves
  * the current body's original-binder-to-instance map; `listen` checks agreement
  * with the requested activation on shared keys, unwraps `value`, and invokes the
  * receiver in the combined compatible activation. An empty request accepts all.
  * The enclosed value separately retains its own substitution: in recursive f[A],
  * it can refer to the caller's A@p while the receiving body uses A@q. Merging those
  * maps would rebind the value or execute the operation in the wrong activation.
  * Despite extending TermShape, this envelope must be unwrapped before lookup.
  * Neither map changes the ordinary mark algebra used for lexical scope crossings.
  */
final case class ActivatedShape(value: TermShape, instances: Map[VarSymbol, TypeParameterInstance]) extends NonAppTermShape:
  def describe: Str = value.describe
  def toLoc: Opt[Loc] = value.toLoc
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    lastWords("Activation events must be unpacked before observing their values")

/** A nominal annotation exposes only declarations, including inherited declarations.
  * In particular, selecting an unannotated field does not inspect its initializer.
  * The annotation is a diagnostic witness, excluded from shape equality; synthesized
  * interfaces such as a tuple's Array parent have no written annotation.
  */
final case class NominalInstanceView(defn: ClassLikeDef, bindings: Map[VarSymbol, DeclaredType],
    parent: Opt[TermShape])(val annotation: Opt[Term])(resolver: NewResolver) extends NonAppTermShape:
  def describe: Str = s"value of type '${defn.sym.nme}'"
  def toLoc: Opt[Loc] = defn.toLoc
  override def isInstanceOfClass(cls: ClassLikeDef)(using NewResolverState): Bool =
    (defn is cls) || parent.exists(_.isInstanceOfClass(cls))
  def ancestor(cls: ClassLikeDef): Opt[NominalInstanceView] =
    if defn is cls then S(this)
    else parent.flatMap:
      case Marked(parent: NominalInstanceView, _) => parent.ancestor(cls)
      case _ => N
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    resolver.nominalMember(this, name, NoMarks)
  override def getMemberThrough(name: Str, receiver: Marks)(using NewResolverState): MemberLookup =
    resolver.nominalMember(this, name, receiver)

/** Parameter types and arity exposed by one list in a declared calling interface.
  * A rest annotation describes the whole trailing array; hasRest also distinguishes
  * an unannotated rest parameter from a fixed-arity list.
  */
final case class DeclaredParams(params: Ls[Opt[DeclaredType]], hasRest: Bool, rest: Opt[DeclaredType])

/** Calls through annotations expose only the declared result. Argument shapes
  * constrain type parameters in the interface; they do not recover its implementation.
  * `scheme` retains binders that are still available for instantiation; capture
  * substitution leaves those binders alone. `instantiateCallable` consumes the
  * scheme by substituting its references and clearing it, so stored values and
  * remaining curried lists reuse the chosen instances. This is the annotated
  * counterpart of SpecializedShape, not an inference-event activation.
  */
final case class CallableTypeShape(source: Term, paramLists: Ls[DeclaredParams],
    result: Opt[DeclaredType], scheme: Opt[TypeScheme], supplied: Opt[Ls[DeclaredType]],
    declaration: Opt[TermDefinition]) extends NonAppTermShape:
  require(paramLists.nonEmpty)
  def tparams: Ls[DeclaredTypeParameter] = scheme.toList.flatMap(_.parameters)
  def describe: Str = declaration.fold("function with a declared signature")(d => s"function '${d.bsym.nme}'")
  def toLoc: Opt[Loc] = declaration.fold(source.toLoc)(_.toLoc)
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup = MemberLookup.Missing

/** An abstract annotation authorizes no operations based on the implementation. */
final case class OpaqueTypeShape(source: Term) extends NonAppTermShape:
  def describe: Str = "value of abstract type"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    MemberLookup.Unknown(MemberLookup.Uncertainty.ValueShape,
      ShapeProvenance(msg"This abstract type does not specify a member interface." -> toLoc :: Nil))

class DefnShape(val defn: Definition, val ext: Opt[TermShape]) extends NonAppTermShape:
  /** Instance lookup is shared by constructor calls and explicit `new`.
    * Inherited members retain their marks before the caller adds its captures. */
  def getInstanceMember(name: Str)(using NewResolverState): MemberLookup = defn match
    case cd: ClassDef => MemberLookup.inClass(cd, ext, name)
    case _: TermDefinition => ext.fold[MemberLookup](MemberLookup.Missing)(_.getMember(name))
    case _ => MemberLookup.Missing
  /** Nominal ancestry of this definition, independent of whether its value is an instance. */
  def classExtends(cls: ClassLikeDef)(using NewResolverState): Bool =
    clsDef.contains(cls) || ext.exists(_.isInstanceOfClass(cls))
  override def isInstanceOfClass(cls: ClassLikeDef)(using NewResolverState): Bool = defn match
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
        case _: ClassCtorSymbol => "class "
        case s => s.k.desc + " "
    }'${defn.bsym.nme}'"
  // override def toString: String = s"DefnShape(${defn.describe} ${defn.bsym.nme})"
  override def toString: String = s"DefnShape(${defn.describe})"
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    defn match
    case defn: ModuleOrObjectDef =>
      MemberLookup.inClass(defn, ext, name)
    case _: TermDefinition => MemberLookup.Missing
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
final case class TupleShape(source: Term, elements: Ls[TupleShape.Element],
    instances: Map[VarSymbol, TypeParameterInstance])(resolver: NewResolver) extends NonAppTermShape:
  def arrayParent(using NewResolverState): NominalInstanceView = resolver.tupleArrayParent(this)
  override def isInstanceOfClass(cls: ClassLikeDef)(using NewResolverState): Bool = arrayParent.isInstanceOfClass(cls)
  private lazy val sourceSegments: Ls[TupleShape.Segment] = elements.flatMap:
    case segment: TupleShape.Segment => segment :: Nil
    case TupleShape.Rest(_, segments) => segments
    case TupleShape.Spread(shape, marks) => shape.segments.map:
      case field: TupleShape.Fixed => field.withMarks(marks :: Nil)
      case TupleShape.Unknown(source, inner, value) => TupleShape.Unknown(source, inner ::: marks :: Nil, value)
  lazy val segments: Ls[TupleShape.Segment] = sourceSegments.map:
    case field: TupleShape.Fixed => field.instantiate(instances)
    case other => other
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
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup = name.toIntOption match
    case S(index) if index >= 0 =>
      def loop(rest: Ls[TupleShape.Segment], index: Int): MemberLookup = rest match
        case (field: TupleShape.Fixed) :: tail =>
          if index == 0 then MemberLookup.Indexed(field, Nil) else loop(tail, index - 1)
        case (segment: TupleShape.Unknown) :: _ =>
          // The position is a valid array operation even when a spread or
          // mutation has erased the element layout. Its value remains unknown.
          MemberLookup.Indexed(TupleShape.ValueField(segment.value, segment.marks), Nil)
        case Nil => MemberLookup.Missing
      loop(segments, index)
    case _ => arrayParent.getMember(name)
  override def getMemberThrough(name: Str, receiver: Marks)(using NewResolverState): MemberLookup = name.toIntOption match
    case S(index) if index >= 0 => super.getMemberThrough(name, receiver)
    case _ => arrayParent.getMemberThrough(name, receiver)

/** Values whose members and call results are deliberately checked only at runtime.
  * Unlike UnknownValueShape, this authorizes dynamic operations; it is introduced
  * by JavaScript interop and explicit `dyn` types, not by failed inference.
  */
final case class DynShape() extends NonAppTermShape:
  def describe: Str = "dynamic value"
  def toLoc: Opt[Loc] = N
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup = MemberLookup.Dynamic(Nil)

/** A shared diagnostic witness, independent of resolution marks. Messages,
  * locations, and the flattened chain are evaluated only when reporting an error.
  * Discovery retains one witness per reached shape to bound recursive paths.
  */
final class ShapeProvenance(notes: => Ls[(Message, Opt[Loc])]):
  lazy val diagnosticNotes: Ls[(Message, Opt[Loc])] = notes
  def via(note: => (Message, Opt[Loc])): ShapeProvenance =
    ShapeProvenance(note :: diagnosticNotes)

object ShapeProvenance:
  val empty = ShapeProvenance(Nil)

/** An unknown input or the element of an opaque or widened spread can be any
  * value. Keep this alternative in the flow graph so known candidates cannot
  * silently make an unresolved operation appear to have a static target.
  * Provenance is outside case-class equality: another diagnostic witness must
  * not turn the same unknown into a new inference candidate.
  */
final case class UnknownValueShape(source: Term)(val provenance: ShapeProvenance) extends NonAppTermShape:
  def describe: Str = "value of unknown shape"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    MemberLookup.Unknown(MemberLookup.Uncertainty.ValueShape, provenance)

/** A generic definition must be valid without choosing a caller's type. This
  * checking witness is not an inferred bound on any call-site parameter.
  */
final case class RigidTypeShape(parameter: VarSymbol, source: Term) extends NonAppTermShape:
  def describe: Str = "value of a type parameter"
  def toLoc: Opt[Loc] = source.toLoc
  def provenance: ShapeProvenance = ShapeProvenance(
    msg"Type parameter '${parameter.nme}' does not specify a member interface." -> parameter.toLoc :: Nil)
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    MemberLookup.Unknown(MemberLookup.Uncertainty.ValueShape, provenance)

object UnknownValueShape:
  def at(source: Term): UnknownValueShape =
    UnknownValueShape(source)(ShapeProvenance(msg"The shape of this value is unknown." -> source.toLoc :: Nil))
  def spread(source: Term, value: TermShape): UnknownValueShape =
    UnknownValueShape(source)(ShapeProvenance {
      val notes = value.applicationHead._1 match
        case unknown: UnknownValueShape => unknown.provenance.diagnosticNotes
        case _ => Nil
      (msg"This spread has no known element shape." -> source.toLoc) :: notes
    })

object TupleShape:
  def apply(source: Term, elements: Ls[Element])(resolver: NewResolver): TupleShape =
    new TupleShape(source, elements, Map.empty)(resolver)
  sealed trait Element
  sealed trait Segment extends Element
  sealed trait Fixed extends Segment:
    def marks: Ls[Marks]
    def withMarks(outer: Ls[Marks]): Fixed = this match
      case Field(field, inner) => Field(field, inner ::: outer)
      case TypedField(tpe, inner) => TypedField(tpe, inner ::: outer)
      case UnknownField(source, inner) => UnknownField(source, inner ::: outer)
      case ValueField(value, inner) => ValueField(value, inner ::: outer)
      case ViewedField(source, instances, inner) => ViewedField(source, instances, inner ::: outer)
    def instantiate(instances: Map[VarSymbol, TypeParameterInstance]): Fixed =
      if instances.isEmpty then this else this match
        case ViewedField(source, previous, marks) => ViewedField(source, instances ++ previous, marks)
        case _ => ViewedField(this, instances, Nil)
  final case class ViewedField(source: Fixed, instances: Map[VarSymbol, TypeParameterInstance], marks: Ls[Marks]) extends Fixed
  final case class Field(field: Fld, marks: Ls[Marks]) extends Fixed
  final case class ValueField(value: TermShape, marks: Ls[Marks]) extends Fixed
  final case class TypedField(tpe: DeclaredType, marks: Ls[Marks]) extends Fixed
  // Mutable tuple slots retain their positions, but their initializer cannot
  // supply the shape of later reads (including reads through a spread copy).
  final case class UnknownField(source: Term, marks: Ls[Marks]) extends Fixed
  /** An arbitrary number of arbitrary values. Use this for opaque layouts and
    * recursive widening, never for a spread whose shape has not arrived yet.
    * `value` distinguishes dynamically typed JS elements from values whose
    * shape was lost through widening; `source` supplies diagnostic locations. */
  final case class Unknown(source: Term, marks: Ls[Marks], value: NonMarkedShape) extends Segment
  final case class Spread(shape: TupleShape, marks: Marks) extends Element
  def unknown(source: Term)(resolver: NewResolver): TupleShape =
    TupleShape(source, Unknown(source, Nil, UnknownValueShape.at(source)) :: Nil)(resolver)
  /** Retain the original candidate as well as the selected residual segments:
    * flattening away the parent would hide recursive producer dependencies from
    * containsSpread, allowing recursion through rest slicing to evade widening. */
  final case class Rest(shape: TupleShape, segments: Ls[Segment]) extends Element
  /** A view of `tuple` retaining only `segments`, which must be taken from
    * `tuple.segments`. A view of another view refers to that view's parent:
    * a view contributes no spreads of its own, so containsSpread gives the same
    * answer for the parent as for the intermediate view. Nesting views instead
    * would make the candidate's identity record the order in which fields were
    * removed. For `if xs is [x, ...rest] then f(rest); [...rest, x] then f(rest)`
    * on an n-tuple, that yields 2^n candidates for only O(n^2) distinct layouts. */
  def restView(tuple: TupleShape, segments: Ls[Segment])(resolver: NewResolver): TupleShape =
    val parent = tuple.elements match
      case Rest(parent, _) :: Nil => parent
      case _ => tuple
    TupleShape(tuple.source, Rest(parent, segments) :: Nil)(resolver)


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
final case class RecordShape(source: Term.Rcd, elements: Ls[RecordShape.Element],
    instances: Map[VarSymbol, TypeParameterInstance]) extends NonAppTermShape:
  def describe: Str = "record literal"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup =
    import MemberLookup.*
    def unknown(source: Located) = Unknown(Uncertainty.RecordOverwrite,
      ShapeProvenance(msg"This computed key can overwrite the selected member." -> source.toLoc :: Nil))
    def loop(rest: Ls[RecordShape.Element]): MemberLookup = rest match
      case Nil => Missing
      case RecordShape.Field(field) :: rest => field.field match
        case Term.Lit(Tree.StrLit(key)) =>
          if key == name then Found(RecordMember(field, source.mut), Nil) else loop(rest)
        case _ => unknown(field.field)
      case (unknown: RecordShape.Unknown) :: _ => Unknown(Uncertainty.RecordOverwrite, unknown.provenance)
      case RecordShape.Dynamic(marks) :: _ => Dynamic(marks)
      case RecordShape.Spread(shape, marks) :: rest =>
        def spread(info: MemberLookup): Opt[MemberLookup] = info match
          case Contextual(source, instances) => spread(source).map(_.instantiate(instances))
          case Dynamic(inner) => S(Dynamic(inner ::: marks :: Nil))
          case Unknown(_, provenance) => S(Unknown(Uncertainty.RecordOverwrite, provenance))
          case Missing => N
          case Found(member: RecordMember, inner) =>
            S(Found(member.copy(mutable = member.mutable || source.mut), inner ::: marks :: Nil))
          case Found(_: BlockMemberSymbol, _) | Declared(_, _, _, _, _) | Indexed(_, _) =>
            // Record spreads recursively look up RecordShapes, which only create RecordMembers.
            lastWords("Record lookup returned a nominal member")
        spread(shape.getMember(name)).getOrElse(loop(rest))
    loop(elements.reverse).instantiate(instances)
  def containsSpread(record: Term.Rcd, marks: Marks): Bool = elements.exists:
    case RecordShape.Spread(shape, inner) =>
      ((shape.source is record) && inner == marks) || shape.containsSpread(record, marks)
    case _ => false

object RecordShape:
  def apply(source: Term.Rcd, elements: Ls[Element]): RecordShape = new RecordShape(source, elements, Map.empty)
  enum Element:
    case Field(field: RcdField)
    case Spread(shape: RecordShape, marks: Marks)
    case Unknown(source: Term)(val provenance: ShapeProvenance)
    case Dynamic(marks: Ls[Marks])
  export Element.*


type IntroTerm = Term.Lit | Term.UnitVal | Term.Lam //| Term.New
class IntroShape(val trm: IntroTerm, val primitive: Opt[NominalInstanceView]) extends NonAppTermShape:
  def describe: Str = trm.describe
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup = trm match
    case _: Term.Lit | _: Term.UnitVal => primitive.fold[MemberLookup](MemberLookup.Missing)(_.getMember(name))
    case lam: Term.Lam => MemberLookup.Missing // TODO: methods on lambdas
    // case newTerm: Term.New =>
    //   Map.empty // TODO
  override def getMemberThrough(name: Str, receiver: Marks)(using NewResolverState): MemberLookup = trm match
    case _: Term.Lit | _: Term.UnitVal => primitive.fold[MemberLookup](MemberLookup.Missing)(_.getMemberThrough(name, receiver))
    case _: Term.Lam => super.getMemberThrough(name, receiver)
  override def isInstanceOfClass(cls: ClassLikeDef)(using NewResolverState): Bool =
    primitive.exists(_.isInstanceOfClass(cls))
  def toLoc: Opt[Loc] = trm.toLoc
  override def toString: Str = s"IntroShape(${trm})"

sealed trait LitShape extends NonAppTermShape:
  self: Term.Lit =>
  protected def getMemberImpl(name: Str)(using NewResolverState): MemberLookup = MemberLookup.Missing // TODO: methods on literals, e.g. string methods


type ShapePublisher = Publisher[Shape]
type ShapeHost = Host[Shape]

