package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.Message.MessageContext


type ShapePublisher = Publisher[ShapeEvent]
type ShapeHost = Host[ShapeEvent]

/** Publisher payloads distinguish ordinary shapes from activation-tagged events.
  * Only Shape supports value operations; an event must be dispatched first.
  * Plain shapes need no allocation to participate in activation-independent flow.
  */
sealed trait ShapeEvent extends IdentityEquality:
  private[semantics] lazy val comparison: ShapeIdentity.Key = ShapeIdentity.comparison(this)

object ShapeEvent:
  given [A <: ShapeEvent]: CandidateKey[A] with
    def apply(value: A)(using ResolutionContext): Any = ShapeIdentity.key(value)


sealed trait Shape extends ShapeEvent:
  def describe: Str
  /** Origin of the value or symbol described by this shape, independently of its use site. */
  def toLoc: Opt[Loc]
  /** Keep the operation's explanation at its interface witness, after any path
    * from the observed value to that witness. Wrappers preserve this ordering.
    * An annotation restricting a value and its class declaration are different
    * witnesses: interface errors use the annotation, while toLoc identifies the
    * declaration. Unknown values cite their provenance; the enclosing resolution
    * error already locates the operation, so repeating its operand adds no evidence.
    * Diagnostic witnesses do not change semantic keys.
    */
  final def diagnostic(message: Message): Ls[(Message, Opt[Loc])] = this match
    case value: TermShape => value.applicationHead._1 match
      case view: NominalInstanceView => view.provenance.diagnostic(message, view.annotation.flatMap(_.toLoc).orElse(toLoc))
      case view: ContextualShape => view.source.diagnostic(message)
      case view: SpecializedShape => view.declaration.diagnostic(message)
      case unknown: UnknownValueShape => unknown.provenance.diagnostic(message, N)
      case opaque: OpaqueTypeShape => opaque.provenance.diagnostic(message, toLoc)
      case rigid: RigidTypeShape => rigid.provenance.diagnostic(message, N)
      case _ => (message -> toLoc) :: Nil
    case _: SymShape => (message -> toLoc) :: Nil
  /** Arity errors also cite where the expected parameter lists are declared, when the
    * witness of `diagnostic` does not show them: a class constructor can take the
    * parameter lists of `constructor(...)` declarations written in the class body. */
  final def arityDiagnostic(message: Message): Ls[(Message, Opt[Loc])] =
    def constructorDeclarations(shape: Shape): Ls[(Message, Opt[Loc])] = shape match
      case value: TermShape => value.applicationHead._1 match
        case view: ContextualShape => constructorDeclarations(view.source)
        case view: SpecializedShape => constructorDeclarations(view.declaration)
        case defn: DefnShape => defn.ctorLoc.map(loc => msg"The constructor is declared here." -> S(loc)).toList
        case _ => Nil
      case _: SymShape => Nil
    diagnostic(message) ::: constructorDeclarations(this)
  def shwDbg(using DebugPrinter): Str = this match
    case ds: DefnShape => ds.defn.sym.showDbg
    case as: AppShape => s"AppShape(${as.receiver.shwDbg}, ${as.args.showDbg})"
    case ms: MarkedShape[?] => s"MarkedShape(${ms.sh.shwDbg}, ${ms.mark.showDbg})"
    case ns: SymShape => s"SymShape(${ns.sym.showDbg})"
    case ns: NewShape => s"NewShape(${ns.cls.showDbg}, ${ns.argss.map(_.showDbg).mkString(", ")})"
    case is: IntroShape => s"IntroShape(${is.trm.showDbg})"
    case _: DynShape => "DynShape"
    case us: UnknownValueShape => s"UnknownValueShape(${us.source.showDbg})"
    case ts: TupleShape => s"TupleShape(${ts.source.showDbg})"
    case rs: RecordShape => s"RecordShape(${rs.source.showDbg})"
    case rs: RecordTypeShape => s"RecordTypeShape(${rs.source.showDbg})"
    case view: IntersectionView => s"IntersectionView(${view.values.map(_.shwDbg).mkString(", ")})"
    case ts: InstanceShape => s"InstanceShape(${ts.tpe.resolution.source.showDbg})"
    case ts: NominalInstanceView => s"NominalInstanceView(${ts.defn.sym.showDbg})"
    case ts: OpaqueTypeShape => s"OpaqueTypeShape(${ts.source.showDbg})"
    case ts: CallableTypeShape => s"CallableTypeShape(${ts.source.showDbg})"
    case view: ContextualShape => s"ContextualShape(${view.source.shwDbg})"
    case specialized: SpecializedShape => s"SpecializedShape(${specialized.declaration.shwDbg})"
    case rigid: RigidTypeShape => s"RigidTypeShape(${rigid.parameter.showDbg})"
    case bs: BaseShape => s"BaseShape(${bs.defn.sym.showDbg})"
    case es: ErrShape => es.describe

/** Construction lookup reads the actual immutable view, rather than building
  * a parallel tree of shape keys. Graph producers are already identity keys.
  * Canonical view keys use cached portable hashes: imports can compare their
  * construction data without modifying the exporter's interning tables.
  */
object ShapeIdentity:
  type Key = ShapeEvent | View

  private[hkmc2] def key(shape: ShapeEvent)(using ResolutionContext): Key = shape.comparison match
    case view: View => rctx.state.shapeIdentities.getOrElseUpdate(view, view)
    case node => node

  private[semantics] def comparison(shape: ShapeEvent): Key = shape match
    case instance: InstanceShape => instance.candidateIdentity
    case _: (MarkedShape[?] | ContextualShape | ClassValueShape | NominalInstanceView |
        CallableTypeShape | RecordTypeShape | IntersectionView | SpecializedShape | UnknownValueShape |
        OpaqueTypeShape | RigidTypeShape | ActivatedShapeEvent) => new View(shape)
    // These producers own graph nodes, including synthesized inference hosts.
    // Adding a variant requires choosing its equality policy here.
    case _: (TupleShape | RecordShape | IntroShape | DefnShape | BaseShape |
        AppShape | NewShape | SymShape | ErrShape | DynShape) => shape

  /** Only one pointer to the existing view; no copied fields or product key. */
  final class View private[ShapeIdentity] (private val shape: ShapeEvent) extends ValueKey:
    private def parentHash(parent: Opt[TermShape]): Int = parent.fold(0)(_.comparison.hashCode)
    private def sameParent(left: Opt[TermShape], right: Opt[TermShape]): Bool =
      left.fold(right.isEmpty)(a => right.exists(b => a.comparison == b.comparison))
    // Views of different shape classes are kept apart by the viewed shape's tag.
    protected val valueHash: Int = ValueKey.mix(ValueKey.tag(shape), shape match
      case MarkedShape(base, marks) => ValueKey.hash(base.comparison.hashCode, marks.hashCode)
      case ContextualShape(source, instances) => ValueKey.hash(source.comparison.hashCode, instances.hashCode)
      case view: ClassValueShape => ValueKey.hash(System.identityHashCode(view.target), parentHash(view.parent))
      case view: NominalInstanceView => ValueKey.hash(System.identityHashCode(view.defn), ValueKey.mapHash(view.bindings)(System.identityHashCode, _.hashCode), parentHash(view.parent))
      case view: CallableTypeShape => ValueKey.hash(System.identityHashCode(view.source), view.paramLists.hashCode,
        view.result.hashCode, view.scheme.hashCode, view.supplied.hashCode,
        view.declaration.fold(0)(System.identityHashCode), view.asyncResult.hashCode)
      case view: RecordTypeShape => ValueKey.hash(
        ValueKey.mapHash(view.fields)(_.hashCode, _.hashCode), view.aliases.hashCode)
      case view: IntersectionView => view.values.map(_.comparison).hashCode
      case view: SpecializedShape => ValueKey.hash(view.declaration.comparison.hashCode,
        view.arguments.hashCode, view.instances.hashCode)
      case view: UnknownValueShape => ValueKey.hash(System.identityHashCode(view.source), view.fromPublicInterface.hashCode)
      case view: OpaqueTypeShape => System.identityHashCode(view.source)
      case view: RigidTypeShape => ValueKey.hash(System.identityHashCode(view.parameter), System.identityHashCode(view.source))
      case event: ActivatedShapeEvent => ValueKey.hash(event.value.comparison.hashCode, event.instances.hashCode)
      case _ => lastWords("A graph producer cannot be a structural view key"))
    protected def sameValue(other: ValueKey): Bool = other match
      case that: View => shape match
        case a: MarkedShape[?] => that.shape match
          case b: MarkedShape[?] => a.sh.comparison == b.sh.comparison && a.mark == b.mark
          case _ => false
        case a: ContextualShape => that.shape match
          case b: ContextualShape => a.source.comparison == b.source.comparison && a.instances == b.instances
          case _ => false
        case a: ClassValueShape => that.shape match
          case b: ClassValueShape => (a.target eq b.target) && sameParent(a.parent, b.parent)
          case _ => false
        case a: NominalInstanceView => that.shape match
          case b: NominalInstanceView => (a.defn eq b.defn) && a.bindings == b.bindings && sameParent(a.parent, b.parent)
          case _ => false
        case a: CallableTypeShape => that.shape match
          case b: CallableTypeShape => (a.source eq b.source) && a.paramLists == b.paramLists && a.result == b.result &&
            a.scheme == b.scheme && a.supplied == b.supplied &&
            a.declaration.fold(b.declaration.isEmpty)(x => b.declaration.exists(_ eq x)) && a.asyncResult == b.asyncResult
          case _ => false
        case a: RecordTypeShape => that.shape match
          case b: RecordTypeShape => a.fields == b.fields && a.aliases == b.aliases
          case _ => false
        case a: IntersectionView => that.shape match
          case b: IntersectionView => a.values.map(_.comparison) == b.values.map(_.comparison)
          case _ => false
        case a: SpecializedShape => that.shape match
          case b: SpecializedShape => a.declaration.comparison == b.declaration.comparison &&
            a.arguments == b.arguments && a.instances == b.instances
          case _ => false
        case a: UnknownValueShape => that.shape match
          case b: UnknownValueShape => (a.source eq b.source) && a.fromPublicInterface == b.fromPublicInterface
          case _ => false
        case a: OpaqueTypeShape => that.shape match
          case b: OpaqueTypeShape => a.source eq b.source
          case _ => false
        case a: RigidTypeShape => that.shape match
          case b: RigidTypeShape => (a.parameter eq b.parameter) && (a.source eq b.source)
          case _ => false
        case a: ActivatedShapeEvent => that.shape match
          case b: ActivatedShapeEvent => a.value.comparison == b.value.comparison && a.instances == b.instances
          case _ => false
        case _ => lastWords("A graph producer cannot be a structural view key")
      case _ => false

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


sealed trait NonMarkedShape extends TermShape:
  /** Whether nothing reachable from this shape (members, call results, captured
    * values, or type arguments) depends on the lexical scope where the value was
    * produced. Such shapes do not record scope exits (see MarkedShape.exit).
    */
  def isSelfContained: Bool = false
sealed trait NonAppTermShape extends NonMarkedShape

/** A shape with its outer contextual/specialization view removed. Application
  * receivers use this family, so a view cannot hide inside an application chain.
  * Marks remain on the receiver and are accumulated by applicationHead.
  */
sealed trait CoreShape extends NonMarkedShape
sealed trait CoreHeadShape extends CoreShape, NonAppTermShape
type CoreTermShape = CoreShape | MarkedShape[CoreShape]

// Only these shapes defer substitution to a ContextualShape. All other cores
// either store substitutions in their own fields or are independent of binders.
type ContextualSource = AppShape | NewShape | DefnShape | BaseShape | IntroShape

/** The value's lexical substitution and any already consumed type arguments.
  * Removing these views preserves the full application chain and its marks.
  */
final case class ShapeParts(value: CoreTermShape, instances: TypeSubstitution,
    supplied: Opt[Ls[DeclaredType]])

/** A lexical resolution boundary, independent of a definition's term/type interpretation.
  * A class and its companion constructor enter the same instance scope. Keeping their
  * symbol identities distinct is still necessary for overload selection and lowering.
  */
final class ResolutionBoundary private (val symbol: AnyDefinitionSymbol) extends ValueKey:
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(symbol))
  protected def sameValue(other: ValueKey): Bool = other match
    case that: ResolutionBoundary => symbol == that.symbol
    case _ => false
  def showDbg(using DebugPrinter): Str = symbol.showDbg
  override def toString: Str = symbol.toString
object ResolutionBoundary:
  def apply(symbol: AnyDefinitionSymbol): ResolutionBoundary =
    assert(!symbol.isInstanceOf[TypeAliasSymbol], "Type aliases do not introduce value resolution scopes")
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
  *
  * A well-scoped walk's adjacent entry/exit steps traverse the same tree edge.
  * Cancelling them preserves endpoints; a reduced walk only ascends, then
  * descends. Neither run can revisit a boundary, and its length is bounded by
  * the sum of the endpoint depths. Producers must preserve those endpoints,
  * including through qualified type selections and deferred type references.
  * See doc/new-resolution-scopes.md for the proof and the producer contracts.
  */
sealed abstract class Marks extends ValueKey:
  def showDbg(using DebugPrinter): Str = this match
    case EntryMark(boundary, id, rest) => s"↘⟨${boundary.showDbg}⟩${id.fold("")("%⟨"+_.showDbg+"⟩")}${rest.showDbg}"
    case ExitMark(boundary, id, rest) => s"↗⟨${boundary.showDbg}⟩${id.fold("")("%⟨"+_.showDbg+"⟩")}${rest.showDbg}"
    case NoMarks => "ϵ"
  @scala.annotation.tailrec
  final def hasEntry(boundary: ResolutionBoundary): Bool = this match
    case EntryMark(b, _, rest) => b == boundary || rest.hasEntry(boundary)
    case _ => false

type SomeMarks = EntryMark | ExitMark
final case class EntryMark(boundary: ResolutionBoundary, id: Opt[FlowSymbol], rest: Marks) extends Marks:
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), boundary.hashCode, id.hashCode, rest.hashCode)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: EntryMark => boundary == that.boundary && id == that.id && rest == that.rest
    case _ => false
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
final case class ExitMark(boundary: ResolutionBoundary, id: Opt[FlowSymbol], rest: ExitMarks) extends ExitMarks:
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), boundary.hashCode, id.hashCode, rest.hashCode)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: ExitMark => boundary == that.boundary && id == that.id && rest == that.rest
    case _ => false
  if checkMarkPaths then
    assert(!rest.hasExit(boundary), "Repeated exit from the same lexical resolution scope")
object NoMarks extends ExitMarks:
  override def toString: Str = "NoMarks"
  protected val valueHash: Int = ValueKey.tag(this)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: NoMarks.type => true
    case _ => false


object Marked:
  // Reattach an already normalized outer path without erasing the core's type.
  def apply[T <: NonMarkedShape](shape: T, marks: Marks): T | MarkedShape[T] = marks match
    case NoMarks => shape
    case marks: SomeMarks => MarkedShape(shape, marks)
  // Both marked and unmarked shapes have this view, independently of their own
  // extractors. The value class erases to TermShape at pattern-matching sites.
  final class Parts(private val shape: TermShape) extends AnyVal:
    def isEmpty: false = false
    def get: Parts = this
    def _1: NonMarkedShape = shape match
      case shape: NonMarkedShape => shape
      case shape: MarkedShape[?] => shape.sh
    def _2: Marks = shape match
      case _: NonMarkedShape => NoMarks
      case shape: MarkedShape[?] => shape.mark
  def unapply(sh: TermShape): Parts = new Parts(sh)
end Marked

final case class MarkedShape[+T <: NonMarkedShape](sh: T, mark: SomeMarks) extends TermShape:
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    sh.getMemberThrough(name, mark)
  override def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool = sh.isInstanceOfClass(cls)
  def describe: Str = sh.describe
  def toLoc: Opt[Loc] = sh.toLoc
object MarkedShape:
  def enter(sh: TermShape, boundary: ResolutionBoundary, id: Opt[FlowSymbol])(using TL): MarkedShape[NonMarkedShape] =
    sh match
    case sh: NonMarkedShape => MarkedShape(sh, EntryMark(boundary, id, NoMarks))
    case MarkedShape(sh, marks) => MarkedShape(sh, EntryMark(boundary, id, marks))
  def exit(sh: TermShape, boundary: ResolutionBoundary, id: Opt[FlowSymbol])(using TL): TermShape | NoShape =
  tl.trace[TermShape | NoShape](dbg".exit MarkedShape (${sh.shwDbg}, ${boundary.showDbg}, ${id.fold("")(_.showDbg)})", res => s"= ${res.shwDbg}"):
    sh match
    // Exits are only ever prepended to a path's trailing exits, never compared
    // against them; they locate what a value refers to. A self-contained value
    // refers to nothing, so its exits carry no information. Recording them would
    // make every route that a dynamic or unknown value takes out of recursive
    // functions a distinct candidate: this multiplied candidates across
    // FingerTreeList. Entries still decide which activations it can leave.
    case sh: NonMarkedShape if sh.isSelfContained => sh
    case MarkedShape(sh, _: ExitMark) if sh.isSelfContained =>
      lastWords("A self-contained shape does not record exits")
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


sealed trait TermShape extends Shape, ShapeLike:
  // Cache all lookup outcomes per shape, without materializing all inherited members.
  final def getMember(name: MemberKey)(using state: ResolutionContext): MemberLookup =
    state.state.membersCache.getOrElseUpdate((this, name), getMemberImpl(name))
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup
  /** Lookup on this shape as reached through the receiver path `receiver`.
    * Shapes whose members are declared by a nominal class override this to
    * locate the member at the class's definition (see NewResolver.nominalMember);
    * other members are transported through the whole path.
    */
  def getMemberThrough(name: MemberKey, receiver: Marks)(using ResolutionContext): MemberLookup = receiver match
    case NoMarks => getMember(name)
    case receiver: SomeMarks => getMember(name).withMarks(receiver :: Nil)
  
  /** Whether this value is an instance of the nominal class. A saturated class
    * value (e.g. a class without parameters) is still not an instance. */
  def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool = false
  
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
  tl.trace[TermShape | NoShape](dbg".exit $shwDbg (${marks.showDbg})", res => s"= ${res.shwDbg}"):
    marks match
    case NoMarks => this
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
  tl.trace[TermShape | NoShape](dbg".enter $shwDbg (${marks.showDbg})", res => s"= ${res.shwDbg}"):
    marks match
    case NoMarks => this
    case EntryMark(sym, id, rest) =>
      MarkedShape.exit(this, sym, id).enter(rest)
    case ExitMark(sym, id, rest) =>
      MarkedShape.enter(this, sym, id).enter(rest)
  
  def enter(revMarkss: Ls[Marks])(using TL): TermShape | NoShape = revMarkss match
    case Nil => this
    case mark :: rest =>
      // Fragments describe travel from the definition out to its consumer.
      // Passing an argument back in must undo that composition in reverse order.
      enter(rest).enter(mark)
  
  def isSaturated: Bool = unappliedParamLists.isEmpty
  
end TermShape


/** Missing means definitely absent; Unknown must not be treated as a miss when
  * searching wildcard opens, since it can introduce an additional candidate. */
enum MemberLookup:
  // A structural intersection can give one source name several runtime keys.
  // Retain each target so selection reports ambiguity instead of choosing one.
  case All(members: Ls[MemberLookup])
  case Contextual(source: MemberLookup, instances: TypeSubstitution)
  case Found(member: BlockMemberSymbol | RecordMember, marks: Ls[Marks])
  // Declared members expose signatures only. Their marks transport dependent
  // type arguments; they never authorize reading an implementation's value flow.
  case Declared(member: BlockMemberSymbol, bindings: Map[VarSymbol, DeclaredType], marks: Ls[Marks], annotation: Opt[Term], positive: Bool)
  // A structural field already has its lexical bindings and intersection applied.
  case Typed(field: RcdField, tpe: DeclaredType, marks: Ls[Marks])
  // A preceding spread can place several different fields at the same index.
  case Indexed(fields: Ls[TupleShape.Fixed], marks: Ls[Marks])
  case Dynamic(marks: Ls[Marks])
  case Missing
  case Unknown(reason: MemberLookup.Uncertainty, fromPublicInterface: Bool, provenance: ShapeProvenance)
  /** A private member of `owner`, found by `own`, which only hides the members of the same name that `owner`
    * inherits, found by `inherited`, from the code that can access the private members of `owner`.
    * Which members a lookup finds thus depends on where it is performed: see `visibleFrom`. */
  case Private(own: MemberLookup, owner: ClassLikeDef, inherited: MemberLookup)
  
  def withMarks(marks: Ls[Marks]): MemberLookup = this match
    case All(members) => All(members.map(_.withMarks(marks)))
    case Contextual(source, instances) => Contextual(source.withMarks(marks), instances)
    case Private(own, owner, inherited) => Private(own.withMarks(marks), owner, inherited.withMarks(marks))
    case Found(member, inner) => Found(member, inner ::: marks)
    case Declared(member, bindings, inner, annotation, positive) => Declared(member, bindings, inner ::: marks, annotation, positive)
    case Typed(field, tpe, inner) => Typed(field, tpe, inner ::: marks)
    case Indexed(fields, inner) => Indexed(fields, inner ::: marks)
    case Dynamic(inner) => Dynamic(inner ::: marks)
    case _ => this

  /** The receiver's annotation remains the diagnostic origin when lookup visits a parent. */
  def withAnnotation(annotation: Opt[Term]): MemberLookup = this match
    case All(members) => All(members.map(_.withAnnotation(annotation)))
    case Contextual(source, instances) => Contextual(source.withAnnotation(annotation), instances)
    case Private(own, owner, inherited) => Private(own.withAnnotation(annotation), owner, inherited.withAnnotation(annotation))
    case Declared(member, bindings, marks, _, positive) => Declared(member, bindings, marks, annotation, positive)
    case _ => this

  def instantiate(instances: TypeSubstitution): MemberLookup =
    if instances.isEmpty then this else this match
      case Contextual(source, previous) => Contextual(source, instances.withOverrides(previous))
      case Missing | Unknown(_, _, _) | Dynamic(_) => this
      case _ => Contextual(this, instances)

  /** The members found by this lookup when it is performed by code that can access the private members of the
    * class-like definitions satisfying `canAccess` (see SrcScope.canAccessPrivatesOf). Inaccessible private members
    * do not hide inherited members, just like JavaScript's private class elements do not hide inherited properties.
    * When there are no such inherited members, the lookup only finds the inaccessible private member
    * if `reportInaccessible` is set, so that its consumer reports the illegal access (see ResolutionContext.checkAccess)
    * rather than a missing member; otherwise, the lookup finds no member.
    */
  def visibleFrom(canAccess: ClassLikeDef => Bool, reportInaccessible: Bool): MemberLookup = this match
    case All(members) => MemberLookup.all(members.map(_.visibleFrom(canAccess, reportInaccessible)))
    case Contextual(source, instances) => source.visibleFrom(canAccess, reportInaccessible).instantiate(instances)
    case Private(own, owner, inherited) =>
      if canAccess(owner) then own
      else inherited.visibleFrom(canAccess, reportInaccessible) match
        case Missing if reportInaccessible => own
        case visible => visible
    case _ => this

object MemberLookup:
  def all(members: Ls[MemberLookup]): MemberLookup = members.filterNot(_ == Missing) match
    case Nil => Missing
    case member :: Nil => member
    case members => All(members)

  enum Uncertainty:
    case ValueShape, RecordOverwrite
  
  /** Own members take precedence over inherited ones, including unknown spreads,
    * except for private members as seen from outside their class (see Private). */
  def inClass(defn: ClassLikeDef, ext: Opt[TermShape], name: MemberKey)(using ResolutionContext): MemberLookup =
    def inherited = ext.fold[MemberLookup](Missing)(_.getMember(name))
    MemberKey.own(defn, name) match
      case S(member) => own(defn, member, Found(member, Nil), inherited)
      case N => inherited
  
  /** Hide a name only when all its definitions are private. A public companion keeps the name
    * available even when its class is private; checkAccess checks the interpretation actually selected.
    * An entirely private name instead permits lookup of the inherited member outside its owner. */
  def own(defn: ClassLikeDef, member: BlockMemberSymbol, found: MemberLookup, inherited: => MemberLookup): MemberLookup =
    if member.symbols.nonEmpty && member.symbols.forall(_.defn.exists(_.visibility is Visibility.Private))
    then Private(found, defn, inherited) else found

end MemberLookup


extension (member: BlockMemberSymbol | RecordMember)
  def memberSymbol: BlockMemberSymbol = member match
    case symbol: BlockMemberSymbol => symbol
    case member: RecordMember => member.field.sym

class ErrShape(val err: ErrorReport) extends CoreHeadShape:
  override def isSelfContained: Bool = true
  def describe: Str = s"error: ${err.mainMsg}"
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup = MemberLookup.Missing
  def toLoc: Opt[Loc] = N

class AppShape(val receiver: CoreTermShape, val args: Term, val src: Term.App)(using DebugPrinter) extends CoreShape:
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    // An unsaturated term definition is just a concrete function shape
    if !isSaturated then MemberLookup.Missing
    else
      applicationHead match
      case (ds: DefnShape, mss) =>
        ds.getInstanceMember(name).withMarks(mss)
      case _ => MemberLookup.Missing
  override def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool =
    isSaturated && (applicationHead._1 match
      case ds: DefnShape => ds.classExtends(cls)
      case _ => false)
  def describe: Str =
    val head = applicationHead._1
    if !isSaturated then s"partially-applied ${head.describe}"
    else head match
      // Constructor applications produce instances of the associated class,
      // so their descriptions must not describe the constructor function itself.
      case ds: DefnShape => s"instance of ${ds.clsDef.fold(ds.describe)(_.describeRef)}"
      case _ => s"instance of ${head.describe}"
  def toLoc: Opt[Loc] = src.toLoc
  override def toString: String = s"AppShape($receiver, ${args.showDbg})"

class NewShape(val receiver: DefnShape, val classTarget: ClassValueTarget, val clsMarks: Ls[Marks], val argss: Ls[Term], val src: Term.New,
    val supplied: Opt[Ls[DeclaredType]])(using DebugPrinter) extends CoreShape:
  def cls: ClassSymbol = ClassValueShape.definitionOf(classTarget).sym
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    if isSaturated then receiver.getInstanceMember(name).withMarks(clsMarks)
    else MemberLookup.Missing
  override def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool =
    isSaturated && receiver.classExtends(cls)
  def describe: Str =
    // s"instantiation of ${receiver.describe}"
    s"instance of ${cls.defn.get.describeRef}"
  override def toString: String = s"NewNewShape(${cls.showDbg}, $argss)"
  def toLoc: Opt[Loc] = src.toLoc

/** A class expression can denote a class directly or recover it from its
  * generated constructor function. Keep the source definition in the inference
  * shape so lowering does not need a separate mutable access-mode annotation.
  */
type ClassValueTarget = ClassSymbol | ClassCtorSymbol

final class ClassValueShape(val target: ClassValueTarget, val parent: Opt[TermShape])
    extends DefnShape(ClassValueShape.definitionOf(target), parent):
  override def toString: Str = s"ClassValueShape($target, $parent)"

object ClassValueShape:
  def definitionOf(target: ClassValueTarget): ClassDef = target match
    case cls: ClassSymbol => cls.defn.get
    case ctor: ClassCtorSymbol => ctor.associatedCls.defn.get

  /** Read the originating unit's completed interpretation. Later inference must
    * preserve both the class identity and whether its operand needs unwrapping.
    */
  def targetsOf(term: Term): Ls[ClassValueTarget] =
    def targets(event: ShapeEvent): Ls[ClassValueTarget] = event match
      case ActivatedShapeEvent(value, _) => targets(value)
      case MarkedShape(value, _) => targets(value)
      case ContextualShape(value, _) => targets(value)
      case SpecializedShape(value, _, _) => targets(value)
      case shape: NewShape => shape.classTarget :: Nil
      case shape: ClassValueShape => shape.target :: Nil
      case _ => Nil
    term.shapes.toList.flatMap(targets).distinct

sealed abstract class SymShape(val sym: BlockMemberSymbol, val resSym: FlowSymbol, val markss: Ls[Marks]) extends Shape:
  def describe: Str = s"${sym.describe} symbol '${sym.nme}'"
  def toLoc: Opt[Loc] = sym.toLoc
  override def toString: String = s"SymShape($sym)"

/** A symbolic value before its captured substitution is attached. Contextual
  * symbol views compose substitutions instead of wrapping one another.
  */
sealed class CoreSymShape(symbol: BlockMemberSymbol, site: FlowSymbol, marks: Ls[Marks])
extends SymShape(symbol, site, marks)

/** The symbolic counterpart of ContextualShape: retain the value's substitution
  * until overload selection produces a term shape. This does not consume a scheme.
  */
final class ContextualSymShape(val source: CoreSymShape, val instances: TypeSubstitution)
extends SymShape(source.sym, source.resSym, source.markss)


/** Keep a declared receiver's boundary while consumers choose between the term,
  * type, and constructor interpretations of the same overload set.
  */
final class DeclaredSymShape(symbol: BlockMemberSymbol, site: FlowSymbol, marks: Ls[Marks],
    val bindings: Map[VarSymbol, DeclaredType], val annotation: Opt[Term], val positive: Bool) extends CoreSymShape(symbol, site, marks)


// TODO: make it not a TermShape?
class BaseShape(val defn: ClassLikeDef, val ext: Opt[TermShape]) extends CoreHeadShape:
  override def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool =
    (defn is cls) || ext.exists(_.isInstanceOfClass(cls))
  def describe: Str = s"${defn.describe}"
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    MemberLookup.inClass(defn, ext, name)
  def toLoc: Opt[Loc] = defn.headerLoc

/** A structural annotation exposes only its declared fields. Their symbols belong
  * to the annotation, not to whichever record happens to be passed by a caller.
  * Field types are deferred references, including for recursive intersections.
  * Source declarations are witnesses for diagnostics and property selection, not
  * part of semantic equality: a merged field may have several such witnesses.
  */
final class RecordTypeShape(val fields: Map[MemberKey, DeclaredType], val aliases: Map[Str, Set[SymbolKey]])(
    val source: Term.Rcd, val declarations: Map[MemberKey, RcdField]) extends CoreHeadShape:
  def describe: Str = "record type"
  override def toString: Str = s"RecordTypeShape($fields)"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    // Aliases affect lookup and therefore semantic identity, independently of
    // diagnostic declarations. Intersections retain all aliases for a shared key.
    val keys = Option.when(fields.contains(name))(name).toList ::: (name match
      case name: Str => aliases.getOrElse(name, Set.empty).toList.sortBy(_.name)
      case _ => Nil)
    MemberLookup.all(keys.map(key => MemberLookup.Typed(declarations(key), fields(key), Nil)))

/** A conjunction exposes members supplied by any component. Keep nominal and
  * structural interfaces together: `Iterator[T] & Iterable[T]` supplies `next`
  * and the iteration method on the same value. Constraint inspection still
  * visits the components separately, retaining every input and output flow.
  */
final class IntersectionView(val values: Ls[TermShape]) extends CoreHeadShape:
  def describe: Str = "intersection type"
  def toLoc: Opt[Loc] = values.headOption.flatMap(_.toLoc)
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    MemberLookup.all(values.map(_.getMember(name)))
  override def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool = values.exists(_.isInstanceOfClass(cls))

/** An instance described by a type, in either position of a constraint. Keep the
  * type reference intact during transport: expanding it to its current positive
  * candidates would lose negative uses of generic arguments and compound types.
  * Operations obtain concrete member/call views through listenInstanceViews.
  */
final class InstanceShape private (val tpe: DeclaredType, canonical: Opt[InstanceShape]) extends CoreHeadShape:
  /** Diagnostic views share the origin-free reference's inference identity. */
  private[semantics] def candidateIdentity: InstanceShape = canonical.getOrElse(this)
  def describe: Str = "value with a declared type"
  override def toString: Str = s"InstanceShape($tpe)"
  def toLoc: Opt[Loc] = tpe.resolution.source.toLoc
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    lastWords("Instance member lookup requires interpreting its type first")

object InstanceShape:
  /** Intern the reference in the consuming graph, adopting an inherited instance
    * when available. The type's substitution is first projected onto its support
    * (NewResolver.projectType): an instance retaining a binding it cannot observe
    * would be a distinct candidate for every unrelated caller environment. This
    * factory is the only way to construct an instance, so that no construction
    * site can skip the projection. Keep each diagnostic witness on its own
    * immutable view: otherwise observing the same type through another annotation
    * reports the first annotation's location. Witness wrappers are not interned;
    * retaining them in a cache would duplicate entries for the same semantic
    * value. All views share the origin-free reference's candidate identity,
    * so diagnostic evidence cannot multiply inference flow.
    */
  def apply(tpe: DeclaredType)(resolver: NewResolver)(using state: ResolutionContext): InstanceShape =
    val projected = resolver.projectType(tpe)
    val semanticType = projected.withoutOrigin
    val canonical = state.canonicalInstance(semanticType)(new InstanceShape(semanticType, N))
    if projected.origin.isEmpty then canonical
    else new InstanceShape(projected, S(canonical))

/** A deferred value view: interpret references in the shared `source` using
  * `instances`, a flat map from original binders to canonical parameter instances.
  * This does not consume the source's own generic scheme. For example, a returned
  * inner[B] can capture outer's A while leaving B available for a later call.
  * `instantiateShape` composes views instead of nesting them; already captured
  * entries take precedence. Aggregates and declared types can store this view
  * directly rather than using a ContextualShape wrapper.
  * Unlike ActivatedShapeEvent.instances, this map belongs to the value, not its receiver.
  * See doc/new-resolution-type-value-flow.md, "Value views, consumed schemes, and activation events".
  */
final case class ContextualShape(source: ContextualSource, instances: TypeSubstitution) extends NonAppTermShape:
  def describe: Str = source.describe
  def toLoc: Opt[Loc] = source.toLoc
  override def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool = source.isInstanceOfClass(cls)
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup = source.getMember(name).instantiate(instances)
  override def getMemberThrough(name: MemberKey, receiver: Marks)(using ResolutionContext): MemberLookup =
    source.getMemberThrough(name, receiver).instantiate(instances)

/** Explicit type application, such as f[Int], has consumed this declaration's
  * scheme before any term argument list need be applied. `arguments` retains the
  * supplied caller type references; `instances` retains the chosen binder group
  * and lexical captures. `shapeParts` tells `appShape` to reuse that group even
  * through stored aliases, rather than instantiate the declaration again.
  * A ContextualShape alone does not record scheme consumption. Complete annotated
  * CallableTypeShape views record consumption by substituting and clearing `scheme`.
  */
final case class SpecializedShape(declaration: DefnShape, arguments: Ls[DeclaredType],
    instances: TypeSubstitution) extends NonAppTermShape:
  def describe: Str = declaration.describe
  def toLoc: Opt[Loc] = declaration.toLoc
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup = declaration.getMember(name).instantiate(instances)

/** An inference-event envelope, not a value interface. `publishActivated` saves
  * the current body's original-binder-to-instance map; `listen` checks agreement
  * with the requested activation on shared keys, unwraps `value`, and invokes the
  * receiver in the combined compatible activation. An empty request accepts all.
  * The enclosed value separately retains its own substitution: in recursive f[A],
  * it can refer to the caller's A@p while the receiving body uses A@q. Merging those
  * maps would rebind the value or execute the operation in the wrong activation.
  * The payload may be a value or an unresolved symbol; it cannot itself be an
  * event. This envelope supports neither value operations nor mark transport.
  * The semantic key includes the activation so distinct deliveries are not deduplicated.
  * Neither map changes the ordinary mark algebra used for lexical scope crossings.
  */
final case class ActivatedShapeEvent(value: Shape, instances: TypeSubstitution) extends ShapeEvent:
  require(instances.nonEmpty, "Publish an activation-independent shape without an envelope")

/** A nominal annotation exposes only declarations, including inherited declarations.
  * In particular, selecting an unannotated field does not inspect its initializer.
  * The annotation is a diagnostic witness, excluded from the semantic key; synthesized
  * interfaces such as a tuple's Array parent have no written annotation.
  * Provenance can instead identify the construct that introduces an interface,
  * such as the async annotation that creates a Promise result.
  */
final class NominalInstanceView(val defn: ClassLikeDef, val bindings: Map[VarSymbol, DeclaredType],
    val parent: Opt[TermShape])(val annotation: Opt[Term], val provenance: ShapeProvenance)(resolver: NewResolver) extends CoreHeadShape:
  def describe: Str = s"value of type '${defn.sym.nme}'"
  override def toString: Str = s"NominalInstanceView(${defn.sym}, $bindings, $parent)"
  def toLoc: Opt[Loc] = defn.headerLoc
  override def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool =
    (defn is cls) || parent.exists(_.isInstanceOfClass(cls))
  def ancestor(cls: ClassLikeDef): Opt[NominalInstanceView] =
    if defn is cls then S(this)
    else parent.flatMap:
      case Marked(parent: NominalInstanceView, _) => parent.ancestor(cls)
      case _ => N
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    resolver.nominalMember(this, name, NoMarks)
  override def getMemberThrough(name: MemberKey, receiver: Marks)(using ResolutionContext): MemberLookup =
    resolver.nominalMember(this, name, receiver)

/** One declared input, keeping its optional/droppable flags with its type through
  * substitution and layout matching. An absent type still occupies a parameter position.
  */
final case class DeclaredParam(tpe: Opt[DeclaredType], flags: FldFlags):
  def mapType(f: DeclaredType => DeclaredType): DeclaredParam = copy(tpe = tpe.map(f))

/** Parameter types and arity exposed by one list in a declared calling interface.
  * Leading parameters may be optional; their types then already include `null`
  * (see `Elaborator.optionalType`). A variadic parameter's type describes the whole
  * array it receives, and its trailing parameters are required.
  */
final class DeclaredParams(val params: Ls[DeclaredParam], val variadic: Opt[Variadic[DeclaredParam]]) extends ValueKey:
  def hasRest: Bool = variadic.isDefined
  def rest: Opt[DeclaredType] = variadic.flatMap(_.param.tpe)
  def trailing: Ls[DeclaredParam] = variadic.fold(Nil)(_.trailing)
  /** The same leading, rest, and trailing order as `ParamList.allParams`. */
  lazy val allParams: Ls[DeclaredParam] = params ::: variadic.fold(Nil)(_.allParams)
  /** The number of leading required (i.e., non-optional) parameters. */
  lazy val leadingRequired: Int = FldFlags.requiredPrefixLength(params.map(_.flags))
  override def toString: Str = s"DeclaredParams($params, $variadic)"
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), params.hashCode, variadic.hashCode)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: DeclaredParams => params == that.params && variadic == that.variadic
    case _ => false
  def mapTypes(f: DeclaredType => DeclaredType): DeclaredParams =
    DeclaredParams(params.map(_.mapType(f)), variadic.map(_.map(_.mapType(f))))

/** Async lowering wraps the result only after all written parameter lists have
  * been applied. A separate signature can encode those lists as nested arrows,
  * so the pending wrapper must survive observing the next callable interface.
  */
final case class AsyncResult(annotation: Annot.Async, remainingLists: Int) extends ValueKey:
  // Every async annotation wraps the result in Promise. Its span is evidence.
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), remainingLists.hashCode)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: AsyncResult => remainingLists == that.remainingLists
    case _ => false
  require(remainingLists > 0)

/** Calls through annotations expose only the declared result. Argument shapes
  * constrain type parameters in the interface; they do not recover its implementation.
  * `scheme` retains binders that are still available for instantiation; capture
  * substitution leaves those binders alone. `instantiateCallable` consumes the
  * scheme by substituting its references and clearing it, so stored values and
  * remaining curried lists reuse the chosen instances. This is the annotated
  * counterpart of SpecializedShape, not an inference-event activation.
  */
final case class CallableTypeShape(source: Term, paramLists: NELs[DeclaredParams],
    result: Opt[DeclaredType], scheme: Opt[TypeScheme], supplied: Opt[Ls[DeclaredType]],
    declaration: Opt[TermDefinition], asyncResult: Opt[AsyncResult]) extends CoreHeadShape:
  def tparams: Ls[DeclaredTypeParameter] = scheme.toList.flatMap(_.parameters)
  def describe: Str = declaration.fold("function with a declared signature")(d => s"function '${d.bsym.nme}'")
  def toLoc: Opt[Loc] = declaration.fold(source.toLoc)(_.headerLoc)
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup = MemberLookup.Missing

/** Why observing a type did not expose a member interface. Keep this evidence
  * separate from semantic candidates: normalization can synthesize Any without
  * making the written input bound an abstract type. Each reason retains a finite
  * source witness, not a path that grows when recursive aliases are revisited.
  */
enum TypeInterfaceReason:
  case MissingOutput(source: Term)
  case ContravariantParameter(parameter: TyParam, source: Term)
  case Unrestricted(source: Term)
  case AbstractDeclaration(symbol: TypeAliasSymbol, source: Term)
  case RecursiveAlias(symbol: TypeAliasSymbol)
  case Negated(source: Term)
  case Unavailable(source: Term)

  def provenance: ShapeProvenance =
    val result = ShapeProvenance(this match
      case MissingOutput(source) =>
        (msg"This type argument specifies only an input bound." -> source.toLoc) ::
          (msg"Values read through it have no output bound more specific than 'Any'." -> N) :: Nil
      case ContravariantParameter(parameter, source) =>
        (msg"This type argument supplies only an input bound for '${parameter.sym.nme}'." -> source.toLoc) ::
          (msg"Type parameter '${parameter.sym.nme}' is declared contravariant here." -> parameter.sym.toLoc) ::
          (msg"Values read through it have no output bound more specific than 'Any'." -> N) :: Nil
      case Unrestricted(source) =>
        msg"This type permits values of any type, so no member interface is guaranteed." -> source.toLoc :: Nil
      case AbstractDeclaration(symbol, _) =>
        (msg"Type '${symbol.nme}' is declared without a member interface." -> symbol.toLoc) :: Nil
      case RecursiveAlias(symbol) =>
        msg"Following type alias '${symbol.nme}' does not expose a member interface." -> symbol.toLoc :: Nil
      case Negated(source) =>
        msg"This negated type does not specify a member interface." -> source.toLoc :: Nil
      case Unavailable(source) =>
        msg"No member interface is known for this type." -> source.toLoc :: Nil
    )
    this match
      case AbstractDeclaration(_, source) => result.withTypeOrigin(source)
      case _ => result

/** A type view that authorizes no member operations. The diagnostic reason is
  * excluded from the semantic key so alternative witnesses do not add inference flow.
  */
final class OpaqueTypeShape(val source: Term)(val reason: TypeInterfaceReason) extends CoreHeadShape:
  override def isSelfContained: Bool = true
  def describe: Str = "value with no known interface"
  override def toString: Str = s"OpaqueTypeShape($source)"
  def toLoc: Opt[Loc] = source.toLoc
  def provenance: ShapeProvenance = reason.provenance
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    MemberLookup.Unknown(MemberLookup.Uncertainty.ValueShape, false, provenance)

class DefnShape(val defn: Definition, val ext: Opt[TermShape]) extends CoreHeadShape:
  /** Instance lookup is shared by constructor calls and explicit `new`.
    * Inherited members retain their marks before the caller adds its captures. */
  def getInstanceMember(name: MemberKey)(using ResolutionContext): MemberLookup = defn match
    case cd: ClassDef => MemberLookup.inClass(cd, ext, name)
    case _: TermDefinition => ext.fold[MemberLookup](MemberLookup.Missing)(_.getMember(name))
    case _ => MemberLookup.Missing
  /** Nominal ancestry of this definition, independent of whether its value is an instance. */
  def classExtends(cls: ClassLikeDef)(using ResolutionContext): Bool =
    clsDef.contains(cls) || ext.exists(_.isInstanceOfClass(cls))
  override def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool = defn match
    case _: ModuleOrObjectDef => classExtends(cls)
    case _ => false
  lazy val clsDef = defn match
    case defn: ClassLikeDef => S(defn)
    case defn: TermDefinition =>
      defn.tsym match
      case ts: ClassCtorSymbol => S(ts.associatedCls.defn.get)
      case _ => N
    case _ => N
  def describe: Str =
    s"${defn match
      case defn: ClassDef => return defn.kind.desc + " value"
      case defn: TypeLikeDef => defn.kind.desc + " "
      case defn: TermDefinition =>
        defn.tsym match
        case _: ClassCtorSymbol => "constructor of class "
        case s => s.k.desc + " "
    }'${defn.bsym.nme}'"
  // override def toString: String = s"DefnShape(${defn.describe} ${defn.bsym.nme})"
  override def toString: String = s"DefnShape(${defn.describe})"
  /** Shape-only counterparts of BufferableTransform's static members. The extra
    * (buffer, index) list precedes the original method/constructor lists; it must
    * not consume their arguments or expose instance fields as static members.
    * These fields are never lowered: their symbols identify the generated names.
    */
  private lazy val bufferedMembers: Map[Str, RecordMember] = defn match
    case cls: ClassDef if cls.annotations.exists(_.isInstanceOf[Annot.Bufferable]) =>
      given Elaborator.State = cls.sym.getState
      given state: ResolutionContext = cls.sym.getState.newResolverState.context
      val binders = state.state.lexicalTypeBinders.get(cls.sym).getOrElse(
        lastWords(s"Buffered class ${cls.sym.nme} must record its enclosing type binders")) ++ cls.tparams.map(_.sym)
      // These synthetic functions read the class's parameter annotations and
      // methods. Record their definition scope in the class's owning graph,
      // just as elaboration records ordinary lambdas and getter references.
      def scoped[T <: Term](term: T): T =
        state.recordLexicalBinders(term, binders)
        term
      def field(name: Str, value: Term): (Str, RecordMember) =
        name -> RecordMember(RcdField(Term.Lit(syntax.Tree.StrLit(name)), value), false)
      def withBuffer(body: Term): Term =
        val params = PlainParamList(List("buffer", "index").map: name =>
          Param.simple(VarSymbol(new syntax.Tree.Ident(name), erasedType = N)))(cls.toLoc)
        scoped(Term.Lam(params, body))
      // Constructors return the allocated index after all their original lists.
      val ctor = (cls.paramsOpt.toList ::: cls.auxParams).foldRight[Term](Term.Lit(syntax.Tree.IntLit(0))):
        (params, body) => scoped(Term.Lam(params, body))
      val methods = cls.body.methods.filter(method => method.body.nonEmpty && !method.tsym.isPrivate).map: method =>
        val ref = scoped(Term.MemberRef(method.bsym)(N, FlowSymbol.memSym(method.bsym)))
        field(method.bsym.nme, withBuffer(ref))
      (field("size", Term.Lit(syntax.Tree.IntLit(0))) ::
        field("ctor", withBuffer(ctor)) :: methods).toMap
    case _ => Map.empty

  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    defn match
    case defn: ModuleOrObjectDef =>
      MemberLookup.inClass(defn, ext, name)
    case cls: ClassDef if cls.annotations.exists(_.isInstanceOf[Annot.Bufferable]) =>
      name match
        case name: Str => bufferedMembers.get(name).fold[MemberLookup](MemberLookup.Missing)(MemberLookup.Found(_, Nil))
        case _: SymbolKey => MemberLookup.Missing
    case _: TermDefinition => MemberLookup.Missing
    case _ => MemberLookup.Missing
  /** A definition is identified by its header; a class constructor, by its class's.
    * The definition's `bsym` would instead span all of its trees: whole definitions,
    * including their bodies, and any overloads, such as the companions of a class. */
  def toLoc: Opt[Loc] = defn.headerLoc.orElse(defn.sym.toLoc)
  /** For a class constructor, the `constructor(...)` declarations of its class with
    * parameter lists, which are not part of the header (see `ClassDef.ctorLoc`). */
  def ctorLoc: Opt[Loc] = defn match
    case _: TermDefinition => clsDef match
      case S(cls: ClassDef) => cls.ctorLoc
      case _ => N
    case _ => N

/*
// TODO – see `RefinedShape`
class RefinedShape(val base: TermShape, val refinements: Ls[Str -> Term]) extends NonAppTermShape:
*/

/** A tuple candidate selects a value shape for each spread. Ordinary fields stay
  * lazy. Recursive spreads can have unknown length; retain the known fields around
  * them instead of discarding either those fields or the unresolved possibilities.
  */
final class TupleShape private (val source: Term, val elements: Ls[TupleShape.Element],
    val instances: TypeSubstitution)(resolver: NewResolver) extends CoreHeadShape:
  def arrayParent(using ResolutionContext): NominalInstanceView = resolver.tupleArrayParent(this)
  override def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool = arrayParent.isInstanceOfClass(cls)
  private lazy val sourceSegments: Ls[TupleShape.Segment] = elements.flatMap:
    case segment: TupleShape.Segment => segment :: Nil
    case TupleShape.Rest(_, segments) => segments
    case TupleShape.Spread(shape, marks) => shape.segments.map:
      case field: TupleShape.Fixed => field.withMarks(marks :: Nil)
      case TupleShape.Unknown(source, element) => TupleShape.Unknown(source, element.withMarks(marks :: Nil))
  lazy val segments: Ls[TupleShape.Segment] = sourceSegments.map:
    case field: TupleShape.Fixed => field.instantiate(instances)
    case TupleShape.Unknown(source, element) => TupleShape.Unknown(source, element.instantiate(instances))
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
  override def toString: Str = s"TupleShape($source, $elements, $instances)"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup = MemberKey.index(name) match
    case S(index) if index >= 0 =>
      // An unknown-length segment can be empty. After reaching one, every
      // following field whose minimum position is at most `index` is possible.
      // Keep an exact prefix precise, and stop once fixed fields alone have
      // passed the index; later segments cannot move those fields backwards.
      def loop(rest: Ls[TupleShape.Segment], index: Int, uncertain: Bool): Ls[TupleShape.Fixed] = rest match
        case (field: TupleShape.Fixed) :: tail =>
          if index == 0 then field :: Nil
          else if uncertain then field :: loop(tail, index - 1, true)
          else loop(tail, index - 1, false)
        case (segment: TupleShape.Unknown) :: tail =>
          segment.element :: loop(tail, index, true)
        case Nil => Nil
      loop(segments, index, false) match
        case Nil => MemberLookup.Missing
        case fields => MemberLookup.Indexed(fields, Nil)
    case _ => arrayParent.getMember(name)
  override def getMemberThrough(name: MemberKey, receiver: Marks)(using ResolutionContext): MemberLookup = MemberKey.index(name) match
    case S(index) if index >= 0 => super.getMemberThrough(name, receiver)
    case _ => arrayParent.getMemberThrough(name, receiver)

/** Values whose members and call results are deliberately checked only at runtime.
  * Unlike UnknownValueShape, this authorizes dynamic operations; it is introduced
  * by JavaScript interop and explicit `dyn` types, not by failed inference.
  */
final class DynShape private () extends CoreHeadShape:
  override def isSelfContained: Bool = true
  def describe: Str = "dynamic value"
  override def toString: Str = "DynShape()"
  def toLoc: Opt[Loc] = N
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup = MemberLookup.Dynamic(Nil)

object DynShape:
  private val instance = new DynShape
  def apply(): DynShape = instance

/** A shared diagnostic witness, independent of resolution marks. Messages,
  * locations, and the flattened chain are evaluated only when reporting an error.
  * Discovery retains one witness per reached shape to bound recursive paths.
  */
final class ShapeProvenance private (path: => Ls[(Message, Opt[Loc])], notes: => Ls[(Message, Opt[Loc])],
    typeOrigin: Opt[Located]):
  private lazy val pathNotes = path
  private lazy val originNotes = notes
  /** A type origin anchors the operation's explanation: first trace the value
    * back to that annotation, then explain the interface it provides. Without
    * an annotation witness, lead with the operation's explanation and follow it
    * with the reasons the value's shape is unknown. The fallback identifies other
    * shape evidence, if any, not the operation already located by the main error.
    */
  def diagnostic(message: Message, fallback: Opt[Loc]): Ls[(Message, Opt[Loc])] = typeOrigin match
    case S(source) => pathNotes ::: (message -> source.toLoc.orElse(fallback)) :: originNotes
    case N => (message -> fallback) :: pathNotes ::: originNotes
  def via(note: => (Message, Opt[Loc])): ShapeProvenance =
    new ShapeProvenance(note :: pathNotes, originNotes, typeOrigin)
  /** Keep the annotation providing this interface separate from the path through
    * parameters, returns, and storage that led to the observation. Besides written
    * types, an async annotation provides the Promise interface of its result.
    */
  def withTypeOrigin(source: Located): ShapeProvenance =
    new ShapeProvenance(pathNotes, originNotes, S(source))

object ShapeProvenance:
  def apply(notes: => Ls[(Message, Opt[Loc])]): ShapeProvenance = new ShapeProvenance(Nil, notes, N)
  val empty = ShapeProvenance(Nil)

/** An unknown input or the element of an opaque or widened spread can be any
  * value. Inputs admitted by an exposed interface always require checking, even
  * when local calls resolve the same selection. Keep that distinction in shape
  * equality so an ordinary unknown cannot hide the public input's obligation.
  * Provenance is outside the semantic key: another diagnostic witness must
  * not turn the same unknown into a new inference candidate.
  */
final class UnknownValueShape(val source: Term, val fromPublicInterface: Bool)(val provenance: ShapeProvenance) extends CoreHeadShape:
  override def isSelfContained: Bool = true
  def describe: Str = "value of unknown shape"
  override def toString: Str = s"UnknownValueShape($source, $fromPublicInterface)"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    MemberLookup.Unknown(MemberLookup.Uncertainty.ValueShape, fromPublicInterface, provenance)

/** A generic definition must be valid without choosing a caller's type. This
  * checking witness is not an inferred bound on any call-site parameter.
  */
final class RigidTypeShape(val parameter: VarSymbol, val source: Term) extends CoreHeadShape:
  override def isSelfContained: Bool = true
  def describe: Str = "value of a type parameter"
  override def toString: Str = s"RigidTypeShape($parameter, $source)"
  def toLoc: Opt[Loc] = source.toLoc
  def provenance: ShapeProvenance = ShapeProvenance(
    msg"Type parameter '${parameter.nme}' does not specify a member interface." -> parameter.toLoc :: Nil)
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    MemberLookup.Unknown(MemberLookup.Uncertainty.ValueShape, false, provenance)

object UnknownValueShape:
  def at(source: Term): UnknownValueShape =
    UnknownValueShape(source, fromPublicInterface = false)(ShapeProvenance(msg"The shape of this value is unknown." -> source.toLoc :: Nil))
  def spread(source: Term, value: TermShape): UnknownValueShape =
    val origin = value.applicationHead._1 match
      case unknown: UnknownValueShape => unknown
      case _ => UnknownValueShape(source, fromPublicInterface = false)(ShapeProvenance.empty)
    UnknownValueShape(source, origin.fromPublicInterface)(origin.provenance.via(msg"This spread has no known element shape." -> source.toLoc))

object TupleShape:
  /** Tuple candidates are compared by identity (see ShapeIdentity), so each
    * distinct tuple is constructed once per source node and element list.
    * Only these factories can construct a tuple; a case-class copy would bypass
    * interning and create a distinct inference candidate for the same tuple.
    */
  def apply(source: Term, elements: Ls[Element])(resolver: NewResolver)(using state: ResolutionContext): TupleShape =
    state.canonicalTuple((source, elements, TypeSubstitution.empty)):
      new TupleShape(source, elements, TypeSubstitution.empty)(resolver)
  /** The view of `tuple` through the complete effective substitution `instances`,
    * canonical like the tuple itself: one identity per source, element list, and
    * substitution, whichever sequence of substitutions produced the view. Copying
    * a tuple instead would make each route to the same view a distinct candidate.
    * NewResolver.instantiateShape composes the substitution before calling this. */
  def view(tuple: TupleShape, instances: TypeSubstitution)(resolver: NewResolver)
      (using state: ResolutionContext): TupleShape =
    state.canonicalTuple((tuple.source, tuple.elements, instances)):
      new TupleShape(tuple.source, tuple.elements, instances)(resolver)
  sealed abstract class Element extends ValueKey
  sealed abstract class Segment extends Element:
    /** The deferred value of one element, independently of the segment's length. */
    def element: Fixed
  sealed abstract class Fixed extends Segment:
    final def element: Fixed = this
    def marks: Ls[Marks]
    def withMarks(outer: Ls[Marks]): Fixed = this match
      case Field(field, inner) => Field(field, inner ::: outer)
      case TypedField(tpe, inner) => TypedField(tpe, inner ::: outer)
      case UnknownField(source, inner) => UnknownField(source, inner ::: outer)
      case ValueField(value, inner) => ValueField(value, inner ::: outer)
      case ViewedField(source, instances, inner) => ViewedField(source, instances, inner ::: outer)
    def instantiate(instances: TypeSubstitution): Fixed =
      if instances.isEmpty then this else this match
        case ViewedField(source, previous, marks) => ViewedField(source, instances.withOverrides(previous), marks)
        case _ => ViewedField(this, instances, Nil)
  final case class ViewedField(source: Fixed, instances: TypeSubstitution, marks: Ls[Marks]) extends Fixed:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), source.hashCode, instances.hashCode, marks.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: ViewedField => source == that.source && instances == that.instances && marks == that.marks
      case _ => false
  final case class Field(field: Fld, marks: Ls[Marks]) extends Fixed:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(field), marks.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Field => (field eq that.field) && marks == that.marks
      case _ => false
  final case class ValueField(value: TermShape, marks: Ls[Marks]) extends Fixed:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), value.comparison.hashCode, marks.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: ValueField => value.comparison == that.value.comparison && marks == that.marks
      case _ => false
  final case class TypedField(tpe: DeclaredType, marks: Ls[Marks]) extends Fixed:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), tpe.hashCode, marks.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: TypedField => tpe == that.tpe && marks == that.marks
      case _ => false
  // Mutable tuple slots retain their positions, but their initializer cannot
  // supply the shape of later reads (including reads through a spread copy).
  final case class UnknownField(source: Term, marks: Ls[Marks]) extends Fixed:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), source.hashCode, marks.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: UnknownField => source == that.source && marks == that.marks
      case _ => false
  /** An unknown number of elements described by the same deferred field as a
    * fixed position. Its marks and retained substitution must survive tuple
    * views, rest slicing, and spreading, even when its length is unknown.
    * Use this for typed arrays, opaque layouts, and recursive widening, never
    * for a spread whose shape has not arrived yet. */
  final case class Unknown(source: Term, element: Fixed) extends Segment:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), source.hashCode, element.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Unknown => source == that.source && element == that.element
      case _ => false
  final case class Spread(shape: TupleShape, marks: Marks) extends Element:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), shape.hashCode, marks.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Spread => shape == that.shape && marks == that.marks
      case _ => false
  def unknown(source: Term)(resolver: NewResolver)(using ResolutionContext): TupleShape =
    TupleShape(source, Unknown(source, UnknownField(source, Nil)) :: Nil)(resolver)
  /** Retain the original candidate as well as the selected residual segments:
    * flattening away the parent would hide recursive producer dependencies from
    * containsSpread, allowing recursion through rest slicing to evade widening. */
  final case class Rest(shape: TupleShape, segments: Ls[Segment]) extends Element:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), shape.hashCode, segments.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Rest => shape == that.shape && segments == that.segments
      case _ => false
  /** A view of `tuple` retaining the fields in `segments`, possibly with their
    * lengths widened by rest slicing. A view of another view refers to that view's parent:
    * a view contributes no spreads of its own, so containsSpread gives the same
    * answer for the parent as for the intermediate view. Nesting views instead
    * would make the candidate's identity record the order in which fields were
    * removed. For `if xs is [x, ...rest] then f(rest); [...rest, x] then f(rest)`
    * on an n-tuple, that yields 2^n candidates for only O(n^2) distinct layouts. */
  def restView(tuple: TupleShape, segments: Ls[Segment])(resolver: NewResolver)(using ResolutionContext): TupleShape =
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
final class RecordShape private (val source: Term.Rcd, val elements: Ls[RecordShape.Element],
    val instances: TypeSubstitution) extends CoreHeadShape:
  def describe: Str = "record literal"
  override def toString: Str = s"RecordShape($source, $elements, $instances)"
  def toLoc: Opt[Loc] = source.toLoc
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    import MemberLookup.*
    def unknown(source: Located) = Unknown(Uncertainty.RecordOverwrite, false,
      ShapeProvenance(msg"This computed key can overwrite the selected member." -> source.toLoc :: Nil))
    def loop(rest: Ls[RecordShape.Element]): MemberLookup = rest match
      case Nil => Missing
      case RecordShape.Field(field) :: rest => field.key match
        case S(key) =>
          if key == name then Found(RecordMember(field, source.mut), Nil) else loop(rest)
        case _ => unknown(field.field)
      case RecordShape.Unknown(shape) :: _ => Unknown(Uncertainty.RecordOverwrite, shape.fromPublicInterface, shape.provenance)
      case RecordShape.Dynamic(marks) :: _ => Dynamic(marks)
      case RecordShape.Spread(shape, marks) :: rest =>
        def spread(info: MemberLookup): Opt[MemberLookup] = info match
          case All(members) => members.flatMap(spread) match
            case Nil => N
            case members => S(MemberLookup.all(members))
          case Contextual(source, instances) => spread(source).map(_.instantiate(instances))
          case Dynamic(inner) => S(Dynamic(inner ::: marks :: Nil))
          case Unknown(_, fromPublicInterface, provenance) => S(Unknown(Uncertainty.RecordOverwrite, fromPublicInterface, provenance))
          case Missing => N
          case Found(member: RecordMember, inner) =>
            S(Found(member.copy(mutable = member.mutable || source.mut), inner ::: marks :: Nil))
          case Found(_: BlockMemberSymbol, _) | Declared(_, _, _, _, _) | Typed(_, _, _) | Indexed(_, _) | Private(_, _, _) =>
            // Record spreads recursively look up RecordShapes, which only create RecordMembers.
            lastWords("Record lookup returned a nominal member")
        spread(shape.getMember(name)).getOrElse(loop(rest))
    loop(elements.reverse).instantiate(instances)
  def containsSpread(record: Term.Rcd, marks: Marks): Bool = elements.exists:
    case RecordShape.Spread(shape, inner) =>
      ((shape.source is record) && inner == marks) || shape.containsSpread(record, marks)
    case _ => false

object RecordShape:
  /** Record candidates are compared by identity (see ShapeIdentity), so each
    * distinct record is constructed once per source node and element list.
    * As for TupleShape, private construction without a case-class copy keeps
    * every record candidate behind these canonical factories.
    */
  def apply(source: Term.Rcd, elements: Ls[Element])(using state: ResolutionContext): RecordShape =
    state.canonicalRecord((source, elements, TypeSubstitution.empty)):
      new RecordShape(source, elements, TypeSubstitution.empty)
  /** The canonical view of `record` through the complete effective substitution
    * `instances`; see TupleShape.view. */
  def view(record: RecordShape, instances: TypeSubstitution)(using state: ResolutionContext): RecordShape =
    state.canonicalRecord((record.source, record.elements, instances)):
      new RecordShape(record.source, record.elements, instances)
  sealed abstract class Element extends ValueKey
  object Element:
    final case class Field(field: RcdField) extends Element:
      protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(field))
      protected def sameValue(other: ValueKey): Bool = other match
        case that: Field => (field eq that.field)
        case _ => false
    final case class Spread(shape: RecordShape, marks: Marks) extends Element:
      protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), shape.hashCode, marks.hashCode)
      protected def sameValue(other: ValueKey): Bool = other match
        case that: Spread => shape == that.shape && marks == that.marks
        case _ => false
    final case class Unknown(shape: UnknownValueShape) extends Element:
      protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), shape.comparison.hashCode)
      protected def sameValue(other: ValueKey): Bool = other match
        case that: Unknown => shape.comparison == that.shape.comparison
        case _ => false
    final case class Dynamic(marks: Ls[Marks]) extends Element:
      protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), marks.hashCode)
      protected def sameValue(other: ValueKey): Bool = other match
        case that: Dynamic => marks == that.marks
        case _ => false
  export Element.*


type IntroTerm = Term.Lit | Term.UnitVal | Term.Lam
class IntroShape(val trm: IntroTerm, val primitive: Opt[NominalInstanceView]) extends CoreHeadShape:
  def describe: Str = trm.describe
  // Literals have global primitive interfaces; lambdas capture their scopes.
  override def isSelfContained: Bool = !trm.isInstanceOf[Term.Lam]
  protected def getMemberImpl(name: MemberKey)(using ResolutionContext): MemberLookup =
    primitive.fold[MemberLookup](MemberLookup.Missing)(_.getMember(name))
  override def getMemberThrough(name: MemberKey, receiver: Marks)(using ResolutionContext): MemberLookup =
    primitive.fold[MemberLookup](MemberLookup.Missing)(_.getMemberThrough(name, receiver))
  override def isInstanceOfClass(cls: ClassLikeDef)(using ResolutionContext): Bool =
    primitive.exists(_.isInstanceOfClass(cls))
  def toLoc: Opt[Loc] = trm.toLoc
  override def toString: Str = s"IntroShape(${trm})"


