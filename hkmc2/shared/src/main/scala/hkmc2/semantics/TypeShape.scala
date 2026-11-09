package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import codegen.Erasure

/** A proper type interpretation, separate from both type arguments and value shapes.
  * Compound types retain links to their operands so forward aliases need not be expanded eagerly.
  */
sealed abstract class TypeShape extends ValueKey

object TypeShape:
  final case class Nominal(defn: ClassLikeDef) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(defn))
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Nominal => (defn eq that.defn)
      case _ => false
  final case class Alias(symbol: TypeAliasSymbol, rhs: Opt[TypeResolution]) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(symbol), rhs.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Alias => symbol == that.symbol && rhs == that.rhs
      case _ => false
  final case class Union(left: TypeResolution, right: TypeResolution) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(left), System.identityHashCode(right))
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Union => left == that.left && right == that.right
      case _ => false
  final case class Intersection(left: TypeResolution, right: TypeResolution) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(left), System.identityHashCode(right))
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Intersection => left == that.left && right == that.right
      case _ => false
  // Negated interfaces remain opaque, but their dependencies must participate
  // in source validation, including the rejection of unguarded alias cycles.
  final case class Negation(base: TypeResolution) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(base))
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Negation => base == that.base
      case _ => false
  // Substituted unions/intersections retain whole interpreted endpoints. Keeping
  // their lattice normal form prevents repeated Boolean substitutions from
  // nesting environments, without expanding bounds or changing endpoint marks.
  final case class Combined(formula: TypeFormula[DeclaredType]) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), formula.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Combined => formula == that.formula
      case _ => false
  final case class TupleField(tpe: TypeResolution, spread: Bool)
  final case class Tuple(fields: Ls[TupleField]) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), fields.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Tuple => fields == that.fields
      case _ => false
  final case class Record(source: Term.Rcd, fields: Ls[(RcdField, TypeResolution)]) extends TypeShape:
    protected val valueHash: Int =
      var hash = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(source))
      var rest = fields
      while rest.nonEmpty do
        val field = rest.head
        hash = ValueKey.hash(hash, System.identityHashCode(field._1), System.identityHashCode(field._2))
        rest = rest.tail
      hash
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Record if source eq that.source =>
        var left = fields
        var right = that.fields
        while left.nonEmpty && right.nonEmpty && (left.head._1 eq right.head._1) && (left.head._2 eq right.head._2) do
          left = left.tail
          right = right.tail
        left.isEmpty && right.isEmpty
      case _ => false
  final case class Function(params: Term, result: TypeResolution) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(params), System.identityHashCode(result))
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Function => params == that.params && result == that.result
      case _ => false
  final case class Polymorphic(params: Ls[TypeQuantifier], outer: Opt[VarSymbol], body: TypeResolution) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), params.hashCode, outer.hashCode, body.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Polymorphic => params == that.params && outer == that.outer && body == that.body
      case _ => false
  final case class Applied(base: TypeResolution, args: Ls[TypeArgumentResolution]) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), base.hashCode, args.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Applied => base == that.base && args == that.args
      case _ => false
  // A transported reference retains its context before any deferred component
  // is observed. The resolver flattens these nodes and normalizes their marks.
  final case class Contextual(reference: ContextualType) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), reference.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Contextual => reference == that.reference
      case _ => false
  // The same third-party symbol can have different inference in two exporters.
  // Retain both originating hosts so a consumer sees the exporter's inferred values
  // and explicit bindings, including bindings added privately by an intermediate exporter.
  // `host` holds the values that reads observe: inferred candidates and the output types
  // of explicit bindings. `arguments` keeps both bounds of each binding for constraints.
  final case class Parameter(symbol: VarSymbol, host: Publisher.Data[ShapeEvent],
      arguments: Publisher.Data[TypeArgumentBinding]) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(symbol),
      System.identityHashCode(host), System.identityHashCode(arguments))
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Parameter => symbol == that.symbol && host == that.host && arguments == that.arguments
      case _ => false
  // An omitted argument owns one source inference node. It is not a quantified
  // binder and is never instantiated at a call site; marks distinguish its flows.
  final case class Hole(host: Publisher.Data[TermShape]) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(host))
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Hole => host == that.host
      case _ => false
  // Synthesized generic arguments retain inferred value shapes, for example
  // the element union of the Array supertype of a tuple. Singleton annotations
  // also retain their literal shape; no implementation is inspected.
  final case class Inferred(value: TermShape) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), value.comparison.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Inferred => value.comparison == that.value.comparison
      case _ => false
  // An open type expression reached through a reference. Unlike Contextual,
  // its free binders still receive the observing declaration's substitution.
  // Qualified references retain the receiver's bindings and lexical path too.
  final case class Reference(base: TypeResolution, marks: Ls[Marks], bindings: Map[VarSymbol, TypeArgument], instances: TypeSubstitution) extends TypeShape:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), base.hashCode, marks.hashCode, bindings.hashCode, instances.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Reference => base == that.base && marks == that.marks && bindings == that.bindings && instances == that.instances
      case _ => false
  object Unit extends TypeShape:
    override def toString: Str = "Unit"
    protected val valueHash: Int = ValueKey.tag(this)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Unit.type => true
      case _ => false
  object Dynamic extends TypeShape:
    override def toString: Str = "Dynamic"
    protected val valueHash: Int = ValueKey.tag(this)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Dynamic.type => true
      case _ => false
  object Abstract extends TypeShape:
    override def toString: Str = "Abstract"
    protected val valueHash: Int = ValueKey.tag(this)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Abstract.type => true
      case _ => false
  object Top extends TypeShape:
    override def toString: Str = "Top"
    protected val valueHash: Int = ValueKey.tag(this)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Top.type => true
      case _ => false
  object Bottom extends TypeShape:
    override def toString: Str = "Bottom"
    protected val valueHash: Int = ValueKey.tag(this)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Bottom.type => true
      case _ => false

/** Candidates are published during elaboration. Erasure reads the resulting graph; it
  * never performs lookup or resolves an alias by inspecting an elaborated definition.
  */
final class TypeResolution(val source: Term, report: Ls[(Message, Opt[Loc])] => Unit) extends Host[TypeShape]:
  override def toString: Str = s"TypeResolution($source)"
  private var reported = false
  def hasErrors: Bool = reported
  def showDbg(using DebugPrinter): Str = s"type of ${source.showDbg}"
  def publish(shape: TypeShape)(using ResolutionContext): Unit =
    if currentShapes.add(shape) then notifyShapeListeners(shape)
  def listen(listener: ShapeListener[TypeShape])(using ResolutionContext): Unit =
    subscribeToShapes(listener)
  def fail(messages: Ls[(Message, Opt[Loc])]): Unit = if !reported then
    reported = true
    report(messages)
  /** Resolution is complete, so each node needs one check per erasure pass.
    * A path-local cycle guard would revisit shared alias bodies through every
    * field that references them, expanding a small graph into an exponential tree.
    */
  def validate(visited: scala.collection.mutable.Set[TypeResolution])(using Erasure): Unit = if visited.add(this) then
    import TypeShape.*
    import Message.MessageContext
    val ambiguousReceiver = source.withoutCaptures match
      case ref: Term.UnresolvedRef => ref.resolvedMembers.distinct.sizeCompare(1) > 0
      case sel: Term.NewSel => sel.hasAmbiguousClass
      case _ => false
    // A name already reported as missing (see NewResolver.settleUnboundReferences) needs no other error.
    val missingName = source.withoutCaptures match
      case ref: Term.UnresolvedRef => ref.isErroneous
      case _ => false
    if shapes.isEmpty then
      if !missingName then fail(msg"This type has no resolved target" -> source.toLoc :: Nil)
    else if ambiguousReceiver || shapes.sizeCompare(1) > 0 then
      def declarations(resolution: TypeResolution, seen: Set[TypeResolution]): Ls[(Message, Opt[Loc])] =
        if seen(resolution) then Nil else resolution.shapes.toList.flatMap:
          case Nominal(defn) => msg"candidate: ${defn.sym.describeKind}" -> defn.headerLoc :: Nil
          case Alias(symbol, _) => msg"candidate: ${symbol.describeKind}" -> symbol.defn.flatMap(_.headerLoc).orElse(symbol.toLoc) :: Nil
          case Reference(base, _, _, _) => declarations(base, seen + resolution)
          case _ => Nil
      val candidates = source.withoutCaptures match
        case ref: Term.UnresolvedRef => ref.resolvedMembers.distinct.map: (prefix, member) =>
          msg"candidate: ${member.describe}" -> member.headerLoc
        case _ => declarations(this, Set.empty).distinct
      fail(msg"This type is ambiguous, as it has multiple resolved targets" -> source.toLoc :: candidates)
    shapes.foreachGrowing:
      case Alias(_, rhs) => rhs.foreach(_.validate(visited))
      case Reference(base, _, _, _) => base.validate(visited)
      case Applied(base, args) =>
        base.validate(visited)
        args.foreach(_.foreachType(_.validate(visited)))
        def checkArity(base: TypeResolution, seen: Set[TypeResolution]): Unit = if !seen(base) then
          def check(name: Str, count: Int, loc: Opt[Loc]): Unit = if args.length > count then
            fail(msg"Type '$name' accepts at most $count type ${"argument".pluralized(count)}, but got ${args.length}." ->
              source.toLoc :: (msg"The type parameters are declared here." -> loc) :: Nil)
          base.shapes.toList match
            case Nominal(defn) :: Nil => check(defn.sym.nme, defn.tparams.length, defn.headerLoc)
            case Alias(symbol, _) :: Nil => symbol.defn.foreach(d => check(symbol.nme, d.tparams.length, d.headerLoc))
            case Reference(inner, _, _, _) :: Nil => checkArity(inner, seen + base)
            case _ => ()
        checkArity(base, Set.empty)
      case Contextual(reference) => reference.tpe.resolution.validate(visited)
      case Function(_, result) => result.validate(visited)
      case Polymorphic(params, _, body) =>
        params.foreach: param =>
          param.lower.foreach(_.validate(visited))
          param.upper.foreach(_.validate(visited))
        body.validate(visited)
      case Tuple(fields) => fields.foreach(_.tpe.validate(visited))
      case Record(_, fields) => fields.foreach(_._2.validate(visited))
      case Union(left, right) => left.validate(visited); right.validate(visited)
      case Intersection(left, right) => left.validate(visited); right.validate(visited)
      case Negation(base) => base.validate(visited)
      case Combined(formula) => formula.orderedAtoms.foreach(_.resolution.validate(visited))
      case _ => ()

/** A type with its lexical type-parameter bindings. These bindings describe declared
  * interfaces, not constructor arguments or value-flow capture paths.
  * `positive` interprets substitutions in the source expression; it is not the
  * direction of a constraint subsequently applied to the interpreted type.
  */
final class DeclaredType private (private[semantics] val reference: DeclaredType.Reference,
    val bindings: Map[VarSymbol, TypeArgument])(val origin: Opt[TypeInterfaceReason],
    private[semantics] val namespaces: Opt[TypeNamespaces], private[semantics] val interpretation: Opt[TypeShape]) extends ValueKey:
  def resolution: TypeResolution = reference.resolution
  def instances: TypeSubstitution = reference.instances
  def positive: Bool = reference.positive
  override def toString: Str = s"DeclaredType($resolution, $bindings, $instances, $positive)"
  protected val valueHash: Int = reference.hashCode
  protected def sameValue(other: ValueKey): Bool = other match
    case that: DeclaredType =>
      if reference.pool eq that.reference.pool then reference eq that.reference
      else DeclaredType.equivalent(reference, that.reference)
    case _ => false

  private[semantics] def shapes(using ResolutionContext): Ls[TypeShape] =
    interpretation.fold(resolution.currentShapes.toList)(_ :: Nil)
  private[semantics] def listen(listener: ShapeListener[TypeShape])(using ResolutionContext): Unit =
    interpretation.fold(resolution.listen(listener))(listener(_))
  /** Evidence is shared only when its immediate payloads are identical. Looking
    * through bound arguments here would expand shared DAG paths on cache hits.
    * A conservative miss retains the caller's witnesses without merging them.
    */
  private[semantics] def sameUse(that: DeclaredType): Bool =
    (this is that) || this == that && (bindings is that.bindings) &&
      (origin is that.origin) && (namespaces is that.namespaces) && (interpretation is that.interpretation)
  /** Synthesized nodes share an interned source, while each use keeps its own
    * diagnostic witnesses and Boolean operand order. Those differences cannot
    * change the child types that identify the source.
    */
  private[semantics] def withInterpretation(shape: TypeShape): DeclaredType =
    val canonical = interpretation.getOrElse(lastWords("A synthesized type must have one fixed interpretation"))
    assert(canonical == shape, "An interpretation must preserve the interned type")
    val shared = (canonical, shape) match
      case (TypeShape.Contextual(previous), TypeShape.Contextual(current)) =>
        if previous.tpe.sameUse(current.tpe) then canonical else
          // Scope paths carry no diagnostic evidence. Even distinct witnesses
          // share the cached path, rather than retaining a freshly rebuilt one.
          TypeShape.Contextual(ContextualType(current.tpe, previous.marks))
      case (TypeShape.Combined(previous), TypeShape.Combined(current)) =>
        val left = previous.orderedAtoms
        val right = current.orderedAtoms
        if left.size == right.size && left.lazyZip(right).forall(_.sameUse(_)) then canonical else shape
      case _ => lastWords("Only synthesized type nodes have a per-use interpretation")
    if shared is canonical then this else new DeclaredType(reference, bindings)(origin, namespaces, S(shared))
  private[semantics] def withNamespaces(plan: TypeNamespaces)(using ResolutionContext): DeclaredType =
    rebuilt(bindings, instances, positive, S(plan))
  private[semantics] def withoutNamespaces(using ResolutionContext): DeclaredType =
    if namespaces.isEmpty then this else rebuilt(bindings, instances, positive, N)
  /** Witnesses belong to this observation and do not multiply inference candidates. */
  def withOrigin(witness: Opt[TypeInterfaceReason]): DeclaredType =
    if witness.isEmpty then this else new DeclaredType(reference, bindings)(witness, namespaces, interpretation)

  private def rebuilt(bindings: Map[VarSymbol, TypeArgument], instances: TypeSubstitution, positive: Bool,
      plans: Opt[TypeNamespaces])(using ResolutionContext): DeclaredType =
    val references = rctx.state.typeReferences
    val aliases = plans.fold(Nil)(_.aliases)
    val updated = if bindings is this.bindings then references.updated(reference, instances, positive, aliases)
      else references(resolution, bindings, instances, positive, aliases)
    new DeclaredType(updated, bindings)(origin, plans, interpretation)

  /** Instantiation changes references to source binders, never expands their bounds.
    * A reference already interpreted in another call retains that interpretation.
    * The finite map contains original binders and canonical site instances only.
    */
  def instantiate(substitution: TypeSubstitution)(using ResolutionContext): DeclaredType =
    withInstances(substitution.withOverrides(instances))

  def withInstances(substitution: TypeSubstitution)(using ResolutionContext): DeclaredType =
    if substitution == instances then this
    else rebuilt(bindings, substitution, positive, namespaces)
  def withPolarity(polarity: Bool)(using ResolutionContext): DeclaredType =
    if polarity == positive then this else rebuilt(bindings, instances, polarity, namespaces)
  def withoutBinders(symbols: Iterable[VarSymbol])(using ResolutionContext): DeclaredType =
    rebuilt(bindings -- symbols, instances.without(symbols), positive, namespaces)
  def withoutOrigin: DeclaredType =
    if origin.isEmpty then this else new DeclaredType(reference, bindings)(N, namespaces, interpretation)

object DeclaredType:
  /** A closed synthesized node retains its shape directly. Cache hits can reuse
    * it without subscribing to, or looking up, its already fixed source host.
    * The node keeps the location and the error reporter of `source`, which must be
    * the type use that the node's cache key identifies. A node shared by uses with
    * different sources has no source instead (see `shared`).
    */
  private[semantics] def synthesized(source: TypeResolution, shape: TypeShape)(using ResolutionContext): DeclaredType =
    closed(new TypeResolution(source.source, source.fail), shape)

  /** A closed synthesized node that every use with the same cache key shares, such as a
    * Boolean combination of the same atoms. No use is its source, so its first use cannot
    * become the location or the error reporter of the others: diagnostics about a use cite
    * that use's own types and witnesses. Such a node is complete by construction, so
    * validating it can only report an internal error (`invalid`).
    */
  private[semantics] def shared(shape: TypeShape)(invalid: Ls[(Message, Opt[Loc])] => Unit)
      (using ResolutionContext): DeclaredType =
    closed(new TypeResolution(Term.Missing, invalid), shape)

  private def closed(resolution: TypeResolution, shape: TypeShape)(using ResolutionContext): DeclaredType =
    resolution.publish(shape)
    new DeclaredType(rctx.state.typeReferences(resolution, Map.empty, TypeSubstitution.empty, true, Nil), Map.empty)(N, N, S(shape))

  /** Canonical bindings retain only interned references. Per-use diagnostic
    * witnesses stay on DeclaredType and cannot keep extra data in the interner.
    */
  private[semantics] final class Bindings private[DeclaredType] (val values: Map[VarSymbol, ArgumentReference]) extends ValueKey:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), ValueKey.mapHash(values)(System.identityHashCode, _.hashCode))
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Bindings => values == that.values
      case _ => false

  /** Both endpoints use this pool's canonical proper-type references. */
  private[semantics] final class ArgumentReference(val input: Reference, val output: Reference) extends ValueKey:
    protected val valueHash: Int = ValueKey.hash(input.hashCode, output.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: ArgumentReference => (input eq that.input) && (output eq that.output)
      case _ => false

  private val emptyBindings = new Bindings(Map.empty)

  private[semantics] final class Reference private[DeclaredType] (val resolution: TypeResolution, val bindings: Bindings,
      val instances: TypeSubstitution, val positive: Bool, val namespaces: Ls[TypeAliasSymbol], val pool: References) extends ValueKey:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(resolution),
      bindings.hashCode, instances.hashCode, positive.hashCode, namespaces.hashCode)
    protected def sameValue(other: ValueKey): Bool = other match
      case that: Reference => equivalent(this, that)
      case _ => false

  /** One interning scope per consumer. Imported references are normalized into
    * it once, without writing to their defining units. A shared DAG is traversed
    * once on import and is then compared through canonical child references.
    */
  private[semantics] final class References(substitutions: scala.collection.mutable.Map[TypeSubstitution, TypeSubstitution]):
    private val bindings = scala.collection.mutable.HashMap.empty[Bindings, Bindings]
    private val references = scala.collection.mutable.HashMap.empty[Reference, Reference]
    private val imported = new java.util.IdentityHashMap[Reference, Reference]
    private[hkmc2] def size: Int = references.size
    private[hkmc2] def importedCount: Int = imported.size
    def local(reference: Reference): Reference =
      if reference.pool eq this then reference
      else
        val known = imported.get(reference)
        if known != null then known
        else
          val children = reference.bindings.values.iterator.map((symbol, child) => symbol -> new ArgumentReference(local(child.input), local(child.output))).toMap
          val result = intern(reference.resolution, internBindings(children),
            reference.instances, reference.positive, reference.namespaces)
          imported.put(reference, result)
          result
    def apply(resolution: TypeResolution, values: Map[VarSymbol, TypeArgument], instances: TypeSubstitution,
        positive: Bool, namespaces: Ls[TypeAliasSymbol]): Reference =
      val children = if values.isEmpty then Map.empty else values.iterator.map((symbol, tpe) => symbol -> new ArgumentReference(local(tpe.input.reference), local(tpe.output.reference))).toMap
      intern(resolution, internBindings(children), instances, positive, namespaces)
    /** Polarity, instances, and local namespaces do not change bound children.
      * Reuse their canonical map, importing it once if the source is foreign.
      */
    def updated(reference: Reference, instances: TypeSubstitution, positive: Bool, namespaces: Ls[TypeAliasSymbol]): Reference =
      intern(reference.resolution, local(reference).bindings, instances, positive, namespaces)
    private def internBindings(values: Map[VarSymbol, ArgumentReference]): Bindings =
      if values.isEmpty then emptyBindings else
        val binding = new Bindings(values)
        bindings.getOrElseUpdate(binding, binding)
    private def intern(resolution: TypeResolution, bindings: Bindings, instances: TypeSubstitution,
        positive: Bool, namespaces: Ls[TypeAliasSymbol]): Reference =
      val environment = if instances.isEmpty then TypeSubstitution.empty else substitutions.getOrElseUpdate(instances, instances)
      val reference = new Reference(resolution, bindings, environment, positive, namespaces, this)
      references.getOrElseUpdate(reference, reference)

  def apply(resolution: TypeResolution, bindings: Map[VarSymbol, TypeArgument],
      instances: TypeSubstitution, positive: Bool)(origin: Opt[TypeInterfaceReason])(using ResolutionContext): DeclaredType =
    new DeclaredType(rctx.state.typeReferences(resolution, bindings, instances, positive, Nil), bindings)(origin, N, N)

  /** Most comparisons stop at reference identity or canonical binding identity.
    * Separate units may retain equivalent DAGs: use a worklist for that boundary,
    * so two edges to a shared child never expand into two recursive traversals.
    * These comparisons only read imported data, including still-live graph nodes.
    */
  private def equivalent(left: Reference, right: Reference): Bool =
    if left eq right then true
    else if left.hashCode != right.hashCode then false
    else if left.pool eq right.pool then
      (left.resolution eq right.resolution) && (left.bindings eq right.bindings) &&
        (left.instances eq right.instances) && left.positive == right.positive && left.namespaces == right.namespaces
    else
      def sameHead(a: Reference, b: Reference): Bool =
        (a.resolution eq b.resolution) && a.positive == b.positive && a.instances == b.instances && a.namespaces == b.namespaces
      if !sameHead(left, right) then false
      else if left.bindings eq right.bindings then true
      else
        val seen = new java.util.IdentityHashMap[Reference, java.util.IdentityHashMap[Reference, java.lang.Boolean]]
        val pending = scala.collection.mutable.ArrayDeque.empty[Reference]
        pending.append(left)
        pending.append(right)
        var equal = true
        while equal && pending.nonEmpty do
          val a = pending.removeHead()
          val b = pending.removeHead()
          if a ne b then
            var partners = seen.get(a)
            if partners == null then
              partners = new java.util.IdentityHashMap
              seen.put(a, partners)
            if partners.put(b, java.lang.Boolean.TRUE) == null then
              if !sameHead(a, b) || a.bindings.values.size != b.bindings.values.size then equal = false
              else if a.bindings ne b.bindings then
                a.bindings.values.foreach: (symbol, child) =>
                  b.bindings.values.get(symbol) match
                    case S(other) =>
                      pending.append(child.input); pending.append(other.input)
                      pending.append(child.output); pending.append(other.output)
                    case N => equal = false
        equal

/** A type reference observed from a common comparison scope. The marks belong
  * to this endpoint: reversing a constraint swaps endpoints, not an expanded
  * candidate's already-normalized path.
  */
final class ContextualType(val tpe: DeclaredType, val marks: Ls[Marks]) extends ValueKey:
  override def toString: Str = s"ContextualType($tpe, $marks)"
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), tpe.hashCode, marks.hashCode)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: ContextualType => tpe == that.tpe && marks == that.marks
    case _ => false

/** Source arguments have their own category: a wildcard is valid only in an argument slot.
  * Its bounds are proper types and may still await forward resolution.
  */
enum TypeArgumentResolution:
  case Type(resolution: TypeResolution)
  case Wildcard(tree: Term, input: Opt[TypeResolution], output: Opt[TypeResolution])

  def source: Term = this match
    case Type(resolution) => resolution.source
    case Wildcard(tree, _, _) => tree

  def foreachType(f: TypeResolution => Unit): Unit = this match
    case Type(resolution) => f(resolution)
    case Wildcard(_, input, output) => input.foreach(f); output.foreach(f)

/** An unqualified argument is interpreted separately in the two polarities;
  * these parts coincide only when substitution gives the same type in both.
  * Missing wildcard parts are Nothing on input and Any on output, never holes.
  */
final class TypeArgument(val input: DeclaredType, val output: DeclaredType) extends ValueKey:
  /** Projection fixes the type before any constraint observes it. Deferred endpoints
    * remain proper type references; their later resolution cannot change this choice.
    */
  def at(positive: Bool): DeclaredType = if positive then output else input
  def map(f: DeclaredType => DeclaredType): TypeArgument =
    val in = f(input)
    val out = if input is output then in else f(output)
    if (in is input) && (out is output) then this else TypeArgument(in, out)
  def instantiate(instances: TypeSubstitution)(using ResolutionContext): TypeArgument = map(_.instantiate(instances))
  def swap: TypeArgument = TypeArgument(output, input)
  override def toString: Str = s"TypeArgument($input, $output)"
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), input.hashCode, output.hashCode)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: TypeArgument => input == that.input && output == that.output
    case _ => false

object TypeArgument:
  /** A type already interpreted at a scalar occurrence has the same meaning in both positions. */
  def invariant(tpe: DeclaredType): TypeArgument = TypeArgument(tpe, tpe)

/** An explicit binding at a parameter's declaration scope. `marks` records the
  * path taken into that scope, so constraints leaving through another activation
  * cannot reach this argument. Reads observe an instance of `argument.output`, which
  * NewResolver.bindTypeArguments publishes into the parameter's value host; incoming
  * constraints use `argument.input`, which a value host cannot represent.
  */
final case class TypeArgumentBinding(argument: TypeArgument, marks: Marks)

/** A quantified binder belongs to the source scheme; its bounds retain graph links
  * so mutually dependent bounds do not require expanding or copying their types.
  */
final class TypeQuantifier(val parameter: TypeShape.Parameter,
    val lower: Opt[TypeResolution], val upper: Opt[TypeResolution]) extends ValueKey:
  override def toString: Str = s"TypeQuantifier($parameter, $lower, $upper)"
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), parameter.hashCode, lower.hashCode, upper.hashCode)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: TypeQuantifier => parameter == that.parameter && lower == that.lower && upper == that.upper
    case _ => false

/** A callable's binder and bounds interpreted in the surrounding lexical bindings. */
final class DeclaredTypeParameter(val parameter: TypeShape.Parameter,
    val lower: Opt[DeclaredType], val upper: Opt[DeclaredType]) extends ValueKey:
  override def toString: Str = s"DeclaredTypeParameter($parameter, $lower, $upper)"
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), parameter.hashCode, lower.hashCode, upper.hashCode)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: DeclaredTypeParameter => parameter == that.parameter && lower == that.lower && upper == that.upper
    case _ => false

/** The owner is the original declaration, or a quantified annotation for an
  * anonymous callable. Applied and imported views retain this identity.
  */
final class TypeScheme(val owner: AnyDefinitionSymbol | TypeResolution, val parameters: Ls[DeclaredTypeParameter]) extends ValueKey:
  override def toString: Str = s"TypeScheme($owner, $parameters)"
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(owner), parameters.hashCode)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: TypeScheme => owner == that.owner && parameters == that.parameters
    case _ => false
