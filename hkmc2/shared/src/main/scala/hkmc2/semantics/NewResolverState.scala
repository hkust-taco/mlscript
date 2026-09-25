package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*

inline def rstate(using state: NewResolverState): NewResolverState = state

object NewResolverState:
  type Listener = TermShape => NewResolverState ?=> Unit

  /** Lazy source lookup preserves existing graph-node identities without copying
    * a unit's memo tables. Mutable bookkeeping values supply an explicit copier.
    */
  final class Cache[K, V](source: Opt[Cache[K, V]], copy: V => V):
    private val entries = mutable.Map.empty[K, V]
    private def peek(key: K): Opt[V] = entries.get(key).orElse(source.flatMap(_.peek(key)))
    def get(key: K): Opt[V] = entries.get(key).orElse:
      source.flatMap(_.peek(key)).map: value =>
        val local = copy(value)
        entries(key) = local
        local
    def getOrElseUpdate(key: K, value: => V): V = get(key).getOrElse:
      val result = value
      entries(key) = result
      result
    def update(key: K, value: V): Unit = entries(key) = value

  final class Seen[A](source: Opt[Seen[A]]):
    private val entries = mutable.Set.empty[A]
    def apply(value: A): Bool = entries(value) || source.exists(_(value))
    def add(value: A): Bool = if apply(value) then false else entries.add(value)

/** Inference belongs to the consuming compilation unit. Imported hosts retain their
  * completed candidates and contextual listeners; this state supplies private copies
  * before a consumer can extend either collection.
  */
final class NewResolverState private (
    val owner: Elaborator.State, private val consumer: Opt[NewResolverState], private val source: Opt[NewResolverState],
    private val contextBase: Opt[NewResolverState], val instances: Map[VarSymbol, TypeParameterInstance]):
  import NewResolverState.{Cache, Seen}

  def this(owner: Elaborator.State) = this(owner, N, N, N, Map.empty)
  private def root: NewResolverState = consumer.getOrElse(this)
  private def inherited: Opt[NewResolverState] = contextBase.orElse(source)
  private val contexts = mutable.Map.empty[(NewResolverState, Map[VarSymbol, TypeParameterInstance]), NewResolverState]
  /** Activations share the consuming unit's hosts and memoized source graph.
    * Only the finite substitution varies; composing views never adds a parent
    * context or changes either endpoint's originating graph.
    */
  def withInstances(substitution: Map[VarSymbol, TypeParameterInstance]): NewResolverState =
    val base = contextBase.getOrElse(this)
    if substitution.isEmpty then base
    else root.contexts.getOrElseUpdate((base, substitution),
      new NewResolverState(owner, S(root), source, S(base), substitution))
  private var reporter: Raise | Null = null
  def withReporter(raise: Raise): this.type =
    root.reporter = raise
    this
  def report(diagnostic: Diagnostic): Unit =
    assert(root.reporter != null, "Resolution requires a diagnostic collector")
    root.reporter.nn(diagnostic)

  def isOwnedSym(symbol: Symbol): Bool = symbol.getState is owner

  // A listener carries its defining graph, not its defining mutable resolver.
  // Views share the consumer's host copies, but consult the source's bindings and
  // memoized nodes individually. Creating a view never traverses a source map.
  private val views = mutable.Map.empty[NewResolverState, NewResolverState]
  private val inheritedViews = mutable.Map.empty[(NewResolverState, NewResolverState), NewResolverState]
  private[hkmc2] def inGraph(graph: NewResolverState): NewResolverState =
    rebase(graph.contextBase.getOrElse(graph), root).withInstances(instances)
  private def rebase(graph: NewResolverState, destination: NewResolverState): NewResolverState =
    val origin = source.fold(graph)(_.rebase(graph, destination))
    if origin.root eq root then origin
    else if root eq destination then
      root.views.getOrElseUpdate(origin, new NewResolverState(owner, S(root), S(origin), N, Map.empty))
    else root.views.get(origin).getOrElse:
      // A previously unused path can require a view of an intermediate exporter.
      // Memoize that read-only view in the consumer, never in the exporter.
      destination.inheritedViews.getOrElseUpdate((root, origin),
        new NewResolverState(owner, S(root), S(origin), N, Map.empty))

  private val copies = mutable.Map.empty[Publisher.Data[?], Publisher.Data[?]]
  private val pending = mutable.Map.empty[Identity[Publisher[?]], Publisher.Data[?]]
  private[hkmc2] def local[A](ref: Publisher.Data[A]): Publisher.Data[A] =
    // Explicit references (notably type parameters) need the same intermediate
    // exporter lookup as references through their syntax or symbol host.
    val origin = source.fold(ref)(_.peekReference(ref))
    if (origin.owner eq root) && !origin.completed then origin
    else
      // Each key and its copy share A; recover that type when looking up the
      // heterogeneous graph-node map.
      root.copies.getOrElseUpdate(origin, origin.copy(root)).asInstanceOf[Publisher.Data[A]]

  private def peekReference[A](ref: Publisher.Data[A]): Publisher.Data[A] =
    val origin = source.fold(ref)(_.peekReference(ref))
    root.copies.get(origin).fold(origin)(_.asInstanceOf[Publisher.Data[A]])

  private def peek[A](publisher: Publisher[A]): Publisher.Data[A] =
    peekReference(publisher.originalData)

  private[hkmc2] def data[A](publisher: Publisher[A]): Publisher.Data[A] =
    val ref = source.fold(publisher.initialData(root))(_.peek(publisher))
    if ref.owner == null then publisher.initialData(root)
    if publisher.isOwnedBy(root) && !root.completedNodes(new Identity(publisher)) then
      root.pending.getOrElseUpdate(new Identity(publisher), ref)
    local(ref)

  /** Number of lazily copied graph nodes, for isolation/scale regressions. */
  private[hkmc2] def copiedHostCount: Int = root.copies.size

  private val completedNodes = mutable.Set.empty[Identity[Publisher[?]]]

  /** Seal the decisions and original host data read by erasure/lowering. The
    * inference graph keeps private, live host data and all its listeners, so
    * later calls can still transport arguments and results through these nodes.
    * This boundary is per block, even when a worksheet reuses its symbol state.
    * Legacy blocks also need sealing: new-resolution consumers may import their
    * syntax concurrently, so no consumer may claim an unowned original host.
    */
  def completeBlock(block: Statement): Unit =
    val visited = mutable.Set.empty[Identity[Statement]]
    def pattern(pat: Pattern): Unit =
      pat match
        case ctor: Pattern.Constructor => data(ctor)
        case _ => ()
      pat.children.foreach:
        case child: Pattern => pattern(child)
        case term: Term => visit(term)
        case _ => ()
    def split(branches: SimpleSplit): Unit = branches match
      case SimpleSplit.Cons(SimpleSplit.Head.Match(_, pat, consequent), tail) =>
        pattern(pat)
        split(consequent)
        split(tail)
      case SimpleSplit.Cons(_, tail) => split(tail)
      case _ => ()
    def visit(statement: Statement): Unit = if visited.add(new Identity(statement)) then
      statement match
        // Bind even unused syntax to this unit. Otherwise its first consumer
        // could become the owner of an imported node's original listener buffer.
        case term: Term => data(term)
        case _ => ()
      statement match
        case cls: ClassLikeDef =>
          cls.ext.foreach(visit)
          cls.auxParams.foreach(_.subTerms.foreach(visit))
          cls match
            case pat: PatternDef => pattern(pat.pattern)
            case _ => ()
        case IfLike(_, _, branches) => split(branches)
        case Rcd(_, stats) => stats.foreach(visit)
        case Forall(params, _, _) =>
          params.foreach: param =>
            param.lb.foreach(visit)
            param.ub.foreach(visit)
        case New(_, _, refinement) => refinement.foreach(r => visit(r._2.blk))
        case _ => ()
      statement.subStatements.foreach(visit)
    visit(block)
    root.pending.foreach: (key, value) =>
      if !key.value.isInstanceOf[Symbol] && root.completedNodes.add(key) then value.completed = true
    root.pending.clear()

  def canResolve(host: Publisher[?]): Bool =
    data(host)
    host.isOwnedBy(root) && !root.completedNodes(new Identity(host))

  private val errors = mutable.Set.empty[Identity[PossiblyErroneous]]
  def hasError(host: PossiblyErroneous): Bool = host.isErroneous || root.errors(new Identity(host))
  def markError(host: Publisher[?] & PossiblyErroneous): Unit =
    root.errors += new Identity(host)
    if canResolve(host) then host.isErroneous = true

  /** Inference may refine an imported result, but the imported code has already
    * been compiled. Its member/constructor targets must remain unchanged.
    */
  def recordResolution(host: Publisher[?], unchanged: Bool)(update: => Unit): Unit =
    if !unchanged then
      assert(canResolve(host), "Inference changed a completed reference target")
      update

  val membersCache: Cache[(Identity[TermShape], Str), MemberLookup] =
    new Cache(inherited.map(_.membersCache), identity)
  val spreadInputs: Cache[Object, mutable.Set[TermShape]] =
    new Cache(inherited.map(_.spreadInputs), _.clone())
  val reportedArities: Cache[Object, mutable.Set[Int]] =
    new Cache(inherited.map(_.reportedArities), _.clone())
  val appShapes: Cache[(TermShape, FlowSymbol), AppShape] =
    new Cache(inherited.map(_.appShapes), identity)
  val newShapes: Cache[(ClassLikeSymbol, Ls[Marks], FlowSymbol, Opt[Ls[DeclaredType]]), NewShape] =
    new Cache(inherited.map(_.newShapes), identity)
  val constructorApplications: Seen[(NewShape, Map[VarSymbol, TypeParameterInstance])] =
    new Seen(inherited.map(_.constructorApplications))
  val introShapes: Cache[Identity[IntroTerm], IntroShape] =
    new Cache(inherited.map(_.introShapes), identity)
  val symShapes: Cache[(BlockMemberSymbol, FlowSymbol, Ls[Marks]), SymShape] =
    new Cache(inherited.map(_.symShapes), identity)
  val declaredSymShapes: Cache[(BlockMemberSymbol, FlowSymbol, Ls[Marks], Map[VarSymbol, DeclaredType], Bool), DeclaredSymShape] =
    new Cache(inherited.map(_.declaredSymShapes), identity)
  val selfShapes: Cache[InnerSymbol, BaseShape] =
    new Cache(inherited.map(_.selfShapes), identity)
  val defnShapes: Cache[DefinitionSymbol[?], DefnShape] =
    new Cache(inherited.map(_.defnShapes), identity)
  val typeInterpretations: Cache[Identity[Term], TypeResolution] =
    new Cache(inherited.map(_.typeInterpretations), identity)
  // Recorded before elaborating a declaration's members, including in legacy
  // exporters. Nominal interfaces may use any enclosing explicit type binder.
  val lexicalTypeBinders: Cache[AnyDefinitionSymbol, Set[VarSymbol]] =
    new Cache(inherited.map(_.lexicalTypeBinders), identity)
  val typeDependencies: Cache[TypeResolution, Set[VarSymbol]] =
    new Cache(inherited.map(_.typeDependencies), identity)
  val unguardedTypeDependencies: Cache[TypeResolution, Set[VarSymbol]] =
    new Cache(inherited.map(_.unguardedTypeDependencies), identity)
  val regularTypes: Cache[TypeResolution, Bool] =
    new Cache(inherited.map(_.regularTypes), identity)
  val combinedTypes: Cache[TypeFormula[DeclaredType], DeclaredType] =
    new Cache(inherited.map(_.combinedTypes), identity)
  val wildcardTypes: Cache[(TypeResolution, TypeArgument), DeclaredType] =
    new Cache(inherited.map(_.wildcardTypes), identity)
  val pendingTypeDependencies: Cache[TypeResolution, TypeDependencyHost] =
    new Cache(inherited.map(_.pendingTypeDependencies), identity)
  val dependencySubscriptions: Seen[(TypeResolution, TypeResolution)] =
    new Seen(inherited.map(_.dependencySubscriptions))
  val quantifiedTypes: Cache[(TypeResolution, Ls[VarSymbol]), TypeResolution] =
    new Cache(inherited.map(_.quantifiedTypes), identity)
  val instantiatedCallables: Cache[(CallableTypeShape, FlowSymbol, Ls[Marks]), CallableTypeShape] =
    new Cache(inherited.map(_.instantiatedCallables), identity)
  val contextualSymbols: Cache[(SymShape, Map[VarSymbol, TypeParameterInstance]), ContextualSymShape] =
    new Cache(inherited.map(_.contextualSymbols), identity)
  val shapeViews: Cache[(TermShape, Map[VarSymbol, TypeParameterInstance]), TermShape] =
    new Cache(inherited.map(_.shapeViews), identity)
  val activatedSymbols: Cache[(SymShape, Map[VarSymbol, TypeParameterInstance]), ActivatedSymShape] =
    new Cache(inherited.map(_.activatedSymbols), identity)
  val inferredInstantiations: Seen[(AnyDefinitionSymbol, FlowSymbol, Map[VarSymbol, TypeParameterInstance], Ls[Marks])] =
    new Seen(inherited.map(_.inferredInstantiations))
  // A scheme is owned by its source definition, or by the original interpretation
  // of an anonymous quantified annotation. Neither a view nor an instance is an owner.
  private val typeInstances: Cache[(AnyDefinitionSymbol | TypeResolution, FlowSymbol), Map[VarSymbol, TypeParameterInstance]] =
    new Cache(inherited.map(_.typeInstances), identity)
  private var allocatedTypeInstances: Int = 0
  private[hkmc2] def allocatedTypeInstanceCount: Int = root.allocatedTypeInstances
  private val typeApplicationSites: Cache[Identity[TyApp], FlowSymbol] =
    new Cache(inherited.map(_.typeApplicationSites), identity)
  /** A type application consumes a scheme even when no term argument follows.
    * Its site is shared across observations and activation views of the source.
    */
  def typeApplicationSite(application: TyApp): FlowSymbol =
    val key = new Identity(application)
    root.typeApplicationSites.getOrElseUpdate(key, typeApplicationSites.get(key).getOrElse(
      FlowSymbol("type application")(using owner)))
  private val fieldProjectionSites: Cache[BlockMemberSymbol, FlowSymbol] =
    new Cache(inherited.map(_.fieldProjectionSites), identity)
  /** A structural field constraint is a static projection site. Recursive
    * observations share it across substitution views; ordinary receiver marks
    * distinguish activations, as they do for a written member selection.
    */
  def fieldProjectionSite(field: BlockMemberSymbol): FlowSymbol =
    root.fieldProjectionSites.getOrElseUpdate(field, fieldProjectionSites.get(field).getOrElse(
      FlowSymbol.memSym(field)(using owner)))
  private[hkmc2] def instantiateTypeParameters(scheme: AnyDefinitionSymbol | TypeResolution,
      site: FlowSymbol, parameters: Ls[VarSymbol]): Map[VarSymbol, TypeParameterInstance] =
    require(parameters.distinct.length == parameters.length, "A scheme cannot bind a parameter twice")
    val origin = scheme match
      case constructor: ClassCtorSymbol => constructor.associatedCls
      case original => original
    val key = (origin, site)
    // Graph views in one consumer must agree even when they reach the same
    // source definition through different imports. Adopt an inherited group
    // before allocating, and put either result in the consumer's canonical cache.
    val instances = root.typeInstances.getOrElseUpdate(key, typeInstances.get(key).getOrElse {
      // Construct the complete group without activating constraints. Recursive
      // subscribers may use it only after the cache contains every binder.
      val result = parameters.map: parameter =>
        parameter -> new TypeParameterInstance(parameter)(using owner)
      root.allocatedTypeInstances += result.length
      result.toMap
    })
    assert(instances.keySet == parameters.toSet, "A source scheme's binders must remain stable")
    instances
  val typeViews: Cache[DeclaredType, TermShapeHost] =
    new Cache(inherited.map(_.typeViews), identity)
  val patternTypes: Cache[(Identity[Pattern.Constructor], InnerSymbol), DeclaredType] =
    new Cache(inherited.map(_.patternTypes), identity)
  val primitiveTypes: Cache[ClassSymbol, DeclaredType] =
    new Cache(inherited.map(_.primitiveTypes), identity)
  val extremeTypes: Cache[(Bool, Opt[TypeResolution]), DeclaredType] =
    new Cache(inherited.map(_.extremeTypes), identity)
  val variantTypes: Cache[(DeclaredType, Bool), DeclaredType] =
    new Cache(inherited.map(_.variantTypes), identity)
  val selectedArguments: Cache[(DeclaredType, Bool), DeclaredType] =
    new Cache(inherited.map(_.selectedArguments), identity)
  val abstractTypes: Cache[TypeResolution, DeclaredType] =
    new Cache(inherited.map(_.abstractTypes), identity)
  val omittedTypes: Cache[(TypeResolution, VarSymbol), DeclaredType] =
    new Cache(inherited.map(_.omittedTypes), identity)
  val exposedTypeHoles: Seen[(DeclaredType, TermShape, Ls[Marks])] =
    new Seen(inherited.map(_.exposedTypeHoles))
  val signatureParameters: Cache[VarSymbol, DeclaredType] =
    new Cache(inherited.map(_.signatureParameters), identity)
  val contextualTypes: Cache[ContextualType, DeclaredType] =
    new Cache(inherited.map(_.contextualTypes), identity)
  val tupleArrayParents: Cache[Identity[TupleShape], NominalInstanceView] =
    new Cache(inherited.map(_.tupleArrayParents), identity)
  val parameterTypes: Cache[TypeShape.Parameter, DeclaredType] =
    new Cache(inherited.map(_.parameterTypes), identity)
  val mutableArrays: Cache[Identity[Term.Mut], TermShape] =
    new Cache(inherited.map(_.mutableArrays), identity)
  // Named tuple fields have stable property identities, shared with consumers
  // through the tuple's original graph rather than allocated per spread candidate.
  val namedTupleRecords: Cache[Identity[Tup], Rcd] =
    new Cache(inherited.map(_.namedTupleRecords), identity)
  val aggregateProducers: Seen[Identity[Tup | Rcd]] =
    new Seen(inherited.map(_.aggregateProducers))
  // Whether a binder is supplied is fixed by its authoritative syntactic site.
  // Each definition/site has its own parameter instances; marks distinguish the
  // enclosing activations of their bounds, not whether the slot is explicit.
  // A method projection or nested constraint can change the observation scope
  // without changing this property. Missing supplied positions remain inferred.
  private val explicitTypeArguments = mutable.Set.empty[VarSymbol]
  def markExplicitTypeArgument(symbol: VarSymbol): Unit =
    root.explicitTypeArguments += symbol
  def hasExplicitTypeArgument(symbol: VarSymbol): Bool =
    root.explicitTypeArguments(symbol) || source.exists(_.hasExplicitTypeArgument(symbol))
  val typeConstraints: Seen[(DeclaredType, TermShape, Ls[Marks])] =
    new Seen(inherited.map(_.typeConstraints))
  val typeRelations: Seen[(ContextualType, ContextualType)] =
    new Seen(inherited.map(_.typeRelations))
  val typeArgumentArityErrors: Seen[(Identity[TyApp], Int)] =
    new Seen(inherited.map(_.typeArgumentArityErrors))

private[semantics] final class TermShapeHost extends Host[TermShape]:
  def showDbg(using DebugPrinter): Str = "instance views"
  def publish(shape: TermShape)(using NewResolverState): Unit =
    if currentShapes.add(shape) then notifyShapeListeners(shape)
  def listen(listener: NewResolverState.Listener)(using NewResolverState): Unit =
    subscribeToShapes(listener)

private[semantics] final class TypeDependencyHost extends Host[Set[VarSymbol]]:
  def showDbg(using DebugPrinter): Str = "type dependencies"
  def publish(binders: Set[VarSymbol])(using NewResolverState): Unit =
    if currentShapes.add(binders) then notifyShapeListeners(binders)
  def listen(listener: ShapeListener[Set[VarSymbol]])(using NewResolverState): Unit =
    subscribeToShapes(listener)
