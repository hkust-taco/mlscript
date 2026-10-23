package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import hkmc2.Message.MessageContext
import Term.*

inline def rctx(using context: ResolutionContext): ResolutionContext = context

object NewResolverState:
  /** Tables belong to a compilation unit; a context only selects a namespace.
    * An inherited lookup is read-only. Mutable values are copied into the
    * consumer's table before use, so extending an imported graph cannot change
    * its exporter. Allocate a namespace only when it receives an entry.
    */
  final class Cache[K, V](select: NewResolverState => Cache[K, V], copy: V => V):
    private val entries = mutable.Map.empty[ResolutionContext, mutable.Map[K, V]]
    // Null is only a lookup miss; stored values are non-null (including None).
    // Keep hits allocation-free despite looking up both a context and a key.
    private def own(key: K)(using context: ResolutionContext): V | Null =
      val scope = entries.getOrElse(context, null)
      if scope == null then null else scope.getOrElse(key, null)
    private def peek(key: K)(using context: ResolutionContext): V | Null =
      val value = own(key)
      if value != null then value else context.inherited match
        case S(parent) => select(parent.state).peek(key)(using parent)
        case N => null
    private def lookup(key: K)(using context: ResolutionContext): V | Null =
      assert(this eq select(context.state), "A resolver table must belong to the current consumer")
      val value = own(key)
      if value != null then value else context.inherited match
        case S(parent) =>
          val inherited = select(parent.state).peek(key)(using parent)
          if inherited == null then null else
            val local = copy(inherited.nn)
            update(key, local)
            local
        case N => null
    def get(key: K)(using ResolutionContext): Opt[V] =
      val value = lookup(key)
      if value == null then N else S(value.nn)
    def getOrElseUpdate(key: K, value: => V)(using ResolutionContext): V =
      val previous = lookup(key)
      if previous != null then previous.nn else
        val result = value
        update(key, result)
        result
    def update(key: K, value: V)(using context: ResolutionContext): Unit =
      assert(this eq select(context.state), "A resolver table must belong to the current consumer")
      assert(value != null, "Resolver cache values must be non-null")
      entries.getOrElseUpdate(context, mutable.Map.empty)(key) = value

  final class Seen[A](select: NewResolverState => Seen[A]):
    private val entries = mutable.Map.empty[ResolutionContext, mutable.Set[A]]
    def apply(value: A)(using context: ResolutionContext): Bool =
      assert(this eq select(context.state), "A resolver table must belong to the current consumer")
      val scope = entries.getOrElse(context, null)
      (scope != null && scope(value)) || (context.inherited match
        case S(parent) => select(parent.state)(value)(using parent)
        case N => false)
    def add(value: A)(using context: ResolutionContext): Bool =
      if apply(value) then false else entries.getOrElseUpdate(context, mutable.Set.empty).add(value)

/** Mutable inference storage owned by one compilation unit. Activations and
  * imported callbacks use immutable ResolutionContexts referring to this store;
  * they never allocate another resolver state or another set of memo tables.
  */
final class NewResolverState(val owner: Elaborator.State):
  import NewResolverState.{Cache, Seen}

  val context: ResolutionContext = new ResolutionContext(this, N, N, TypeSubstitution.empty)
  def isOwnedSym(symbol: Symbol): Bool = symbol.getState is owner
  private[semantics] val contexts = mutable.Map.empty[(ResolutionContext, TypeSubstitution), ResolutionContext]
  private[semantics] var reporter: Raise | Null = null
  private[semantics] val exposureInputs = mutable.LinkedHashMap.empty[(ShapeIdentity.Key, ResolutionContext), InterfaceExposure.Input]
  private[semantics] val views = mutable.Map.empty[ResolutionContext, ResolutionContext]
  private[semantics] val inheritedViews = mutable.Map.empty[(NewResolverState, ResolutionContext), ResolutionContext]
  private[semantics] val copies = mutable.Map.empty[Publisher.Data[?], Publisher.Data[?]]
  private[semantics] val pending = mutable.Map.empty[Identity[Publisher[?]], Publisher.Data[?]]
  private[semantics] val completedNodes = mutable.Set.empty[Identity[Publisher[?]]]
  private[semantics] val resolutionProblems =
    mutable.LinkedHashMap.empty[Identity[NewSel | App], mutable.ListBuffer[() => Ls[(Message, Opt[Loc])]]]
  // The references, selections, and instantiations written in this unit's current block,
  // with the lexical scope in which each is written (see ResolutionContext.checkAccess).
  private[semantics] val accessSites = mutable.ArrayBuffer.empty[(NewResolvable | New, SrcScope)]
  private[semantics] val errors = mutable.Set.empty[Identity[PossiblyErroneous]]
  private[semantics] val shapeIdentities = mutable.HashMap.empty[ShapeIdentity.View, ShapeIdentity.View]
  private[semantics] val substitutions = mutable.HashMap.empty[TypeSubstitution, TypeSubstitution]
  private[semantics] val typeReferences = new DeclaredType.References(substitutions)
  val membersCache: Cache[(TermShape, MemberKey), MemberLookup] =
    new Cache(_.membersCache, identity)
  // Shape components of cache keys use ShapeIdentity.key, like hosts' candidates.
  val spreadInputs: Cache[Object, mutable.Set[ShapeIdentity.Key]] =
    new Cache(_.spreadInputs, _.clone())
  val reportedArities: Cache[Object, mutable.Set[Int]] =
    new Cache(_.reportedArities, _.clone())
  // * The `FlowSymbol`s are currently used to uniquely identify terms
  val appShapes: Cache[(ShapeIdentity.Key, FlowSymbol), AppShape] =
    new Cache(_.appShapes, identity)
  val newShapes: Cache[(ClassValueTarget, Ls[Marks], FlowSymbol, Opt[Ls[DeclaredType]]), NewShape] =
    new Cache(_.newShapes, identity)
  val constructorApplications: Seen[(NewShape, TypeSubstitution)] =
    new Seen(_.constructorApplications)
  // Canonical producers anchor synthesized inference hosts (for example a
  // tuple's Array parent); their identities must survive reconstruction. Tuple and
  // record views are keyed by their effective binder substitution, so the same
  // view has one identity whichever sequence of substitutions produced it.
  private[semantics] val tupleShapes: Cache[(Term, Ls[TupleShape.Element], TypeSubstitution), TupleShape] =
    new Cache(_.tupleShapes, identity)
  private[semantics] val recordShapes: Cache[(Term.Rcd, Ls[RecordShape.Element], TypeSubstitution), RecordShape] =
    new Cache(_.recordShapes, identity)
  private[semantics] val instanceShapes: Cache[DeclaredType, InstanceShape] =
    new Cache(_.instanceShapes, identity)
  // Views constructed by this consumer, for allocation/growth regressions.
  // Adopted canonical producers are not newly allocated (see canonical).
  private[semantics] var allocatedShapeViews: Int = 0
  private[semantics] var largestShapeViewSubstitution: Int = 0
  // Stable iteration observations and joined elements for each spread operand.
  private[semantics] val spreadElements: Cache[Identity[Term], IterationFlow] =
    new Cache(_.spreadElements, identity)
  val introShapes: Cache[Identity[IntroTerm], IntroShape] =
    new Cache(_.introShapes, identity)
  val symShapes: Cache[(BlockMemberSymbol, FlowSymbol, Ls[Marks]), CoreSymShape] =
    new Cache(_.symShapes, identity)
  // Member `let`s have no TermDefinition body. Their initializers and subsequent
  // assignments feed this host, just as assignments feed a local variable.
  // Keep the host in resolver state so imported observations use the existing
  // consumer-local publisher machinery rather than mutating the source symbol.
  private[semantics] val memberVariables: Cache[TermSymbol, ShapeHost] =
    new Cache(_.memberVariables, identity)
  val declaredSymShapes: Cache[(BlockMemberSymbol, FlowSymbol, Ls[Marks], Map[VarSymbol, DeclaredType], Bool), DeclaredSymShape] =
    new Cache(_.declaredSymShapes, identity)
  val selfShapes: Cache[InnerSymbol, BaseShape] =
    new Cache(_.selfShapes, identity)
  val defnShapes: Cache[DefinitionSymbol[?], DefnShape] =
    new Cache(_.defnShapes, identity)
  // Parameterless definition bodies share a result node before following their
  // references. Keep distinct generic activations separate, and inherit the host
  // identity so imported listeners use the consumer's private publisher data.
  val byNameResults: Cache[(TermSymbol, TypeSubstitution), ShapeHost] =
    new Cache(_.byNameResults, identity)
  // Async payloads are deferred type edges, not snapshots of the body's current
  // candidates. Register each host before following recursive function results.
  val resultTypes: Cache[(Identity[Term], TypeSubstitution), DeclaredType] =
    new Cache(_.resultTypes, identity)
  // Keyed like inference candidates (see ShapeIdentity), so each candidate has one awaited type.
  val awaitedValues: Cache[(ShapeIdentity.Key, TypeSubstitution), DeclaredType] =
    new Cache(_.awaitedValues, identity)
  val typeInterpretations: Cache[Identity[Term], TypeResolution] =
    new Cache(_.typeInterpretations, identity)
  // Qualification can deliver the same declaration in several environments.
  // Its open source type is shared before any environment observes the body.
  val selectedTypes: Cache[(Identity[Term], TypeSymbol), TypeResolution] =
    new Cache(_.selectedTypes, identity)
  // Recorded before elaborating a declaration's members, including in legacy
  // exporters. Nominal interfaces may use any enclosing explicit type binder.
  // Term definitions record the binders enclosing their definition too, without
  // their own binders, which every application or specialization binds afresh.
  val lexicalTypeBinders: Cache[AnyDefinitionSymbol, Set[VarSymbol]] =
    new Cache(_.lexicalTypeBinders, identity)
  // The explicit type binders in scope where a term is written, for the terms
  // listed at Elaborator.withTypeBinders. The elaborator records them when
  // it creates the term, before any listener can build the term's shape, and
  // binds the term's inference owner at the same time; the resolver reads them
  // through that owner (see NewResolver.lexicalBinders), so an unowned term is
  // one that was never recorded. A synthesized record standing in for a tuple's
  // named fields is recorded by the resolver when it creates the record.
  private[semantics] val lexicalTermBinders: Cache[Identity[Term], Set[VarSymbol]] =
    new Cache(_.lexicalTermBinders, identity)
  // The explicit type binders in scope at the site a flow symbol identifies,
  // for every site where a by-name definition can be instantiated: a reference
  // or selection (recorded with its lexicalTermBinders), a type application, a
  // constructor pattern, or a structural field projection. A symbol shape keeps
  // its selection's flow symbol wherever the value flows, so the term observing
  // the shape is not the instantiation site. Recorded in, and read through, the
  // unit that creates the flow symbol (see ResolutionContext.siteBindersOf).
  private[semantics] val siteBinders: Cache[FlowSymbol, Set[VarSymbol]] =
    new Cache(_.siteBinders, identity)
  // Recorded with lexicalTypeBinders: the resolution scopes enclosing a type
  // definition. Declared members are located at their class's definition.
  val lexicalBoundaries: Cache[AnyDefinitionSymbol, Set[ResolutionBoundary]] =
    new Cache(_.lexicalBoundaries, identity)
  val typeDependencies: Cache[TypeResolution, Set[VarSymbol]] =
    new Cache(_.typeDependencies, identity)
  // Like typeDependencies, but following the references of synthesized nodes;
  // N when not fixed by the source graph (see NewResolver.instanceDependencies).
  val typeInstanceDependencies: Cache[TypeResolution, Opt[Set[VarSymbol]]] =
    new Cache(_.typeInstanceDependencies, identity)
  // How many type arguments a type reference receives where it is the base of
  // a type application, recorded when the application is interpreted. A generic
  // reference without a record is a bare use. Either is intrinsic to the
  // reference, so a cached dependency summary of its resolution does not depend
  // on which traversal reached it first (see NewResolver.dependencies). Read
  // through the reference's owning graph, like lexicalTermBinders.
  private[semantics] val appliedTypeArguments: Cache[Identity[Term], Int] =
    new Cache(_.appliedTypeArguments, identity)
  // The scope of the templates that a synthesized inferred-element or
  // omitted-argument host receives: the binders that reading its values through
  // a substitution can require, or N when that scope is not known. Recorded by
  // the resolver when it creates the host, in the host's owning graph.
  private[semantics] val templateBinders: Cache[TypeResolution, Opt[Set[VarSymbol]]] =
    new Cache(_.templateBinders, identity)
  val unguardedTypeDependencies: Cache[TypeResolution, Set[VarSymbol]] =
    new Cache(_.unguardedTypeDependencies, identity)
  val regularTypes: Cache[TypeResolution, Bool] =
    new Cache(_.regularTypes, identity)
  val combinedTypes: Cache[TypeFormula[DeclaredType], DeclaredType] =
    new Cache(_.combinedTypes, identity)
  val argumentTypes: Cache[(TypeResolution, TypeArgument), DeclaredType] =
    new Cache(_.argumentTypes, identity)
  val pendingTypeDependencies: Cache[TypeResolution, TypeDependencyHost] =
    new Cache(_.pendingTypeDependencies, identity)
  val dependencySubscriptions: Seen[(TypeResolution, TypeResolution)] =
    new Seen(_.dependencySubscriptions)
  val quantifiedTypes: Cache[(TypeResolution, Ls[VarSymbol]), TypeResolution] =
    new Cache(_.quantifiedTypes, identity)
  val instantiatedCallables: Cache[(ShapeIdentity.Key, FlowSymbol, Ls[Marks]), CallableTypeShape] =
    new Cache(_.instantiatedCallables, identity)
  val contextualSymbols: Cache[(CoreSymShape, TypeSubstitution), ContextualSymShape] =
    new Cache(_.contextualSymbols, identity)
  val inferredInstantiations: Seen[(AnyDefinitionSymbol, FlowSymbol, TypeSubstitution, Ls[Marks])] =
    new Seen(_.inferredInstantiations)
  // A scheme is owned by its source definition, or by the original interpretation
  // of an anonymous quantified annotation. Neither a view nor an instance is an owner.
  private[semantics] val typeInstances: Cache[(AnyDefinitionSymbol | TypeResolution, FlowSymbol), TypeSubstitution] =
    new Cache(_.typeInstances, identity)
  private[semantics] var allocatedTypeInstances: Int = 0
  private[semantics] val typeApplicationSites: Cache[Identity[TyApp], FlowSymbol] =
    new Cache(_.typeApplicationSites, identity)
  private[semantics] val fieldProjectionSites: Cache[BlockMemberSymbol, FlowSymbol] =
    new Cache(_.fieldProjectionSites, identity)
  // The flag selects merged member interfaces versus independent constraint inputs.
  val typeViews: Cache[(DeclaredType, Bool), TermShapeHost] =
    new Cache(_.typeViews, identity)
  val patternTypes: Cache[(Identity[Pattern.Constructor], InnerSymbol), DeclaredType] =
    new Cache(_.patternTypes, identity)
  // A pattern's unknown output has one source identity across repeated inputs.
  // Rebuilding its synthetic term on every match would create fresh candidates
  // in recursive pattern calls, where hosts compare source identities.
  private[semantics] val patternOutputs: Cache[Identity[Pattern], UnknownValueShape] =
    new Cache(_.patternOutputs, identity)
  // Repeated refinement of one input must reuse its synthesized type hosts.
  // Constructor paths distinguish references to the same captured class.
  val patternRefinements: Cache[(Identity[Pattern.Constructor], InnerSymbol, Ls[Marks], ShapeIdentity.Key), DeclaredType] =
    new Cache(_.patternRefinements, identity)
  val primitiveTypes: Cache[ClassSymbol, DeclaredType] =
    new Cache(_.primitiveTypes, identity)
  val extremeTypes: Cache[Bool, DeclaredType] =
    new Cache(_.extremeTypes, identity)
  val variantTypes: Cache[(DeclaredType, Bool), DeclaredType] =
    new Cache(_.variantTypes, identity)
  val selectedArguments: Cache[(DeclaredType, Bool), DeclaredType] =
    new Cache(_.selectedArguments, identity)
  val abstractTypes: Cache[TypeResolution, DeclaredType] =
    new Cache(_.abstractTypes, identity)
  val omittedTypes: Cache[(TypeResolution, VarSymbol), DeclaredType] =
    new Cache(_.omittedTypes, identity)
  val exposedTypeHoles: Seen[(DeclaredType, ShapeIdentity.Key, Ls[Marks])] =
    new Seen(_.exposedTypeHoles)
  val signatureParameters: Cache[VarSymbol, DeclaredType] =
    new Cache(_.signatureParameters, identity)
  // Synthesized applications share their type graph, including the symbolic arguments.
  val appliedTypes: Cache[(ClassSymbol | TypeAliasSymbol, Ls[DeclaredType]), DeclaredType] =
    new Cache(_.appliedTypes, identity)
  val contextualTypes: Cache[ContextualType, DeclaredType] =
    new Cache(_.contextualTypes, identity)
  val tupleArrayParents: Cache[Identity[TupleShape], NominalInstanceView] =
    new Cache(_.tupleArrayParents, identity)
  val parameterTypes: Cache[TypeShape.Parameter, DeclaredType] =
    new Cache(_.parameterTypes, identity)
  val mutableArrays: Cache[Identity[Term.Mut], TermShape] =
    new Cache(_.mutableArrays, identity)
  // Named tuple fields have stable property identities, shared with consumers
  // through the tuple's original graph rather than allocated per spread candidate.
  val namedTupleRecords: Cache[Identity[Tup | CtxTup], Rcd] =
    new Cache(_.namedTupleRecords, identity)
  val aggregateProducers: Seen[Identity[Tup | CtxTup | Rcd]] =
    new Seen(_.aggregateProducers)
  // Whether a binder is supplied is fixed by its authoritative syntactic site.
  // Each definition/site has its own parameter instances; marks distinguish the
  // enclosing activations of their bounds, not whether the slot is explicit.
  // A method projection or nested constraint can change the observation scope
  // without changing this property. Missing supplied positions remain inferred.
  private[semantics] val explicitTypeArguments = mutable.Set.empty[VarSymbol]
  private[semantics] val typeConstraints: Seen[(DeclaredType, ShapeIdentity.Key, Ls[Marks])] =
    new Seen(_.typeConstraints)
  val typeRelations: Seen[(ContextualType, ContextualType)] =
    new Seen(_.typeRelations)
  val typeArgumentArityErrors: Seen[(Identity[TyApp], Int)] =
    new Seen(_.typeArgumentArityErrors)
  val arrayIndexErrors: Seen[Identity[Term]] =
    new Seen(_.arrayIndexErrors)

object ResolutionContext:
  type Listener = TermShape => ResolutionContext ?=> Unit

/** The graph being observed and the active generic substitution. All contexts
  * of a consumer share its mutable state. The source records the import path,
  * including intermediate exporters' private inference, while contextBase
  * keeps substitution changes flat rather than building activation chains.
  */
final class ResolutionContext private[semantics] (
    val state: NewResolverState, private val source: Opt[ResolutionContext],
    private val contextBase: Opt[ResolutionContext], val instances: TypeSubstitution):
  import NewResolverState.Cache

  private given ResolutionContext = this
  def owner: Elaborator.State = state.owner
  private[semantics] def inherited: Opt[ResolutionContext] = contextBase.orElse(source)
  import state.*
  /** Activations share the consuming unit's hosts and memoized source graph.
    * Only the finite substitution varies; composing views never adds a parent
    * context or changes either endpoint's originating graph.
    */
  def withInstances(substitution: TypeSubstitution): ResolutionContext =
    val base = contextBase.getOrElse(this)
    val canonical = TypeSubstitution.canonical(substitution)
    if canonical.isEmpty then base
    else state.contexts.getOrElseUpdate((base, canonical),
      new ResolutionContext(state, source, S(base), canonical))
  def withReporter(raise: Raise): this.type =
    state.reporter = raise
    this
  def report(diagnostic: Diagnostic): Unit =
    assert(state.reporter != null, "Resolution requires a diagnostic collector")
    state.reporter.nn(diagnostic)
  def reportResolutionError(src: Term | Pattern, messages: Ls[(Message, Opt[Loc])]): Unit =
    report(ErrorReport(msg"Resolution error in ${src.describe}" -> src.toLoc :: messages, source = Diagnostic.Source.Compilation))

  // Annotation constraints record escaping implementations in the consuming
  // unit, including their activation context. The block's exposure pass drains
  // these roots before sealing resolution; they are neither copied from imports
  // nor retained across worksheet blocks. One witness suffices for each value.
  def exposeValue(shape: TermShape, provenance: ShapeProvenance): Unit =
    state.exposureInputs.getOrElseUpdate((ShapeIdentity.key(shape), this), InterfaceExposure.Input(shape, this)(provenance))
  def takeExposureInputs(): Ls[InterfaceExposure.Input] =
    val inputs = state.exposureInputs.values.toList
    state.exposureInputs.clear()
    inputs

  // A listener carries its defining graph, not its defining mutable resolver.
  // Views share the consumer's host copies, but consult the source's bindings and
  // memoized nodes individually. Creating a view never traverses a source map.
  private[hkmc2] def inGraph(graph: ResolutionContext): ResolutionContext =
    rebase(graph.contextBase.getOrElse(graph), state).withInstances(instances)
  private def rebase(graph: ResolutionContext, destination: NewResolverState): ResolutionContext =
    // A callback registered in this consuming unit already names its graph.
    // Sending it through the current import view would create X(Y(X(...)))
    // when an imported callback invokes a consumer callback and returns.
    if graph.state eq state then graph
    else
      val origin = source.fold(graph)(_.rebase(graph, destination))
      if origin.state eq state then origin
      else if state eq destination then
        state.views.getOrElseUpdate(origin, new ResolutionContext(state, S(origin), N, TypeSubstitution.empty))
      else state.views.get(origin).getOrElse:
        // A previously unused path can require a view of an intermediate exporter.
        // Memoize that read-only view in the consumer, never in the exporter.
        destination.inheritedViews.getOrElseUpdate((state, origin),
          new ResolutionContext(state, S(origin), N, TypeSubstitution.empty))

  private[hkmc2] def local[A](ref: Publisher.Data[A]): Publisher.Data[A] =
    // Explicit references (notably type parameters) need the same intermediate
    // exporter lookup as references through their syntax or symbol host.
    val origin = source.fold(ref)(_.peekReference(ref))
    if (origin.owner eq state) && !origin.completed then origin
    else
      // Each key and its copy share A; recover that type when looking up the
      // heterogeneous graph-node map.
      state.copies.getOrElseUpdate(origin, origin.copy(state)).asInstanceOf[Publisher.Data[A]]

  private def peekReference[A](ref: Publisher.Data[A]): Publisher.Data[A] =
    val origin = source.fold(ref)(_.peekReference(ref))
    state.copies.get(origin).fold(origin)(_.asInstanceOf[Publisher.Data[A]])

  private def peek[A](publisher: Publisher[A]): Publisher.Data[A] =
    peekReference(publisher.originalData)

  private[hkmc2] def data[A](publisher: Publisher[A]): Publisher.Data[A] =
    val ref = source.fold(publisher.initialData(state))(_.peek(publisher))
    if ref.owner == null then publisher.initialData(state)
    if publisher.isOwnedBy(state) && !state.completedNodes(new Identity(publisher)) then
      state.pending.getOrElseUpdate(new Identity(publisher), ref)
    local(ref)

  /** Number of lazily copied graph nodes, for isolation/scale regressions. */
  private[hkmc2] def copiedHostCount: Int = state.copies.size

  // A candidate can lack a member or be non-callable while another candidate
  // supplies a target later in inference. Retain lazy witnesses by use site,
  // including later activations of completed syntax, and report them together
  // at block completion. Eager problems invalidate the use immediately;
  // delaying their report lets the same error include every relevant witness.
  def resolutionProblem(term: NewSel | App, eager: Bool)(messages: => Ls[(Message, Opt[Loc])]): Unit =
    val key = new Identity[NewSel | App](term)
    // Accumulate witnesses for this block's error without replaying errors on
    // completed terms or adding follow-on errors to unrelated failures.
    if !hasError(term) || state.resolutionProblems.contains(key) then
      if eager then markError(term)
      state.resolutionProblems.getOrElseUpdate(key, mutable.ListBuffer.empty) += (() =>
        // Keep this observation's graph: an intermediate exporter can have
        // callable witnesses in its private copy of a third file's application.
        val unresolved = term match
          case selection: NewSel =>
            selection.resolvedTargets.isEmpty && !selection.hasDynamicTarget && selection.tupleIndex.isEmpty
          case application: App => application.callableTargets.currentShapes(using this).isEmpty
        if eager || unresolved then messages else Nil)

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
        case application: App => data(application.callableTargets)
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
    state.resolutionProblems.foreach: (key, problems) =>
      val term = key.value
      val messages = problems.iterator.flatMap(_()).toList.distinct
      if messages.nonEmpty then
        markError(term)
        reportResolutionError(term, messages)
    state.resolutionProblems.clear()
    state.accessSites.foreach: (term, scope) =>
      checkAccess(term, scope)
      // Access checks can insert already-resolved key expressions. Bind their
      // hosts to this unit before sealing, just like the written source terms.
      term match
        case ref: NewResolvable => ref.keyAccess.foreach(visit)
        case nw: New if nw.args.isEmpty && nw.rft.isEmpty => checkPartialInstantiation(nw)
        case _ => ()
    state.accessSites.clear()
    state.pending.foreach: (key, value) =>
      if !key.value.isInstanceOf[Symbol] && state.completedNodes.add(key) then value.completed = true
    state.pending.clear()

  /** Check the accessibility of the definitions that `term`, written in `scope`, refers to once
    * its block is complete, as its targets are only final then (see checkAccess). The elaborator
    * records the references, selections, and instantiations written in the source.
    */
  def recordAccessSite(term: NewResolvable | New, scope: SrcScope): Unit =
    state.accessSites += ((term, scope))

  /** Check written instantiations once their aliases and forward references have
    * resolved. Using the per-block source sites avoids repeating the warning when
    * generic functions are instantiated or their inference is imported elsewhere. */
  private def checkPartialInstantiation(term: New): Unit = if !hasError(term) then
    ClassValueShape.targetsOf(term).map(ClassValueShape.definitionOf).distinct match
      case cls :: Nil =>
        (cls.paramsOpt.toList ::: cls.auxParams) match
          case params :: Nil if params.paramCountLB == 0 && !params.flags.ctx =>
            val construction = term.toLoc.fold(s"new ${cls.sym.nme}"): loc =>
              loc.origin.fph.blockStr.slice(loc.spanStart, loc.spanEnd)
            report(WarningReport(
              msg"This 'new' expression partially applies class '${cls.sym.nme}' instead of constructing an instance." -> term.toLoc ::
              msg"Use `$construction()` to construct an instance, or `=> $construction()` to create an explicit zero-argument lambda." -> N ::
              msg"The constructor accepts an empty argument list." -> params.toLoc :: Nil))
          case _ => ()
      case _ => ()

  /** Private members are only accessible from within their owner and its companion (see
    * SrcScope.canAccessPrivatesOf); member lookups performed elsewhere skip them in favor of
    * inherited members (see MemberLookup.visibleFrom), so a reference written there only
    * targets a private member when there is no such alternative, which is an error.
    * Likewise, a private constructor is only accessible from within its class and its companion.
    * Both referring to the class's constructor function and instantiating the class with `new`,
    * including in another class's `extends` clause, access its constructor. Instantiating
    * a class through a variable also accesses the constructor of each class that the variable
    * may hold; calling a constructor function held by a variable does not, as the reference
    * that produced this function already did.
    * Finally, a reference that may target an accessible private member must target only that member:
    * see checkPrivateMix below.
    */
  private def checkAccess(term: NewResolvable | New, scope: SrcScope): Unit = if !hasError(term) then
    val loc = term match
      case ref: MemberRef => ref.toLoc
      case sel: NewSel => sel.id.toLoc
      case ref: UnresolvedRef => ref.id.toLoc
      case sup: Super => sup.id.toLoc
      case nw: New => nw.toLoc
    def declaredAt(definition: Definition): Opt[Loc] = definition match
      case td: TermDefinition => td.tsym.toLoc
      case _ => definition.sym.toLoc
    def checkPrivate(kind: Str, definition: Definition, owner: Opt[InnerSymbol]): Ls[Diagnostic] =
      if definition.visibility isnt Visibility.Private then Nil else owner match
        // File-private definitions are handled by compilation-unit exports.
        case S(_: TopLevelSymbol) | N => Nil
        case S(owner) => owner.asDefnSym.defn match
          case S(ownerDefn) if !scope.canAccessPrivatesOf(ownerDefn) =>
            ErrorReport(msg"Cannot access private $kind '${definition.bsym.nme}' outside its declaring owner" -> loc ::
              msg"private $kind declared here" -> declaredAt(definition) :: Nil,
              source = Diagnostic.Source.Compilation) :: Nil
          case _ => Nil
    /** The definition of `target` if it is a member stored privately at runtime,
      * along with a description of its kind. */
    def privateMember(target: DefinitionSymbol[?]): Opt[(Str, Definition)] =
      codegen.MemberStorage.sourcePrivateDefinition(target).map: definition =>
        val kind = target match
          case ctor: ClassCtorSymbol => ctor.associatedCls.describeKind
          case _: TermSymbol => "member"
          case _ => target.describeKind
        kind -> definition
    /** Lowering compiles a reference with several targets, or with a receiver of unknown shape, to a property access
      * (see Lowering.newSelection and Lowering.openSelection). That access cannot reach private storage, so it would
      * silently select another member for the receivers whose private member is accessible.
      * Since private members are never overridden, no other target can stand for a private target either. */
    def checkPrivateMix(ref: NewResolvable): Ls[Diagnostic] =
      val targets = ref.resolvedTargets.distinct
      val (privates, others) = targets.partitionMap(target => privateMember(target).toLeft(target))
      val dynamic = ref match
        case sel: NewSel => sel.hasDynamicTarget
        case ref: UnresolvedRef => ref.dynamicPrefixes.nonEmpty
        case _ => false
      if privates.isEmpty || targets.sizeIs == 1 && !dynamic then Nil
      else
        ErrorReport(
          msg"This reference may target a private member, which cannot be selected together with other members" -> loc ::
          privates.map((kind, definition) => msg"private $kind '${definition.bsym.nme}' declared here" -> declaredAt(definition)) :::
          others.map(target => msg"other target: ${target.describeKind} '${target.nme}'" -> target.toLoc) :::
          (if dynamic then msg"The receiver may also have a shape whose members are unknown" -> N :: Nil else Nil),
          source = Diagnostic.Source.Compilation) :: Nil
    def checkConstructor(cls: ClassDef): Ls[Diagnostic] = cls.privateCtor match
      case S(modifier) if !scope.canAccessPrivatesOf(cls) =>
        ErrorReport(msg"Cannot access the private constructor of class '${cls.sym.nme}' outside the class" -> loc ::
          msg"private constructor declared here" -> modifier.toLoc :: Nil, source = Diagnostic.Source.Compilation) :: Nil
      case _ => Nil
    val accessViolations = term match
      case nw: New =>
        ClassValueShape.targetsOf(nw).map(ClassValueShape.definitionOf).distinct.flatMap(checkConstructor)
      case ref: NewResolvable => ref.resolvedTargets.distinct.flatMap:
        case ctor: ClassCtorSymbol => ctor.associatedCls.defn.toList.flatMap: cls =>
          checkPrivate("class", cls, cls.owner) ::: checkConstructor(cls)
        case member: TermSymbol => member.defn.toList.flatMap(checkPrivate("member", _, member.owner))
        case member: InnerSymbol => member.asDefnSym.defn.toList.flatMap: definition =>
          checkPrivate(member.asDefnSym.describeKind, definition, definition.owner)
        case _ => Nil
    // An inaccessible private target, reported above, already explains why the reference is rejected.
    val violations =
      if accessViolations.nonEmpty then accessViolations
      else term match
        case ref: NewResolvable => checkPrivateMix(ref)
        case _: New => Nil
    if violations.nonEmpty then
      markError(term)
      violations.foreach(report)
    else term match
      case ref: NewResolvable =>
        // Overrides can have several targets but still share one property key.
        // Keep those targets and their flows; recover only their common operand.
        ref.resolvedTargets.map(_.asTrm.flatMap(_.defn).flatMap(MemberKey.symbol)).distinct match
          case S(key) :: Nil =>
            AccessPath.symbolKey(scope, key)(using state.owner) match
              case R(path) => ref.keyAccess = S(path)
              case L(AccessPath.Failure.PrivateMember(member)) =>
                markError(ref)
                report(ErrorReport(
                  msg"Cannot use @jsSymbol key '${key.name}' here: private member '${member.nme}' belongs to another file." -> loc ::
                    msg"The private member is declared here." -> member.toLoc ::
                    ref.resolvedTargets.distinct.map(target =>
                      msg"The keyed member '${target.nme}' is defined here." -> target.toLoc),
                  source = Diagnostic.Source.Compilation))
              case L(AccessPath.Failure.OutOfScope) =>
                markError(ref)
                report(ErrorReport(
                  msg"Cannot use @jsSymbol key '${key.name}' here: '${key.path.head.nme}' is not in scope." -> loc ::
                    msg"The key's root binding is defined here." -> key.path.head.toLoc :: Nil,
                  source = Diagnostic.Source.Compilation))
          case keys if keys.exists(_.nonEmpty) =>
            markError(ref)
            report(ErrorReport(
              msg"This reference has targets with different property keys." -> loc ::
                ref.resolvedTargets.distinct.map(target => msg"Candidate '${target.nme}' is declared here." -> target.toLoc),
              source = Diagnostic.Source.Compilation))
          case _ => ()
      case _: New => ()

  def canResolve(host: Publisher[?]): Bool =
    data(host)
    host.isOwnedBy(state) && !state.completedNodes(new Identity(host))

  def hasError(host: PossiblyErroneous): Bool = host.isErroneous || state.errors(new Identity(host))
  def markError(host: Publisher[?] & PossiblyErroneous): Unit =
    state.errors += new Identity(host)
    if canResolve(host) then host.isErroneous = true

  /** Inference may refine an imported result, but the imported code has already
    * been compiled. Its member/constructor targets must remain unchanged.
    */
  def recordResolution(host: Publisher[?], unchanged: Bool)(update: => Unit): Unit =
    if !unchanged then
      assert(canResolve(host), "Inference changed a completed reference target")
      update

  private[semantics] def shapeView[A](substitution: TypeSubstitution)(make: => A): A =
    if substitution.nonEmpty then
      state.allocatedShapeViews += 1
      state.largestShapeViewSubstitution = state.largestShapeViewSubstitution.max(substitution.size)
    make
  /** Number of shape views (substituted tuples, records, instances, interface
    * views, and contextual wrappers) newly constructed in the consuming unit. */
  private[hkmc2] def allocatedShapeViewCount: Int = state.allocatedShapeViews
  /** The largest binder substitution retained by any of those views. */
  private[hkmc2] def largestRetainedSubstitution: Int = state.largestShapeViewSubstitution
  /** Number of activation contexts created by withInstances in the consuming unit. */
  private[hkmc2] def activationContextCount: Int = state.contexts.size
  /** Activation views share their consumer's hosts, so they must also share its
    * canonical shapes. As for type instances, adopt an inherited shape before
    * constructing one, and record either result in the consumer's cache.
    * A shape built from another unit's syntax is looked up through that syntax's
    * owning graph, as for named tuple records, so importers reuse the exporter's
    * shape instead of adding an equal copy to imported hosts.
    */
  private def canonical[K, V](origin: Publisher[?] | Null, cache: NewResolverState => Cache[K, V], key: K)(make: => V): V =
    val graph = if origin == null then null else origin.originalData.owner
    val defining = if graph == null then this else inGraph(graph.context)
    cache(state).getOrElseUpdate(key, cache(defining.state).get(key)(using defining).getOrElse(make))(using state.context)
  def canonicalTuple(key: (Term, Ls[TupleShape.Element], TypeSubstitution))(make: => TupleShape): TupleShape =
    canonical(key._1, _.tupleShapes, key)(shapeView(key._3)(make))
  def canonicalRecord(key: (Term.Rcd, Ls[RecordShape.Element], TypeSubstitution))(make: => RecordShape): RecordShape =
    canonical(key._1, _.recordShapes, key)(shapeView(key._3)(make))
  def canonicalInstance(tpe: DeclaredType)(make: => InstanceShape): InstanceShape =
    canonical(tpe.resolution, _.instanceShapes, tpe)(shapeView(tpe.instances)(make))
  def spreadFlow(spread: Term)(make: => IterationFlow): IterationFlow =
    canonical(spread, _.spreadElements, new Identity(spread))(make)
  def memberVariable(symbol: TermSymbol): ShapeHost =
    state.memberVariables.getOrElseUpdate(symbol,
      symbol.getState.newResolverState.memberVariables.get(symbol)(using symbol.getState.newResolverState.context).getOrElse(
        new Host[ShapeEvent]:
          def showDbg(using DebugPrinter): Str = s"assignments to ${symbol.nme}"
      ))(using state.context)
  def recordLexicalBinders(term: Term, binders: Set[VarSymbol]): Unit =
    term.initialData(state)
    state.lexicalTermBinders.update(new Identity(term), binders)(using state.context)
    // A reference or selection is also the site where it invokes a by-name definition.
    val site = term match
      case ref: MemberRef => S(ref.resSym)
      case sel: NewSel => S(sel.resSym)
      case ref: UnresolvedRef => S(ref.resSym)
      case sup: Super => S(sup.resSym)
      case _ => N
    site.foreach(recordSiteBinders(_, binders))
  private[semantics] def lexicalBindersOf(term: Term): Opt[Set[VarSymbol]] =
    val graph = term.originalData.owner
    if graph == null then N else lexicalTermBinders.get(new Identity(term))(using inGraph(graph.context))
  def recordSiteBinders(site: FlowSymbol, binders: Set[VarSymbol]): Unit =
    assert(site.getState is owner, "A site's binders belong to the unit that creates its flow symbol")
    state.siteBinders.update(site, binders)(using state.context)
  private[semantics] def siteBindersOf(site: FlowSymbol): Opt[Set[VarSymbol]] =
    val graph = site.getState.newResolverState
    graph.siteBinders.get(site)(using graph.context)
  /** The type binders enclosing a definition, recorded in its own unit before its
    * members are elaborated (see Elaborator.recordDefinitionScope), even when the
    * definition is reached through an imported reference. */
  private[semantics] def definitionBindersOf(symbol: AnyDefinitionSymbol): Opt[Set[VarSymbol]] =
    val graph = symbol.getState.newResolverState
    graph.lexicalTypeBinders.get(symbol)(using graph.context)
  def recordAppliedTypeArguments(base: Term, count: Int): Unit =
    state.appliedTypeArguments.update(new Identity(base), count)(using state.context)
  private[semantics] def appliedTypeArgumentsOf(base: Term): Opt[Int] =
    val key = new Identity(base)
    val graph = base.originalData.owner
    (if graph == null then N else appliedTypeArguments.get(key)(using inGraph(graph.context))).orElse(appliedTypeArguments.get(key))
  def recordTemplateBinders(host: TypeResolution, binders: Opt[Set[VarSymbol]]): Unit =
    host.initialData(state)
    state.templateBinders.update(host, binders)(using state.context)
  private[semantics] def templateBindersOf(host: TypeResolution): Opt[Opt[Set[VarSymbol]]] =
    val graph = host.originalData.owner
    if graph == null then N else templateBinders.get(host)(using inGraph(graph.context))
  private[hkmc2] def allocatedTypeInstanceCount: Int = state.allocatedTypeInstances
  /** A type application consumes a scheme even when no term argument follows.
    * Its site is shared across observations and activation views of the source.
    */
  def typeApplicationSite(application: TyApp): FlowSymbol =
    val key = new Identity(application)
    state.typeApplicationSites.getOrElseUpdate(key, typeApplicationSites.get(key).getOrElse:
      val site = FlowSymbol("type application")(using owner)
      lexicalBindersOf(application).foreach(recordSiteBinders(site, _))
      site
    )(using state.context)
  /** A structural field constraint is a static projection site. Recursive
    * observations share it across substitution views; ordinary receiver marks
    * distinguish activations, as they do for a written member selection.
    */
  def fieldProjectionSite(field: BlockMemberSymbol): FlowSymbol =
    state.fieldProjectionSites.getOrElseUpdate(field, fieldProjectionSites.get(field).getOrElse:
      val site = FlowSymbol.memSym(field)(using owner)
      // The projection reads the field where its record type is written.
      field.tsym.flatMap(definitionBindersOf).foreach(recordSiteBinders(site, _))
      site
    )(using state.context)
  private[hkmc2] def instantiateTypeParameters(scheme: AnyDefinitionSymbol | TypeResolution,
      site: FlowSymbol, parameters: Ls[VarSymbol], siteBinders: Opt[Set[VarSymbol]]): TypeSubstitution =
    require(parameters.distinct.length == parameters.length, "A scheme cannot bind a parameter twice")
    val origin = scheme match
      case constructor: ClassCtorSymbol => constructor.associatedCls
      case original => original
    val key = (origin, site)
    // Graph views in one consumer must agree even when they reach the same
    // source definition through different imports. Adopt an inherited group
    // before allocating, and put either result in the consumer's canonical cache.
    val instances = state.typeInstances.getOrElseUpdate(key, typeInstances.get(key).getOrElse {
      // Construct the complete group without activating constraints. Recursive
      // subscribers may use it only after the cache contains every binder.
      val result = parameters.map: parameter =>
        new TypeParameterInstance(parameter, siteBinders)(using owner)
      state.allocatedTypeInstances += result.length
      TypeSubstitution(result)
    })(using state.context)
    assert(instances.keySet == parameters.toSet, "A source scheme's binders must remain stable")
    instances
  def patternOutput(pattern: Pattern)(make: => UnknownValueShape): UnknownValueShape =
    canonical(pattern, _.patternOutputs, new Identity(pattern))(make)
  def markExplicitTypeArgument(symbol: VarSymbol): Unit =
    state.explicitTypeArguments += symbol
  def hasExplicitTypeArgument(symbol: VarSymbol): Bool =
    state.explicitTypeArguments(symbol) || source.exists(_.hasExplicitTypeArgument(symbol))
  /** Whether this constraint is new; values are keyed like inference candidates.
    * Install each constraint edge before subscribing: callback parameter/result
    * flow can revisit it immediately. Distinct instantiations retain their marks.
    */
  def addTypeConstraint(tpe: DeclaredType, value: TermShape, marks: Ls[Marks]): Bool =
    typeConstraints.add((tpe, ShapeIdentity.key(value), marks))
  def hasTypeConstraint(tpe: DeclaredType, value: TermShape, marks: Ls[Marks]): Bool =
    typeConstraints((tpe, ShapeIdentity.key(value), marks))

/** One pair of call sites per spread source. Incoming alternatives share these
  * observations and the element host, so their Cartesian product is never built.
  * Publisher storage and listeners remain owned by the consuming resolution graph.
  */
private[semantics] final class IterationFlow(
    val elements: TypeResolution, val iterator: Term.App, val next: Term.App,
    val iteratorMember: FlowSymbol, val nextMember: FlowSymbol, val doneMember: FlowSymbol, val valueMember: FlowSymbol)

private[semantics] final class TermShapeHost extends Host[TermShape]:
  def showDbg(using DebugPrinter): Str = "instance views"
  def publish(shape: TermShape)(using ResolutionContext): Unit =
    if currentShapes.add(shape) then notifyShapeListeners(shape)
  def listen(listener: ResolutionContext.Listener)(using ResolutionContext): Unit =
    subscribeToShapes(listener)

private[semantics] final class TypeDependencyHost extends Host[Set[VarSymbol]]:
  def showDbg(using DebugPrinter): Str = "type dependencies"
  def publish(binders: Set[VarSymbol])(using ResolutionContext): Unit =
    if currentShapes.add(binders) then notifyShapeListeners(binders)
  def listen(listener: ShapeListener[Set[VarSymbol]])(using ResolutionContext): Unit =
    subscribeToShapes(listener)
