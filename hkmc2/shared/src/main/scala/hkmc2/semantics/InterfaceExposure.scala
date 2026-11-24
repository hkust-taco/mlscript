package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*
import hkmc2.Message.MessageContext
import ResolutionContext.Listener

object InterfaceExposure:
  final case class Input(shape: TermShape, state: ResolutionContext)(val provenance: ShapeProvenance)

  /** The path from a member's body out through its enclosing declarations. An absent site
    * accepts values from every invocation of those declarations. */
  def declarationExits(td: TermDefinition, site: Opt[FlowSymbol]): Ls[Marks] =
    def exits(scope: SrcScope): Ls[Marks] =
      val outer = scope.parent.fold[Ls[Marks]](Nil)(exits)
      scope.outer.resolutionBoundary.fold(outer)(sym => ExitMark(ResolutionBoundary(sym), site, NoMarks) :: outer)
    ExitMark(ResolutionBoundary(td.tsym), site, NoMarks) :: td.scope.toList.flatMap(exits)

  /** The unknown argument admitted by an external call and the value bound to the formal.
    * A rest formal receives a tuple of those unknown arguments. */
  def parameterInput(param: Param, rest: Bool, path: ShapeProvenance)(resolver: NewResolver)(using ResolutionContext): (UnknownValueShape, TermShape) =
    val ref = SimpleRef(param.sym)(N)
    val message = if rest then msg"Rest parameter '${param.sym.nme}' admits elements of unknown shape."
      else msg"Parameter '${param.sym.nme}' admits values of unknown shape."
    val unknown = UnknownValueShape(ref, fromPublicInterface = true)(path.via(message -> param.toLoc))
    val input = if rest then TupleShape(ref, TupleShape.Unknown(ref, TupleShape.ValueField(unknown, Nil)) :: Nil)(resolver)
      else unknown
    (unknown, input)

  /** The write admitted by a mutable field before any annotation restricts its representation. */
  def fieldInput(field: TermSymbol, source: Term, path: ShapeProvenance): UnknownValueShape =
    UnknownValueShape(source, fromPublicInterface = true)(path.via(
      // A mutable copy can also make an immutable record literal's field assignable.
      msg"Field '${field.nme}' admits assigned values of unknown shape." -> field.toLoc))

  def isPublic(definition: Definition): Bool =
    (definition.visibility is Visibility.Public) && (definition match
      case td: TermDefinition => (td.k isnt syntax.LetBind) || td.annotations.contains(Annot.Modifier(syntax.Keyword.`public`)(N))
      case _ => true)

/** Check the inputs admitted by the exposed interface before resolution is sealed.
  * Existing flow listeners propagate external inputs; temporary observers discover
  * escaping values incrementally. Calling a private helper does not expose it, but
  * returning that helper (possibly inside a record or tuple) does.
  */
final class InterfaceExposure(resolver: NewResolver)(using ResolutionContext, TL):
  private given Elaborator.State = rctx.owner
  private val work = mutable.Queue.empty[() => Unit]
  private val detach = mutable.ArrayBuffer.empty[() => Unit]
  private val watched = mutable.Set.empty[Any]
  // Keyed by ShapeIdentity.key, like inference hosts' candidates.
  private val exposed = mutable.Set.empty[ShapeIdentity.Key]
  private val sources = mutable.Map.empty[BlockMemberSymbol, MemberRef]
  private val exposedTypes = mutable.Set.empty[TypeResolution]
  // A class contributes its declarations once. A method that escapes separately can still expose
  // just its remaining parameter lists until the whole declaration is reached.
  private val admitted = mutable.Set.empty[ClassLikeDefSymbol | TermSymbol]
  // Each formal admits one external value, including the tuple allocated for a rest formal.
  // Different receivers or partial applications can still require different scope crossings.
  private val externalArguments = mutable.Map.empty[VarSymbol, (UnknownValueShape, TermShape)]
  private val declarationContext = rctx

  /** Forwarding edges belong to the inference graph. Only the final observer
    * captures this pass's queue and visited sets, and it is detached on exit.
    */
  private def watch(key: Any)(connect: Listener => Unit)(receive: Listener)(using state: ResolutionContext): Unit =
    if watched.add((key, state)) then
      val host = new TermShapeHost
      connect(host.publish)
      detach += host.inferenceHost.observe: shape =>
        val current = rctx
        work.enqueue(() => receive(shape)(using current))

  private type Path = ShapeProvenance

  private def term(value: Term, marks: Ls[Marks], path: Path)(using ResolutionContext): Unit =
    watch((value, marks))(resolver.listenTerm(value)): shape =>
      emit(shape.exit(marks), path)

  private def emit(shape: TermShape | NoShape, path: Path)(using ResolutionContext): Unit = shape match
    case shape: TermShape if exposed.add(ShapeIdentity.key(shape)) =>
      val current = rctx
      work.enqueue(() => exposeValue(shape, path)(using current))
    case _ => ()

  private def source(symbol: BlockMemberSymbol): MemberRef =
    val ref = sources.getOrElseUpdate(symbol, MemberRef(symbol)(N, FlowSymbol("exposed")))
    // An exported definition is invoked from outside the unit, where no binder is in scope.
    rctx.recordLexicalBinders(ref, Set.empty)
    ref

  /** Expose the public operations of every class named in an exported signature, in the written
    * type of an escaping value, or in a type reachable from either. An omitted type argument
    * admits unknown external values at any position. */
  private def exposeType(res: TypeResolution, path: Path)(using ResolutionContext): Unit = if exposedTypes.add(res) then
    detach += res.inferenceHost.observe: shape =>
      work.enqueue: () =>
        resolver.foreachOmittedArgument(res, shape): (param, hole) =>
          // The annotation can be far from the definition that exposes it, such as the result
          // type of a private function whose result an exported function returns.
          resolver.exposeTypeHoles(hole, UnknownValueShape(res.source, fromPublicInterface = true)(path.via(
            msg"Type argument '${param.sym.nme}' is omitted here and admits values of unknown shape." -> res.source.toLoc)))
          // The omitted argument may also carry an inferred value, such as a stored callback.
          emit(resolver.instanceShape(hole), path.via(
            msg"Type argument '${param.sym.nme}' is inferred here." -> res.source.toLoc))
        shape match
          case TypeShape.Nominal(cls) => members(cls, N, path)
          case TypeShape.Applied(base, args) =>
            exposeType(base, path)
            args.foreach(_.foreachType(arg => exposeType(arg, path.via(
              msg"This type argument appears in an exposed annotation." -> arg.source.toLoc))))
          case TypeShape.Record(_, fields) => fields.foreach: (field, arg) =>
            val at = path.via(msg"Field '${field.sym.nme}' is accessible here." -> field.toLoc)
            arg.foreachType(exposeType(_, at))
          case _ => resolver.foreachTypeComponent(shape)(exposeType(_, path))

  private def annotation(sign: Term, path: Path)(using ResolutionContext): Unit =
    exposeType(resolver.typeResolution(sign), path)

  private def signature(td: TermDefinition, path: Path)(using ResolutionContext): Unit =
    resolver.writtenSignature(td).foreach(annotation(_, path))
    td.params.foreach(_.allParams.foreach(_.sign.foreach(annotation(_, path))))

  /** Expose a member through its declaring class. Without a written result type, a caller
    * can obtain any value returned by the member or an override.
    */
  private def memberInterface(td: TermDefinition, path: Path)(using ResolutionContext): Unit =
    signature(td, path)
    if resolver.writtenSignature(td).isEmpty then
      memberResult(td, InterfaceExposure.declarationExits(td, N), path)(using declarationContext)

  private def memberResult(td: TermDefinition, marks: Ls[Marks], path: Path)(using ResolutionContext): Unit =
    if watched.add((td.tsym, marks, rctx)) then resolver.exposeMemberResult(td, marks, path)

  private def alias(symbol: BlockMemberSymbol, path: Path)(using ResolutionContext): Unit =
    symbol.asAls.flatMap(_.defn).filter(InterfaceExposure.isPublic).foreach(_.rhs.foreach(annotation(_, path)))

  private def member(symbol: BlockMemberSymbol, marks: Ls[Marks], path: Path)(using ResolutionContext): Unit =
    alias(symbol, path)
    if (symbol.getState is rctx.owner) && (symbol.asModOrObj.isDefined || symbol.asTrm.isDefined || symbol.asCls.isDefined) then
      val ref = source(symbol)
      def interpretation(receiver: Bool): Unit =
        resolver.valueTarget(symbol, receiver).flatMap(_.defn).filter(InterfaceExposure.isPublic).foreach: d =>
          d match
            case td: TermDefinition => signature(td, path)
            case _ => ()
          watch((symbol, marks, receiver))(
            resolver.fromBMS(symbol, ref.resSym, marks, _, ref, _ => (), receiver))(emit(_, path))
      interpretation(false)
      // Only expose the public interpretations of the name. A public factory
      // can hide its class; returning an instance still exposes that instance's members.
      if symbol.asModOrObj.isDefined && symbol.asTrm.isDefined then
        interpretation(true)
      // A term companion can hide the constructor in term position, but clients
      // still have access to the class through `new` and class projections.
      if symbol.asModOrObj.isDefined || symbol.asTrm.exists(!_.isInstanceOf[ClassCtorSymbol]) then
        symbol.asCls.flatMap(_.defn).filter(InterfaceExposure.isPublic).foreach: cls =>
          val resolver = this.resolver
          watch((cls.sym, marks))(listener => resolver.listenExt(cls, ext =>
            DefnShape(cls, ext).exit(ExitMark(ResolutionBoundary(cls.sym), S(ref.resSym), NoMarks)).exit(marks) match
              case shape: TermShape => listener(shape)
              case NoShape => ()))(emit(_, path))

  private def parameter(param: Param, rest: Bool, marks: Ls[Marks], path: Path, method: Opt[TermDefinition])(using ResolutionContext): Unit =
    if !rctx.state.isOwnedSym(param.sym) then return
    param.sign.foreach(annotation(_, path))
    // An inherited signature can arrive after this walk. Its listener only needs the resolver.
    val resolver = this.resolver
    if resolver.parameterSignature(param).isEmpty then
      val (unknown, input) = externalArguments.getOrElseUpdate(param.sym,
        InterfaceExposure.parameterInput(param, rest, path)(resolver))
      resolver.listenInheritedParameterType(method, param, marks):
        // The override already receives its inherited type from the base parameter.
        case S(tpe) => resolver.exposeTypeHoles(tpe, unknown)
        case N => resolver.publishParameter(param.sym, input.enter(marks))

  private def parameters(lists: Ls[(ParamList, Ls[Marks])], path: Path, method: Opt[TermDefinition])(using ResolutionContext): Unit =
    lists.foreach: (params, marks) =>
      params.params.foreach(parameter(_, false, marks, path, method))
      params.trailingParams.foreach(parameter(_, false, marks, path, method))
      params.variadic.foreach(v => parameter(v.param, true, marks, path, method))

  /** Records an exposed overridable member of a class or object that other compilation units may
    * extend. An override in such a unit inherits the member's parameter and result representations,
    * so [[codegen.OverrideChecks]] later requires them to be specified. Members of other classes and
    * objects are overridden only inside their own compilation unit and need no annotations.
    */
  private def recordOpenMember(cls: ClassLikeDef, td: TermDefinition, path: Path)(using ResolutionContext): Unit =
    // An imported class's members belong to the interface its own compilation unit exposes.
    if Inheritance.isExtensible(cls) && rctx.state.isOwnedSym(td.tsym) && Inheritance.isOpen(td)
        && !rctx.state.exposedOpenMembers.contains(td.tsym) then
      rctx.state.exposedOpenMembers(td.tsym) = path
  
  /** External calls cross the member's defining scopes even when only its class name escaped.
    * Rest tuples and captured input types need the same scope crossings as ordinary calls.
    */
  private def operation(td: TermDefinition, path: Path)(using ResolutionContext): Unit =
    memberInterface(td, path)
    val virtual = Inheritance.isOpen(td)
    if td.params.nonEmpty && (virtual || !Inheritance.isExternal(td)) then
      admitted += td.tsym
      val site = S(source(td.bsym).resSym)
      val inside = InterfaceExposure.declarationExits(td, site)
      parameters(td.params.map(_ -> inside), path, S(td))

  /** Expose a class's public operations and the type arguments supplied by an escaping receiver.
    * A receiver's marks locate its member values, and the current scope binds its type parameters.
    * A named type contributes arguments through its written annotation.
    */
  private def members(cls: ClassLikeDef, receiver: Opt[Ls[Marks]], path: Path)(using ResolutionContext): Unit =
    // A local argument can specialize an imported class or a class whose members we already visited.
    receiver.foreach: marks =>
      val instances = rctx.instances
      cls.tparams.foreach: param =>
        instances.get(param.sym).filter(rctx.hasExplicitTypeArgument).foreach: instance =>
          exposeSuppliedArgument(rctx.typeParameter(instance), instances, marks, path)
    if !rctx.state.isOwnedSym(cls.sym) then return
    val first = admitted.add(cls.sym)
    if first || receiver.nonEmpty then cls.body.blk.stats.foreach:
      case d: Definition if InterfaceExposure.isPublic(d) =>
        val memberPath = path.via(msg"Member '${d.bsym.nme}' is accessible here." -> d.headerLoc)
        d match
          case td: TermDefinition =>
            if first then
              recordOpenMember(cls, td, path)
              if td.k is syntax.MutVal then exposeWrite(td, MemberLookup.Found(td.bsym, Nil), path)(using declarationContext)
              operation(td, memberPath)(using declarationContext)
            receiver.foreach: marks =>
              if resolver.writtenSignature(td).nonEmpty then member(td.bsym, marks, memberPath)
          case _ => member(d.bsym, receiver.getOrElse(Nil), memberPath)
      case _ => ()
    cls.ext.foreach: parent =>
      val inherited = path.via(msg"This parent contributes inherited members." -> parent.toLoc)
      receiver match
        case S(marks) => term(parent, marks, inherited)
        // A class named in an annotation exposes its parent clause even if one of its instances
        // escaped first: `exposeType` visits the clause once. A class that only escapes by value
        // does not expose the clause as a type, because its parent can be a class value, as in
        // `class Derived extends storedClass(1)`, which no type denotes.
        case N => annotation(parent.cls, inherited)(using declarationContext)

  /** Admit what an external client can write through this field selection. */
  private def exposeWrite(field: TermDefinition, target: MemberLookup, path: Path)(using ResolutionContext): Unit =
    if rctx.state.isOwnedSym(field.tsym) && resolver.writtenSignature(field).isEmpty then
      val resolver = this.resolver
      val unknown = InterfaceExposure.fieldInput(field.tsym, source(field.bsym), path)
      resolver.resolveFieldWrite(target)((field, marks) => resolver.writeField(field, unknown, marks))(
        resolver.exposeTypeHoles(_, unknown))

  /** Expose the types that an application supplies for a formal parameter. A wildcard can
    * name different types on input and output, both of which occur in the exposed interface.
    */
  private def exposeSuppliedArgument(parameter: TypeShape.Parameter, instances: TypeSubstitution, marks: Ls[Marks], path: Path)
      (using ResolutionContext): Unit =
    detach += parameter.arguments.observe: binding =>
      // The binding carries the argument from the application site into the declaration.
      // From there the escaping value's marks lead back to the client.
      binding.argument.foreachBound: bound =>
        emit(resolver.instanceShape(bound.instantiate(instances)).exit(binding.marks).exit(marks),
          path.via(msg"This type argument is supplied here." -> bound.resolution.source.toLoc))

  /** Expose the interface of an escaping value whose type is written, such as the result of
    * a private function with a result annotation. Clients use the value at that type, so the
    * annotation is exposed like the signature of an exported definition (see `exposeType`).
    * The value also carries types and values that its annotation does not name. A local
    * ascription such as `Box(item) as Box` contributes the contents inferred for that box.
    * A generic call that returns `Box[T]` contributes the type supplied for T at that call.
    */
  private def declaredValue(tpe: DeclaredType, marks: Ls[Marks], path: Path)(using ResolutionContext): Unit =
    // Clients supply the arguments of an escaping function and the values written to an escaping
    // mutable record or instance. The written type restricts these inputs, except at its omitted
    // type arguments. Reading only the values inferred for such an argument would let
    // `private fun reader(): Box -> Str`, returned by an exported function without a result
    // annotation, receive boxes with contents that no local caller supplies.
    exposeType(tpe.resolution, path)
    def bound(part: DeclaredType, context: Ls[Marks])(using ResolutionContext): Unit =
      emit(resolver.instanceShape(part).exit(context), path)
    def candidate(value: TermShape)(using ResolutionContext): Unit =
      emit(resolver.instantiateShape(value, tpe.instances).exit(marks), path)
    detach += tpe.resolution.inferenceHost.observe: shape =>
      work.enqueue: () =>
        shape match
          case parameter: TypeShape.Parameter if !tpe.bindings.contains(parameter.symbol) =>
            // Written formals stay abstract until a call supplies an instance. Synthesized
            // element hosts can also read the original binder with an allocation-specific
            // scope path, as a mutable array literal does for the values stored in it.
            val target = tpe.instances.get(parameter.symbol).map(rctx.typeParameter).orElse:
              Option.when(parameter.symbol.isInstanceOf[TypeParameterInstance] ||
                rctx.templateBindersOf(tpe.resolution).nonEmpty)(parameter)
            target.foreach: actual =>
              if rctx.hasExplicitTypeArgument(actual.symbol) then exposeSuppliedArgument(actual, tpe.instances, marks, path)
              else watch((tpe, marks, "type argument"))(resolver.listenTypeParameterValues(actual))(candidate)
          case TypeShape.Hole(host) => watch((tpe, marks, "inferred argument"))(host.subscribe(_))(candidate)
          case TypeShape.Inferred(value) => candidate(value)
          case _ => ()
        resolver.foreachInterfaceComponent(tpe, shape)((part, inner) => bound(part, inner ::: marks))

  /** Expose the operations available on a value in its captured lexical scope. */
  private def exposeValue(value: TermShape, path: Path)(using origin: ResolutionContext): Unit =
    val ShapeParts(shape, lexical, supplied) = resolver.shapeParts(value)
    val instances = origin.instances.withOverrides(lexical)
    given ResolutionContext = origin.withInstances(instances)
    val (head, marks) = shape.applicationHead
    def exposeClassInterface(cls: ClassLikeDef): Unit =
      val memberContext = shape match
        case Marked(_: DefnShape, _) =>
          // A method returning its own class's constructor can bind the same parameters on its
          // receiver. The constructor keeps enclosing bindings and its own explicit arguments.
          val constructorContext = if supplied.nonEmpty then rctx
            else rctx.withInstances(instances.without(cls.tparams.iterator.map(_.sym)))
          if cls.paramsOpt.isEmpty then parameters(cls.auxParams.map(_ -> marks), path, N)(using constructorContext)
          constructorContext
        case _ => rctx
      members(cls, S(marks), path)(using memberContext)
    head match
      case _: (ContextualShape | SpecializedShape) => lastWords("A core application head cannot contain a substitution wrapper")
      case instance: InstanceShape =>
        declaredValue(instance.tpe, marks, path)
      case ds: DefnShape =>
        if rctx.state.isOwnedSym(ds.defn.sym) then ds.defn match
          case td: TermDefinition =>
            // A method may escape on its own, including after partial application.
            // A previously exposed class already admits calls to the whole method.
            if !admitted(td.tsym) then parameters(shape.unappliedParams, path, S(td))
            if ds.clsDef.isEmpty then
              signature(td, path)
              memberResult(td, marks, path)
          case _ => parameters(shape.unappliedParams, path, N)
        ds.clsDef.foreach(exposeClassInterface)
      case intro: IntroShape => intro.trm match
        case Lam(_, body) =>
          parameters(shape.unappliedParams, path, N)
          watch((body, marks, instances, "result"))(
            listener => resolver.listenResult(body)(listener)(using rctx.withInstances(instances))): shape =>
              emit(resolver.instantiateShape(shape, instances).exit(marks),
                path.via(msg"This value is returned here." -> body.toLoc))
        case _ => ()
      case tuple: TupleShape => tuple.segments.foreach: segment =>
        // A spread's length can be unknown while its elements still contain
        // private functions whose inputs become public through this tuple.
        val field = segment.element
        watch((tuple, field, marks))(resolver.listenTupleField(field)): shape =>
          emit(shape.exit(marks), path.via(msg"This value is stored in this tuple." -> tuple.source.toLoc))
      case record: RecordShape => record.foreachReadableField(marks, instances): (member, writable, context, bindings) =>
        val field = member.field
        val lookup = MemberLookup.Found(member, context)
        watch((field.tsym, member.mutable, context, bindings))(resolver.listenMemberValue(lookup,
          rctx.fieldProjectionSite(field.sym), field.rhs, bindings, () => ())): value =>
          emit(value, path.via(msg"This value is stored in this record field." -> field.toLoc))
        if writable then field.tsym.defn.foreach(exposeWrite(_, lookup.instantiate(bindings), path))
      case base: BaseShape => exposeClassInterface(base.defn)
      case callable: CallableTypeShape =>
        callable.declaration.filter(origin => rctx.state.isOwnedSym(origin.definition.tsym)).foreach: origin =>
          val td = origin.definition
          memberInterface(td, path)
          if !admitted(td.tsym) then
            parameters(origin.remaining.map(_ -> marks), path, S(td))
        // A callable can carry type arguments fixed by an earlier application.
        // Its remaining parameters can receive external values for any omitted arguments.
        val unknown = UnknownValueShape(callable.source, fromPublicInterface = true)(path)
        callable.paramLists.foreach: params =>
          params.allParams.flatMap(_.tpe).foreach: input =>
            unknown.enter(marks) match
              case value: TermShape => resolver.exposeTypeHoles(input, value)
              case NoShape => ()
        watch((ShapeIdentity.key(callable), marks, "call result"))(resolver.listenCallableResult(callable)): shape =>
          emit(shape.exit(marks), path)
      case nominal: NominalInstanceView =>
        members(nominal.defn, N, path)
        // Watch keys follow candidate identity, as `emit` does: hashing a nominal
        // view structurally would hash its class declaration's syntax.
        watch((ShapeIdentity.key(shape), "promise payload"))(listener => { resolver.listenPromisePayload(shape)(listener); () }): payload =>
          emit(payload, path.via(msg"This value is fulfilled by this promise." -> nominal.toLoc))
        // Array element bindings may contain escaping closures. Follow only the
        // declared binding; concrete annotations still hide implementation shapes.
        resolver.arrayElementType(nominal).foreach: binding =>
          watch((ShapeIdentity.key(shape), "array elements"))(listener => { resolver.listenArrayElements(shape)(listener); () }): element =>
            emit(element, path.via(msg"This value is stored in this array." -> binding.output.resolution.source.toLoc))
      // The written type already visits every structural field. Projecting these fields here
      // would generate a new record interface for every permutation in a recursive alias.
      case _: RecordTypeShape => ()
      case view: IntersectionView => view.values.foreach(value => emit(value.exit(marks), path))
      // Unknown and dynamic values have no static graph; namespace probes denote no value.
      case _: (OpaqueTypeShape | RigidTypeShape | UnknownValueShape | DynShape | ErrShape | NamespaceProbe) => ()

  /** An exposed value can be a synthesized local reference. Keep the exposure
    * site's location in its diagnostic provenance, not on that reference. */
  def check(exports: Ls[BlockMemberSymbol], values: Ls[(Term, Opt[Loc])]): Unit =
    try
      exports.foreach: symbol =>
        member(symbol, Nil, ShapeProvenance.empty.via(msg"'${symbol.nme}' is exposed by this compilation unit." -> symbol.headerLoc))
      values.foreach: (value, loc) =>
        term(value, Nil, ShapeProvenance.empty.via(msg"This value is exposed by this compilation unit." -> loc))
      // Annotated callbacks can escape even from private code. Delay their
      // exposure until the block is elaborated, so forward definitions and
      // returned closures are available. Processing one root may discover more.
      def pending(): Unit = rctx.takeExposureInputs().foreach: input =>
        emit(input.shape, input.provenance)(using input.state)
      pending()
      while work.nonEmpty do
        work.dequeue()()
        pending()
    finally detach.reverseIterator.foreach(_())
