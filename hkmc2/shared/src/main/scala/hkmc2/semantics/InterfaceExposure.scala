package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*
import hkmc2.Message.MessageContext
import ResolutionContext.Listener

object InterfaceExposure:
  final case class Input(shape: TermShape, state: ResolutionContext)(val provenance: ShapeProvenance)

  def isPublic(definition: Definition): Bool =
    (definition.visibility is Visibility.Public) && (definition match
      case td: TermDefinition => (td.k isnt syntax.LetBind) || td.annotations.contains(Annot.Modifier(syntax.Keyword.`public`)(N))
      case _: TypeDef => false
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
  private val flows = mutable.Map.empty[BlockMemberSymbol, FlowSymbol]

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
    watch((new Identity(value), marks))(resolver.listenTerm(value)): shape =>
      emit(shape.exit(marks), path)

  private def emit(shape: TermShape | NoShape, path: Path)(using ResolutionContext): Unit = shape match
    case shape: TermShape if exposed.add(ShapeIdentity.key(shape)) =>
      val current = rctx
      work.enqueue(() => value(shape, path)(using current))
    case _ => ()

  private def source(symbol: BlockMemberSymbol): MemberRef =
    val flow = flows.getOrElseUpdate(symbol, FlowSymbol("exposed"))
    val ref: MemberRef = MemberRef(symbol)(N, flow)
    // An exported definition is invoked from outside the unit, where no binder is in scope.
    rctx.recordLexicalBinders(ref, Set.empty)
    ref

  private def member(symbol: BlockMemberSymbol, marks: Ls[Marks], path: Path)(using ResolutionContext): Unit =
    if (symbol.getState is rctx.owner) && (symbol.asModOrObj.isDefined || symbol.asTrm.isDefined || symbol.asCls.isDefined) then
      val ref = source(symbol)
      def interpretation(receiver: Bool): Unit =
        if resolver.valueTarget(symbol, receiver).flatMap(_.defn).exists(InterfaceExposure.isPublic) then
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

  private def parameter(param: Param, marks: Ls[Marks], path: Path)(using ResolutionContext): Unit =
    val ref = SimpleRef(param.sym)(N)
    val unknown = UnknownValueShape(ref, fromPublicInterface = true)(path.via(
      msg"Parameter '${param.sym.nme}' admits values of unknown shape." -> param.toLoc))
    resolver.parameterSignature(param) match
      case N => resolver.constrainParameter(param, unknown.enter(marks), marks)
      case S(tpe) => unknown.enter(marks) match
        case value: TermShape => resolver.exposeTypeHoles(tpe.instantiate(rctx.instances), value, marks)
        case NoShape => ()

  private def parameters(lists: Ls[(ParamList, Ls[Marks])], path: Path)(using ResolutionContext): Unit =
    lists.foreach: (params, marks) =>
      params.params.foreach(parameter(_, marks, path))
      params.trailingParams.foreach(parameter(_, marks, path))
      params.variadic.map(_.param).foreach: rest =>
        val ref = SimpleRef(rest.sym)(N)
        val unknown = UnknownValueShape(ref, fromPublicInterface = true)(path.via(
          msg"Rest parameter '${rest.sym.nme}' admits elements of unknown shape." -> rest.toLoc))
        val tuple = TupleShape(ref, TupleShape.Unknown(ref, TupleShape.ValueField(unknown, Nil)) :: Nil)(resolver)
        resolver.constrainParameter(rest, tuple.enter(marks), marks)

  private def members(cls: ClassLikeDef, marks: Ls[Marks], path: Path)(using ResolutionContext): Unit =
    cls.body.blk.stats.foreach:
      case d: Definition if InterfaceExposure.isPublic(d) => member(d.bsym, marks, path.via(msg"Member '${d.bsym.nme}' is accessible here." -> d.headerLoc))
      case _ => ()
    cls.ext.foreach: parent =>
      term(parent, marks, path.via(msg"This parent contributes inherited members." -> parent.toLoc))

  private def result(body: Term, sign: Opt[Term], marks: Ls[Marks], path: Path)(using ResolutionContext): Unit = sign match
    case N =>
      watch((new Identity(body), marks, "result"))(resolver.listenResult(body)): shape =>
        emit(shape.exit(marks), path.via(msg"This value is returned here." -> body.toLoc))
    case S(sign) =>
      // checkDeclaredResult already checks the body during elaboration.
      // Exposure follows the declared result's interface.
      val declared = resolver.declaredType(resolver.typeResolution(sign), Map.empty).instantiate(rctx.instances)
      watch((declared, marks))(resolver.listenTypeInstances(declared)): shape =>
        emit(shape.exit(marks), path)

  private def value(shape: TermShape, path: Path)(using ResolutionContext): Unit = valueIn(shape, path, rctx.instances)

  private def valueIn(shape: TermShape, path: Path, instances: TypeSubstitution)(using ResolutionContext): Unit =
    val (head, marks) = shape.applicationHead
    def contextualTerm(value: Term, context: Ls[Marks], path: Path,
        substitution: TypeSubstitution)(using ResolutionContext): Unit =
      watch((new Identity(value), context, substitution))(
        listener => resolver.listenTerm(value)(listener)(using rctx.withInstances(substitution))): shape =>
          emit(resolver.instantiateShape(shape, substitution).exit(context), path)
    head match
      case contextual: ContextualShape => contextual.source.exit(marks) match
        case value: TermShape =>
          val substitution = instances.withOverrides(contextual.instances)
          valueIn(value, path, substitution)(using rctx.withInstances(substitution))
        case NoShape => ()
      case specialized: SpecializedShape =>
        resolver.instantiateShape(specialized.declaration, instances.withOverrides(specialized.instances)).exit(marks) match
          case value: TermShape => valueIn(value, path, instances)
          case NoShape => ()
      case _: InstanceShape =>
        watch((ShapeIdentity.key(shape), "instance view"))(resolver.listenInstanceViews(shape))(emit(_, path))
      case ds: DefnShape if ds.defn.sym.getState is rctx.owner =>
        parameters(shape.unappliedParams, path)
        ds.clsDef match
          case S(cls) =>
            // Exposing a constructor also exposes instances clients can create.
            shape match
              case Marked(_: DefnShape, _) if cls.paramsOpt.isEmpty =>
                parameters(cls.auxParams.map(_ -> marks), path)
              case _ => ()
            members(cls, marks, path)
          case N => ds.defn match
            case td: TermDefinition => td.body.foreach(result(_, resolver.resultSignature(td), marks, path))
            case _ => ()
      case _: DefnShape => () // Imported definitions were checked before publication.
      case intro: IntroShape => intro.trm match
        case Lam(_, body) =>
          parameters(shape.unappliedParams, path)
          watch((new Identity(body), marks, instances, "result"))(
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
      case record: RecordShape => record.elements.foreach:
        case RecordShape.Field(field) => contextualTerm(field.rhs, marks,
          path.via(msg"This value is stored in this record field." -> field.toLoc), instances.withOverrides(record.instances))
        case RecordShape.Spread(inner, context) =>
          emit(resolver.instantiateShape(inner, instances.withOverrides(record.instances)).exit(context).exit(marks), path)
        case _ => ()
      case base: BaseShape => members(base.defn, marks, path)
      case callable: CallableTypeShape =>
        // Written structure constrains external values; missing output parts
        // still admit unknown shapes even when local callers supplied evidence.
        val unknown = UnknownValueShape(callable.source, fromPublicInterface = true)(path)
        callable.paramLists.foreach: params =>
          params.allParams.flatMap(_.tpe).foreach: input =>
            unknown.enter(marks) match
              case value: TermShape => resolver.exposeTypeHoles(input, value, marks)
              case NoShape => ()
        watch((ShapeIdentity.key(callable), marks, "call result"))(resolver.listenCallableResult(callable)): shape =>
          emit(shape.exit(marks), path)
      case nominal: NominalInstanceView =>
        // Watch keys follow candidate identity, as `emit` does: hashing a nominal
        // view structurally would hash its class declaration's syntax.
        watch((ShapeIdentity.key(shape), "promise payload"))(listener => { resolver.listenPromisePayload(shape)(listener); () }): payload =>
          emit(payload, path.via(msg"This value is fulfilled by this promise." -> nominal.toLoc))
        // Array element bindings may contain escaping closures. Follow only the
        // declared binding; concrete annotations still hide implementation shapes.
        resolver.arrayElementType(nominal).foreach: binding =>
          watch((ShapeIdentity.key(shape), "array elements"))(listener => { resolver.listenArrayElements(shape)(listener); () }): element =>
            emit(element, path.via(msg"This value is stored in this array." -> binding.resolution.source.toLoc))
      case view: IntersectionView => view.values.foreach(value => emit(value.exit(marks), path))
      // Structural annotations hide initializer implementations. Unknown and
      // dynamic values have no static graph.
      case _: (RecordTypeShape | OpaqueTypeShape | UnknownValueShape | RigidTypeShape | DynShape | ErrShape) => ()

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
