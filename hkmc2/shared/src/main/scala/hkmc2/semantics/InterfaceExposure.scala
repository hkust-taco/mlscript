package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*
import hkmc2.Message.MessageContext
import NewResolverState.Listener

object InterfaceExposure:
  def isPublic(definition: Definition): Bool =
    !definition.annotations.contains(Annot.Private) && (definition match
      case td: TermDefinition => (td.k isnt syntax.LetBind) || td.annotations.contains(Annot.Modifier(syntax.Keyword.`public`))
      case _: TypeDef => false
      case _ => true)

/** Check the inputs admitted by the exposed interface before resolution is sealed.
  * Existing flow listeners propagate external inputs; temporary observers discover
  * escaping values incrementally. Calling a private helper does not expose it, but
  * returning that helper (possibly inside a record or tuple) does.
  */
final class InterfaceExposure(resolver: NewResolver)(using NewResolverState, TL):
  private given Elaborator.State = rstate.owner
  private val work = mutable.Queue.empty[() => Unit]
  private val detach = mutable.ArrayBuffer.empty[() => Unit]
  private val watched = mutable.Set.empty[Any]
  private val exposed = mutable.Set.empty[TermShape]
  private val flows = mutable.Map.empty[BlockMemberSymbol, FlowSymbol]

  /** Forwarding edges belong to the inference graph. Only the final observer
    * captures this pass's queue and visited sets, and it is detached on exit.
    */
  private def watch(key: Any)(connect: Listener => Unit)(receive: Listener)(using state: NewResolverState): Unit =
    if watched.add((key, state)) then
      val host = new TermShapeHost
      connect(host.publish)
      detach += host.inferenceHost.observe: shape =>
        val current = rstate
        work.enqueue(() => receive(shape)(using current))

  private type Path = ShapeProvenance

  private def term(value: Term, marks: Ls[Marks], path: Path)(using NewResolverState): Unit =
    watch((new Identity(value), marks))(resolver.listenTerm(value)): shape =>
      emit(shape.exit(marks), path)

  private def emit(shape: TermShape | NoShape, path: Path)(using NewResolverState): Unit = shape match
    case shape: TermShape if exposed.add(shape) =>
      val current = rstate
      work.enqueue(() => value(shape, path)(using current))
    case _ => ()

  private def source(symbol: BlockMemberSymbol): MemberRef =
    val flow = flows.getOrElseUpdate(symbol, FlowSymbol("exposed"))
    MemberRef(symbol)(new syntax.Tree.Ident(symbol.nme).withLocOf(symbol), flow)

  private def member(symbol: BlockMemberSymbol, marks: Ls[Marks], path: Path)(using NewResolverState): Unit =
    if (symbol.getState is rstate.owner) && (symbol.asModOrObj.isDefined || symbol.asTrm.isDefined || symbol.asCls.isDefined) then
      val ref = source(symbol)
      watch((symbol, marks))(resolver.fromBMS(symbol, ref.resSym, marks, _, ref, _ => (), false))(emit(_, path))
      // Both overloads are public: selecting a module member must not hide the
      // function's inputs, and exposing a function must not hide module members.
      if symbol.asModOrObj.isDefined && symbol.asTrm.isDefined then
        watch((symbol, marks, true))(resolver.fromBMS(symbol, ref.resSym, marks, _, ref, _ => (), true))(emit(_, path))
      // A term companion can hide the constructor in term position, but clients
      // still have access to the class through `new` and class projections.
      if symbol.asModOrObj.isDefined || symbol.asTrm.exists(!_.isInstanceOf[ClassCtorSymbol]) then
        symbol.asCls.flatMap(_.defn).foreach: cls =>
          val resolver = this.resolver
          watch((cls.sym, marks))(listener => resolver.listenExt(cls, ext =>
            DefnShape(cls, ext).exit(ExitMark(ResolutionBoundary(cls.sym), S(ref.resSym), NoMarks)).exit(marks) match
              case shape: TermShape => listener(shape)
              case NoShape => ()))(emit(_, path))

  private def parameter(param: Param, marks: Ls[Marks], path: Path)(using NewResolverState): Unit = if resolver.parameterSignature(param).isEmpty then
    val ref = SimpleRef(param.sym)(param.sym.id)
    val unknown = UnknownValueShape(ref)(ShapeProvenance(
      (msg"Parameter '${param.sym.nme}' admits values of unknown shape." -> param.toLoc) :: path.diagnosticNotes))
    resolver.constrainParameter(param, unknown.enter(marks), marks)

  private def parameters(lists: Ls[(ParamList, Ls[Marks])], path: Path)(using NewResolverState): Unit =
    lists.foreach: (params, marks) =>
      params.params.foreach(parameter(_, marks, path))
      params.restParam.foreach: rest =>
        val ref = SimpleRef(rest.sym)(rest.sym.id)
        val unknown = UnknownValueShape(ref)(ShapeProvenance(
          (msg"Rest parameter '${rest.sym.nme}' admits elements of unknown shape." -> rest.toLoc) :: path.diagnosticNotes))
        val tuple = TupleShape(ref, TupleShape.Unknown(ref, Nil, unknown) :: Nil)(resolver)
        resolver.constrainParameter(rest, tuple.enter(marks), marks)

  private def members(cls: ClassLikeDef, marks: Ls[Marks], path: Path)(using NewResolverState): Unit =
    cls.body.blk.stats.foreach:
      case d: Definition if InterfaceExposure.isPublic(d) => member(d.bsym, marks, path.via(msg"Member '${d.bsym.nme}' is accessible here." -> d.toLoc))
      case _ => ()
    cls.ext.foreach: parent =>
      term(parent, marks, path.via(msg"This parent contributes inherited members." -> parent.toLoc))

  private def result(body: Term, sign: Opt[Term], marks: Ls[Marks], path: Path)(using NewResolverState): Unit = sign match
    case N => term(body, marks, path.via(msg"This value is returned here." -> body.toLoc))
    case S(sign) =>
      // Check returned implementations against the declared calling interface.
      // Its parameter types constrain returned closures instead of unrestricted
      // unknowns, and consumers see only the annotated result.
      val declared = resolver.declaredType(resolver.typeResolution(sign), Map.empty).instantiate(rstate.instances)
      watch((new Identity(body), declared, marks))(resolver.listenTerm(body)): shape =>
        resolver.constrainFunction(declared, shape, marks)
      watch((declared, marks))(resolver.listenTypeInstances(declared)): shape =>
        emit(shape.exit(marks), path)

  private def value(shape: TermShape, path: Path)(using NewResolverState): Unit = valueIn(shape, path, rstate.instances)

  private def valueIn(shape: TermShape, path: Path, instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit =
    val (head, marks) = shape.applicationHead
    def contextualTerm(value: Term, context: Ls[Marks], path: Path,
        substitution: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit =
      watch((new Identity(value), context, substitution))(
        listener => resolver.listenTerm(value)(listener)(using rstate.withInstances(substitution))): shape =>
          emit(resolver.instantiateShape(shape, substitution).exit(context), path)
    head match
      case _: ActivatedShape => lastWords("Exposure must observe values after activation dispatch")
      case contextual: ContextualShape => contextual.source.exit(marks) match
        case value: TermShape =>
          val substitution = instances ++ contextual.instances
          valueIn(value, path, substitution)(using rstate.withInstances(substitution))
        case NoShape => ()
      case _: InstanceShape =>
        watch((shape, "instance view"))(resolver.listenInstanceViews(shape))(emit(_, path))
      case ds: DefnShape if ds.defn.sym.getState is rstate.owner =>
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
          contextualTerm(body, marks, path.via(msg"This value is returned here." -> body.toLoc), instances)
        case _ => ()
      case tuple: TupleShape => tuple.segments.foreach:
        case field: TupleShape.Fixed =>
          watch((tuple, field, marks))(resolver.listenTupleField(field)): shape =>
            emit(shape.exit(marks), path.via(msg"This value is stored in this tuple." -> tuple.source.toLoc))
        case _ => ()
      case record: RecordShape => record.elements.foreach:
        case RecordShape.Field(field) => contextualTerm(field.rhs, marks,
          path.via(msg"This value is stored in this record field." -> field.toLoc), instances ++ record.instances)
        case RecordShape.Spread(inner, context) =>
          emit(resolver.instantiateShape(inner, instances ++ record.instances).exit(context).exit(marks), path)
        case _ => ()
      case base: BaseShape => members(base.defn, marks, path)
      case callable: CallableTypeShape =>
        callable.result.foreach: result =>
          watch((result, marks))(resolver.listenTypeInstances(result)): shape =>
            emit(shape.exit(marks), path)
      case nominal: NominalInstanceView =>
        // Array element bindings may contain escaping closures. Follow only the
        // declared binding; concrete annotations still hide implementation shapes.
        resolver.arrayElementType(nominal).foreach: binding =>
          watch((shape, "array elements"))(listener => { resolver.listenArrayElements(shape)(listener); () }): element =>
            emit(element, path.via(msg"This value is stored in this array." -> binding.resolution.source.toLoc))
      // Structural annotations hide initializer implementations. Unknown and
      // dynamic values have no static graph.
      case _: (RecordTypeShape | OpaqueTypeShape | UnknownValueShape | RigidTypeShape | DynShape | ErrShape) => ()

  def check(exports: Ls[BlockMemberSymbol], values: Ls[Term]): Unit =
    try
      exports.foreach: symbol =>
        member(symbol, Nil, ShapeProvenance.empty.via(msg"'${symbol.nme}' is exposed by this compilation unit." -> symbol.toLoc))
      values.foreach: value =>
        term(value, Nil, ShapeProvenance.empty.via(msg"This value is exposed by this compilation unit." -> value.toLoc))
      while work.nonEmpty do work.dequeue()()
    finally detach.reverseIterator.foreach(_())
