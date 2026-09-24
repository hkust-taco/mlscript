package hkmc2
package semantics

import scala.collection.mutable
import scala.annotation.tailrec

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.Message.MessageContext
import hkmc2.io
import utils.TraceLogger
import syntax.*
// import Tree.*
import Term.*

import Elaborator.*
import hkmc2.syntax.LetBind


class NewResolver:
  self: Elaborator =>
  import tl.*
  import NewResolverState.Listener
  
  /* 
  class Constraint(val lhs: Term, val rhs: Term):
    override def equals(obj: Any): Bool = obj match
      case that: Constraint => (this.lhs is that.lhs) && (this.rhs is that.rhs)
      case _ => false
    private var _hash: Int = 0
    override def hashCode(): Int = 
      if _hash =/= 0 then _hash
      else
        var h = lhs.hashCode() * 31 + rhs.hashCode()
        if h === 0 then h += 1
        _hash = h
        h
    def showDbg(using DebugPrinter): Str =
      s"${lhs.showDbg} <: ${rhs.showDbg}"
  
  val processedConstraints: mutable.Set[Constraint] = mutable.Set.empty
  val collectedConstraints: mutable.Buffer[Constraint] = mutable.Buffer.empty
  */
  
  // * The `FlowSymbol`s are currently used to uniquely identify terms
  private def appShapes(using rs: NewResolverState) = rs.appShapes
  private def newShapes(using rs: NewResolverState) = rs.newShapes
  private def introShapes(using rs: NewResolverState) = rs.introShapes
  private def symShapes(using rs: NewResolverState) = rs.symShapes
  private def declaredSymShapes(using rs: NewResolverState) = rs.declaredSymShapes
  private def selfShapes(using rs: NewResolverState) = rs.selfShapes
  // Tuple and record AST nodes for which we have subscribed to spread operands.
  // Each node owns its shapes and listeners. Comparing nodes by structural equality
  // would skip subscriptions for a second equal expression, leaving its listeners
  // without results; compare their identities instead.
  private def aggregateProducers(using rs: NewResolverState) = rs.aggregateProducers
  private def defnShapes(using rs: NewResolverState) = rs.defnShapes
  
  /** Interpret types through completed symbolic candidates, independently of term overloads. */
  def typeResolution(term: Term)(using rs: NewResolverState): TypeResolution =
    rs.typeInterpretations.get(new Identity(term)).orElse(term.typeInterpretation) match
      case S(result) => result
      case N =>
        val result = new TypeResolution(term, messages => resolError(term, messages))
        // Cache before following a recursive alias. Imported legacy annotations
        // have no stored interpretation: their new inference graph must remain
        // private to this consumer, including listeners on synthesized hosts.
        rs.typeInterpretations(new Identity(term)) = result
        def select(symbol: TypeSymbol)(using NewResolverState): Unit =
          term.withoutCaptures match
            case ref: NewResolvable =>
              rstate.recordResolution(ref, ref.resolvedTargets.contains(symbol))(ref.resolvedTargets ::= symbol)
            case _ => ()
          def definition(defn: Definition)(using NewResolverState): Unit = defn match
            case cls: ClassLikeDef => result.publish(TypeShape.Nominal(cls))
            case alias: TypeDef => result.publish(TypeShape.Alias(alias.sym, alias.rhs.map(typeResolution)))
            case _ => result.publish(TypeShape.Abstract)
          symbol.defn match
            case S(defn) => definition(defn)
            case N => symbol.defnListeners += definition
        def reject(shape: Shape)(using NewResolverState): Unit =
          result.fail(msg"${shape.describe.capitalize} cannot be used as a type" -> shape.toLoc :: Nil)
          result.publish(TypeShape.Abstract)
        def selectMember(member: BlockMemberSymbol)(using NewResolverState): Unit = member.onComplete: () =>
          member.asTpe.orElse(member.asModOrObj) match
            case S(symbol) => select(symbol)
            case N =>
              result.fail(msg"${member.describe.capitalize} cannot be used as a type" -> member.toLoc :: Nil)
              result.publish(TypeShape.Abstract)
        term match
          // Imported prelude declarations can still contain legacy references.
          case Ref(symbol: TypeSymbol) => select(symbol)
          case Ref(member: BlockMemberSymbol) => selectMember(member)
          case Capture(base, thru) => result.publish(TypeShape.Captured(typeResolution(base), thru))
          case TyApp(base, args) => result.publish(TypeShape.Applied(typeResolution(base), args.map(typeResolution)))
          case Forall(_, _, body) => typeResolution(body).listen(result.publish)
          case CompType(left, right, union) =>
            val l = typeResolution(left)
            val r = typeResolution(right)
            result.publish(if union then TypeShape.Union(l, r) else TypeShape.Intersection(l, r))
          case DynTy() => result.publish(TypeShape.Dynamic)
          case FunTy(params, ret, _) => result.publish(TypeShape.Function(params, typeResolution(ret)))
          case UnitVal() => result.publish(TypeShape.Unit)
          case SimpleRef(sym: VarSymbol) if sym.decl.exists(_.isInstanceOf[TyParam]) =>
            result.publish(TypeShape.Parameter(sym, sym.inferenceHost))
          case Ref(sym: VarSymbol) if sym.decl.exists(_.isInstanceOf[TyParam]) =>
            result.publish(TypeShape.Parameter(sym, sym.inferenceHost))
          case Tup(fields) if fields.forall(_.isInstanceOf[Fld]) =>
            result.publish(TypeShape.Tuple(fields.collect { case Fld(_, sign, _) => typeResolution(sign) }))
          case _: WildcardTy | _: Neg | _: Rcd | _: Tup | _: Lit | Missing | Error() =>
            result.publish(TypeShape.Abstract)
          case _ => listen(term, discardMarks = true):
            case shape: SymShape => shape.sym.onComplete: () =>
              shape.sym.asTpe.orElse(shape.sym.asModOrObj) match
                case S(symbol) => select(symbol)
                case N => reject(shape)
            case shape: TermShape => reject(shape)
        result

  /** Register complete signatures while resolution can still publish candidates. Arrow operands
    * need their own interpretations: erasure may consume the arrows as physical parameter lists.
    */
  def registerSignature(sign: Term)(using NewResolverState): Unit =
    sign.typeInterpretation = S(typeResolution(sign))
    sign match
      case Forall(_, _, body) => registerSignature(body)
      case FunTy(lhs, rhs, _) =>
        lhs match
          case Tup(fields) => fields.foreach:
            case Fld(_, term, _) => registerSignature(term)
            case _ => ()
          case single => registerSignature(single)
        registerSignature(rhs)
      case _ => ()

  /** Substitute a bound parameter before storing an argument. Otherwise recursive
    * interfaces such as Tree[A] = Node[A] | Empty would accumulate equivalent
    * A-to-A environments every time a recursive field is selected.
    */
  private def declaredType(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType])(using NewResolverState): DeclaredType =
    resolution.currentShapes.toList match
      case TypeShape.Parameter(symbol, _) :: Nil if bindings.contains(symbol) => bindings(symbol)
      case _ => DeclaredType(resolution, bindings)

  private def typeValues(using rs: NewResolverState) = rs.typeValues
  private def abstractTypes(using rs: NewResolverState) = rs.abstractTypes
  // An omitted argument in a nominal annotation must not subscribe to the
  // class parameter's constructor inference and silently refine that annotation.
  private def abstractType(source: TypeResolution)(using NewResolverState): DeclaredType = abstractTypes.getOrElseUpdate(source, {
    val resolution = new TypeResolution(source.source, source.fail)
    resolution.publish(TypeShape.Abstract)
    declaredType(resolution, Map.empty)
  })

  /** An annotation is an abstraction boundary, even when its implementation is
    * available. Subscribe to the type graph, never to values flowing into it.
    * Shared hosts retain subscriptions for forward and recursive type references.
    */
  def listenTypeValues(sign: Term)(listener: Listener)(using NewResolverState): Unit =
    listenTypeValues(declaredType(typeResolution(sign), Map.empty))(listener)

  private def listenTypeValues(tpe: DeclaredType)(listener: Listener)(using NewResolverState): Unit =
    typeValues.get(tpe) match
      case S(host) => host.listen(listener)
      case N =>
        val host = new TypeValues
        typeValues(tpe) = host
        host.listen(listener)
        def follow(current: DeclaredType, args: Ls[DeclaredType], aliases: Set[TypeResolution], publish: Listener)(using NewResolverState): Unit =
          current.resolution.listen: shape =>
            def bind(params: Ls[TyParam])(using NewResolverState): Map[VarSymbol, DeclaredType] =
              current.bindings ++ params.map(_.sym).zip(args.padTo(params.length, abstractType(current.resolution)))
            def next(res: TypeResolution)(using NewResolverState): Unit = follow(declaredType(res, current.bindings), Nil, aliases, publish)
            shape match
              case TypeShape.Dynamic => publish(DynShape())
              case TypeShape.Inferred(value) => publish(value)
              case TypeShape.Nominal(defn) =>
                val bindings = bind(defn.tparams)
                defn.ext match
                  case N => publish(NominalTypeShape(defn, bindings, N))
                  case S(parent) =>
                    // Only the parent's declared type is relevant here. Evaluating
                    // its constructor arguments would reintroduce implementation flow.
                    listenTypeValues(declaredType(typeResolution(parent.cls), bindings)): ext =>
                      publish(NominalTypeShape(defn, bindings, S(ext)))
              case TypeShape.Alias(symbol, rhs) =>
                // Revisiting the same alias reference without reaching an outer
                // nominal/function shape supplies no additional interface. Track
                // references, not symbols: Id[Id[T]] has two distinct references.
                // This also terminates aliases that recursively grow their arguments.
                if aliases(current.resolution) then publish(OpaqueTypeShape(tpe.resolution.source))
                else rhs match
                  case S(rhs) => follow(declaredType(rhs, bind(symbol.defn.get.tparams)), Nil,
                    aliases + current.resolution, publish)
                  case N => publish(OpaqueTypeShape(tpe.resolution.source))
              case TypeShape.Applied(base, params) =>
                follow(declaredType(base, current.bindings), params.map(declaredType(_, current.bindings)), aliases, publish)
              case TypeShape.Parameter(symbol, host) => current.bindings.get(symbol) match
                case S(bound) => follow(bound, Nil, aliases, publish)
                case N =>
                  listenTypeArgument(host)(publish)
              case TypeShape.Captured(base, thru) =>
                follow(declaredType(base, current.bindings), args, aliases,
                  shape => publish(shape match
                    // Nominal/function interfaces are closed descriptions. Only
                    // parameter flow carries a lexical activation to transport.
                    case _: MarkedShape => MarkedShape.enter(shape, ResolutionBoundary(thru), N)
                    case _ => shape))
              case TypeShape.Function(params, ret) =>
                val ps = params match
                  case Tup(fields) => DeclaredParams(fields.collect:
                    case Fld(_, sign, _) => S(declaredType(typeResolution(sign), current.bindings))
                  , fields.exists(!_.isInstanceOf[Fld]))
                  case single => DeclaredParams(S(declaredType(typeResolution(single), current.bindings)) :: Nil, false)
                publish(CallableTypeShape(tpe.resolution.source, ps :: Nil,
                  S(declaredType(ret, current.bindings)), Nil))
              case TypeShape.Tuple(fields) =>
                publish(TupleShape(current.resolution.source,
                  fields.map(field => TupleShape.TypedField(declaredType(field, current.bindings), Nil)))(this))
              case TypeShape.Union(left, right) => next(left); next(right)
              case TypeShape.Intersection(left, right) => next(left); next(right)
              case TypeShape.Unit | TypeShape.Abstract => publish(OpaqueTypeShape(tpe.resolution.source))
        follow(tpe, Nil, Set.empty, host.publish)

  // A separate full signature also annotates the implementation's parameters.
  // Register these before its body is elaborated, so observed calls can never
  // publish inferred alternatives for parameters behind this boundary.
  private def signatureParameters(using rs: NewResolverState) = rs.signatureParameters
  def registerParameterSignature(paramLists: Ls[ParamList], sign: Term)(using NewResolverState): Unit =
    def bind(paramLists: Ls[ParamList], tpe: DeclaredType)(using NewResolverState): Unit = paramLists match
      case Nil => ()
      case ps :: tail => listenTypeValues(tpe):
        case callable: CallableTypeShape =>
          val declared = callable.paramLists.head
          if !declared.hasRest then ps.params.zip(declared.params).foreach: (param, sign) =>
            if param.sign.isEmpty then sign.foreach: tpe =>
              signatureParameters(param.sym) = tpe
              listenTypeValues(tpe): shape =>
                if param.sym.currentShapes.add(shape) then param.sym.notifyShapeListeners(shape)
          callable.result.foreach(bind(tail, _))
        case _ => ()
    bind(paramLists, declaredType(typeResolution(sign), Map.empty))

  /** Synthesized constructor fields retain their source declaration on the symbol. */
  private def resultSignature(td: TermDefinition)(using NewResolverState): Opt[Term] = td.tsym.decl match
    case S(p: Param) => p.sign
    case _ => td.resultSignature

  private def capturedTypes(using rs: NewResolverState) = rs.capturedTypes
  private def captureType(bound: DeclaredType, scope: TermSymbol)(using NewResolverState): DeclaredType =
    capturedTypes.getOrElseUpdate((bound, scope), {
      val captured = new TypeResolution(bound.resolution.source, bound.resolution.fail)
      captured.publish(TypeShape.Captured(bound.resolution, scope))
      declaredType(captured, bound.bindings)
    })

  private def listenDeclaredMember(member: BlockMemberSymbol, bindings: Map[VarSymbol, DeclaredType], flow: FlowSymbol,
      source: Term, selected: ShapeListener[DefinitionSymbol[?]])(listener: Listener)(using NewResolverState): Unit =
    member.onComplete: () =>
      member.asModOrObj.orElse(member.asTrm).orElse(member.asCls) match
        case S(symbol: TermSymbol) if !symbol.isInstanceOf[ClassCtorSymbol] =>
          selected(symbol)
          val td = symbol.defn.get
          def publish(shape: TermShape)(using NewResolverState): Unit =
            val generic = shape match
              case callable: CallableTypeShape => callable.copy(tparams = td.tparams.toList.flatten.map(p => new TypeShape.Parameter(p.sym, p.sym.inferenceHost)))
              case _ => shape
            // A synthesized field's signature is in the constructor parameter's
            // scope. Written member signatures are in their own definition scope.
            val exited = td.tsym.decl match
              case S(_: Param) => generic
              case _ => MarkedShape.exit(generic, ResolutionBoundary(td.tsym), S(flow))
            exited match
              case value: TermShape => listener(value)
              case NoShape => ()
          def signature(sign: Term)(using NewResolverState): DeclaredType =
            // Legacy annotations have plain references instead of Capture nodes.
            // Rebase substituted class parameters into this member's scope, just
            // as a new-resolution Capture does, before the member exits it.
            val legacyParameters = mutable.Set.empty[VarSymbol]
            def visit(term: Term)(using NewResolverState): Unit = term match
              case Ref(symbol: VarSymbol) if bindings.contains(symbol) => legacyParameters += symbol
              case _ => term.subTerms.foreach(visit)
            if !td.tsym.decl.exists(_.isInstanceOf[Param]) then visit(sign)
            val scopedBindings = bindings.map: (symbol, bound) =>
              symbol -> (if legacyParameters(symbol) then captureType(bound, td.tsym) else bound)
            declaredType(typeResolution(sign), scopedBindings)
          val result = resultSignature(td).map(signature)
          if td.sign.nonEmpty && (td.k is syntax.Fun) && !td.flags.hasResultAnnotation then
            listenTypeValues(signature(td.sign.get))(publish)
          else if td.params.nonEmpty then
            publish(CallableTypeShape(source,
              td.params.map(ps => DeclaredParams(ps.params.map(_.sign.map(signature)), ps.restParam.nonEmpty)), result, Nil))
          else result match
            case S(tpe) => listenTypeValues(tpe)(publish)
            case N => publish(UnknownValueShape(source))
        case _ =>
          // A nested nominal declaration denotes its statically selected symbol;
          // selecting it does not inspect an instance field or method body.
          fromBMS(member, flow, Nil, listener, source, selected)

  def resolError(src: Term | Pattern, msgs: Ls[(Message, Opt[Loc])])(using rs: NewResolverState): Unit = rs.report:
    ErrorReport(msg"Resolution error in ${src.describe}" -> src.toLoc ::msgs, source = Diagnostic.Source.Compilation)
  
  /** Explicit and inferred type arguments use the same entry/exit paths as term
    * arguments. An explicit argument fixes that instantiation; its value argument
    * must not add a more precise implementation shape to the declared interface.
    */
  private def listenTypeArgument(symbol: VarSymbol)(listener: Listener)(using NewResolverState): Unit =
    listenTypeArgument(symbol.inferenceHost)(listener)

  private def listenTypeArgument(host: Publisher.Data[Shape])(listener: Listener)(using NewResolverState): Unit =
    host.subscribe:
      case value: TermShape => listener(value)
      case _ => softAssert(false, "A type parameter received a symbolic overload set")

  private def publishParameter(symbol: VarSymbol, shape: TermShape | NoShape)(using NewResolverState): Unit =
    publishParameter(symbol.inferenceHost, shape)

  private def publishParameter(host: Publisher.Data[Shape], shape: TermShape | NoShape)(using NewResolverState): Unit = shape match
    case value: TermShape => host.publish(value)
    case _ => ()

  private def applyTypeArguments(callee: DefnShape | CallableTypeShape, marks: Ls[Marks], args: Ls[Term], source: Term)(using NewResolverState): Unit =
    val params = callee match
      case callable: CallableTypeShape => callable.tparams
      case defn: DefnShape => defn.clsDef match
        case S(cls) => cls.tparams.map(p => new TypeShape.Parameter(p.sym, p.sym.inferenceHost))
        case N => defn.defn match
          case td: TermDefinition => td.tparams.toList.flatten.map(p => new TypeShape.Parameter(p.sym, p.sym.inferenceHost))
          case _ => Nil
    if params.length != args.length then
      resolError(source, msg"${callee.describe.capitalize} expected ${params.length} type ${
        "argument".pluralized(params.length)}, but got ${args.length}" -> callee.toLoc :: Nil)
    params.zip(args).foreach: (param, arg) =>
      rstate.markExplicitTypeArgument(param.symbol, marks)
      listenTypeValues(arg): tpe =>
        publishParameter(param.host, tpe.enter(marks))

  // Install each constraint edge before subscribing: callback parameter/result
  // flow can revisit it immediately. Distinct instantiations retain their marks.
  private def typeConstraints(using rs: NewResolverState) = rs.typeConstraints
  private def inferTypeArguments(tpe: DeclaredType, value: TermShape, marks: Ls[Marks])(using NewResolverState): Unit =
    if !typeConstraints.add((tpe, value, marks)) then return
    def follow(tpe: DeclaredType, args: Ls[DeclaredType], captures: Ls[Marks],
        seen: Set[TypeResolution])(using NewResolverState): Unit = if !seen(tpe.resolution) then
      val next = seen + tpe.resolution
      tpe.resolution.listen:
        case TypeShape.Parameter(symbol, host) => tpe.bindings.get(symbol) match
          case S(bound) => follow(bound, Nil, captures, next)
          case N if !rstate.hasExplicitTypeArgument(symbol, marks) => publishParameter(host, value.enter(captures))
          case _ => ()
        case TypeShape.Captured(base, thru) =>
          follow(declaredType(base, tpe.bindings), args,
            EntryMark(ResolutionBoundary(thru), N, NoMarks) :: captures, next)
        case TypeShape.Applied(base, params) =>
          follow(declaredType(base, tpe.bindings), params.map(declaredType(_, tpe.bindings)), captures, next)
        case TypeShape.Alias(symbol, S(rhs)) =>
          val bindings = tpe.bindings ++ symbol.defn.get.tparams.map(_.sym).zip(args)
          follow(declaredType(rhs, bindings), Nil, captures, next)
        case TypeShape.Tuple(fields) => value.enter(captures) match
          case Marked(tuple: TupleShape, context) =>
            fields.zipWithIndex.foreach: (field, index) =>
              tuple.getMember(index.toString) match
                case MemberLookup.Indexed(actual, inner) => listenTupleField(actual): shape =>
                  shape.exit(inner).exit(context) match
                    case value: TermShape =>
                      inferTypeArguments(declaredType(field, tpe.bindings), value, marks)
                    case NoShape => ()
                case _ => ()
          case _ => ()
        case TypeShape.Function(_, _) => value.enter(captures) match
          case actual: TermShape =>
            constrainFunction(declaredType(tpe.resolution, tpe.bindings), actual, marks)
          case NoShape => ()
        case TypeShape.Nominal(cls) if args.nonEmpty =>
          val (head, context) = value.applicationHead
          def constrain(param: TyParam, pattern: DeclaredType)(using NewResolverState): Unit =
            listenTypeArgument(param.sym): shape =>
              shape.exit(context) match
                case actual: TermShape => inferTypeArguments(pattern, actual, marks)
                case NoShape => ()
          def constrainNominal(nominal: NominalTypeShape)(using NewResolverState): Unit =
            if nominal.defn is cls then cls.tparams.zip(args).foreach: (param, pattern) =>
              nominal.bindings.get(param.sym).foreach: bound =>
                listenTypeValues(bound): shape =>
                  shape.exit(context) match
                    case actual: TermShape => inferTypeArguments(pattern, actual, marks)
                    case NoShape => ()
          head match
            case ds: DefnShape if ds.clsDef.contains(cls) => cls.tparams.zip(args).foreach(constrain)
            case nominal: NominalTypeShape => constrainNominal(nominal)
            case tuple: TupleShape => constrainNominal(tuple.arrayParent)
            case _ => ()
        case _ => () // Concrete annotations are opaque, irrespective of the argument value.
    // Alias expansion guards only unproductive cycles. Descending into a tuple,
    // nominal argument, or arrow installs another edge with its own cycle guard.
    follow(tpe, Nil, Nil, Set.empty)

  /** Function constraints reverse the parameter flow and preserve result flow.
    * Read an implementation only while checking it against its declared interface;
    * calls through that interface continue to expose only the declared result.
    */
  private def constrainFunction(expected: DeclaredType, actual: TermShape, marks: Ls[Marks])(using NewResolverState): Unit =
    val context = actual.applicationHead._2
    def results(listener: Listener)(using NewResolverState): Unit = actual.applicationHead._1 match
      case intro: IntroShape => intro.trm match
        case Lam(_, body) => listenTerm(body)(listener)
        case _ => ()
      case ds: DefnShape => ds.defn match
        case td: TermDefinition => td.sign match
          case S(sign) => listenSignatureResult(declaredType(typeResolution(sign), Map.empty),
            if td.flags.hasResultAnnotation then 0 else td.params.length)(listener)
          case N => td.body.foreach(listenTerm(_)(listener))
        case _ => ()
      case _ => ()
    def matchLists(expected: DeclaredType, remaining: Ls[(ParamList, Ls[Marks])])(using NewResolverState): Unit =
      listenTypeValues(expected):
        case Marked(callable: CallableTypeShape, expectedContext) => remaining match
          case (params, _) :: tail =>
            val declared = callable.paramLists.head
            if declared.params.length < params.params.length
                || (declared.params.length > params.params.length && params.restParam.isEmpty)
                || (declared.hasRest && params.restParam.isEmpty) then
              resolError(expected.resolution.source, msg"Callback parameter list does not match its declared function type." -> actual.toLoc :: Nil)
            else
              params.params.zip(declared.params).foreach: (param, sign) =>
                sign.foreach: tpe =>
                  listenTypeValues(tpe): shape =>
                    constrainParameter(param, shape.exit(expectedContext).enter(context), context)
              params.restParam.foreach: rest =>
                val fields = declared.params.drop(params.params.length).map:
                  case S(tpe) => TupleShape.TypedField(tpe, Nil)
                  case N => TupleShape.UnknownField(callable.source, Nil)
                val suffix = if declared.hasRest
                  then TupleShape.Unknown(callable.source, Nil, UnknownValueShape(callable.source)) :: Nil
                  else Nil
                val tuple = TupleShape(callable.source, fields ::: suffix)(this)
                constrainParameter(rest, tuple.exit(expectedContext).enter(context), context)
              callable.result.foreach: ret =>
                tail match
                  case Nil => results: shape =>
                    shape.exit(context).enter(expectedContext) match
                      case value: TermShape => inferTypeArguments(ret, value, marks)
                      case NoShape => ()
                  case _ => matchLists(ret, tail)
          case Nil => ()
        case _ => ()
    actual match
      case Marked(givenType: CallableTypeShape, actualContext) =>
        listenTypeValues(expected):
          case Marked(wanted: CallableTypeShape, expectedContext) =>
            val domain = givenType.paramLists.head
            val expectedDomain = wanted.paramLists.head
            if domain.params.length != expectedDomain.params.length || domain.hasRest != expectedDomain.hasRest then
              resolError(expected.resolution.source, msg"Callback parameter list does not match its declared function type." -> actual.toLoc :: Nil)
            else
              domain.params.zip(expectedDomain.params).foreach:
                case (S(givenParam), S(wantedParam)) =>
                  listenTypeValues(wantedParam): shape =>
                    shape.exit(expectedContext).enter(actualContext) match
                      case value: TermShape => inferTypeArguments(givenParam, value, context)
                      case NoShape => ()
                case _ => ()
              wanted.result.foreach: ret =>
                def receive(shape: TermShape)(using NewResolverState): Unit = shape.exit(actualContext).enter(expectedContext) match
                  case value: TermShape => inferTypeArguments(ret, value, marks)
                  case NoShape => ()
                givenType.paramLists.tail match
                  case Nil => givenType.result.foreach(listenTypeValues(_)(receive))
                  case tail => receive(givenType.copy(paramLists = tail))
          case _ => ()
      case _ => matchLists(expected, actual.unappliedParams)

  private def listenSignatureResult(tpe: DeclaredType, count: Int)(listener: Listener)(using NewResolverState): Unit =
    if count == 0 then listenTypeValues(tpe)(listener)
    else listenTypeValues(tpe):
      case Marked(callable: CallableTypeShape, _) =>
        callable.result.foreach(listenSignatureResult(_, count - 1)(listener))
      case _ => ()

  private def tupleArrayParents(using rs: NewResolverState) = rs.tupleArrayParents
  /** A tuple is an Array whose element argument is the union of its field shapes.
    * Cache the parent before following fields: a recursive tuple can require its
    * own Array interface while one of those fields is still being resolved.
    */
  private[semantics] def tupleArrayParent(tuple: TupleShape)(using NewResolverState): NominalTypeShape =
    tupleArrayParents.get(new Identity(tuple)) match
      case S(parent) => parent
      case N =>
        val cls = prelude.builtins.Array.defn.get
        softAssert(cls.tparams.length == 1, "The builtin Array must have one element type parameter")
        val elements = new TypeResolution(tuple.source, messages => resolError(tuple.source, messages))
        val parent = NominalTypeShape(cls, Map(cls.tparams.head.sym -> declaredType(elements, Map.empty)), N)
        tupleArrayParents(new Identity(tuple)) = parent
        tuple.segments.foreach:
          case field: TupleShape.Fixed => listenTupleField(field): value =>
            elements.publish(TypeShape.Inferred(value))
          case TupleShape.Unknown(_, marks, value) => value.exit(marks) match
            case value: TermShape => elements.publish(TypeShape.Inferred(value))
            case NoShape => ()
        parent

  private def listenTupleField(field: TupleShape.Fixed)(listener: Listener)(using NewResolverState): Unit =
    def receive(shape: TermShape)(using NewResolverState): Unit = shape.exit(field.marks) match
      case value: TermShape => listener(value)
      case NoShape => ()
    field match
      case TupleShape.Field(field, _) => listenTerm(field.term)(receive)
      case TupleShape.TypedField(tpe, _) => listenTypeValues(tpe)(receive)
      case TupleShape.UnknownField(source, _) => receive(UnknownValueShape(source))

  /** Subscribe once to complete argument-tuple candidates. A pending spread is not
    * an argument, nor evidence of an arity mismatch; each resolved combination is.
    */
  def zipArgs(mss: Ls[Marks], ps: Ls[Param], r: Opt[Param], args: Term, src: Term, funSh: TermShape)(using NewResolverState): Unit =
    val params = ps ::: r.toList
    zipArgumentShapes(mss, ps.length, r.nonEmpty, args, src, funSh): (index, shape) =>
      constrainParameter(params(index), shape, mss)

  private def constrainParameter(p: Param, shape: TermShape | NoShape, marks: Ls[Marks])(using NewResolverState): Unit =
    shape match
      case NoShape => ()
      case sh: TermShape =>
        val sign = p.sign.map(sign => declaredType(typeResolution(sign), Map.empty)).orElse(signatureParameters.get(p.sym))
          .orElse(p.sym.getState.newResolverState.signatureParameters.get(p.sym))
        sign match
          case S(tpe) => inferTypeArguments(tpe, sh, marks)
          case N => publishParameter(p.sym, sh)

  private def zipArgumentShapes(mss: Ls[Marks], expectedCount: Int, hasRest: Bool,
      args: Term, src: Term, funSh: TermShape)(publish: (Int, TermShape | NoShape) => NewResolverState ?=> Unit)(using NewResolverState): Unit =
    def matchSegments(tuple: TupleShape, marks: Marks)(using NewResolverState): Unit =
      val segments = tuple.segments
      val knownCount = segments.count(_.isInstanceOf[TupleShape.Fixed])
      // Distribute only successful argument counts. Unknown spreads retain all
      // possible fixed positions and the residual tail for a rest parameter.
      val extra = (expectedCount - knownCount).max(0)
      def assign(segment: TupleShape.Segment, positions: Range)(using NewResolverState): Unit =
        positions.foreach: index =>
          segment match
            case field: TupleShape.Fixed => listenTupleField(field): sh =>
              publish(index, sh.exit(marks).enter(mss))
            case TupleShape.Unknown(_, inner, value) =>
              publish(index, value.exit(inner).exit(marks).enter(mss))
      def loop(rest: Ls[TupleShape.Segment], before: Int, unknownBefore: Bool)(using NewResolverState): Unit = rest match
        case Nil => ()
        case (field: TupleShape.Fixed) :: tail =>
          val unknownAfter = tail.exists(_.isInstanceOf[TupleShape.Unknown])
          // With no later unknown segment, preceding spreads must supply all
          // missing fixed arguments, even when the function has a rest parameter.
          val first = if unknownBefore && !unknownAfter then before + extra else before
          val last = if !unknownBefore then before
            else if hasRest then expectedCount - 1 else before + extra
          assign(field, first.max(0) until (last + 1).min(expectedCount))
          loop(tail, before + 1, unknownBefore)
        case (unknown: TupleShape.Unknown) :: tail =>
          val end = if hasRest then expectedCount else before + extra
          assign(unknown, before until end)
          loop(tail, before, true)
      loop(segments, 0, false)
      if hasRest then
        // If consumption reaches an unknown segment, some subsequent fields
        // may have been consumed too. Approximate that optional prefix with an
        // unknown segment, retaining the suffix that must remain. Publishing
        // separate concrete tails here would turn uncertainty into false arity
        // failures when the rest tuple is spread into another call.
        def drop(xs: Ls[TupleShape.Segment], count: Int, approximate: Bool)(using NewResolverState): Ls[TupleShape.Segment] =
          if count == 0 then xs
          else xs match
            case Nil => Nil
            case (_: TupleShape.Fixed) :: rest => drop(rest, count - 1, approximate)
            case (unknown: TupleShape.Unknown) :: Nil =>
              // Consuming a prefix changes the length, but not the element
              // shape, when there are no following fields to merge into it.
              if approximate then unknown :: Nil else Nil
            case (_: TupleShape.Unknown) :: rest =>
              val suffix = drop(rest, count, false)
              if approximate then TupleShape.Unknown(tuple.source, Nil, UnknownValueShape(tuple.source)) :: suffix else suffix
        val remaining = drop(segments, expectedCount, true)
        val rest = if expectedCount == 0 then tuple else TupleShape(tuple.source, TupleShape.Rest(tuple, remaining) :: Nil)(this)
        publish(expectedCount, rest.exit(marks).enter(mss))
    checkArgumentArity(args, expectedCount, hasRest, src, funSh):
      case (tuple, marks) => matchSegments(tuple, marks)
  
  private def checkArgumentArity(args: Term, expected: Int, rest: Bool, src: Term,
      callable: TermShape)(matched: ShapeListener[(TupleShape, Marks)])(using NewResolverState): Unit =
    val reportKey = new Object
    listenTerm(args):
      case Marked(tuple: TupleShape, marks) =>
        val known = tuple.segments.count(_.isInstanceOf[TupleShape.Fixed])
        val unknown = known != tuple.segments.length
        val mismatch = (!unknown && known < expected) || (!rest && known > expected)
        if mismatch then
          if rstate.reportedArities.getOrElseUpdate(reportKey, mutable.Set.empty).add(known) then
            val count = if unknown then msg"at least ${known}" else msg"${known}"
            resolError(src, msg"${callable.describe.capitalize} expected ${expected} ${
              "argument".pluralized(expected)}, but got ${count}" -> callable.toLoc :: Nil)
        else matched((tuple, marks))
      case _ => resolError(src, msg"Expected an argument tuple." -> args.toLoc :: Nil)
  
  /** Resolve every constructor pattern through the same symbolic interpretation.
    * A class overload takes precedence over its term companion in this context.
    * Keep every candidate so lowering can diagnose ambiguity independently of
    * the order in which definitions and receiver shapes become available. */
  def constructorPattern(res: Pattern.Constructor)(using NewResolverState): Unit = if newResolution then
    val lhs = res.target
    def select(sym: DefinitionSymbol[?])(using NewResolverState): Bool =
      lhs.withoutCaptures match
        case trm: NewResolvable =>
          rstate.recordResolution(trm, trm.resolvedTargets.contains(sym))(trm.resolvedTargets ::= sym)
        case _ => ()
      if res.resolvedTargets.contains(sym) then false
      else
        rstate.recordResolution(res, false)(res.resolvedTargets ::= sym)
        true
    def reject(sh: TermShape)(using NewResolverState): Unit =
      rstate.markError(res)
      resolError(res, msg"${sh.describe.capitalize} cannot be used as a constructor pattern." -> sh.toLoc :: Nil)
    def classPattern(cls: ClassLikeDef)(using NewResolverState): Unit = if select(cls.sym) then
      val assoc = res.arguments match
        case N => Nil
        case S(args) => cls.paramsOpt match
          case N =>
            if args.nonEmpty || cls.isInstanceOf[ClassDef] then
              rstate.markError(res)
              resolError(res, msg"${cls.describe.capitalize} does not take pattern arguments." -> cls.toLoc :: Nil)
            Nil
          case S(ps) =>
            if ps.restParam.nonEmpty then TODO(ps.restParam)
            if args.sizeCompare(ps.params) =/= 0 then
              rstate.markError(res)
              resolError(res,
                msg"${cls.describe.capitalize} expected ${ps.params.length} ${
                  "pattern argument".pluralized(ps.params.length)}, but got ${args.length}" -> cls.toLoc :: Nil)
            ps.params.lazyZip(args).flatMap: (p, a) =>
              p.fldSym match
                case S(fldSym: BlockMemberSymbol) =>
                  // withFields reports member/alias conflicts before dropping all
                  // generated fields for recovery. Parameters retain their fldSym,
                  // so verify its identity in the recovered body: a body member may
                  // occupy the same name. Do not publish dangling pattern fields or
                  // report another error for this already-diagnosed class.
                  if cls.body.members.get(fldSym.nme).contains(fldSym) then (fldSym -> a) :: Nil
                  else
                    rstate.markError(res)
                    Nil
                case _ =>
                  rstate.markError(res)
                  resolError(res, msg"Pattern argument requires an accessible constructor field." -> p.toLoc :: Nil)
                  Nil
      if !rstate.hasError(res) then
        val psh = CtorPatternShape(cls, assoc, res, FlowSymbol.pat()(using rstate.owner))
        if res.currentShapes.add(psh) then res.notifyShapeListeners(psh)
    def valuePattern(sh: TermShape)(using NewResolverState): Unit = sh.applicationHead match
      case (ds: DefnShape, _) => ds.defn match
        case cls: ClassDef => classPattern(cls)
        case obj: ModuleOrObjectDef if obj.sym.asObj.isDefined => classPattern(obj)
        case td: TermDefinition => td.tsym match
          case ctor: ClassCtorSymbol => classPattern(ctor.associatedCls.defn.get)
          case _ => reject(sh)
        case _ => reject(sh)
      case _ => reject(sh)
    lhs.withoutCaptures match
      case Term.Error() => rstate.markError(res)
      case Term.Ref(sym: VarSymbol) if sym.decl.exists(_.isPatternConstructor) =>
        res.resolvedTargets ::= sym
      case Term.SimpleRef(sym: VarSymbol) if sym.decl.exists(_.isPatternConstructor) =>
        res.resolvedTargets ::= sym
      case _ => listen(lhs, discardMarks = true): sh =>
        sh match
          case sh: SymShape =>
            val bms = sh.sym
            bms.onComplete: () =>
              bms.asPat.orElse(bms.asCls).orElse(bms.asObj) match
                case S(sym: PatternSymbol) => select(sym)
                case S(sym: (ClassSymbol | ModuleOrObjectSymbol)) =>
                  sym.defn match
                    case S(cls) => classPattern(cls)
                    case N => softAssert(false, "Completed pattern member has no definition")
                case N =>
                  fromBMS(bms, FlowSymbol.pat()(using rstate.owner), sh.markss, valuePattern, lhs, _ => ())
          case sh: TermShape => valuePattern(sh)
  
  /** Propagate possible values to pattern bindings. Constructor tests filter by
    * nominal class; guards and literal tests may conservatively retain shapes.
    * Both scrutinee and constructor shapes can arrive after this registration. */
  def matchShapePat(shape: Shape, pattern: Pattern)(matched: ShapeListener[Shape])(using NewResolverState): Unit =
    pattern match
      case al @ Pattern.Alias(pat, _) =>
        matchShapePat(shape, pat): sh =>
          // Rejected duplicate/negated bindings have no allocated symbol. Pattern
          // validation already reports them; only valid bindings receive flow.
          al.symbolOption.foreach: symbol =>
            if symbol.currentShapes.add(sh) then symbol.notifyShapeListeners(sh)
          matched(sh)
      case Pattern.Wildcard() | Pattern.Literal(_) => matched(shape)
      case Pattern.Chain(left, right) =>
        matchShapePat(shape, left)(sh => matchShapePat(sh, right)(matched))
      case Pattern.Composition(true, left, right) =>
        matchShapePat(shape, left)(matched)
        matchShapePat(shape, right)(matched)
      case Pattern.Guarded(pat, _) => matchShapePat(shape, pat)(matched)
      // Compilation-strategy annotations do not change the pattern's bindings.
      case Pattern.Annotated(pat, _) => matchShapePat(shape, pat)(matched)
      case ctor: Pattern.Constructor =>
        def listenConstructor(psh: PatternShape)(using NewResolverState): Unit = psh match
          case CtorPatternShape(cls, fs, _, resSym) =>
            def check(sh: TermShape)(using NewResolverState): Unit =
              if sh.isInstanceOfClass(cls) then
                fs.foreach: (bms, pat) =>
                  sh.getMember(bms.nme) match
                    case MemberLookup.Found(sym: BlockMemberSymbol, marks) =>
                      val field = symShapes.getOrElseUpdate((sym, resSym, marks), SymShape(sym, resSym, marks))
                      matchShapePat(field, pat)(_ => ())
                    case MemberLookup.Declared(member, bindings, marks) =>
                      listenDeclaredMember(member, bindings, resSym, ctor.target, _ => ()): field =>
                        field.exit(marks) match
                          case value: TermShape => matchShapePat(value, pat)(_ => ())
                          case NoShape => ()
                    case _ =>
                      // classPattern only publishes fields present in cls.body.
                      // The nominal test above admits only that class's instances,
                      // this-values, and subclasses. Their member lookup follows
                      // the same class bodies and inheritance chain; overrides are
                      // also BlockMemberSymbols. Record members cannot replace a
                      // class's own field. Thus this branch is an internal mismatch
                      // between nominal matching and member lookup, not recovery
                      // from a malformed class (filtered by classPattern above).
                      softAssert(false, "Matched constructor is missing its field")
                matched(sh)
            shape match
              case sh: TermShape => check(sh)
              case sh: SymShape => fromSymbol(sh, check, ctor.target, _ => ())
        ctor.subscribeToShapes(listenConstructor)
      case Pattern.Tuple(_, _) => () // Tuple binding shapes are not inferred yet.
      case _ => TODO(pattern)
  
  def matchScrutPat(scrutinee: Term.Ref, pattern: Pattern)(using NewResolverState): Unit = if newResolution then
    listenTerm(scrutinee)(sh => matchShapePat(sh, pattern)(_ => ()))
  
  def appShape(lhs: TermShape, args: Term, res: App)(using NewResolverState): Unit =
    // An unknown element used as a callee stays a dynamic call. Propagate its
    // unknown result rather than inferring callability from a different candidate.
    lhs match
      case Marked(_: (DynShape | UnknownValueShape), _) =>
        if res.currentShapes.add(lhs) then res.notifyShapeListeners(lhs)
        return
      case _ => ()
    lhs match
      case Marked(callable: CallableTypeShape, context) =>
        val ps = callable.paramLists.head
        zipArgumentShapes(context :: Nil, ps.params.length, ps.hasRest, args, res, lhs): (index, value) =>
          if index < ps.params.length then ps.params(index).foreach: tpe =>
            value match
              case value: TermShape => inferTypeArguments(tpe, value, context :: Nil)
              case NoShape => ()
        def publish(shape: TermShape)(using NewResolverState): Unit = shape.exit(context) match
          case value: TermShape =>
            if res.currentShapes.add(value) then res.notifyShapeListeners(value)
          case NoShape => ()
        callable.paramLists.tail match
          case Nil => callable.result match
            case S(tpe) => listenTypeValues(tpe)(publish)
            case N => publish(UnknownValueShape(callable.source))
          case tail => publish(callable.copy(paramLists = tail))
        return
      case _ => ()
    // log(s"appShape? lhs = $lhs, args = $args, res = $res")
    val sh = appShapes.getOrElseUpdate((lhs, res.resSym), {
      log(s"appShape: lhs = ${lhs.shwDbg}, args = ${args.showDbg}, res = ${res.showDbg}")
      new AppShape(lhs, args, res)
    })
    lhs.unappliedParams match
    case Nil => ()
    case (ps, mss) :: pss =>
      zipArgs(mss, ps.params, ps.restParam, args, res, lhs)
    log(s"appShape isSaturated? ${sh.isSaturated}; head? ${sh.applicationHead}")
    def register(using NewResolverState) = if res.currentShapes.add(sh) then
      res.notifyShapeListeners(sh)
    log(s"lhs ${lhs.isSaturated} ${lhs.unappliedParams.map(_.mapFirst(_.showDbg).mapSecond(_.map(_.showDbg)))}")
    if lhs.isSaturated && !rstate.hasError(res) then
      rstate.markError(res)
      // Marks transport a value across scopes; they do not apply arguments.
      // Inspect the value beneath them, retaining actual calls/instantiations
      // so an already constructed instance never gets the suggestion to use new.
      val message = lhs match
        case Marked(ds: DefnShape, _) if ds.defn.isInstanceOf[ClassDef] =>
          msg"Class '${ds.defn.bsym.nme}' must be instantiated with 'new'."
        case Marked(_: (AppShape | NewShape), _) =>
          msg"${lhs.describe.capitalize} cannot receive more argument lists."
        case _ =>
          msg"${lhs.describe.capitalize} cannot be called like a function."
      resolError(res, message -> lhs.toLoc :: Nil)
    if sh.isSaturated then
      def go(body: Term, mss: Ls[Marks])(using NewResolverState) =
        listenTerm(body): sh =>
          sh.exit(mss) match
          case NoShape =>
          case sh: TermShape =>
            if res.currentShapes.add(sh) then
              res.notifyShapeListeners(sh)
      sh.applicationHead match
      case (ds: DefnShape, mss) =>
        ds.defn match
        case cd: ClassDef =>
          // TODO: resolve ctor?
          // TODO: handle `mss`
          register
        case td: TermDefinition =>
          // listenTerm(td.body, sh => newShape(sh, args, res))
          td.tsym match
          case ccs: ClassCtorSymbol => // TOOD: to avoid the special case, give this the actual body?
            softAssert(td.body.isEmpty)
            // ccs.associatedCls
            // TODO: handle `mss`
            register
          case _ =>
            log(s"appShape: td.body = ${td.body}")
            td.sign match
              case S(sign) =>
                val count = if td.flags.hasResultAnnotation then 0 else td.params.length
                listenSignatureResult(declaredType(typeResolution(sign), Map.empty), count): result =>
                  result.exit(mss) match
                    case value: TermShape =>
                      if res.currentShapes.add(value) then res.notifyShapeListeners(value)
                    case NoShape => ()
              case N => td.body.foreach(go(_, mss))
        case _ =>
          softAssert(rstate.hasError(res))
      case (sh: IntroShape, mss) =>
        sh.trm match
        case Lam(params, body) =>
          // Exit the same context that zipArgs enters, filtering results from other uses.
          go(body, mss)
        case _ =>
          softAssert(rstate.hasError(res))
      case _ =>
        softAssert(rstate.hasError(res))
    else register
  
  private def publishMember(host: NewResolvable & ShapeHost, member: BlockMemberSymbol | RecordMember,
      flow: FlowSymbol, marks: Ls[Marks])(using NewResolverState): Unit =
    def publish(shape: Shape)(using NewResolverState): Unit =
      if host.currentShapes.add(shape) then host.notifyShapeListeners(shape)
    def definition(sym: BlockMemberSymbol)(using NewResolverState): Unit =
      publish(symShapes.getOrElseUpdate((sym, flow, marks), SymShape(sym, flow, marks)))
    member match
      case member: BlockMemberSymbol => definition(member)
      case RecordMember(field, false) => definition(field.sym)
      case RecordMember(field, true) =>
        // Assignments can replace the stored value, so its initializer no longer
        // determines what a read returns. Publish the known property symbol for
        // selection/assignment, but an unknown shape for the value being read.
        rstate.recordResolution(host, host.resolvedTargets.contains(field.tsym))(host.resolvedTargets ::= field.tsym)
        publish(UnknownValueShape(field.rhs))

  private def publishDeclared(host: NewResolvable & ShapeHost, member: BlockMemberSymbol, flow: FlowSymbol,
      bindings: Map[VarSymbol, DeclaredType], marks: Ls[Marks])(using NewResolverState): Unit =
    val shape = declaredSymShapes.getOrElseUpdate((member, flow, marks, bindings),
      DeclaredSymShape(member, flow, marks, bindings))
    if host.currentShapes.add(shape) then host.notifyShapeListeners(shape)

  private def publishDynamic(host: NewResolvable & ShapeHost, marks: Ls[Marks])(using NewResolverState): Unit =
    DynShape().exit(marks) match
      case shape: TermShape =>
        if host.currentShapes.add(shape) then host.notifyShapeListeners(shape)
      case NoShape => ()

  private def unknownMember(host: NewResolvable, name: Str, reason: MemberLookup.Uncertainty, loc: Opt[Loc])(using NewResolverState): Unit =
    rstate.markError(host)
    val message = reason match
      case MemberLookup.Uncertainty.ValueShape =>
        msg"Cannot resolve member '$name' of a value with unknown shape."
      case MemberLookup.Uncertainty.RecordOverwrite =>
        msg"Cannot resolve member '$name' across a computed key or unknown record spread."
    resolError(host, message -> loc :: Nil)

  def unresolvedRef(ref: UnresolvedRef)(using NewResolverState): Unit =
    ref.prefixes.foreach: prefix =>
      listenTerm(prefix): shape =>
        shape.getMember(ref.id.name) match
          case MemberLookup.Found(member, marks) if rstate.canResolve(ref) || ref.resolvedMembers.contains(prefix -> member.memberSymbol) =>
            val candidate = prefix -> member.memberSymbol
            rstate.recordResolution(ref, ref.resolvedMembers.contains(candidate))(ref.resolvedMembers ::= candidate)
            publishMember(ref, member, ref.resSym, marks)
          case MemberLookup.Declared(member, bindings, marks) if rstate.canResolve(ref) || ref.resolvedMembers.contains(prefix -> member) =>
            val candidate = prefix -> member
            rstate.recordResolution(ref, ref.resolvedMembers.contains(candidate))(ref.resolvedMembers ::= candidate)
            publishDeclared(ref, member, ref.resSym, bindings, marks)
          case MemberLookup.Indexed(_, _) if rstate.canResolve(ref) =>
            resolError(ref, msg"Tuple elements must be selected by index." -> ref.toLoc :: Nil)
          case MemberLookup.Dynamic(marks) if rstate.canResolve(ref) || ref.dynamicPrefixes.contains(prefix) =>
            rstate.recordResolution(ref, ref.dynamicPrefixes.contains(prefix))(ref.dynamicPrefixes ::= prefix)
            publishDynamic(ref, marks)
          case MemberLookup.Missing =>
            // A known miss in one wildcard source is not an error: another may
            // provide the name. Lowering diagnoses references with no candidates.
            ()
          case MemberLookup.Unknown(reason, loc) if rstate.canResolve(ref) => unknownMember(ref, ref.id.name, reason, loc)

          case _ => () // Completed references only route their selected members.

  /** Inspect an overload set only once its definitions have all been published. */
  private def completedClass(shape: SymShape)(selected: ShapeListener[ClassDef], absent: () => NewResolverState ?=> Unit)(using NewResolverState): Unit =
    shape.sym.onComplete: () =>
      shape.sym.asCls match
        case S(cls) => selected(cls.defn.get)
        case N => absent()

  /** Class interpretations wait for completed overload sets, independently of term
    * companions. Aliases can supply constructor shapes; applied instances cannot.
    * Capture marks are retained for subsequent instance-member lookup. */
  private def listenClass(trm: Term)(selected: (ClassDef, Ls[Marks]) => NewResolverState ?=> Unit, reject: ShapeListener[Shape])(using NewResolverState): Unit =
    def select(cls: ClassDef, marks: Ls[Marks])(using NewResolverState): Unit =
      trm.classHead match
        case ref: NewResolvable =>
          rstate.recordResolution(ref, ref.resolvedTargets.contains(cls.sym))(ref.resolvedTargets ::= cls.sym)
        case _ => ()
      selected(cls, marks)
    def value(sh: TermShape)(using NewResolverState): Unit = sh match
      case Marked(ds: DefnShape, marks) => ds.defn match
        case cls: ClassDef => select(cls, marks :: Nil)
        case td: TermDefinition => td.tsym match
          case ctor: ClassCtorSymbol => select(ctor.associatedCls.defn.get, marks :: Nil)
          case _ => reject(sh)
        case _ => reject(sh)
      case _ => reject(sh)
    trm match
      case TyApp(base, _) => listenClass(base)(select, reject)
      case Capture(base, thru) =>
        listenClass(base)((cls, marks) => select(cls, marks ::: EntryMark(ResolutionBoundary(thru), N, NoMarks) :: Nil), reject)
      case _ => listen(trm):
        case sh: SymShape =>
          completedClass(sh)(cls => select(cls,
            ExitMark(ResolutionBoundary(cls.sym), S(sh.resSym), NoMarks) :: sh.markss),
            () => fromSymbol(sh, value, trm, _ => ()))
        case sh: TermShape => value(sh)

  def newSel(sel: NewSel)(using NewResolverState): Unit =
    log(s"newSel? sel = ${sel.showDbg}")
    def member(info: MemberLookup, description: Message, loc: Opt[Loc])(using NewResolverState): Unit = info match
      case MemberLookup.Found(bms, marks) if rstate.canResolve(sel) || sel.resolvedMembers.contains(bms.memberSymbol) =>
        log(s"newSel member: bms = ${bms.memberSymbol.showDbg}, mss = ${marks.map(_.showDbg)}")
        rstate.recordResolution(sel, sel.resolvedMembers.contains(bms.memberSymbol))(sel.resolvedMembers ::= bms.memberSymbol)
        publishMember(sel, bms, sel.resSym, marks)
      case MemberLookup.Declared(member, bindings, marks) if rstate.canResolve(sel) || sel.resolvedMembers.contains(member) =>
        rstate.recordResolution(sel, sel.resolvedMembers.contains(member))(sel.resolvedMembers ::= member)
        publishDeclared(sel, member, sel.resSym, bindings, marks)
      case MemberLookup.Indexed(field, marks) if rstate.canResolve(sel) || sel.tupleIndex == sel.id.name.toIntOption =>
        val index = sel.id.name.toIntOption
        softAssert(index.exists(_ >= 0), "Tuple lookup must identify a nonnegative index")
        rstate.recordResolution(sel, sel.tupleIndex == index)(sel.tupleIndex = index)
        listenTupleField(field): shape =>
          shape.exit(marks) match
            case value: TermShape =>
              if sel.currentShapes.add(value) then sel.notifyShapeListeners(value)
            case NoShape => ()
      case MemberLookup.Dynamic(marks) if rstate.canResolve(sel) || sel.hasDynamicTarget =>
        rstate.recordResolution(sel, sel.hasDynamicTarget)(sel.hasDynamicTarget = true)
        publishDynamic(sel, marks)
      case MemberLookup.Missing if rstate.canResolve(sel) =>
        rstate.markError(sel)
        resolError(sel, msg"$description does not contain member '${sel.id.name}'" -> loc :: Nil)
      case MemberLookup.Unknown(reason, loc) if rstate.canResolve(sel) => unknownMember(sel, sel.id.name, reason, loc)
      // Later activations still transport field values through the compiled
      // selection, but cannot choose a different member for that old syntax.
      case _ => ()
    sel.cls match
      case N => listenTerm(sel.prefix): shape =>
        log(s"newSel: sel = ${sel.showDbg}, shape = ${shape.shwDbg}")
        member(shape.getMember(sel.id.name), msg"${shape.describe.capitalize}", shape.toLoc)
      case S(cls) =>
        listenClass(cls)((cd, marks) =>
          val candidate = cd.sym -> marks
          rstate.recordResolution(sel, sel.resolvedClasses.contains(candidate))(sel.resolvedClasses ::= candidate)
          listenExt(cd.ext, ext =>
            val info = DefnShape(cd, ext).getInstanceMember(sel.id.name).withMarks(marks)
            info match
              case MemberLookup.Found(bms: BlockMemberSymbol, _) =>
                // Resolve the projection target even in an unused function. Wait
                // for the receiver before deciding whether its result may expose
                // implementation flow or only the declared member signature.
                rstate.recordResolution(sel, sel.resolvedMembers.contains(bms))(sel.resolvedMembers ::= bms)
                bms.onComplete: () =>
                  bms.asModOrObj.orElse(bms.asTrm).orElse(bms.asCls).foreach: sym =>
                    rstate.recordResolution(sel, sel.resolvedTargets.contains(sym))(sel.resolvedTargets ::= sym)
                listenTerm(sel.prefix): receiver =>
                  val selected = receiver match
                    case Marked(nominal: NominalTypeShape, context) =>
                      nominal.ancestor(cd) match
                        case S(view) => view.getMember(sel.id.name).withMarks(context :: Nil)
                        case N =>
                          // An explicit projection can name a narrower class, but
                          // it cannot recover that class's implementation arguments.
                          val opaque = abstractType(new TypeResolution(sel, msgs => resolError(sel, msgs)))
                          MemberLookup.Declared(bms, cd.tparams.map(_.sym -> opaque).toMap, context :: Nil)
                    case _ => info
                  member(selected, msg"Class '${cd.sym.nme}'", cd.toLoc)
              case _ => member(info, msg"Class '${cd.sym.nme}'", cd.toLoc))
        , sh =>
          rstate.markError(sel)
          resolError(sel, msg"${sh.describe.capitalize} cannot be used as a projection class." -> sh.toLoc :: Nil)
        )
  
  /** Both constructor references and explicit `new` use the same definition and
    * parameter lists, including auxiliary constructor(...) lists. A partial `new`
    * therefore retains the same callable head and contexts as a partial C(...).
    */
  private def constructorShape(cls: ClassDef, ext: Opt[TermShape])(using NewResolverState): DefnShape =
    // The shared cache distinguishes the constructor's TermDefinition from its
    // ClassDef, even though both definitions cross the same resolution boundary.
    val symbol: ClassCtorSymbol | ClassSymbol = cls.ctorSym.getOrElse(cls.sym)
    val definition = symbol.defn.get
    val shape = defnShapes.getOrElseUpdate(symbol, {
      val base = if cls.ctorSym.isDefined then S(BaseShape(cls, ext)) else ext
      DefnShape(definition, base)
    })
    softAssert(shape.defn is definition)
    if cls.ctorSym.isDefined then shape.ext match
      case S(base: BaseShape) => softAssert((base.defn is cls) && base.ext == ext)
      case _ => softAssert(false, "Constructor shape is missing its class base")
    else softAssert(shape.ext == ext)
    shape
  
  def resolveNew(nw: Term.New)(using NewResolverState): Unit = nw.cls.classHead match
    case Term.Error() => rstate.markError(nw)
    // Static construction records a resolved class on its reference for lowering.
    // Other expression forms require dynamic construction, even if they publish
    // no shapes (for example an unsupported reference in an extends clause).
    case _: NewResolvable => resolveNewClass(nw)
    case _ =>
      rstate.markError(nw)
      resolError(nw, msg"Invalid class expression: ${nw.cls.describe}" -> nw.cls.toLoc :: Nil)
  
  private def resolveNewClass(nw: Term.New)(using NewResolverState): Unit =
    // listenClass preserves captures and supplies the same class-body exit as a
    // constructor value. In particular, a captured constructor already carries
    // that exit; adding a second one here would duplicate its instance boundary.
    listenClass(nw.cls)((cd, marks) =>
      listenExt(cd.ext, extsh =>
        val dsh = constructorShape(cd, extsh)
        val sh = newShapes.getOrElseUpdate((cd.sym, marks, nw.resSym), {
          def typeArgs(term: Term)(using NewResolverState): Opt[Ls[Term]] = term match
            case TyApp(_, args) => S(args)
            case Capture(base, _) => typeArgs(base)
            case _ => N
          typeArgs(nw.cls).foreach(applyTypeArguments(dsh, marks, _, nw))
          dsh.unappliedParams.lazyZip(nw.args).foreach:
            case ((ps, _), args) => zipArgs(marks, ps.params, ps.restParam, args, nw, dsh)
          NewShape(dsh, cd.sym, marks, nw.args, nw)
        })
        if nw.currentShapes.add(sh) then nw.notifyShapeListeners(sh)
      )
    , shape =>
      if !rstate.hasError(nw) then
        rstate.markError(nw)
        resolError(nw, msg"${shape.describe.capitalize} cannot be instantiated with keyword 'new'." -> shape.toLoc :: Nil)
    )
  
  def defineVar(sym: LocalSymbol | TermSymbol, rhs: Term)(using NewResolverState): DefineVar =
    if newResolution then sym match
      case sym: TermSymbol =>
        // symShape(sym, rhs)
        // ???
        // sym.defn.get
        println(s"TODO: defineVar for TermSymbol ${sym.showDbg}")
      case sym: LocalSymbol =>
        listen(rhs): sh =>
          if sym.currentShapes.add(sh) then
            sym.notifyShapeListeners(sh)
    DefineVar(sym, rhs)
  
  def listenDefn(sym: TermSymbol, listener: Listener)(using NewResolverState): Unit =
    sym.defn match
    case S(td: TermDefinition) if td.params.isEmpty =>
      td.body match
      case S(body) =>
        listenTerm(body)(listener)
      case N =>
        ??? // TODO error
    case S(d) =>
      listener(defnShapes.getOrElseUpdate(sym, DefnShape(d, N)))
    case N =>
      sym.defnListeners += (d => listener(defnShapes.getOrElseUpdate(sym, DefnShape(d, N))))
  
  def pipeTerm(from: Term, to: ShapeHost)(using NewResolverState): Unit =
    log(s"pipeTerm: from = ${from.showDbg}, to = ${to.showDbg}; ${to.currentShapes}")
    listenTerm(from): sh =>
      if to.currentShapes.add(sh) then
        to.notifyShapeListeners(sh)
  
  def listenExt(ext: Opt[Term], listener: ShapeListener[Opt[TermShape]])(using NewResolverState): Unit =
    ext match
    case S(trm) =>
      listenTerm(trm): sh =>
        listener(S(sh))
    case N =>
      listener(N)
  
  private def fromSymbol(shape: SymShape, listener: Listener, source: Term,
      selected: ShapeListener[DefinitionSymbol[?]])(using NewResolverState): Unit = shape match
    case declared: DeclaredSymShape =>
      listenDeclaredMember(shape.sym, declared.bindings, shape.resSym, source, selected): value =>
        value.exit(shape.markss) match
          case value: TermShape => listener(value)
          case NoShape => ()
    case _ => fromBMS(shape.sym, shape.resSym, shape.markss, listener, source, selected)

  def fromBMS(bms: BlockMemberSymbol, resSym: FlowSymbol, markss: Ls[Marks], listener: Listener,
      trm: Term, selected: ShapeListener[DefinitionSymbol[?]])(using NewResolverState) =
    log(s"listenBMS: bms = ${bms.describe}")
    bms.onComplete: () =>
      log(s"listenedBMS: bms = ${bms.describe}")
      bms.asModOrObj orElse bms.asTrm orElse bms.asCls match
      case S(sym: (ModuleOrObjectSymbol | TermSymbol | ClassSymbol)) =>
        // Selection is independent of the selected value's shape. In particular,
        // an assignment needs its target even if the value has no inferred shape.
        // Pattern resolution supplies its own interpretation of the selected head.
        selected(sym)
        val wrappedListener: Listener = sh =>
          log(s"fromBMS: bms = ${bms.showDbg}, sh = ${sh.shwDbg}, flow = ${resSym.showDbg}, markss = ${markss.map(_.showDbg)}")
          val sh0 = sh
          // Modules and objects introduce no enter/exit boundary of their own.
          // Adding an exit here would create a mismatch because we do not track module captures explicitly.
          val exited = sym match
            case _: ModuleOrObjectSymbol => sh
            case _ => MarkedShape.exit(sh, ResolutionBoundary(sym), S(resSym))
          exited.exit(markss) match
            case NoShape =>
              log(s"FILTER OUT ${sh.shwDbg} for ${sym.showDbg} % ${resSym.showDbg}")
            case sh: TermShape =>
              // if sh is sh0
              if sh0.isInstanceOf[MarkedShape]
              then log(s"MATCH ${sh.shwDbg} for ${sym.showDbg} % ${resSym.showDbg}")
              else log(s"PUSH ${sh.shwDbg}")
              listener(sh)
        sym.defn match
        case S(td: TermDefinition) if td.params.isEmpty =>
          log(s"listenTerm: td.body = ${td.body.fold("N")(_.showDbg)}")
          resultSignature(td) match
            case S(sign) => listenTypeValues(sign): shape =>
              td.tsym.decl match
                case S(_: Param) => wrappedListener(MarkedShape.enter(shape, ResolutionBoundary(td.tsym), N))
                case _ => wrappedListener(shape)
            case N => td.body.foreach: body =>
              listenTerm(body): shape =>
                // Legacy synthesized fields use a plain reference to their
                // constructor parameter. Supply the field capture explicitly;
                // new-resolution fields already carry it in their body syntax.
                val captured = (td.tsym.decl, body) match
                  case (S(_: Param), Ref(_: VarSymbol)) =>
                    MarkedShape.enter(shape, ResolutionBoundary(td.tsym), N)
                  case _ => shape
                wrappedListener(captured)
        case S(d: TermDefinition) =>
          d.tsym match
          case ccs: ClassCtorSymbol =>
            val cls = ccs.associatedCls.defn.get
            listenExt(cls.ext, extsh => wrappedListener(constructorShape(cls, extsh)))
          case _ =>
            wrappedListener(defnShapes.getOrElseUpdate(sym, DefnShape(d, N)))
        case S(d: ClassLikeDef) =>
          listenExt(d.ext, extsh =>
            // defnShapes.get(sym).foreach: existing =>
            //   ??? // TODO error?
            wrappedListener(defnShapes.getOrElseUpdate(sym, DefnShape(d, extsh)))
          )
        case N =>
          // sym.defnListeners += (d => listener(defnShapes.getOrElseUpdate(sym, DefnShape(d))))
          softAssert(false, s"Symbol definition of ${sym} is not set upon completion of ${bms}")
      case _ =>
        def reportError(using NewResolverState) = resolError(trm,
          msg"Expected a term; got ${bms.describe} '${bms.nme}'" -> N :: Nil)
        trm.withoutCaptures match
          case ref: NewResolvable =>
            if !rstate.hasError(ref) then
              rstate.markError(ref)
              reportError
          case _ => reportError
  
  /** Request the term interpretation of a reference without requiring a consumer
    * of its value shape. Direct definition references already identify the target;
    * overload sets need listeners, including when their definitions arrive later.
    */
  def requireTerm(trm: Term)(using NewResolverState): Unit = trm.withoutCaptures match
    case direct @ MemberRef(sym: TermSymbol) =>
      // Selecting a known field does not require resolving the field's value.
      softAssert(direct.resolvedTargets.forall(_ is sym))
      direct.resolvedTargets = sym :: Nil
    case _: NewResolvable => listenTerm(trm)(_ => ())
    case _ => ()

  /** Annotation identity is needed before elaborating the annotated body. Read
    * the main symbol now, without waiting for a value or inspecting unfinished
    * definitions. Keep validating selections/opens: a later distinct candidate
    * must be an error, since it cannot change an already interpreted annotation.
    */
  def annotationSymbol(trm: Term)(using NewResolverState): Opt[Symbol] = trm match
    case Capture(base, _) => annotationSymbol(base)
    case TyApp(base, _) => annotationSymbol(base)
    case App(base, _) => annotationSymbol(base)
    case ref: NewRefImpl => S(ref.sym)
    case _: NewSel | _: UnresolvedRef =>
      val symbols = mutable.LinkedHashSet.empty[BlockMemberSymbol]
      var collecting = true
      var failed = false
      def fail()(using NewResolverState): Unit = if !failed then
        failed = true
        resolError(trm, msg"An annotation's main symbol must be uniquely known when the annotation is elaborated." -> N :: Nil)
      // This listener validates an elaboration decision; it transports no values.
      // Keep checking late candidates in the defining block, but never mutate its
      // local bookkeeping when a completed block's listeners run in a consumer.
      listen(trm): shape =>
        if rstate.canResolve(trm) then shape match
          case sh: SymShape =>
            if symbols.add(sh.sym) && !collecting then fail()
          case _ => fail()
      collecting = false
      symbols.toList match
        case symbol :: Nil if !failed => S(symbol)
        case _ => fail(); N
    // TODO: Ref(sym: BuiltinSymbol) is a legacy representation that still needs
    // updating to the new reference forms, even when using new resolution.
    case Ref(sym: BuiltinSymbol) => S(sym)
    case _ =>
      resolError(trm, msg"An annotation must have a known main symbol." -> N :: Nil)
      N

  def listenTerm(trm: Term)(listener: Listener)(using NewResolverState): Unit =
    log(s"listenTerm: trm = ${trm.showDbg}")
    listen(trm):
      case sh: TermShape =>
        listener(sh)
      case ss: SymShape =>
        fromSymbol(ss, listener, trm, sym =>
          trm.withoutCaptures match
          case ref: NewResolvable =>
            rstate.recordResolution(ref, ref.resolvedTargets.contains(sym))(ref.resolvedTargets ::= sym)
          case _ => ()
        )
  
  /** Subscribe to spread operands once for each tuple or record AST node. Record
    * the node before calling start: a recursive spread can call listen on the same
    * node before start returns. Testing shapes.isEmpty would not prevent duplicate
    * subscriptions while the node is waiting for a forward definition. Deliver
    * cached shapes to each listener, which is already registered for future shapes.
    */
  private def listenAggregate(aggregate: Tup | Rcd, listener: ShapeListener[Shape])
      (start: (Listener) => Unit)(using NewResolverState): Unit =
    val first = aggregateProducers.add(new Identity(aggregate))
    // An imported definition can already have shapes computed by its own elaborator.
    // Send those shapes to this listener even if first is true; recomputing the same
    // shapes below will not notify it, because shapes.add rejects duplicates.
    aggregate.replayShapes(listener)
    if first then
      start: shape =>
        if aggregate.currentShapes.add(shape) then aggregate.notifyShapeListeners(shape)

  def listen(trm: Term, discardMarks: Bool = false)(listener: ShapeListener[Shape])(using NewResolverState): Unit =
    log(s"listen: trm = ${trm.showDbg}")
    trm.addShapeListener(listener)
    trm match
    case _: SynthSel =>
      lastWords("Synthetic selections must not enter new resolution")
    case Asc(_, sign) => listenTypeValues(sign)(listener)
    case _: DynSel | _: DynNew => listener(DynShape())
    case TyApp(underlying, args) =>
      listen(underlying, discardMarks): shape =>
        def instantiate(value: TermShape)(using NewResolverState): Unit = value.applicationHead match
          case (callee: (DefnShape | CallableTypeShape), marks) => applyTypeArguments(callee, marks, args, trm)
          case _ => ()
        shape match
          case sym: SymShape => fromSymbol(sym, instantiate, underlying, _ => ())
          case value: TermShape => instantiate(value)
        listener(shape)
    case Mut(underlying: Tup) => listenTerm(underlying):
      case Marked(tuple: TupleShape, marks) =>
        // Array methods can change both the elements and the length. Retain the
        // producer dependency, but none of the initializer's fixed layout.
        val fields = TupleShape.Unknown(trm, Nil, UnknownValueShape(trm)) :: Nil
        TupleShape(trm, TupleShape.Rest(tuple, fields) :: Nil)(this).exit(marks) match
          case shape: TermShape => listener(shape)
          case NoShape => ()
      case shape => listener(shape)
    case Mut(underlying) => listenTerm(underlying)(listener)
    case tuple: Tup => listenAggregate(tuple, listener): publish =>
        def expand(elems: Ls[Elem], reversed: Ls[TupleShape.Element])(using NewResolverState): Unit = elems match
          case Nil =>
            // A sole spread preserves its operand's shape and context exactly.
            // Besides avoiding wrappers, this lets recursive rest forwarding
            // reach the same fixed point as forwarding an ordinary parameter.
            val shape = reversed match
              case TupleShape.Spread(shape, NoMarks) :: Nil => shape
              case TupleShape.Spread(shape, marks: SomeMarks) :: Nil => MarkedShape(shape, marks)
              case _ => TupleShape(tuple, reversed.reverse)(this)
            publish(shape)
          case (field: Fld) :: rest => expand(rest, TupleShape.Field(field, Nil) :: reversed)
          case Spd(_, term) :: rest =>
            val spreadKey = new Object
            listenTerm(term): sh =>
              if rstate.spreadInputs.getOrElseUpdate(spreadKey, mutable.Set.empty).add(sh) then sh match
                case Marked(shape: TupleShape, marks) =>
                  // Widen an incoming candidate that already contains its own
                  // producer in this context. For `fun growing(n) = ‹...› [n, ...growing(n - 1)] ‹...›`,
                  // this replaces the recursive operand with an arbitrary sequence,
                  // retaining the surrounding `n` field and the spread's marks.
                  // Further feedback in the same context produces the same widened
                  // candidate, so the host's deduplication stops that expansion.
                  // Earlier candidates remain valid alternatives. A pending spread
                  // never reaches this branch: it waits for a shape notification.
                  val spread = if shape.containsSpread(shape.source, marks)
                    then TupleShape.unknown(shape.source)(this)
                    else shape
                  expand(rest, TupleShape.Spread(spread, marks) :: reversed)
                case Marked(_: DynShape, marks) =>
                  val spread = TupleShape(term, TupleShape.Unknown(term, Nil, DynShape()) :: Nil)(this)
                  expand(rest, TupleShape.Spread(spread, marks) :: reversed)
                case Marked(_, marks) =>
                  // Opaque iterables (e.g. external Arrays) have no resolved
                  // element layout. Their runtime spread is still permitted.
                  expand(rest, TupleShape.Spread(TupleShape.unknown(term)(this), marks) :: reversed)
        expand(tuple.fields, Nil)
    case record: Rcd => listenAggregate(record, listener): publish =>
        def expand(stats: Ls[Statement], reversed: Ls[RecordShape.Element])(using NewResolverState): Unit = stats match
          case Nil =>
            val shape = RecordShape(record, reversed.reverse)
            publish(shape)
          case (field: RcdField) :: rest => expand(rest, RecordShape.Field(field) :: reversed)
          case RcdSpread(term) :: rest =>
            val spreadKey = new Object
            listenTerm(term): shape =>
              if rstate.spreadInputs.getOrElseUpdate(spreadKey, mutable.Set.empty).add(shape) then shape match
                case Marked(shape: RecordShape, marks) =>
                  // Bound recursive record producers just as for tuple spreads.
                  // Keep surrounding explicit fields even when the spread widens.
                  val spread = if shape.containsSpread(shape.source, marks)
                    then RecordShape(shape.source, RecordShape.Unknown :: Nil)
                    else shape
                  expand(rest, RecordShape.Spread(spread, marks) :: reversed)
                case Marked(_: DynShape, marks) => expand(rest, RecordShape.Dynamic(marks :: Nil) :: reversed)
                case _ => expand(rest, RecordShape.Unknown :: reversed)
          case _ :: rest => expand(rest, reversed)
        expand(record.stats, Nil)
    case intro: IntroTerm =>
      val sh = introShapes.getOrElseUpdate(new Identity(intro), {
        log(s"introShape: intro = $intro")
        IntroShape(intro)
      })
      listener(sh)
    case Ref(sym) if sym is sym.getState.globalThisSymbol => listener(DynShape())
    case SelfRef(sym) if sym is sym.getState.globalThisSymbol => listener(DynShape())
    case ref @ Ref(loc: LocalSymbol) =>
      loc.subscribeToShapes(listener)
    case ref @ SimpleRef(sym) =>
      sym match
      case loc: LocalSymbol =>
        loc.subscribeToShapes(listener)
      case _: BuiltinSymbol =>
        lastWords("Builtin symbols must not enter new resolution as SimpleRef")
    case SelfRef(sym) =>
      // A receiver can be referenced before its body is complete or after its
      // definition has already been published. The definition listener handles both.
      def completed(defn: ClassLikeDef)(using NewResolverState): Unit =
        listenExt(defn.ext, ext =>
          // Each inner symbol has one self shape; repeated notifications must agree.
          val shape = selfShapes.getOrElseUpdate(sym, BaseShape(defn, ext))
          softAssert(shape.defn is defn)
          softAssert(shape.ext == ext)
          listener(shape))
      val symbol = sym.asDefnSym
      symbol.defn match
        case S(defn) => completed(defn)
        case N => symbol.defnListeners += completed
    case ref @ MemberRef(sym: TermSymbol) =>
      ???
      // listenDefn(sym, sh =>
      //   listener(MarkedShape.enter(sh, sym, S(ref.resSym))))
    case ref @ MemberRef(sym: BlockMemberSymbol) =>
      val fs = ref.resSym
      val sh = symShapes.getOrElseUpdate((sym, fs, Nil), SymShape(sym, fs, Nil))
      listener(sh)
    case Capture(base, thru) =>
      if discardMarks then
        listen(base)(listener)
      else listenTerm(base): sh =>
        listener(MarkedShape.enter(sh, ResolutionBoundary(thru), N))
    case ref @ Ref(sym: InnerSymbol) => // TODO: remove remaining occurrences of such refs
      sym.addShapeListener(listener)
    case ref @ Ref(bsym: BlockMemberSymbol) =>
      ???
    case res: ResolvableImpl =>
      res.replayShapes(listener)
      // ???
    case sh: ShapeHost =>
      sh.replayShapes(listener)
    case Blk(sts, rs) =>
      listen(rs)(listener)
    // case u: UnitVal =>
    case Missing =>
      () // FIXME: Currently get this from light-elaborated Predef import
    case _ =>
      println(s"TODO: listen for ${trm.describe} (${trm.getClass})")
      ()
  
end NewResolver
