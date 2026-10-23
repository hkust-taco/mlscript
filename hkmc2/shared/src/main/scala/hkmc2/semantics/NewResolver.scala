package hkmc2
package semantics

import scala.collection.mutable
import scala.annotation.tailrec

import hkmc2.utils.*, shorthands.*
import hkmc2.Message.MessageContext
import syntax.*
import Term.*

import Elaborator.*
import hkmc2.syntax.LetBind


/** Best-effort name, member, and call resolution, not a type checker.
  * Shape propagation helps find targets and diagnose obvious mistakes; it does
  * not prove type safety, even in strict mode. Leave complicated or expensive
  * compatibility checks to a later type-checking pass and accept those cases
  * leniently. This does not permit dropping flows: selections and ambiguity
  * detection need every possible target. Approximate complicated relationships
  * by joining their flows, even when lengths or correlations are lost.
  */
class NewResolver:
  self: Elaborator =>
  import tl.*
  import ResolutionContext.Listener
  
  private def appShapes(using rs: ResolutionContext) = rs.state.appShapes
  private def newShapes(using rs: ResolutionContext) = rs.state.newShapes
  private def introShapes(using rs: ResolutionContext) = rs.state.introShapes
  private def symShapes(using rs: ResolutionContext) = rs.state.symShapes
  private def declaredSymShapes(using rs: ResolutionContext) = rs.state.declaredSymShapes
  private def selfShapes(using rs: ResolutionContext) = rs.state.selfShapes
  // Tuple and record AST nodes for which we have subscribed to spread operands.
  // Each node owns its shapes and listeners. Comparing nodes by structural equality
  // would skip subscriptions for a second equal expression, leaving its listeners
  // without results; compare their identities instead.
  private def aggregateProducers(using rs: ResolutionContext) = rs.state.aggregateProducers
  private def defnShapes(using rs: ResolutionContext) = rs.state.defnShapes
  // These results carry no value flow or lexical context. Reuse one immutable
  // shape so repeated subscriptions do not manufacture distinct unit candidates.
  private lazy val unitResultShape = IntroShape(unit, N)
  
  /** Interpret types through completed symbolic candidates, independently of term overloads. */
  def typeResolution(term: Term)(using rs: ResolutionContext): TypeResolution =
    rs.state.typeInterpretations.get(new Identity(term)).orElse(term.typeInterpretation) match
      case S(result) => result
      case N =>
        val result = new TypeResolution(term, messages => resolError(term, messages))
        // Cache before following a recursive alias. Imported legacy annotations
        // have no stored interpretation: their new inference graph must remain
        // private to this consumer, including listeners on synthesized hosts.
        rs.state.typeInterpretations(new Identity(term)) = result
        def selectInto(symbol: TypeSymbol, publish: ShapeListener[TypeShape])(using ResolutionContext): Unit =
          term.withoutCaptures match
            case ref: NewResolvable =>
              rctx.recordResolution(ref, ref.resolvedTargets.contains(symbol))(ref.resolvedTargets ::= symbol)
            case _ => ()
          def definition(defn: Definition)(using ResolutionContext): Unit = defn match
            case cls: ClassLikeDef => publish(TypeShape.Nominal(cls))
            // Nothing admits no values. In particular, a rejected promise must
            // not contribute an unknown fulfillment alternative to catch or any.
            case alias: TypeDef if alias.sym is prelude.builtins.Nothing => publish(TypeShape.Bottom)
            case alias: TypeDef =>
              publish(TypeShape.Alias(alias.sym, alias.rhs.map(typeResolution)))
              // Validate unused annotations too, once their forward source graph
              // is complete. Interface observation uses the same gate below.
              withCanonicalType(DeclaredType(result, Map.empty, TypeSubstitution.empty, true)(N))(_ => ())
            case _ => publish(TypeShape.Abstract)
          symbol.defn match
            case S(defn) => definition(defn)
            case N => symbol.defnListeners += definition
        def select(symbol: TypeSymbol)(using ResolutionContext): Unit = selectInto(symbol, result.publish)
        def selectReference(symbol: TypeSymbol, shape: SymShape)(using ResolutionContext): Unit =
          val (source, instances) = shape match
            case contextual: ContextualSymShape => (contextual.source, contextual.instances)
            case source: CoreSymShape => (source, TypeSubstitution.empty)
          val bindings = source match
            case declared: DeclaredSymShape => declared.bindings
            case _ => Map.empty[VarSymbol, DeclaredType]
          if shape.markss.isEmpty && bindings.isEmpty && instances.isEmpty then select(symbol)
          else
            // A symbol identity determines erasure, but not the environment of
            // its free binders. Keep the selected declaration at its own endpoint
            // and transport it just as a syntactic Capture transports a type.
            val key = (new Identity(term), symbol)
            val base = rctx.state.selectedTypes.get(key).getOrElse:
              val base = new TypeResolution(term, result.fail)
              rctx.state.selectedTypes(key) = base
              selectInto(symbol, base.publish)
              base
            result.publish(TypeShape.Reference(base, shape.markss, bindings, instances))
        def reject(shape: Shape)(using ResolutionContext): Unit =
          result.fail(msg"${shape.describe.capitalize} cannot be used as a type" -> shape.toLoc :: Nil)
          result.publish(TypeShape.Abstract)
        def selectMember(member: BlockMemberSymbol)(using ResolutionContext): Unit = member.onComplete: () =>
          member.asTpe.orElse(member.asModOrObj) match
            case S(symbol) => select(symbol)
            case N =>
              result.fail(msg"${member.describe.capitalize} cannot be used as a type" -> member.headerLoc :: Nil)
              result.publish(TypeShape.Abstract)
        term match
          // Imported declarations can still contain legacy references.
          case Ref(symbol: TypeSymbol) => select(symbol)
          case Ref(member: BlockMemberSymbol) => selectMember(member)
          // Imported parent declarations can contain legacy synthesized selections.
          // Their identities were fixed by the old resolver; do not reinterpret
          // their term syntax or consult unfinished new-resolution candidates.
          case ref: (SynthSel | Sel | Resolved) => ref.legacyResolvedSym match
            case S(symbol: TypeSymbol) => select(symbol)
            case S(ctor: ClassCtorSymbol) => select(ctor.associatedCls)
            case S(member: BlockMemberSymbol) => selectMember(member)
            case _ =>
              result.fail(msg"This reference does not denote a type." -> ref.toLoc :: Nil)
              result.publish(TypeShape.Abstract)
          // An alias's lexical qualification substitutes type references; it
          // does not cross an invocation boundary. Captured function and class
          // parameters still retain their actual value-scope crossings.
          case Capture(base, _: TypeAliasSymbol) => typeResolution(base).listen(result.publish)
          case Capture(base, thru) => result.publish(TypeShape.Reference(typeResolution(base),
            EntryMark(ResolutionBoundary(thru), N, NoMarks) :: Nil, Map.empty, TypeSubstitution.empty))
          case TyApp(base, args) =>
            rctx.recordAppliedTypeArguments(base.withoutCaptures, args.length)
            result.publish(TypeShape.Applied(typeResolution(base), args.map(typeResolution)))
          case Forall(params, outer, body) =>
            result.publish(TypeShape.Polymorphic(params.map: param =>
              TypeQuantifier(TypeShape.Parameter(param.sym, param.sym.inferenceHost),
                param.lb.map(typeResolution), param.ub.map(typeResolution))
            , outer, typeResolution(body)))
          case CompType(left, right, union) =>
            val l = typeResolution(left)
            val r = typeResolution(right)
            result.publish(if union then TypeShape.Union(l, r) else TypeShape.Intersection(l, r))
          case Neg(base) => result.publish(TypeShape.Negation(typeResolution(base)))
          case DynTy() => result.publish(TypeShape.Dynamic)
          case FunTy(params, ret, _) => result.publish(TypeShape.Function(params, typeResolution(ret)))
          case UnitVal() => result.publish(TypeShape.Unit)
          case WildcardTy(input, output) => result.publish(TypeShape.Wildcard(input.map(typeResolution), output.map(typeResolution)))
          case SimpleRef(sym: VarSymbol) if sym.decl.exists(_.isInstanceOf[TyParam]) =>
            result.publish(TypeShape.Parameter(sym, sym.inferenceHost))
          case Ref(sym: VarSymbol) if sym.decl.exists(_.isInstanceOf[TyParam]) =>
            result.publish(TypeShape.Parameter(sym, sym.inferenceHost))
          case Tup(fields) => result.publish:
            TypeShape.Tuple:
              fields.map:
                case Fld(_, sign, _) => TypeShape.TupleField(typeResolution(sign), spread = false)
                case Spd(_, sign, _) => TypeShape.TupleField(typeResolution(sign), spread = true)
          case record: Rcd =>
            val fields = record.stats.collect { case field: RcdField => field }
            if fields.length != record.stats.length || fields.exists(_.key.isEmpty)
            then
              result.fail(msg"A record type requires statically named fields." -> record.toLoc :: Nil)
              result.publish(TypeShape.Abstract)
            else result.publish(TypeShape.Record(record,
              fields.reverse.distinctBy(_.key).reverse.map(field => field -> typeResolution(field.rhs))))
          // Signed numeric literals use operator applications in the syntax tree.
          // Their primitive interface is not recovered from these applications yet.
          case App(op: AnyRef_, Tup(Fld(_, Lit(_: Tree.IntLit | _: Tree.DecLit), _) :: Nil))
              if op.sym.isInstanceOf[BuiltinSymbol] && (op.sym.nme === "-" || op.sym.nme === "+") =>
            result.publish(TypeShape.Abstract)
          // Ignore undefined in annotations: `T | undefined` has the same
          // resolution candidates as T.
          case Lit(Tree.UnitLit(false)) => result.publish(TypeShape.Bottom)
          case literal: Lit =>
            // Singleton annotations retain literal values, which read no binders.
            rctx.recordTemplateBinders(result, S(Set.empty))
            listenTerm(literal)(shape => result.publish(TypeShape.Inferred(shape)))
          case Missing | Error() =>
            result.publish(TypeShape.Abstract)
          case _ => listen(term, discardMarks = true):
            case shape: SymShape => shape.sym.onComplete: () =>
              shape.sym.asTpe.orElse(shape.sym.asModOrObj) match
                case S(symbol) => selectReference(symbol, shape)
                case N => reject(shape)
            case shape: TermShape => reject(shape)
        result

  /** Register complete signatures while resolution can still publish candidates. Arrow operands
    * need their own interpretations: erasure may consume the arrows as physical parameter lists.
    */
  def registerSignature(sign: Term)(using ResolutionContext): Unit =
    sign.typeInterpretation = S(typeResolution(sign))
    sign match
      case Forall(params, _, body) =>
        params.foreach: param =>
          param.lb.foreach(registerSignature)
          param.ub.foreach(registerSignature)
        registerSignature(body)
      case FunTy(lhs, rhs, _) =>
        lhs match
          case Tup(fields) => fields.foreach:
            case Fld(_, term, _) => registerSignature(term)
            case _ => ()
          case single => registerSignature(single)
        registerSignature(rhs)
      case _ => ()

  // Guard and dependency analysis inspect the declaration behind a capture;
  // its value-scope marks do not change whether it supplies a type constructor.
  private def typeApplicationTarget(base: TypeResolution)(using ResolutionContext): Opt[TypeShape] =
    @tailrec
    def loop(base: TypeResolution, seen: Set[TypeResolution]): Opt[TypeShape] =
      if seen(base) then N else base.currentShapes.toList match
        case TypeShape.Reference(inner, _, _, _) :: Nil => loop(inner, seen + base)
        case shape :: Nil => S(shape)
        case _ => N
    loop(base, Set.empty)

  /** Compute free binders on the finite source graph, not on substituted types.
    * Each edge can hide binders introduced by an alias or quantifier. Iterating
    * finite binder sets reaches a fixed point even for mutually recursive types.
    * An unresolved target is a dependency still to discover, never a closed type.
    * Valid written types have one target (validation rejects ambiguity). The
    * synthetic nodes that can receive more candidates use no ambient bindings.
    * The unguarded variant uses the same equations but stops dependencies at
    * structural constructors, to distinguish forwarding and guarding aliases.
    */
  private def typeDependencies(resolution: TypeResolution)(using ResolutionContext)
      : Either[Set[TypeResolution], Set[VarSymbol]] = typeDependencies(resolution, false)

  private def typeDependencies(resolution: TypeResolution, unguardedOnly: Bool)(using ResolutionContext)
      : Either[Set[TypeResolution], Set[VarSymbol]] =
    dependencies(resolution, if unguardedOnly then DependencyMode.UnguardedBindings else DependencyMode.Bindings).map(_.getOrElse(
      lastWords("Binding dependencies are finite: only template hosts are unbounded")))

  /** The binders whose call-site instances an observation of the type can read,
    * or N when the source graph does not fix them. These are the free binders
    * above, plus those of the references retained by the synthesized nodes: such
    * a node reads no ambient binding, but it does instantiate its retained
    * reference with the ambient instances, so the reference's own free binders
    * count (see instantiateShape). An inferred-element or omitted-argument host
    * contributes the scope of its templates (NewResolverState.templateBinders).
    */
  private def instanceDependencies(resolution: TypeResolution)(using ResolutionContext)
      : Either[Set[TypeResolution], Opt[Set[VarSymbol]]] = dependencies(resolution, DependencyMode.Instances)

  // All three queries solve the same source-graph equations, but only instance
  // support follows retained references and only guardedness stops at constructors.
  private enum DependencyMode:
    case Bindings, UnguardedBindings, Instances

  // N is the unbounded set: binding dependencies never produce it.
  private type Binders = Opt[Set[VarSymbol]]
  private def union(left: Binders, right: => Binders): Binders =
    left.flatMap(binders => right.map(binders ++ _))
  private def hide(binders: Binders, bound: Set[VarSymbol]): Binders = binders.map(_ -- bound)

  private def dependencies(resolution: TypeResolution, mode: DependencyMode)(using ResolutionContext)
      : Either[Set[TypeResolution], Binders] =
    val throughReferences = mode == DependencyMode.Instances
    val unguardedOnly = mode == DependencyMode.UnguardedBindings
    val bindingCache = if unguardedOnly then rctx.state.unguardedTypeDependencies else rctx.state.typeDependencies
    def cached(res: TypeResolution)(using ResolutionContext): Opt[Binders] =
      if throughReferences then rctx.state.typeInstanceDependencies.get(res)
      else bindingCache.get(res).map(S(_))
    def store(res: TypeResolution, binders: Binders)(using ResolutionContext): Unit =
      if throughReferences then rctx.state.typeInstanceDependencies(res) = binders
      else bindingCache(res) = binders.getOrElse(
        lastWords("Binding dependencies are finite: only template hosts are unbounded"))
    cached(resolution) match
    case S(binders) => R(binders)
    case N =>
      val graph = mutable.LinkedHashMap.empty[TypeResolution, (Binders, Ls[(TypeResolution, Set[VarSymbol])])]
      val argumentUses = mutable.Map.empty[TypeResolution, Ls[(TypeResolution, VarSymbol, TypeResolution)]]
      val pending = mutable.Set.empty[TypeResolution]
      // Instance mode: a generic type use that omits arguments expands them to
      // holes (see omittedType) whose bounds are templates written where the
      // use is, so the use's scope counts. Whether a reference is bare or the
      // base of an application, and with how many arguments, was recorded when
      // the application was interpreted: it is intrinsic to the reference, so
      // this summary does not depend on which traversal reached the node first.
      def omitsArguments(res: TypeResolution, formals: Int)(using ResolutionContext): Bool =
        formals > 0 && rctx.appliedTypeArgumentsOf(res.source.withoutCaptures).forall(_ < formals)
      def useScope(res: TypeResolution)(using ResolutionContext): Binders = rctx.lexicalBindersOf(res.source)
      def visit(res: TypeResolution): Unit = if !graph.contains(res) then
        graph(res) = (S(Set.empty), Nil)
        cached(res) match
          case S(binders) => graph(res) = (binders, Nil)
          case N =>
            val shapes = res.currentShapes.toList
            if shapes.isEmpty then pending += res
            // A host of templates reads the binders of their scope (instance mode).
            val templates = if throughReferences then rctx.templateBindersOf(res) else N
            var direct: Binders = templates.getOrElse(S(Set.empty))
            var edges = List.empty[(TypeResolution, Set[VarSymbol])]
            def edge(child: TypeResolution, hidden: Set[VarSymbol]): Unit =
              edges ::= child -> hidden
              visit(child)
            def child(res: TypeResolution): Unit = edge(res, Set.empty)
            // All modes discover the whole source graph. Guardedness alone
            // stops propagating dependencies across a structural constructor.
            def guardedChild(res: TypeResolution): Unit = if unguardedOnly then visit(res) else child(res)
            def reference(tpe: DeclaredType): Unit =
              if throughReferences then
                child(tpe.resolution)
                // Reading through the instances the reference already retains
                // reads the templates written at their sites (see closure).
                direct = tpe.instances.values.foldLeft(direct)((acc, instance) => union(acc, instance.siteBinders))
              else visit(tpe.resolution)
              tpe.bindings.values.foreach(reference)
            shapes.foreach:
              case TypeShape.Parameter(symbol, _) => symbol match
                // A reference to an already selected instance reads the
                // templates written at its site; no ambient binding selects it.
                case instance: TypeParameterInstance if throughReferences => direct = union(direct, instance.siteBinders)
                case _ => direct = union(direct, S(Set(symbol)))
              case TypeShape.Nominal(defn) =>
                // This immutable declaration metadata belongs to the original
                // graph, even when the type was reached through an imported AST.
                // An unrecorded declaration (reported by lexicalBinders) has an
                // unknown scope. Binding dependencies must stay finite: they then
                // omit the enclosing binders, which may drop a needed binding.
                if !unguardedOnly then
                  direct = union(direct, lexicalBinders(defn.sym).orElse(if throughReferences then N else S(Set.empty)))
                if throughReferences && omitsArguments(res, defn.tparams.length) then direct = union(direct, useScope(res))
              case TypeShape.Alias(symbol, rhs) =>
                val bound = symbol.defn.get.tparams.map(_.sym).toSet
                rhs.foreach(edge(_, bound))
                if throughReferences && omitsArguments(res, bound.size) then direct = union(direct, useScope(res))
              case TypeShape.Reference(base, _, bindings, instances) =>
                edge(base, bindings.keySet)
                bindings.values.foreach(reference)
                if throughReferences then
                  direct = instances.values.foldLeft(direct)((acc, instance) => union(acc, instance.siteBinders))
              case TypeShape.Applied(base, args) =>
                child(base)
                // An alias argument contributes dependencies only if the body
                // uses its formal. Solve this with the other equations: a cycle
                // such as Loop[A] = {next: Loop[Array[A]]} has no use of A.
                typeApplicationTarget(base) match
                  case S(TypeShape.Alias(symbol, S(rhs))) =>
                    visit(rhs)
                    val formals = symbol.defn.get.tparams
                    args.zipWithIndex.foreach: (arg, index) =>
                      formals.lift(index) match
                        case S(formal) =>
                          visit(arg)
                          argumentUses(res) = (rhs, formal.sym, arg) :: argumentUses.getOrElse(res, Nil)
                        case N => child(arg)
                  case S(TypeShape.Nominal(_)) => args.foreach(guardedChild)
                  // An abstract constructor could forward an argument unchanged.
                  case _ => args.foreach(child)
              case TypeShape.Tuple(fields) => fields.foreach: field =>
                if field.spread then child(field.tpe) else guardedChild(field.tpe)
              case TypeShape.Record(_, fields) => fields.foreach((_, field) => guardedChild(field))
              case TypeShape.Function(params, result) => guardedChild(typeResolution(params)); guardedChild(result)
              case TypeShape.Polymorphic(params, _, body) =>
                val bound = params.map(_.parameter.symbol).toSet
                params.foreach: param =>
                  param.lower.foreach(edge(_, bound))
                  param.upper.foreach(edge(_, bound))
                edge(body, bound)
              case TypeShape.Union(left, right) => child(left); child(right)
              case TypeShape.Intersection(left, right) => child(left); child(right)
              case TypeShape.Negation(base) => child(base)
              case TypeShape.Wildcard(input, output) => input.foreach(child); output.foreach(child)
              // These synthesized nodes retain their own interpreted references
              // or inference hosts; none reads the surrounding binding map.
              case TypeShape.Combined(formula) => formula.orderedAtoms.foreach(reference)
              case TypeShape.Argument(parts) => reference(parts.input); reference(parts.output)
              case TypeShape.SelectedArgument(argument, _) => reference(argument)
              case TypeShape.Contextual(context) => reference(context.tpe)
              case TypeShape.Inferred(_) | TypeShape.Hole(_) =>
                if throughReferences && templates.isEmpty then
                  lastWords(s"Template host for ${res.source.describe} must record its scope")
              case TypeShape.Unit | TypeShape.Dynamic | TypeShape.Abstract | TypeShape.Top | TypeShape.Bottom => ()
            graph(res) = (direct, edges)
      visit(resolution)
      if pending.nonEmpty then L(pending.toSet) else
        val dependencies = mutable.Map.from(graph.iterator.map((res, node) => res -> node._1))
        var changed = true
        while changed do
          changed = false
          graph.foreach: (res, node) =>
            val direct = argumentUses.getOrElse(res, Nil).foldLeft(node._1): (acc, use) =>
              // An unbounded body may use the formal.
              if dependencies(use._1).forall(_(use._2)) then union(acc, dependencies(use._3)) else acc
            val next = node._2.foldLeft(direct): (acc, edge) =>
              union(acc, hide(dependencies(edge._1), edge._2))
            if next != dependencies(res) then
              dependencies(res) = next
              changed = true
        dependencies.foreach((res, binders) => store(res, binders))
        R(dependencies(resolution))

  /** Check guarded recursion and substitutions on the finite source graph, before observing
    * structural children can generate an unbounded sequence of environments.
    * Edges connect original formal parameters, and record whether their argument
    * puts the source formal underneath a non-Boolean constructor. A growing edge
    * is forbidden only when its destination can reach its source: constants and
    * resets break dependency cycles, while permutations do not add constructors.
    * Alias and Boolean reduction is shared with ordinary argument interpretation.
    * This is a conservative sufficient condition, not an exact regularity test:
    * argument-part selection and absorption across recursive steps can make a
    * rejected cycle finite. Do not describe rejection as proof of non-regularity.
    */
  private def regularType(root: TypeResolution)(using ResolutionContext): Bool = rctx.state.regularTypes.get(root) match
    case S(result) => result
    case N =>
      val visited = mutable.LinkedHashSet.empty[TypeResolution]
      val applications = mutable.ArrayBuffer.empty[(TypeResolution, TypeAliasSymbol, TypeResolution, Ls[TypeResolution])]
      def alias(base: TypeResolution): Opt[(TypeAliasSymbol, TypeResolution)] =
        typeApplicationTarget(base) match
          case S(TypeShape.Alias(symbol, S(rhs))) => S(symbol -> rhs)
          case _ => N
      def visit(res: TypeResolution): Unit = if visited.add(res) then
        res.currentShapes.foreachGrowing:
          case TypeShape.Alias(_, rhs) => rhs.foreach(visit)
          case TypeShape.Reference(base, _, _, _) => visit(base)
          case TypeShape.Applied(base, args) =>
            alias(base).foreach: (symbol, rhs) =>
              applications += ((res, symbol, rhs, args))
            visit(base)
            args.foreach(visit)
          case TypeShape.Tuple(fields) => fields.foreach(field => visit(field.tpe))
          case TypeShape.Record(_, fields) => fields.foreach((_, field) => visit(field))
          case TypeShape.Function(params, result) => visit(typeResolution(params)); visit(result)
          case TypeShape.Polymorphic(params, _, body) =>
            params.foreach: param =>
              param.lower.foreach(visit)
              param.upper.foreach(visit)
            visit(body)
          case TypeShape.Union(left, right) => visit(left); visit(right)
          case TypeShape.Intersection(left, right) => visit(left); visit(right)
          case TypeShape.Negation(base) => visit(base)
          case TypeShape.Wildcard(input, output) => input.foreach(visit); output.foreach(visit)
          case TypeShape.Combined(formula) => formula.orderedAtoms.foreach(atom => visit(atom.resolution))
          case TypeShape.Argument(parts) => visit(parts.input.resolution); visit(parts.output.resolution)
          case TypeShape.SelectedArgument(argument, _) => visit(argument.resolution)
          case TypeShape.Contextual(reference) => visit(reference.tpe.resolution)
          case _ => ()
      visit(root)
      // Check source cycles before substitution or Boolean normalization can
      // hide an unguarded occurrence. Alias applications are transparent, but
      // their arguments are followed only through unguarded formal uses:
      // Id[Loop] is unguarded, whereas RecordWrapper[Loop] can be guarded.
      val checked = mutable.Set.empty[TypeResolution]
      var guarded = true
      def checkGuarded(res: TypeResolution, path: Ls[TypeResolution]): Unit =
        if path.contains(res) then
          val cycle = res :: path.takeWhile(_ != res)
          cycle.iterator.flatMap(node => node.currentShapes.collect:
            case TypeShape.Alias(symbol, S(rhs)) => (node, symbol, rhs)
          ).nextOption().foreach: (reference, symbol, rhs) =>
            guarded = false
            rhs.fail(msg"Unguarded recursive type alias '${symbol.nme}'." -> reference.source.toLoc ::
              (msg"Recursive references must pass through a record, tuple, function, or nominal type." -> symbol.toLoc) :: Nil)
        else if checked.add(res) then
          val next = res :: path
          def follow(child: TypeResolution): Unit = checkGuarded(child, next)
          res.currentShapes.foreachGrowing:
            case TypeShape.Alias(_, rhs) => rhs.foreach(follow)
            case TypeShape.Reference(base, _, _, _) => follow(base)
            case TypeShape.Applied(base, args) =>
              follow(base)
              typeApplicationTarget(base) match
                case S(TypeShape.Alias(symbol, S(rhs))) =>
                  val uses = typeDependencies(rhs, true) match
                    case R(binders) => binders
                    case L(_) => lastWords("Guardedness requires a completed source dependency graph")
                  symbol.defn.get.tparams.zip(args).foreach: (formal, argument) =>
                    if uses(formal.sym) then follow(argument)
                case S(TypeShape.Nominal(_)) => ()
                case _ => args.foreach(follow)
            case TypeShape.Union(left, right) => follow(left); follow(right)
            // A spread splices its operand into this tuple; it does not place
            // that operand under a tuple field that could guard recursion.
            case TypeShape.Tuple(fields) => fields.filter(_.spread).foreach(field => follow(field.tpe))
            case TypeShape.Intersection(left, right) => follow(left); follow(right)
            case TypeShape.Negation(base) => follow(base)
            case TypeShape.Wildcard(input, output) => input.foreach(follow); output.foreach(follow)
            case TypeShape.Polymorphic(params, _, body) =>
              params.foreach: param =>
                param.lower.foreach(follow)
                param.upper.foreach(follow)
              follow(body)
            case TypeShape.Combined(formula) => formula.orderedAtoms.foreach(atom => follow(atom.resolution))
            case TypeShape.Argument(parts) => follow(parts.input.resolution); follow(parts.output.resolution)
            case TypeShape.SelectedArgument(argument, _) => follow(argument.resolution)
            case TypeShape.Contextual(reference) => follow(reference.tpe.resolution)
            case _ => ()
      // Structural children start fresh paths, so every cycle is checked even
      // when an enclosing interface guards the use of an invalid alias.
      visited.foreach(checkGuarded(_, Nil))
      if !guarded then
        rctx.state.regularTypes(root) = false
        return false
      def dependencies(res: TypeResolution): Set[VarSymbol] = typeDependencies(res) match
        case R(binders) => binders
        case L(_) => lastWords("Regularity requires a completed source dependency graph")
      def uses(tpe: DeclaredType, wrapped: Bool, seen: Set[DeclaredType], aliases: Set[TypeAliasSymbol]): Set[(VarSymbol, Bool)] =
        if seen(tpe) then Set.empty else
          val next = seen + tpe
          def bound(symbol: VarSymbol, inside: Bool): Set[(VarSymbol, Bool)] = tpe.bindings.get(symbol) match
            case S(argument) => uses(selectArgument(argument, tpe.positive), inside, next, aliases)
            case N => Set(symbol -> inside)
          tpe.resolution.currentShapes.toList match
            case TypeShape.Parameter(symbol, _) :: Nil => bound(symbol, wrapped)
            case TypeShape.Combined(formula) :: Nil => formula.atoms.flatMap(uses(_, wrapped, next, aliases))
            case TypeShape.Contextual(reference) :: Nil => uses(reference.tpe, wrapped, next, aliases)
            case TypeShape.Wildcard(input, output) :: Nil =>
              input.toSet.flatMap(part => uses(declaredType(part, tpe.withPolarity(!tpe.positive)), wrapped, next, aliases)) ++
                output.toSet.flatMap(part => uses(declaredType(part, tpe), wrapped, next, aliases))
            case TypeShape.Argument(parts) :: Nil => uses(parts.input, wrapped, next, aliases) ++ uses(parts.output, wrapped, next, aliases)
            case TypeShape.SelectedArgument(argument, _) :: Nil => uses(argument, wrapped, next, aliases)
            case TypeShape.Applied(base, args) :: Nil => alias(base) match
              case S((symbol, rhs)) if !aliases(symbol) =>
                // Constructor analysis ignores scope crossings, but still follows
                // the alias's substitution. The guard bounds body expansion;
                // substitution values are finite immutable reference DAGs.
                val substitutions = aliasBindings(tpe, typeApplication(args, tpe), symbol.defn.get.tparams, tpe.positive)
                uses(declaredType(rhs, substitutions, tpe.positive), wrapped, next, aliases + symbol)
              case S(_) => dependencies(tpe.resolution).flatMap(bound(_, wrapped))
              case N => dependencies(tpe.resolution).flatMap(bound(_, true))
            case _ => dependencies(tpe.resolution).flatMap(bound(_, true))
      val edges = applications.toList.flatMap: (source, symbol, rhs, args) =>
        symbol.defn.get.tparams.zip(args).flatMap: (formal, argument) =>
          if !dependencies(rhs)(formal.sym) then Nil
          else uses(declaredType(argument, Map.empty), false, Set.empty, Set.empty).toList.map:
            case (origin, growing) => (origin, formal.sym, growing, source, symbol)
      val successors = edges.groupMap(_._1)(_._2)
      def reaches(current: VarSymbol, target: VarSymbol, seen: Set[VarSymbol]): Bool =
        current == target || (!seen(current) && successors.getOrElse(current, Nil).exists(reaches(_, target, seen + current)))
      val invalid = edges.filter: (origin, target, growing, _, _) =>
        growing && reaches(target, origin, Set.empty)
      invalid.foreach: (_, formal, _, source, symbol) =>
        source.fail(msg"Recursive type '${symbol.nme}' is not supported by the current regularity check." -> source.source.toLoc ::
          (msg"Type parameter '${formal.nme}' occurs under a type constructor on a recursive dependency cycle." -> formal.toLoc) :: Nil)
      val result = invalid.isEmpty
      // Failure belongs to this reachable graph, not to unrelated children in
      // it. A later root may observe a regular subgraph of a rejected alias.
      rctx.state.regularTypes(root) = result
      result

  /** Wait for the source graph before observing a substituted interface. The
    * retained environment is projected only after every forward dependency has
    * a target. Subscriptions and completed summaries are shared by source node;
    * callbacks and their hosts remain private to each consuming inference graph.
    */
  private def withCanonicalType(tpe: DeclaredType)(listener: ShapeListener[DeclaredType])(using ResolutionContext): Unit =
    withTypeDependencies(tpe.resolution): binders =>
      if regularType(tpe.resolution) then
        listener(declaredType(tpe.resolution, tpe.bindings.filter((symbol, _) => binders(symbol)), tpe.positive)
          .instantiate(tpe.instances).withOrigin(tpe.origin))

  /** Discover binders without normalizing the type. Parent annotations must
    * receive their bindings at the original lexical endpoint: normalization
    * can move captures into references with their own closed environments.
    */
  private def withTypeDependencies(resolution: TypeResolution)(listener: ShapeListener[Set[VarSymbol]])
      (using ResolutionContext): Unit =
    typeDependencies(resolution) match
      case R(binders) => listener(binders)
      case L(_) =>
        rctx.state.pendingTypeDependencies.get(resolution) match
          case S(host) => host.listen(listener)
          case N =>
            val host = new TypeDependencyHost
            rctx.state.pendingTypeDependencies(resolution) = host
            host.listen(listener)
            def retry()(using ResolutionContext): Unit = typeDependencies(resolution) match
              case R(binders) => host.publish(binders)
              case L(pending) => pending.foreach: unresolved =>
                if rctx.state.dependencySubscriptions.add((resolution, unresolved)) then
                  unresolved.listen(_ => retry())
            retry()

  /** Substitute a bound parameter before storing an argument. Otherwise recursive
    * interfaces such as Tree[A] = Node[A] | Empty would accumulate equivalent
    * A-to-A environments every time a recursive field is selected.
    */
  private[semantics] def declaredType(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType])(using ResolutionContext): DeclaredType =
    declaredType(resolution, bindings, true)

  private def declaredType(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType], positive: Bool)
      (using ResolutionContext): DeclaredType =
    declaredType(resolution, bindings, positive, asArgument = false)

  private def declaredType(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType], positive: Bool, asArgument: Bool)
      (using ResolutionContext): DeclaredType =
    // Splitting each argument visits both polarities. Share work within this
    // traversal so nested alias applications do not repeatedly normalize the
    // same source and environment along an exponential number of paths.
    val normalized = mutable.Map.empty[(TypeResolution, Map[VarSymbol, DeclaredType], Set[TypeAliasSymbol], Bool), DeclaredType]
    def argument(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType], aliases: Set[TypeAliasSymbol], positive: Bool): DeclaredType =
      resolution.currentShapes.toList match
        case TypeShape.Wildcard(_, _) :: Nil | TypeShape.Argument(_) :: Nil => loop(resolution, bindings, aliases, positive)
        case _ => normalizedArgument(resolution, TypeArgument(
          loop(resolution, bindings, aliases, !positive), loop(resolution, bindings, aliases, positive)))
    def loop(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType], aliases: Set[TypeAliasSymbol], positive: Bool): DeclaredType =
      normalized.getOrElseUpdate((resolution, bindings, aliases, positive), interpret(resolution, bindings, aliases, positive))
    def interpret(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType], aliases: Set[TypeAliasSymbol], positive: Bool): DeclaredType =
      def retain: DeclaredType =
        val relevant = if bindings.isEmpty then bindings else typeDependencies(resolution) match
          case R(binders) => bindings.filter((symbol, _) => binders(symbol))
          case L(_) => bindings
        DeclaredType(resolution, relevant, TypeSubstitution.empty, positive)(N)
      resolution.currentShapes.toList match
        case TypeShape.Parameter(symbol, _) :: Nil if bindings.contains(symbol) => selectArgument(bindings(symbol), positive)
        case (reference: TypeShape.Reference) :: Nil =>
          transportType(loop(reference.base, bindings ++ reference.bindings, aliases, positive)
            .instantiate(reference.instances), reference.marks)
        case TypeShape.Union(left, right) :: Nil =>
          combinedType(resolution, loop(left, bindings, aliases, positive), loop(right, bindings, aliases, positive), true)
        case TypeShape.Intersection(left, right) :: Nil =>
          combinedType(resolution, loop(left, bindings, aliases, positive), loop(right, bindings, aliases, positive), false)
        case TypeShape.Wildcard(input, output) :: Nil =>
          // Normalize both parts before retaining the argument. Otherwise even
          // out A keeps another A-to-wildcard environment at each recursive
          // step. Preserve the written source: it overrides declaration variance.
          val parts = TypeArgument(input.fold(extremeType(false))(loop(_, bindings, aliases, !positive)),
            output.fold(missingOutput(resolution))(loop(_, bindings, aliases, positive)))
          normalizedArgument(resolution, parts)
        case TypeShape.Applied(base, arguments) :: Nil =>
          def applyAlias(base: DeclaredType, arguments: => TypeApplication, seen: Set[TypeResolution]): Opt[DeclaredType] =
            lazy val supplied = arguments
            if seen(base.resolution) then N else base.resolution.currentShapes.toList match
              case TypeShape.Alias(symbol, S(rhs)) :: Nil if !aliases(symbol) =>
                val parameters = symbol.defn.get.tparams
                if supplied.arguments.length > parameters.length then N else
                  // Omitted formals use the same source holes as deferred
                  // interpretation. Retaining a partial forwarding application
                  // would nest its environment at each recursive projection.
                  S(loop(rhs, aliasBindings(base, supplied, parameters, positive), aliases + symbol, positive))
              case TypeShape.Contextual(reference) :: Nil =>
                // Use exactly the interpreter's application rule: move caller
                // arguments to the template endpoint, substitute there, then
                // transport the result back. A wildcard exit followed by entry
                // is not cancelled; transportType retains its ordinary marks.
                applyAlias(reference.tpe.instantiate(base.instances).withOrigin(base.origin),
                  supplied.move(inverseMarks(reference.marks)), seen + base.resolution)
                  .map(transportType(_, reference.marks))
              case _ => N
          // Reduce arguments in their caller environment before binding formals.
          // The alias guard grows only on body expansion, so nested Identity
          // applications reduce while unproductive recursive aliases stop.
          lazy val supplied = TypeApplication(arguments.map(res => AppliedTypeArgument(
            argument(res, bindings, aliases, false), argument(res, bindings, aliases, true))))
          applyAlias(loop(base, bindings, aliases, positive), supplied, Set.empty).getOrElse(retain)
        case _ => retain
    if asArgument then argument(resolution, bindings, Set.empty, positive)
    else loop(resolution, bindings, Set.empty, positive)

  /** Preserve both occurrences of an unqualified argument before substitution
    * can select either bound. Applications compose these with their polarity;
    * aliasBindings also accounts for the alias body's local substitution scope.
    */
  private def declaredArgument(resolution: TypeResolution, context: DeclaredType, positive: Bool)
      (using ResolutionContext): DeclaredType =
    declaredType(resolution, context.bindings, positive, asArgument = true).instantiate(context.instances).withOrigin(context.origin)

  private def normalizedArgument(source: TypeResolution, parts: TypeArgument)(using ResolutionContext): DeclaredType =
    rctx.state.argumentTypes.getOrElseUpdate((source, parts), {
      val normalized = new TypeResolution(source.source, source.fail)
      normalized.publish(TypeShape.Argument(parts))
      DeclaredType(normalized, Map.empty, TypeSubstitution.empty, true)(N)
    })

  /** Normalize Boolean combinations without observing an atom's candidates.
    * Transport distributes over components using the ordinary transportType
    * operation; no exit/entry cancellation is introduced by normalization.
    */
  private def typeFormula(tpe: DeclaredType)(using ResolutionContext): TypeFormula[DeclaredType] =
    tpe.resolution.currentShapes.toList match
      case (parameter: TypeShape.Parameter) :: Nil if !tpe.bindings.contains(parameter.symbol) =>
        // Different written occurrences of A are the same lattice atom. Limit
        // this canonicalization to combinations, so ordinary annotation and
        // storage references retain their precise diagnostic source location.
        TypeFormula.atom(parameterType(parameter).withPolarity(tpe.positive).withOrigin(tpe.origin).instantiate(tpe.instances))
      case TypeShape.Combined(formula) :: Nil => formula.map(_.instantiate(tpe.instances))
      case TypeShape.Contextual(reference) :: Nil =>
        typeFormula(reference.tpe.instantiate(tpe.instances).withOrigin(tpe.origin)).map(transportType(_, reference.marks))
      case TypeShape.Top :: Nil => TypeFormula.top
      case TypeShape.Bottom :: Nil => TypeFormula.bottom
      case _ => TypeFormula.atom(tpe)

  private def combinedType(source: TypeResolution, left: DeclaredType, right: DeclaredType, union: Bool)
      (using ResolutionContext): DeclaredType =
    val lhs = typeFormula(left)
    val rhs = typeFormula(right)
    val formula = if union then lhs.union(rhs) else lhs.intersection(rhs)
    if formula.clauses.isEmpty then extremeType(false)
    else if formula.clauses.contains(Set.empty) then
      // A top operand can explain a top result after Boolean normalization has
      // erased its atom. Do not blame an opaque operand when a union/intersection
      // instead simplifies to a more precise type that still has an interface.
      val witness = (if lhs.clauses.contains(Set.empty) then left.origin else N)
        .orElse(if rhs.clauses.contains(Set.empty) then right.origin else N)
      extremeType(true).withOrigin(witness.orElse(S(TypeInterfaceReason.Unrestricted(source.source))))
    else if formula.clauses.size == 1 && formula.atoms.size == 1 then formula.atoms.head
    else rctx.state.combinedTypes.getOrElseUpdate(formula, {
      val resolution = new TypeResolution(source.source, source.fail)
      resolution.publish(TypeShape.Combined(formula))
      DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
    })

  private def declaredType(resolution: TypeResolution, context: DeclaredType)(using ResolutionContext): DeclaredType =
    declaredType(resolution, context.bindings, context.positive).instantiate(context.instances).withOrigin(context.origin)

  /** A scalar occurrence selects one endpoint of a substituted argument. Keep
    * that endpoint fixed when subsequent constraints inspect the resulting type.
    * Nominal arguments select both endpoints separately in declaredArgument.
    * Only delayed/captured pairs need a node, and selecting a selection is inert.
    */
  private[semantics] def selectArgument(argument: DeclaredType, positive: Bool)(using ResolutionContext): DeclaredType =
    def deferred(using ResolutionContext): DeclaredType =
      rctx.state.selectedArguments.getOrElseUpdate((argument, positive), {
        val resolution = new TypeResolution(argument.resolution.source, argument.resolution.fail)
        resolution.publish(TypeShape.SelectedArgument(argument, positive))
        declaredType(resolution, Map.empty)
      })
    rctx.state.selectedArguments.get((argument, positive)).getOrElse:
      argument.resolution.currentShapes.toList match
        case TypeShape.SelectedArgument(_, _) :: Nil => argument
        case TypeShape.Argument(parts) :: Nil =>
          val selected = (if positive then parts.output else parts.input).instantiate(argument.instances)
          if positive then selected.withOrigin(argument.origin) else selected
        case TypeShape.Wildcard(input, output) :: Nil =>
          // Keep the wildcard's source for a missing part's diagnostics; the
          // shared extreme node itself has no source location.
          (if positive then output else input).fold(deferred): part =>
            declaredType(part, argument.withPolarity(if positive then argument.positive else !argument.positive))
        case TypeShape.Contextual(reference) :: Nil =>
          transportType(selectArgument(reference.tpe.instantiate(argument.instances).withOrigin(argument.origin), positive), reference.marks)
        case Nil | TypeShape.Reference(_, _, _, _) :: Nil => deferred
        case _ => argument

  private def instanceType(instance: TypeParameterInstance)(using ResolutionContext): DeclaredType =
    parameterType(TypeShape.Parameter(instance, instance.inferenceHost))

  private def parameterType(parameter: TypeShape.Parameter)(using ResolutionContext): DeclaredType =
    rctx.state.parameterTypes.getOrElseUpdate(parameter, {
      // This endpoint is shared across occurrences. Written uses and declaration
      // notes carry their own locations; the canonical parameter has no source use.
      val source = SimpleRef(parameter.symbol)(N)
      val resolution = new TypeResolution(source, messages => resolError(source, messages))
      resolution.publish(parameter)
      declaredType(resolution, Map.empty)
    })

  private def extremeType(top: Bool)(using ResolutionContext): DeclaredType =
    rctx.state.extremeTypes.getOrElseUpdate(top, {
      val resolution = new TypeResolution(Term.Missing,
        _ => lastWords("A synthesized extreme type cannot be invalid"))
      resolution.publish(if top then TypeShape.Top else TypeShape.Bottom)
      declaredType(resolution, Map.empty)
    })

  private def missingOutput(source: TypeResolution)(using ResolutionContext): DeclaredType =
    extremeType(true).withOrigin(S(TypeInterfaceReason.MissingOutput(source.source)))

  /** Written wildcards override declaration variance. Unqualified arguments have
    * already been interpreted in both polarities; declaration variance keeps the
    * appropriate endpoint and supplies an extreme for the unused one.
    */
  private def argumentType(tpe: DeclaredType, parameter: TyParam)(using ResolutionContext): DeclaredType =
    val variance = parameter.vce
    // SelectedArgument fixes one endpoint of a type argument. If the argument
    // was a wildcard, its source survives for diagnostics even though it no
    // longer denotes an input/output pair. Treating that retained syntax as a
    // fresh use-site override would wrongly skip this parameter's variance.
    // Only an unselected written wildcard overrides declaration-site variance.
    val selected = tpe.resolution.currentShapes.exists:
      case TypeShape.SelectedArgument(_, _) => true
      case _ => false
    if variance.isEmpty || (!selected && tpe.resolution.source.withoutCaptures.isInstanceOf[WildcardTy]) then tpe else
      val varianceValue = variance.get
      val variant = rctx.state.variantTypes.getOrElseUpdate((tpe, varianceValue), {
        val selected = selectArgument(tpe, varianceValue)
        val parts = if varianceValue then TypeArgument(extremeType(false), selected)
          else TypeArgument(selected, extremeType(true))
        normalizedArgument(tpe.resolution, parts)
      })
      // Different parameters can share the same semantic argument pair.
      // Keep the declaration witness on this use, outside the interned pair.
      if varianceValue then variant else variant.withOrigin(
        S(TypeInterfaceReason.ContravariantParameter(parameter, tpe.resolution.source)))

  private def listenArgumentParts(tpe: DeclaredType)(listener: ShapeListener[TypeArgument])(using ResolutionContext): Unit =
    tpe.resolution.listen:
      case TypeShape.Wildcard(input, output) =>
        listener(TypeArgument(input.fold(extremeType(false))(declaredType(_, tpe.withPolarity(!tpe.positive))),
          output.fold(missingOutput(tpe.resolution))(declaredType(_, tpe))))
      case TypeShape.Argument(parts) =>
        listener(TypeArgument(parts.input.instantiate(tpe.instances), parts.output.instantiate(tpe.instances).withOrigin(tpe.origin)))
      case reference: TypeShape.Reference =>
        listenArgumentParts(referenceType(reference, tpe))(listener)
      case TypeShape.Contextual(reference) =>
        listenArgumentParts(reference.tpe.instantiate(tpe.instances).withOrigin(tpe.origin)): parts =>
          listener(TypeArgument(transportType(parts.input, reference.marks), transportType(parts.output, reference.marks)))
      case TypeShape.Parameter(symbol, _) if tpe.bindings.contains(symbol) =>
        val selected = selectArgument(tpe.bindings(symbol).instantiate(tpe.instances), tpe.positive)
        listener(TypeArgument(selected, selected))
      case _ => listener(TypeArgument(tpe, tpe))

  private def effectiveBindings(tpe: DeclaredType)(using ResolutionContext): Map[VarSymbol, DeclaredType] =
    tpe.instances.map((parameter, instance) => parameter -> instanceType(instance)) ++
      tpe.bindings.map((parameter, bound) => parameter -> bound.instantiate(tpe.instances))

  /** A parameterless generic declaration returns a polymorphic value. Keep its
    * binders around the annotation until the value's interface is observed.
    */
  private def quantifiedType(tpe: DeclaredType, parameters: Ls[VarSymbol])(using ResolutionContext): DeclaredType =
    if parameters.isEmpty then tpe else
      val resolution = rctx.state.quantifiedTypes.getOrElseUpdate((tpe.resolution, parameters), {
        val result = new TypeResolution(tpe.resolution.source, tpe.resolution.fail)
        result.publish(TypeShape.Polymorphic(parameters.map: parameter =>
          TypeQuantifier(TypeShape.Parameter(parameter, parameter.inferenceHost), N, N)
        , N, tpe.resolution))
        result
      })
      declaredType(resolution, tpe)

  private def typeViews(using rs: ResolutionContext) = rs.state.typeViews
  /** Each missing formal position belongs to its source type use. Keeping one
    * live host preserves late bounds without allocating a quantified parameter.
    */
  private[semantics] def omittedType(source: TypeResolution, parameter: VarSymbol)(using ResolutionContext): DeclaredType =
    rctx.state.omittedTypes.getOrElseUpdate((source, parameter), {
      val resolution = new TypeResolution(source.source, source.fail)
      val bounds = new TermShapeHost
      // The hole's bounds are templates written where the type use is; an
      // unrecorded type use (a synthesized or legacy annotation) gives them no
      // fixed scope.
      rctx.recordTemplateBinders(resolution, rctx.lexicalBindersOf(source.source))
      resolution.publish(TypeShape.Hole(bounds.inferenceHost))
      declaredType(resolution, Map.empty)
    })

  /** Save both interpretations before traversing the template reference. Each
    * interpretation is itself an input/output argument pair, interpreted in the
    * caller's scope. Applications choose their polarity before applying variance;
    * aliasBindings reorients new formals for lookup inside the alias body without
    * changing the bindings of captured enclosing parameters.
    *
    * Supplied arguments belong to the application scope and move back to the
    * template's endpoint before substitution. Omitted arguments instead belong
    * to the source type reference: all views must read and constrain their shared
    * host in that same scope. Rebasing an omitted host with each observation's
    * path would reinterpret its bounds in unrelated callers' lexical scopes.
    */
  private case class AppliedTypeArgument(negative: DeclaredType, positive: DeclaredType):
    def at(polarity: Bool): DeclaredType = if polarity then positive else negative
    def move(marks: Ls[Marks])(using ResolutionContext): AppliedTypeArgument =
      AppliedTypeArgument(transportType(negative, marks), transportType(positive, marks))

  private case class TypeApplication(arguments: Ls[AppliedTypeArgument]):
    def move(marks: Ls[Marks])(using ResolutionContext): TypeApplication =
      TypeApplication(arguments.map(_.move(marks)))
  private val noTypeArguments = TypeApplication(Nil)

  private def typeApplication(arguments: Ls[TypeResolution], context: DeclaredType)(using ResolutionContext): TypeApplication =
    TypeApplication(arguments.map(res => AppliedTypeArgument(
      declaredArgument(res, context, false), declaredArgument(res, context, true))))

  private def typeArguments(source: DeclaredType, application: TypeApplication, parameters: Ls[TyParam], positive: Bool)
      (using ResolutionContext): Ls[DeclaredType] =
    parameters.zipWithIndex.map: (parameter, index) =>
      application.arguments.lift(index).map(_.at(positive)).getOrElse(
        omittedType(source.resolution, parameter.sym).instantiate(source.instances))

  private def typeBindings(source: DeclaredType, arguments: TypeApplication, parameters: Ls[TyParam], positive: Bool)
      (using ResolutionContext): Map[VarSymbol, DeclaredType] =
    effectiveBindings(source) ++ parameters.zip(typeArguments(source, arguments, parameters, positive)).map: (parameter, argument) =>
      parameter.sym -> argumentType(argument, parameter)

  /** Interpret arguments in the caller's polarity, but select their bounds
    * relative to the alias body. The body retains the caller's polarity for its
    * captured binders; reverse the new formal bindings under a negative caller
    * so the enclosing domain does not also reverse which bound they select.
    * Thus `Source[in Nothing out A]` still reads A from `{item: T}` under a
    * domain. Both declaration variance and written bounds use this same rule.
    */
  private def aliasBindings(source: DeclaredType, arguments: TypeApplication, parameters: Ls[TyParam], positive: Bool)
      (using ResolutionContext): Map[VarSymbol, DeclaredType] =
    effectiveBindings(source) ++ parameters.zip(typeArguments(source, arguments, parameters, positive)).map: (parameter, argument) =>
      val bound = argumentType(argument, parameter)
      parameter.sym -> (if positive then bound else normalizedArgument(bound.resolution,
        TypeArgument(selectArgument(bound, true), selectArgument(bound, false))))

  /** External inputs contribute unknowns only to missing annotation parts.
    * A written binder still denotes its declared type, including after a partial
    * application fixes it; exposure must not add arbitrary values to that binder.
    */
  private[semantics] def exposeTypeHoles(tpe: DeclaredType, unknown: TermShape, marks: Ls[Marks])
      (using ResolutionContext): Unit =
    if !rctx.state.exposedTypeHoles.add((tpe, ShapeIdentity.key(unknown), marks)) then return
    def follow(current: DeclaredType, args: TypeApplication, captures: Ls[Marks], seen: Set[TypeResolution])
        (using ResolutionContext): Unit = if !seen(current.resolution) then
      val next = seen + current.resolution
      def descend(child: DeclaredType)(using ResolutionContext): Unit = unknown.enter(captures) match
        case value: TermShape => exposeTypeHoles(child, value, marks)
        case NoShape => ()
      current.resolution.listen:
        case TypeShape.Hole(host) => unknown.enter(captures) match
          case value: TermShape => host.publish(value)
          case NoShape => ()
        case TypeShape.Parameter(symbol, _) =>
          current.bindings.get(symbol).foreach(bound => follow(selectArgument(bound.instantiate(current.instances), current.positive), noTypeArguments, captures, next))
        case reference: TypeShape.Reference =>
          follow(referenceType(reference, current), args, captures, next)
        case TypeShape.Contextual(reference) =>
          follow(reference.tpe.instantiate(current.instances).withOrigin(current.origin), args.move(inverseMarks(reference.marks)),
            reference.marks ::: captures, next)
        case TypeShape.Applied(base, arguments) =>
          follow(declaredType(base, current), typeApplication(arguments, current), captures, next)
        case TypeShape.Alias(symbol, S(rhs)) =>
          follow(declaredType(rhs, aliasBindings(current, args, symbol.defn.get.tparams, current.positive), current.positive), noTypeArguments, captures, next)
        case TypeShape.Nominal(cls) =>
          cls.tparams.zip(typeArguments(current, args, cls.tparams, current.positive)).foreach: (param, argument) =>
            listenArgumentParts(argumentType(argument, param)): parts =>
              exposeTypeHoles(transportType(parts.output, captures), unknown, marks)
        case TypeShape.Tuple(fields) => fields.foreach(field => descend(declaredType(field.tpe, current)))
        case TypeShape.Record(_, fields) => fields.foreach((_, field) => descend(declaredType(field, current)))
        case TypeShape.Function(_, result) => descend(declaredType(result, current))
        case TypeShape.Polymorphic(parameters, _, body) =>
          val symbols = parameters.map(_.parameter.symbol)
          val lexical = current.withoutBinders(symbols)
          follow(declaredType(body, lexical), args, captures, next)
        case TypeShape.Wildcard(_, output) => output.foreach(res => follow(declaredType(res, current), args, captures, next))
        case TypeShape.Argument(parts) => follow(parts.output.instantiate(current.instances).withOrigin(current.origin), args, captures, next)
        case TypeShape.SelectedArgument(argument, positive) =>
          listenArgumentParts(argument.instantiate(current.instances)): parts =>
            follow(if positive then parts.output else parts.input, args, captures, next)
        case TypeShape.Union(left, right) =>
          follow(declaredType(left, current), noTypeArguments, captures, next)
          follow(declaredType(right, current), noTypeArguments, captures, next)
        case TypeShape.Intersection(left, right) =>
          follow(declaredType(left, current), noTypeArguments, captures, next)
          follow(declaredType(right, current), noTypeArguments, captures, next)
        case TypeShape.Combined(formula) => formula.orderedAtoms.foreach: atom =>
          follow(atom.instantiate(current.instances), noTypeArguments, captures, next)
        case _ => ()
    withCanonicalType(tpe)(follow(_, noTypeArguments, Nil, Set.empty))

  private def abstractTypes(using rs: ResolutionContext) = rs.state.abstractTypes
  // Narrowing a nominal receiver by projection does not infer the narrower
  // class's arguments. This abstract interface is distinct from an inference hole.
  private def abstractType(source: TypeResolution)(using ResolutionContext): DeclaredType = abstractTypes.getOrElseUpdate(source, {
    val resolution = new TypeResolution(source.source, source.fail)
    resolution.publish(TypeShape.Abstract)
    declaredType(resolution, Map.empty)
  })

  /** An annotation is an abstraction boundary, even when its implementation is
    * available. Subscribe to the type graph, never to values flowing into it.
    * Shared hosts retain subscriptions for forward and recursive type references.
    */
  def listenTypeInstances(sign: Term)(listener: Listener)(using ResolutionContext): Unit =
    listenTypeInstances(declaredType(typeResolution(sign), Map.empty))(listener)

  /** Instances of a type are compared by identity (see ShapeIdentity). The type
    * is first projected onto its support, so instances that differ only in
    * bindings the type cannot observe share one shape (see instantiateShape).
    */
  private[semantics] def instanceShape(tpe: DeclaredType)(using ResolutionContext): InstanceShape =
    InstanceShape(tpe)(this)

  private[semantics] def listenTypeInstances(tpe: DeclaredType)(listener: Listener)(using ResolutionContext): Unit =
    listener(instanceShape(tpe.instantiate(rctx.instances)))

  /** Expanding a type is an observation, not a type-argument constraint. Cache
    * observations before following parameters so recursive interfaces reach the
    * same graph nodes instead of allocating fresh inference variables.
    */
  private[semantics] def listenInstanceViews(value: TermShape)(listener: Listener)(using ResolutionContext): Unit =
    listenInstanceViews(value, mergeIntersections = true)(listener)

  private def listenConstraintViews(value: TermShape)(listener: Listener)(using ResolutionContext): Unit =
    listenInstanceViews(value, mergeIntersections = false)(listener)

  private def listenInstanceViews(value: TermShape, mergeIntersections: Bool)(listener: Listener)(using ResolutionContext): Unit = value match
    case Marked(view: IntersectionView, marks) if !mergeIntersections =>
      view.values.foreach: value =>
        transportShape(value, marks :: Nil) match
          case value: TermShape => listenInstanceViews(value, mergeIntersections)(listener)
          case NoShape => ()
    case Marked(instance: InstanceShape, marks) =>
      listenTypeViews(transportType(instance.tpe, marks :: Nil), mergeIntersections)(listener)
    case _ => listener(value)

  private def listenTermViews(term: Term)(listener: Listener)(using ResolutionContext): Unit =
    listenTerm(term)(shape => listenInstanceViews(shape)(listener))

  /** Apply a value's binder substitution without copying the source inference
    * graph, allocating parameter instances, or consuming a callable's scheme.
    * Deferred children inherit the flat map; existing captures take precedence
    * over incoming entries. Each representation stores the view in its own form
    * (DeclaredType, aggregate fields, or ContextualShape), preserving outer marks.
    * Receiver activation is separate and is attached by publishActivated.
    *
    * Only the part of `instances` that the value can observe is retained (its
    * binder support, see shapeSupport), and bindings the value already captured
    * take precedence over the ambient ones. Substitutions therefore stay bounded
    * by the value's own dependencies, however many activations a value passes
    * through: a value produced in a non-generic scope keeps its identity across
    * every generic caller, instead of becoming a distinct candidate per caller
    * environment. Semantic keys describe the effective substitution rather than
    * the sequence of substitutions. Tuple and record producers also retain their
    * canonical object identity because they anchor synthesized inference hosts.
    */
  private[semantics] def instantiateShape(value: TermShape, instances: TypeSubstitution)(using ResolutionContext): TermShape =
    if instances.isEmpty then value else
      val Marked(source, marks) = value
      val instantiated: NonMarkedShape = source match
        case contextual: ContextualShape => contextualView(contextual, contextual.source, contextual.instances, instances)
        case instance: InstanceShape => instanceShape(instantiateType(instance.tpe, instances))
        case rigid: RigidTypeShape => instances.get(rigid.parameter).fold[NonMarkedShape](rigid)(p => instanceShape(instanceType(p)))
        case tuple: TupleShape =>
          val projected = project(instances, tupleDependencies(tuple), tuple.instances)
          if projected.isEmpty then tuple else TupleShape.view(tuple, projected.withOverrides(tuple.instances))(this)
        case record: RecordShape =>
          val projected = project(instances, recordDependencies(record), record.instances)
          if projected.isEmpty then record else RecordShape.view(record, projected.withOverrides(record.instances))
        case nominal: NominalInstanceView =>
          val projected = project(instances, shapeDependencies(nominal), TypeSubstitution.empty)
          if projected.isEmpty then nominal else rctx.shapeView(projected):
            // Own arguments are already bound; only enclosing binders acquire
            // new entries. Other dependencies instantiate the retained arguments.
            val lexical = lexicalBinders(nominal.defn.sym)
            val bindings = projected.iterator.filter((parameter, _) => lexical.forall(_(parameter))).map((parameter, instance) => parameter -> instanceType(instance)).toMap ++
              nominal.bindings.map((parameter, bound) => parameter -> instantiateType(bound, projected))
            NominalInstanceView(nominal.defn, bindings, nominal.parent.map(instantiateShape(_, projected)))(nominal.annotation, nominal.provenance)(this)
        case record: RecordTypeShape =>
          val projected = project(instances, shapeDependencies(record), TypeSubstitution.empty)
          if projected.isEmpty then record else rctx.shapeView(projected):
            RecordTypeShape(record.fields.map((name, tpe) => name -> instantiateType(tpe, projected)), record.aliases)(record.source, record.declarations)
        case view: IntersectionView =>
          IntersectionView(view.values.map(instantiateShape(_, instances)))
        case specialized: SpecializedShape =>
          val projected = project(instances, shapeDependencies(specialized), specialized.instances)
          if projected.isEmpty then specialized else rctx.shapeView(projected):
            SpecializedShape(specialized.declaration, specialized.arguments.map(instantiateType(_, projected)),
              projected.withOverrides(specialized.instances))
        case callable: CallableTypeShape =>
          // A callable's own quantified parameters are bound at its instantiation site.
          val captured = project(instances.without(callable.tparams.map(_.parameter.symbol)), shapeDependencies(callable), TypeSubstitution.empty)
          if captured.isEmpty then callable else rctx.shapeView(captured):
            def instantiate(tpe: DeclaredType): DeclaredType = instantiateType(tpe, captured)
            val scheme = callable.scheme.map: scheme =>
              TypeScheme(scheme.owner, scheme.parameters.map: parameter =>
                DeclaredTypeParameter(parameter.parameter, parameter.lower.map(instantiate), parameter.upper.map(instantiate)))
            CallableTypeShape(callable.source, callable.paramLists.ne_map: params =>
              params.mapTypes(instantiate)
            , callable.result.map(instantiate), scheme, callable.supplied, callable.declaration, callable.asyncResult)
        case literal: IntroShape if !literal.trm.isInstanceOf[Lam] => literal
        case _: (UnknownValueShape | DynShape | OpaqueTypeShape | ErrShape) => source
        case source: ContextualSource => contextualView(source, source, TypeSubstitution.empty, instances)
      if instantiated eq source then value else marks match
        case NoMarks => instantiated
        case marks: SomeMarks => MarkedShape(instantiated, marks)

  /** The view of `source` through `captured` and the observable part of `incoming`;
    * `original` is the existing view of `source` through `captured` alone.
    */
  private def contextualView(original: NonMarkedShape, source: ContextualSource, captured: TypeSubstitution,
      incoming: TypeSubstitution)(using ResolutionContext): NonMarkedShape =
    val projected = project(incoming, shapeDependencies(source), captured)
    if projected.isEmpty then original else
      val effective = projected.withOverrides(captured)
      rctx.shapeView(effective)(ContextualShape(source, effective))

  /** The part of an ambient substitution that a value with the given
    * dependencies can observe and that its `captured` substitution does not
    * already bind: the dependencies are closed over the instances that
    * `captured`, then `incoming`, select for them. Unbounded dependencies (N)
    * retain every binding not already captured.
    */
  private def project(incoming: TypeSubstitution, dependencies: Binders,
      captured: TypeSubstitution): TypeSubstitution =
    closure(dependencies, binder => captured.get(binder).orElse(incoming.get(binder))) match
      case N => incoming.without(captured.keysIterator)
      case S(relevant) => incoming.restrictTo(relevant -- captured.keySet)

  /** The ambient binders a value with the given dependencies still needs once
    * it retains `captured`: the dependencies closed over the instances that
    * `captured` selects, without the binders `captured` binds. This is the
    * support of a nested value; see shapeSupport.
    */
  private def ambientSupport(dependencies: Binders, captured: TypeSubstitution): Binders =
    closure(dependencies, captured.get).map(_ -- captured.keySet)

  /** Close a set of binders over the sites of the instances that a
    * substitution selects for them. The bounds of an instance are templates
    * written at its site: a supplied type argument, or an argument shape
    * observed there, can mention any binder in scope at that site, and is
    * instantiated with the same substitution when the instance is read. An
    * instance of an unknown site makes the result unbounded.
    */
  private def closure(binders: Binders, instanceOf: VarSymbol => Opt[TypeParameterInstance]): Binders =
    @tailrec def loop(relevant: Set[VarSymbol], frontier: Ls[VarSymbol]): Binders = frontier match
      case Nil => S(relevant)
      case binder :: rest => instanceOf(binder) match
        case N => loop(relevant, rest)
        case S(instance) => instance.siteBinders match
          case N => N
          case S(site) =>
            val fresh = site -- relevant
            loop(relevant ++ fresh, fresh.toList ::: rest)
    binders.flatMap(binders => loop(binders, binders.toList))

  /** The substitution a shape already retains; see shapeSupport. */
  private def retainedSubstitution(shape: NonMarkedShape): TypeSubstitution = shape match
    case contextual: ContextualShape => contextual.instances
    case tuple: TupleShape => tuple.instances
    case record: RecordShape => record.instances
    case specialized: SpecializedShape => specialized.instances
    case instance: InstanceShape => instance.tpe.instances
    case _ => TypeSubstitution.empty

  /** The ambient binders a deferred observation of `shape` can still read, as a
    * value nested in another shape or type: its dependencies (shapeDependencies)
    * closed over the substitution it already retains (retainedSubstitution),
    * without the binders that substitution binds. `N` means the set is not
    * fixed and no binding may be dropped.
    *
    * Two questions are kept apart. Which of its retained bindings a view must
    * keep is answered by closing its dependencies over the retained substitution
    * alone (projectType). Which further ambient bindings it needs is answered
    * here and by project: the same closure continued through the ambient
    * substitution, minus what is retained. Reading a retained instance reads the
    * templates written at that instance's site, so its site binders are ambient
    * requirements of the enclosing value, however deeply the instance is saved:
    * in a captured substitution, a tuple view's field, a bound type, or a direct
    * reference to the instance (see dependencies).
    */
  private def shapeSupport(shape: TermShape)(using ResolutionContext): Binders = shape match
    case MarkedShape(inner, _) => shapeSupport(inner)
    case shape: NonMarkedShape => ambientSupport(shapeDependencies(shape), retainedSubstitution(shape))

  /** The original type binders whose call-site instances can change what a
    * deferred observation of `shape` sees, before the substitution the shape
    * itself retains is considered: the members it exposes, the fields it
    * stores, the arguments already bound to its parameters, or the body it runs
    * when called. Nested values contribute their support, so their retained
    * substitutions are already accounted for.
    *
    * This is a conservative lexical analysis, not a free-variable analysis of the
    * value: it never inspects inference candidates or parameter bounds, and it
    * retains every binder in scope whether or not the value mentions it.
    *
    * - A lambda, tuple, record, application, or construction reads its source
    *   expression, so every explicit type binder in scope where that expression
    *   is written counts (the elaborator records them, see lexicalBinders).
    * - A constructed instance, or a partial application, also depends on the
    *   binders of the class or function applied: the arguments were bound to its
    *   parameter symbols in the activation carrying this application's own
    *   instances of those binders, and its fields, methods, and remaining
    *   parameter lists are read back through that activation. The class's
    *   binders are not in scope at the application site, so the site's lexical
    *   scope alone would drop them; likewise a synthesized aggregate view carries
    *   values whose dependencies its source term does not describe, so contents
    *   contribute their own support.
    * - A definition value depends on the binders enclosing its definition; its own
    *   binders are excluded since every application or specialization binds them
    *   afresh, and an inherited binding for them is always overridden. A class
    *   base (a this-value) does include them: its inherited members are
    *   interpreted through them without another instantiation.
    * - A declared type depends on the free binders of its finite source graph and
    *   on the types bound to its formals (typeDependencySet), and on the scopes of
    *   the templates it reads: the bounds of the binder instances it selects, the
    *   elements of an inferred host, and the bounds of an omitted-argument hole
    *   are all written at a site whose binders the reader must supply.
    */
  private def shapeDependencies(shape: TermShape)(using ResolutionContext): Binders = shape match
    case MarkedShape(inner, _) => shapeDependencies(inner)
    case contextual: ContextualShape => shapeDependencies(contextual.source)
    case _: (UnknownValueShape | DynShape | OpaqueTypeShape | ErrShape) => S(Set.empty)
    case rigid: RigidTypeShape => S(Set(rigid.parameter))
    case intro: IntroShape => intro.trm match
      case lam: Lam => lexicalBinders(lam)
      case _ => S(Set.empty)
    case definition: DefnShape =>
      union(lexicalBinders(definitionSymbol(definition.defn)), definition.ext.fold(S(Set.empty))(shapeSupport))
    case base: BaseShape =>
      union(lexicalBinders(base.defn.sym).map(_ ++ ownBinders(base.defn)), base.ext.fold(S(Set.empty))(shapeSupport))
    case application: AppShape =>
      union(lexicalBinders(application.src).map(_ ++ headBinders(application)), shapeSupport(application.receiver))
    case construction: NewShape =>
      union(lexicalBinders(construction.src).map(_ ++ ownBinders(construction.cls.defn.get)), shapeSupport(construction.receiver))
    case tuple: TupleShape => tupleDependencies(tuple)
    case record: RecordShape => recordDependencies(record)
    case specialized: SpecializedShape =>
      specialized.arguments.foldLeft(shapeSupport(specialized.declaration))((acc, argument) => union(acc, typeSupport(argument)))
    case instance: InstanceShape => typeDependencySet(instance.tpe)
    case nominal: NominalInstanceView =>
      // Member signatures may use the binders enclosing the class; the class's
      // own formals are always bound by the view's bindings.
      val declared = nominal.bindings.values.foldLeft[Binders](lexicalBinders(nominal.defn.sym))((acc, bound) => union(acc, typeSupport(bound)))
      union(declared, nominal.parent.fold(S(Set.empty))(shapeSupport))
    case record: RecordTypeShape =>
      record.fields.values.foldLeft[Binders](S(Set.empty))((acc, field) => union(acc, typeSupport(field)))
    case view: IntersectionView =>
      view.values.foldLeft[Binders](S(Set.empty))((acc, value) => union(acc, shapeSupport(value)))
    case callable: CallableTypeShape =>
      val types = callable.paramLists.flatMap(params => params.allParams.flatMap(_.tpe)) :::
        callable.result.toList ::: callable.supplied.toList.flatten :::
        callable.scheme.toList.flatMap(_.parameters.flatMap(parameter => parameter.lower.toList ::: parameter.upper.toList))
      types.foldLeft[Binders](S(Set.empty))((acc, tpe) => union(acc, typeSupport(tpe)))
        .map(_ -- callable.tparams.map(_.parameter.symbol))

  private def headBinders(application: AppShape): Set[VarSymbol] = application.applicationHead._1 match
    case definition: DefnShape => ownBinders(definition.defn)
    case _ => Set.empty

  /** The binders a definition instantiates at each of its applications. */
  private def ownBinders(defn: Definition): Set[VarSymbol] = defn match
    case td: TermDefinition => definitionBinders(td).toSet
    case td: TypeLikeDef => td.tparams.iterator.map(_.sym).toSet

  private def definitionSymbol(defn: Definition): AnyDefinitionSymbol = defn match
    case td: TermDefinition => td.tsym
    case cls: ClassLikeDef => cls.sym
    case alias: TypeDef => alias.sym

  private def tupleDependencies(tuple: TupleShape)(using ResolutionContext): Binders =
    // Rest views and spreads retain their fields' original tuple sources.
    def segmentSupport(segment: TupleShape.Segment): Binders = segment match
      case TupleShape.Field(_, _) => lexicalBinders(tuple.source)
      case TupleShape.ValueField(value, _) => shapeSupport(value)
      case TupleShape.TypedField(tpe, _) => typeSupport(tpe)
      case TupleShape.UnknownField(_, _) => S(Set.empty)
      case TupleShape.ViewedField(source, instances, _) => ambientSupport(segmentSupport(source), instances)
      case TupleShape.Unknown(_, element) => segmentSupport(element)
    tuple.elements.foldLeft[Binders](S(Set.empty)): (acc, element) =>
      union(acc, element match
        case segment: TupleShape.Segment => segmentSupport(segment)
        case TupleShape.Spread(shape, _) => shapeSupport(shape)
        case TupleShape.Rest(shape, segments) => segments.foldLeft(shapeSupport(shape))((acc, rest) => union(acc, segmentSupport(rest))))

  private def recordDependencies(record: RecordShape)(using ResolutionContext): Binders =
    record.elements.foldLeft[Binders](S(Set.empty)): (acc, element) =>
      union(acc, element match
        case RecordShape.Field(_) => lexicalBinders(record.source)
        case RecordShape.Spread(shape, _) => shapeSupport(shape)
        case _ => S(Set.empty))

  /** The binders a declared type reads before the instances it retains are
    * considered: the free binders of its source graph (instanceDependencies),
    * or N while a forward source target is still unresolved, and the support of
    * the types bound to its formals. The formals themselves need no instance.
    */
  private def typeDependencySet(tpe: DeclaredType)(using ResolutionContext): Binders =
    instanceDependencies(tpe.resolution) match
      case L(_) => N
      case R(binders) =>
        tpe.bindings.values.foldLeft(binders)((acc, bound) => union(acc, typeSupport(bound)))

  /** The ambient binders a type nested in another value can still read; see shapeSupport. */
  private def typeSupport(tpe: DeclaredType)(using ResolutionContext): Binders =
    ambientSupport(typeDependencySet(tpe), tpe.instances)

  /** `tpe` instantiated by the observable part of an ambient substitution. */
  private def instantiateType(tpe: DeclaredType, instances: TypeSubstitution)(using ResolutionContext): DeclaredType =
    val projected = project(instances, typeDependencySet(tpe), tpe.instances)
    if projected.isEmpty then tpe else tpe.instantiate(projected)

  /** `tpe` without the retained instances it cannot observe. */
  private[semantics] def projectType(tpe: DeclaredType)(using ResolutionContext): DeclaredType =
    if tpe.instances.isEmpty then tpe else closure(typeDependencySet(tpe), tpe.instances.get) match
      case N => tpe
      case S(support) =>
        val relevant = tpe.instances.restrictTo(support)
        if relevant.size == tpe.instances.size then tpe else tpe.withInstances(relevant)

  /** The explicit type binders in scope where `term` is written. The elaborator
    * records them for every term whose scope resolution reads, before it can
    * observe the term (see Elaborator.withTypeBinders), so a missing record is a
    * compiler bug. The scope is then unknown (N), which retains every binding.
    */
  private def lexicalBinders(term: Term)(using ResolutionContext): Binders =
    val binders = rctx.lexicalBindersOf(term)
    softAssert(binders.nonEmpty, s"${term.describe.capitalize} must record its enclosing type binders before it is observed")
    binders

  /** The type binders enclosing a definition, recorded by the elaborator before
    * its members (see Elaborator.recordDefinitionScope); N if missing, as above.
    * A class and its constructor share one definition site (see ResolutionBoundary).
    */
  private def lexicalBinders(symbol: AnyDefinitionSymbol)(using ResolutionContext): Binders =
    val origin = symbol match
      case ctor: ClassCtorSymbol => ctor.associatedCls
      case symbol => symbol
    val binders = rctx.definitionBindersOf(origin)
    softAssert(binders.nonEmpty, s"Definition ${origin.nme} must record its enclosing type binders")
    binders

  /** Decode outer views only. ContextualSource excludes views and marked shapes;
    * SpecializedShape contains a DefnShape; AppShape receivers are CoreTermShapes.
    * After peeling outer marks, at most one view remains; application receivers
    * cannot hide another view. MarkedShape preserves the decoded core's type.
    * Keep applications intact: their consumed term lists are not view wrappers.
    */
  private def shapeParts(value: TermShape): ShapeParts =
    val Marked(source, marks) = value
    source match
      case ContextualShape(source, instances) => ShapeParts(Marked(source, marks), instances, N)
      case SpecializedShape(declaration, arguments, instances) =>
        ShapeParts(Marked(declaration, marks), instances, S(arguments))
      case source: CoreShape => ShapeParts(Marked(source, marks), TypeSubstitution.empty, N)

  /** Merge only the outer fields, retaining symbolic references at every depth.
    * Shared names use the same interned Boolean combinations as written types;
    * recursively selecting a merged field therefore returns to existing typeViews.
    * No merged shape is embedded in another or used as a new type atom. A finite
    * set of regular field references yields finitely many normalized field types.
    * The enclosing typeViews host caches the observation, and combinedTypes caches
    * field combinations; a separate cache keyed by whole record sets is unnecessary.
    */
  private def intersectViews(values: Ls[TermShape])(publish: Listener)(using ResolutionContext): Unit =
    val flattened = values.flatMap:
      case Marked(view: IntersectionView, marks) => view.values.flatMap(value => transportShape(value, marks :: Nil) match
        case value: TermShape => S(value)
        case NoShape => N)
      case value => value :: Nil
    val records = flattened.collect:
      case Marked(record: RecordTypeShape, marks) =>
        RecordTypeShape(record.fields.map((name, tpe) => name -> transportType(tpe, marks :: Nil)), record.aliases)(record.source, record.declarations)
    val merged = records.headOption.map: first =>
      val merged = records.tail.foldLeft(first): (left, right) =>
        val fields = right.fields.foldLeft(left.fields):
          case (fields, (name, tpe)) => fields.updated(name, fields.get(name).fold(tpe)(previous =>
            combinedType(previous.resolution, previous, tpe, false)))
        val aliases = right.aliases.foldLeft(left.aliases):
          case (aliases, (name, keys)) => aliases.updated(name, aliases.getOrElse(name, Set.empty) ++ keys)
        RecordTypeShape(fields, aliases)(left.source, right.declarations ++ left.declarations)
      merged
    val components = merged.toList ::: flattened.filter:
      case Marked(_: RecordTypeShape, _) => false
      case _ => true
    components.distinctBy(ShapeIdentity.key) match
      case value :: Nil => publish(value)
      case Nil => ()
      case values => publish(IntersectionView(values))

  private def listenTypeViews(tpe: DeclaredType)(listener: Listener)(using ResolutionContext): Unit =
    listenTypeViews(tpe, mergeIntersections = true)(listener)

  /** Constraint inspection propagates every intersection component separately.
    * L1 & L2 <: R installs both L1 <: R and L2 <: R; it does not choose one.
    * Do not wait for every component or form products of their candidates.
    * Member lookup still merges record intersections, so cache the two kinds of
    * observation separately and retain the choice through deferred references.
    */
  private def listenTypeViews(tpe: DeclaredType, mergeIntersections: Bool)(listener: Listener)(using ResolutionContext): Unit =
    // Equal types can be observed through different input-only arguments. Reuse
    // their semantic host, but report this observation's witness rather than the
    // parameter declaration retained by the host's first subscriber.
    def observe(shape: TermShape)(using ResolutionContext): Unit =
      val origin = tpe.origin.orElse:
        if tpe.resolution.currentShapes.exists(_ == TypeShape.Top) then S(TypeInterfaceReason.Unrestricted(tpe.resolution.source)) else N
      (shape, origin) match
        case (Marked(opaque: OpaqueTypeShape, marks), S(reason)) => listener(Marked(OpaqueTypeShape(opaque.source)(reason), marks))
        case _ => listener(shape)
    val key = (tpe, mergeIntersections)
    typeViews.get(key) match
      case S(host) => host.listen(observe)
      case N =>
        val host = new TermShapeHost
        typeViews(key) = host
        host.listen(observe)
        def follow(current: DeclaredType, args: TypeApplication, aliases: Set[TypeResolution], source: Term,
            publish: Listener)(using ResolutionContext): Unit =
          current.resolution.listen: shape =>
            def bind(params: Ls[TyParam], positive: Bool)(using ResolutionContext): Map[VarSymbol, DeclaredType] =
              typeBindings(current, args, params, positive)
            def next(res: TypeResolution)(using ResolutionContext): Unit =
              follow(declaredType(res, current), noTypeArguments, aliases, res.source, publish)
            // Each type can expose several union alternatives. Form products
            // within a conjunction, never across separate union clauses.
            // Each component is also its own diagnostic witness. Aliases and
            // applications preserve that witness while following their definition.
            def conjunction(remaining: Ls[DeclaredType], values: Ls[TermShape])(using ResolutionContext): Unit = remaining match
              case head :: tail => follow(head, noTypeArguments, aliases, head.resolution.source,
                value => conjunction(tail, value :: values))
              case Nil => intersectViews(values.reverse)(publish)
            shape match
              case TypeShape.Dynamic => publish(DynShape())
              case TypeShape.Top => publish(OpaqueTypeShape(source)(
                current.origin.getOrElse(TypeInterfaceReason.Unrestricted(source))))
              case TypeShape.Bottom => ()
              case TypeShape.Wildcard(_, output) =>
                output.fold(publish(OpaqueTypeShape(source)(TypeInterfaceReason.MissingOutput(current.resolution.source))))(next)
              case TypeShape.Argument(parts) => follow(parts.output.instantiate(current.instances).withOrigin(current.origin), noTypeArguments, aliases, source, publish)
              case TypeShape.SelectedArgument(argument, positive) =>
                // An argument cycle can forward this selection without exposing
                // an interface. Keep the subscription for later parts, but stop
                // traversing the same unproductive reference in this observation.
                if !aliases(current.resolution) then
                  listenArgumentParts(argument.instantiate(current.instances)): parts =>
                    follow(if positive then parts.output else parts.input, args, aliases + current.resolution, source, publish)
              case TypeShape.Inferred(value) => listenInstanceViews(instantiateShape(value, current.instances), mergeIntersections)(publish)
              case TypeShape.Hole(host) => host.subscribe: value =>
                listenInstanceViews(instantiateShape(value, current.instances), mergeIntersections)(publish)
              case TypeShape.Nominal(defn) =>
                val enclosing = lexicalBinders(defn.sym)
                val own = defn.tparams.map(_.sym).toSet
                val bindings = bind(defn.tparams, current.positive).filter((parameter, _) => own(parameter) || enclosing.forall(_(parameter)))
                defn.ext match
                  case N => publish(NominalInstanceView(defn, bindings, implicitParent(defn))(S(source), ShapeProvenance.empty)(this))
                  case S(parent) =>
                    // Only the parent's declared type is relevant here. Evaluating
                    // its constructor arguments would reintroduce implementation flow.
                    // Restrict substitution before capturing: a recursive field
                    // can supply an argument already inside this class. A parent
                    // that does not use it must not attempt that scope crossing.
                    val parentType = typeResolution(parent.cls)
                    withTypeDependencies(parentType): dependencies =>
                      val local = captureNominalBindings(defn, bindings.filter((symbol, _) => dependencies(symbol)))
                      listenTypeViews(declaredType(parentType, local), mergeIntersections): ext =>
                        publish(NominalInstanceView(defn, bindings, S(ext))(S(source), ShapeProvenance.empty)(this))
              case TypeShape.Alias(symbol, _) if symbol is prelude.builtins.Awaited =>
                val arguments = typeArguments(current, args, symbol.defn.get.tparams, true)
                softAssert(arguments.length == 1)
                listenTypeViews(arguments.head)(value => listenAwaitedValue(value, source)(publish))
              case TypeShape.Alias(symbol, rhs) =>
                // Revisiting the same alias reference without reaching a structural
                // shape supplies no additional interface. Track
                // references, not symbols: Id[Id[T]] has two distinct references.
                if aliases(current.resolution) then publish(OpaqueTypeShape(source)(TypeInterfaceReason.RecursiveAlias(symbol)))
                else rhs match
                  case S(rhs) => follow(declaredType(rhs, aliasBindings(current, args, symbol.defn.get.tparams, current.positive), current.positive), noTypeArguments,
                    aliases + current.resolution, source, publish)
                  case N => publish(OpaqueTypeShape(source)(TypeInterfaceReason.AbstractDeclaration(symbol, source)))
              case TypeShape.Applied(base, params) =>
                follow(declaredType(base, current), typeApplication(params, current), aliases, source, publish)
              case TypeShape.Parameter(symbol, host) => current.bindings.get(symbol) match
                case S(bound) => follow(selectArgument(bound.instantiate(current.instances), current.positive), noTypeArguments, aliases, source, publish)
                case N =>
                  val target = current.instances.get(symbol).fold(host)(_.inferenceHost)
                  listenTypeArgument(target): value =>
                    // Report the use of an abstract parameter in a signature, not
                    // just its declaration. This survives substitution through
                    // generic members and nested tuple or function annotations.
                    val annotated = value match
                      case Marked(rigid: RigidTypeShape, marks) =>
                        UnknownValueShape(rigid.source, fromPublicInterface = false)(rigid.provenance.withTypeOrigin(source)).exit(marks)
                      case Marked(unknown: UnknownValueShape, marks) =>
                        UnknownValueShape(unknown.source, unknown.fromPublicInterface)(unknown.provenance.withTypeOrigin(source)).exit(marks)
                      case _ => value
                    annotated match
                      case value: TermShape => listenInstanceViews(instantiateShape(value, current.instances), mergeIntersections)(publish)
                      case NoShape => ()
              case reference: TypeShape.Reference =>
                follow(referenceType(reference, current), args, aliases, source, publish)
              case TypeShape.Contextual(reference) =>
                // Arguments belong to the application scope, whereas the
                // template belongs to the reference's source scope. Move the
                // arguments back before substitution, then transport the result.
                follow(reference.tpe.instantiate(current.instances).withOrigin(current.origin), args.move(inverseMarks(reference.marks)), aliases, source,
                  shape => shape.exit(reference.marks) match
                    case value: TermShape => publish(value)
                    case NoShape => ())
              case TypeShape.Function(params, ret) =>
                val ps = params match
                  case Tup(fields) =>
                    def parameter(fld: Fld) =
                      DeclaredParam(S(declaredType(typeResolution(fld.term), current.withPolarity(!current.positive))), fld.flags)
                    // Elaboration reports function types with several variadic parameters.
                    val (leading, variadic) = fields.span(_.isInstanceOf[Fld])
                    val leadingFlds = leading.collect { case fld: Fld => fld }
                    DeclaredParams(leadingFlds.map(parameter), variadic match
                      case (spd: Spd) :: trailing =>
                        val trailingFlds = trailing.collect { case fld: Fld => fld }
                        S(Variadic(DeclaredParam(S(declaredType(typeResolution(spd.term), current.withPolarity(!current.positive))),
                          FldFlags.empty.copy(droppable = spd.droppable)), trailingFlds.map(parameter)))
                      case _ => N)
                  case single =>
                    DeclaredParams(DeclaredParam(S(declaredType(typeResolution(single), current.withPolarity(!current.positive))),
                      FldFlags.empty) :: Nil, N)
                publish(CallableTypeShape(source, ps ne_:: Nil,
                  S(declaredType(ret, current)), N, N, N, N))
              case TypeShape.Polymorphic(params, _, body) =>
                val symbols = params.map(_.parameter.symbol)
                val lexical = current.withoutBinders(symbols)
                val binders = params.map: param =>
                  DeclaredTypeParameter(param.parameter,
                    param.lower.map(declaredType(_, lexical)),
                    param.upper.map(declaredType(_, lexical)))
                follow(declaredType(body, lexical), args, aliases, source, shape => shape match
                  case Marked(callable: CallableTypeShape, marks) =>
                    callable.copy(scheme = S(TypeScheme(current.resolution, binders ::: callable.tparams))).exit(marks) match
                      case value: TermShape => publish(value)
                      case NoShape => ()
                  case _ => publish(shape))
              case TypeShape.Tuple(fields) =>
                def expand(rest: Ls[TypeShape.TupleField], reversed: Ls[TupleShape.Element])(using ResolutionContext): Unit = rest match
                  case Nil => publish(TupleShape(current.resolution.source, reversed.reverse)(this))
                  case TypeShape.TupleField(field, false) :: tail =>
                    expand(tail, TupleShape.TypedField(declaredType(field, current), Nil) :: reversed)
                  case TypeShape.TupleField(field, true) :: tail =>
                    listenTypeViews(declaredType(field, current), mergeIntersections = false):
                      case Marked(tuple: TupleShape, marks) =>
                        expand(tail, TupleShape.Spread(tuple, marks) :: reversed)
                      case Marked(array: NominalInstanceView, marks) if arrayElementType(array).nonEmpty =>
                        // Retain the symbolic element endpoint: sampling its
                        // current values would lose inference from later calls.
                        val element = TupleShape.TypedField(arrayElementType(array).get, marks :: Nil)
                        expand(tail, TupleShape.Unknown(field.source, element) :: reversed)
                      case shape @ Marked(_: DynShape | _: UnknownValueShape | _: OpaqueTypeShape, _) =>
                        expand(tail, TupleShape.Unknown(field.source, TupleShape.ValueField(shape, Nil)) :: reversed)
                      case shape =>
                        field.fail(msg"A tuple type spread requires an Array or tuple interface." -> field.source.toLoc ::
                          shape.diagnostic(msg"This type does not supply an array interface."))
                expand(fields, Nil)
              case TypeShape.Record(source, fields) =>
                val aliases = fields.flatMap:
                  case (field @ RcdField(Lit(Tree.StrLit(name)), _, _), _) => field.key.collect:
                    case key: SymbolKey => name -> Set(key)
                  case _ => N
                publish(RecordTypeShape(fields.map((field, sign) => field.key.get -> declaredType(sign, current)).toMap, aliases.toMap)(
                  source, fields.map((field, _) => field.key.get -> field).toMap))
              case TypeShape.Union(left, right) => next(left); next(right)
              case TypeShape.Intersection(left, right) if !mergeIntersections => next(left); next(right)
              case TypeShape.Intersection(left, right) =>
                conjunction(declaredType(left, current) :: declaredType(right, current) :: Nil, Nil)
              case TypeShape.Combined(formula) if !mergeIntersections =>
                formula.orderedAtoms.foreach: atom =>
                  val component = atom.instantiate(current.instances)
                  follow(component, noTypeArguments, aliases, component.resolution.source, publish)
              case TypeShape.Combined(formula) =>
                // Choose witnesses in source order, independently of set hashing.
                val clauses = formula.clauses.toList.sortWith((left, right) =>
                  formula.orderedAtoms.find(atom => left(atom) != right(atom)).exists(left))
                clauses.foreach: clause =>
                  conjunction(formula.orderedAtoms.filter(clause).map(_.instantiate(current.instances)).toList, Nil)
              case TypeShape.Negation(_) => publish(OpaqueTypeShape(source)(TypeInterfaceReason.Negated(current.resolution.source)))
              case TypeShape.Unit | TypeShape.Abstract =>
                publish(OpaqueTypeShape(source)(TypeInterfaceReason.Unavailable(current.resolution.source)))
        withCanonicalType(tpe)(follow(_, noTypeArguments, Set.empty, tpe.resolution.source, host.publish))

  // A separate full signature also annotates the implementation's parameters.
  // Register these before its body is elaborated, so observed calls can never
  // publish inferred alternatives for parameters behind this boundary.
  private def signatureParameters(using rs: ResolutionContext) = rs.state.signatureParameters
  def registerParameterSignature(paramLists: Ls[ParamList], sign: Term)(using ResolutionContext): Unit =
    paramLists.flatMap(_.allParams).filter(_.sign.isEmpty).foreach: param =>
      val resolution = new TypeResolution(sign, messages => resolError(sign, messages))
      // Components can arrive later through aliases. Keep one endpoint for every
      // parameter so existing observations and input constraints see all of them.
      // Its templates may mention binders inside any quantified component.
      rctx.recordTemplateBinders(resolution, N)
      // Bottom contributes no values and keeps this accumulating union distinct
      // from a single immutable reference that normalization could substitute away.
      resolution.publish(TypeShape.Bottom)
      val tpe = declaredType(resolution, Map.empty)
      signatureParameters(param.sym) = tpe
      listenTypeInstances(tpe): shape =>
        if param.sym.currentShapes.add(shape) then param.sym.notifyShapeListeners(shape)
    // Check only signatures that explicitly specify one calling convention,
    // following aliases and quantifiers. Compound signatures still contribute
    // every component's flows, but rejecting one possible layout would turn this
    // best-effort check into a false incompatibility.
    def singleArrow(res: TypeResolution, seen: Set[TypeResolution])(using ResolutionContext): Bool =
      if seen(res) then false else
        def next(inner: TypeResolution): Bool = singleArrow(inner, seen + res)
        res.currentShapes.toList match
          case TypeShape.Function(_, _) :: Nil => true
          case TypeShape.Reference(base, _, _, _) :: Nil => next(base)
          case TypeShape.Contextual(ref) :: Nil => next(ref.tpe.resolution)
          case TypeShape.Applied(base, _) :: Nil => next(base)
          case TypeShape.Alias(_, S(rhs)) :: Nil => next(rhs)
          case TypeShape.Polymorphic(_, _, body) :: Nil => next(body)
          case _ => false
    def bind(paramLists: Ls[ParamList], tpe: DeclaredType, checkLayout: Bool)(using ResolutionContext): Unit = paramLists match
      case Nil => ()
      case ps :: tail => listenTypeViews(tpe, mergeIntersections = false):
        case Marked(callable: CallableTypeShape, marks) =>
          val declared = callable.paramLists.head
          // Once alternatives have been approximated, a later curried list is
          // still part of those alternatives, even if this component is one arrow.
          val check = checkLayout && singleArrow(tpe.resolution, Set.empty)
          if Arity(ps) != Arity(declared) then
            if check then
              rctx.report(ErrorReport(
                msg"Implementation parameter list does not match its separate signature." -> ps.toLoc ::
                msg"The signature has different required, optional, variadic, or trailing parameter positions." -> sign.toLoc :: Nil))
          val params = ps.allParams
          zipDeclaredParameters(Arity(ps), declared): (index, tpe) =>
            val param = params(index)
            val component = transportType(tpe, marks :: Nil)
            if param.sign.isEmpty then
              signatureParameters.get(param.sym).get.resolution.publish(TypeShape.Combined(TypeFormula.atom(component)))
            else
              // An inline annotation keeps its interface, but its inferred type
              // arguments still receive constraints from the separate signature.
              constrainParameter(param, instanceShape(component), Nil)
          callable.result.foreach(tpe => bind(tail, transportType(tpe, marks :: Nil), check))
        case _ => ()
    bind(paramLists, declaredType(typeResolution(sign), Map.empty), true)

  /** Synthesized constructor fields retain their source declaration on the symbol. */
  private[semantics] def resultSignature(td: TermDefinition)(using ResolutionContext): Opt[Term] = td.tsym.decl match
    case S(p: Param) => p.sign
    case _ => td.resultSignature

  /** Normalize paths with ordinary value transport. An unobserved bottom instance
    * is a reusable carrier that retains scope exits, unlike self-contained shapes.
    * Its type is independent of the transported reference, so composing marks
    * does not intern that reference just to discard the resulting shape.
    */
  private def markCarrier(using ResolutionContext): InstanceShape = instanceShape(extremeType(false))

  /** Materialize a deferred value result as a type edge, preserving the value's
    * lexical marks until its consumer leaves the definition scope. In particular,
    * observing an async result must not mix payloads from separate generic calls.
    * The result is produced by terms written where the binders `scope` are in
    * scope (N if unknown). The host stays specific to the activation `instances`, because
    * parameters deliver each activation's own arguments to the body.
    */
  private def resultType(source: Term, scope: Binders, instances: TypeSubstitution)(connect: Listener => Unit)
      (using ResolutionContext): DeclaredType =
    val key = (new Identity(source), instances)
    rctx.state.resultTypes.get(key) match
      case S(tpe) => tpe
      case N =>
        val resolution = new TypeResolution(source, messages => resolError(source, messages))
        // Reading a payload value can require the binders in `scope`. A declared
        // result arrives already instantiated by `instances` or by the observing
        // activation, so reading it also reads the sites of the instances these
        // select for those binders (see closure).
        rctx.recordTemplateBinders(resolution,
          closure(scope, binder => instances.get(binder).orElse(rctx.instances.get(binder))))
        val tpe = declaredType(resolution, Map.empty)
        rctx.state.resultTypes(key) = tpe
        connect(value => resolution.publish(TypeShape.Inferred(value)))
        tpe

  private def promiseShape(annotation: Annot.Async, payload: DeclaredType)(using ResolutionContext): NominalInstanceView =
    val cls = prelude.builtins.Promise.defn.get
    softAssert(cls.tparams.length == 1 && cls.ext.isEmpty,
      "The builtin Promise must have one fulfillment parameter and the implicit Object parent")
    val provenance = ShapeProvenance(
      msg"This async annotation wraps the body's result in a promise." -> N :: Nil).withTypeOrigin(annotation)
    NominalInstanceView(cls, Map(cls.tparams.head.sym -> awaitedType(payload)), implicitParent(cls))(N, provenance)(this)

  /** Reify the projection before observing its operand. Expanding an inferred
    * body's type parameter here would freeze the declaration's abstract view
    * before a caller can substitute its own type argument.
    */
  private def awaitedType(tpe: DeclaredType)(using ResolutionContext): DeclaredType =
    val symbol = prelude.builtins.Awaited match
      case symbol: TypeAliasSymbol => symbol
      case _ => lastWords("The builtin Awaited must be an abstract type alias")
    appliedType(symbol, new ::(tpe, Nil))

  private def listenAwaitedValue(value: TermShape, source: Term)(listener: Listener)(using ResolutionContext): Unit =
    listenInstanceViews(value)(view => listenAwaitedView(view, source)(listener))

  private def listenAwaitedView(value: TermShape, source: Term)(listener: Listener)(using ResolutionContext): Unit =
    // Intern before following nested promises, so recursive fulfillment edges
    // share a host and late candidates still reach the existing consumers.
    val key = (ShapeIdentity.key(value), rctx.instances)
    val tpe = rctx.state.awaitedValues.get(key) match
      case S(result) => result
      case N =>
        val resolution = new TypeResolution(source, messages => resolError(source, messages))
        // The fulfillment values are the value itself, unknown values, or are read
        // from its promise payload, so they observe at most the value's own support.
        rctx.recordTemplateBinders(resolution, shapeSupport(value))
        val result = declaredType(resolution, Map.empty)
        rctx.state.awaitedValues(key) = result
        def publish(value: TermShape)(using ResolutionContext): Unit = resolution.publish(TypeShape.Inferred(value))
        if !listenPromisePayload(value)(payload => listenAwaitedValue(payload, source)(publish)) then
          value.applicationHead._1 match
            case _: (DynShape | UnknownValueShape | OpaqueTypeShape | RigidTypeShape) => publish(value)
            // JavaScript may adopt a structural thenable instead of returning
            // the object itself. Until its callback interface can be inferred,
            // preserve uncertainty rather than exposing the object's fields.
            // Awaiting a value only calls its public `then` method.
            case _ => value.getMember("then").visibleFrom(_ => false, reportInaccessible = false) match
              case MemberLookup.Missing => publish(value)
              case _ => publish(UnknownValueShape(source, fromPublicInterface = false)(ShapeProvenance(
                msg"This value may be a thenable; its fulfillment interface is not known." -> value.toLoc :: Nil)))
        result
    listenTypeViews(tpe)(listener)

  /** Result annotations constrain the body before async lowering. Consumers of
    * the function observe Promise[Awaited[result]], including explicit returns.
    * Inferred values retain their lexical endpoint until callers leave the scope.
    */
  private def listenDefinitionResult(td: TermDefinition, instances: TypeSubstitution)(listener: Listener)(using ResolutionContext): Unit =
    def bodyResult(listener: Listener): Unit = td.sign match
      case S(sign) => listenSignatureResult(declaredType(typeResolution(sign), Map.empty).instantiate(instances),
        if td.flags.hasResultAnnotation then 0 else td.params.length)(listener)
      case N => td.body.foreach(body => listenResult(body)(listener))
    td.asyncAnnotation match
      case S(annotation) =>
        val source = td.sign.orElse(td.body).get
        // The body and signature are written inside the definition, where its own binders are in scope.
        val scope = lexicalBinders(td.tsym).map(_ ++ definitionBinders(td))
        listener(promiseShape(annotation, resultType(source, scope, instances)(bodyResult)))
      case N => bodyResult(listener)

  /** Observe one application of a declared callable. Partial application keeps
    * the async wrapper pending, even across the nested arrows of a full signature.
    */
  private[semantics] def listenCallableResult(callable: CallableTypeShape)(listener: Listener)(using ResolutionContext): Unit =
    callable.asyncResult match
      case S(AsyncResult(annotation, 1)) =>
        softAssert(callable.paramLists.tail.isEmpty)
        // A nominal member without a result annotation still returns Promise,
        // but its interface must not recover a payload type from the hidden body.
        listener(promiseShape(annotation, callable.result.getOrElse(extremeType(true))))
      case pending =>
        val remaining = pending.map(info => AsyncResult(info.annotation, info.remainingLists - 1))
        callable.paramLists.tail match
          case tail: NELs[DeclaredParams] => listener(callable.copy(paramLists = tail, asyncResult = remaining))
          case Nil => callable.result match
            case S(tpe) if remaining.nonEmpty => listenTypeViews(tpe):
              case Marked(next: CallableTypeShape, marks) => listener(Marked(next.copy(asyncResult = remaining), marks))
              case other => listener(other)
            case S(tpe) => listenTypeInstances(tpe)(listener)
            case N => listener(UnknownValueShape.at(callable.source))

  /** Retain a scope transfer on the reference, including deferred fields and
    * both argument parts. Flatten existing transfers before interning, so a
    * recursive projection cannot build a tower of transport wrappers.
    */
  private[semantics] def transportType(bound: DeclaredType, marks: Ls[Marks])(using ResolutionContext): DeclaredType =
    val (base, previous) = bound.resolution.currentShapes.toList match
      case TypeShape.Contextual(reference) :: Nil => (reference.tpe.instantiate(bound.instances).withOrigin(bound.origin), reference.marks)
      case _ => (bound, Nil)
    softAssert(!base.resolution.currentShapes.exists:
      case TypeShape.Contextual(_) => true
      case _ => false
    , "Contextual references must be flattened before they are interned")
    // A wildcard exit followed by an entry is not an identity: the exit
    // consumes a candidate's entry site and the new entry supplies its own.
    // Deferred references use exactly the same transport as ordinary values.
    // The nested trace shows the carrier standing in for `base` (see markCarrier).
    trace[DeclaredType](dbg"transportType ${base.resolution.showDbg} (previous = ${previous.map(_.showDbg)}, marks = ${marks.map(_.showDbg)})"):
      markCarrier.exit(previous).exit(marks) match
        case Marked(_, NoMarks) => base
        case Marked(_, path: SomeMarks) =>
          val reference = ContextualType(base, path :: Nil)
          rctx.state.contextualTypes.getOrElseUpdate(reference, {
            val resolution = new TypeResolution(base.resolution.source, base.resolution.fail)
            resolution.publish(TypeShape.Contextual(reference))
            declaredType(resolution, Map.empty)
          }).withOrigin(base.origin)
        case NoShape => extremeType(false)

  private def inverseMarks(marks: Ls[Marks])(using ResolutionContext): Ls[Marks] =
    // Reverse directions using ordinary mark operations, not a reordered list
    // of scopes. This is not an inverse on candidates: a wildcard exit can lose
    // a call-site ID, which the reversed path cannot reconstruct.
    markCarrier.enter(marks) match
      case Marked(_, NoMarks) => Nil
      case Marked(_, path: SomeMarks) => path :: Nil
      case NoShape => lastWords("Inverting a scope path cannot reject a candidate")

  private def referenceType(reference: TypeShape.Reference, context: DeclaredType)(using ResolutionContext): DeclaredType =
    transportType(declaredType(reference.base, context.bindings ++ reference.bindings, context.positive)
      .instantiate(context.instances.withOverrides(reference.instances)).withOrigin(context.origin), reference.marks)

  private[semantics] def captureType(bound: DeclaredType, scope: AnyDefinitionSymbol)(using ResolutionContext): DeclaredType =
    transportType(bound, EntryMark(ResolutionBoundary(scope), N, NoMarks) :: Nil)

  /** Finish a projection on the deferred reference before delivering it to a
    * caller. Leaving a wildcard entry outside InstanceShape would let a later
    * call exit cancel it before the reference's own path had been composed.
    */
  private def transportShape(value: TermShape, marks: Ls[Marks])(using ResolutionContext): TermShape | NoShape = value match
    case Marked(instance: InstanceShape, inner) =>
      instanceShape(transportType(instance.tpe, inner :: marks))
    case _ => value.exit(marks)

  private def listenDeclaredMember(member: BlockMemberSymbol, bindings: Map[VarSymbol, DeclaredType], flow: FlowSymbol,
      source: Term, annotation: Opt[Term], selected: ShapeListener[DefinitionSymbol[?]], receiver: Bool, positive: Bool,
      receiverMarks: Ls[Marks], specialization: Opt[(FlowSymbol, Ls[DeclaredType])])(listener: Listener)(using ResolutionContext): Unit =
    member.onComplete: () =>
      valueTarget(member, receiver) match
        case S(symbol: TermSymbol) if !symbol.isInstanceOf[ClassCtorSymbol] =>
          selected(symbol)
          val td = symbol.defn.get
          val crossesValueScope = !(td.k is syntax.RecordField) && !td.tsym.decl.exists(_.isInstanceOf[Param])
          val callerInstances = rctx.instances
          // A selected generic method binds its own parameters anew. Receiver
          // bindings can mention an earlier call of that same source method in
          // their values, but cannot bind the new method's local names.
          val capturedBindings = bindings -- definitionBinders(td)
          val instances = if isByName(td) then instantiateByName(td, flow,
            ExitMark(ResolutionBoundary(td.tsym), S(flow), NoMarks) :: receiverMarks, specialization, capturedBindings) else callerInstances
          def publish(shape: TermShape)(using ResolutionContext): Unit =
            val Marked(interface, context) = shape
            val generic = interface match
              case callable: CallableTypeShape if !isByName(td) =>
                val parameters = td.tparams.toList.flatten.map(p => declaredParameter(p.sym)) ::: callable.tparams
                CallableTypeShape(callable.source, callable.paramLists, callable.result,
                  if parameters.isEmpty then N else S(TypeScheme(td.tsym, parameters)), callable.supplied, S(td),
                  td.asyncAnnotation.map(AsyncResult(_, td.params.length)))
              case instance: InstanceShape if !isByName(td) =>
                instanceShape(quantifiedType(instance.tpe, td.tparams.toList.flatten.map(_.sym)))
              case _ => interface
            // Constructor fields keep their parameter scope; structural fields
            // follow their written type directly. Other members leave their own
            // definition scope when their declared interface is selected.
            val path = context :: (if crossesValueScope then
              ExitMark(ResolutionBoundary(td.tsym), S(flow), NoMarks) :: Nil else Nil)
            val exited = transportShape(generic, path)
            exited match
              case value: TermShape => listener(instantiateShape(value, instances))(using rctx.withInstances(callerInstances))
              case NoShape => ()
          def signature(sign: Term, polarity: Bool)(using ResolutionContext): DeclaredType =
            val tpe = declaredType(typeResolution(sign), capturedBindings, polarity)
            if isByName(td) then tpe.instantiate(instances) else tpe
          val result = resultSignature(td).map(signature(_, positive))
          if td.sign.nonEmpty && (td.k is syntax.Fun) && !td.flags.hasResultAnnotation && !isByName(td) then
            listenTypeViews(signature(td.sign.get, positive))(publish)
          else td.params match
            case params: NELs[ParamList] => publish(CallableTypeShape(source,
              params.ne_map: ps =>
                def parameter(p: Param) = DeclaredParam(p.sign.map(signature(_, !positive)), p.flags)
                DeclaredParams(ps.params.map(parameter), ps.variadic.map(_.map(parameter)))
              ,
              result, N, N, S(td), N))
            case Nil if td.asyncAnnotation.nonEmpty =>
              publish(promiseShape(td.asyncAnnotation.get, result.getOrElse(extremeType(true))))
            case Nil => result match
              case S(tpe) => listenTypeInstances(tpe)(publish)
              case N =>
                // Keep the missing constructor annotation on the unknown value so
                // later selections and calls can explain why argument flow is hidden.
                val unknown = td.tsym.decl match
                  case S(param: Param) => UnknownValueShape(source, fromPublicInterface = false)(ShapeProvenance(
                    (msg"Constructor parameter '${param.sym.nme}' has no type annotation." -> param.toLoc) ::
                    annotation.toList.map(sign =>
                      msg"This type annotation does not provide a type for field '${member.nme}'." -> sign.toLoc)))
                  case _ => UnknownValueShape.at(source)
                publish(unknown)
        case _ =>
          // A nested nominal declaration denotes its statically selected symbol;
          // selecting it does not inspect an instance field or method body.
          fromBMSAt(member, flow, Nil, listener, source, selected, receiver, specialization)

  def resolError(src: Term | Pattern, msgs: Ls[(Message, Opt[Loc])])(using rs: ResolutionContext): Unit =
    rs.reportResolutionError(src, msgs)
  
  def registerTypeParameters(owner: AnyDefinitionSymbol, params: Ls[VarSymbol])(using State, ResolutionContext): Unit =
    if params.nonEmpty then
      // Check every generic body under an abstract activation, including private
      // definitions and non-strict worksheets. Its fresh entry site cannot match
      // a real caller's exit, so identity-like results still substitute the actual
      // type argument without leaking this abstract candidate into the caller.
      val site = FlowSymbol("generic interface")
      params.foreach: param =>
        val ref = SimpleRef(param)(N)
        val unknown = RigidTypeShape(param, ref)
        publishParameter(param, MarkedShape.enter(unknown, ResolutionBoundary(owner), S(site)))

  /** Explicit and inferred type arguments use the same entry/exit paths as term
    * arguments. An explicit argument fixes that instantiation; its value argument
    * must not add a more precise implementation shape to the declared interface.
    */
  private def listenTypeArgument(symbol: VarSymbol)(listener: Listener)(using ResolutionContext): Unit =
    listenTypeArgument(symbol.inferenceHost)(listener)

  private def listenTypeArgument(host: Publisher.Data[ShapeEvent])(listener: Listener)(using ResolutionContext): Unit =
    host.subscribe:
      case value: TermShape => listener(value)
      case _ => softAssert(false, "A type parameter's bounds must contain values without activation envelopes")

  private[semantics] def publishParameter(symbol: VarSymbol, shape: TermShape | NoShape)(using ResolutionContext): Unit =
    shape match
      case value: TermShape if !symbol.decl.exists(_.isInstanceOf[TyParam]) => publishActivated(symbol, value)
      case _ => publishParameter(symbol.inferenceHost, shape)

  private[semantics] def publishParameter(host: Publisher.Data[ShapeEvent], shape: TermShape | NoShape)(using ResolutionContext): Unit = shape match
    case value: TermShape => host.publish(value)
    case _ => ()

  private def declaredParameter(symbol: VarSymbol)(using ResolutionContext): DeclaredTypeParameter =
    DeclaredTypeParameter(TypeShape.Parameter(symbol, symbol.inferenceHost), N, N)

  private def bindTypeArguments(parameters: Ls[TypeShape.Parameter], marks: Ls[Marks], arguments: Ls[DeclaredType])
      (using ResolutionContext): Unit =
    // Establish every supplied position before publication can replay body
    // constraints or trigger observations of a mutually dependent parameter.
    parameters.zip(arguments).foreach((p, _) => rctx.markExplicitTypeArgument(p.symbol))
    parameters.zip(arguments).foreach: (parameter, argument) =>
      publishParameter(parameter.host, instanceShape(argument).enter(marks))

  /** Bounds constrain the instantiated references, never the shared checking
    * binders. Install them after suppliedness is recorded, so a lower bound is
    * checked against an explicit argument rather than widening its interface.
    * Recursive and mutually dependent bounds reuse the ordinary relation graph.
    */
  private def constrainQuantifiedBounds(parameters: Ls[DeclaredTypeParameter], substitution: TypeSubstitution)
      (using ResolutionContext): Unit =
    parameters.foreach: parameter =>
      val instance = ContextualType(parameterType(parameter.parameter).instantiate(substitution), Nil)
      parameter.lower.foreach(bound => constrainTypes(ContextualType(bound.instantiate(substitution), Nil), instance, N))
      parameter.upper.foreach(bound => constrainTypes(instance, ContextualType(bound.instantiate(substitution), Nil), N))

  /** Consume the scheme at its authoritative site. Specialized values and curried
    * tails carry instantiated references and no scheme, so later calls reuse it.
    */
  private def instantiateCallable(callable: CallableTypeShape, site: FlowSymbol, siteBinders: Opt[Set[VarSymbol]],
      marks: Ls[Marks])(using ResolutionContext): CallableTypeShape = callable.scheme match
    case N => callable
    case S(scheme) =>
      val key = (ShapeIdentity.key(callable), site, marks)
      rctx.state.instantiatedCallables.get(key) match
        case S(instantiated) => instantiated
        case N =>
          val substitution = rctx.instantiateTypeParameters(scheme.owner, site, scheme.parameters.map(_.parameter.symbol), siteBinders)
          def instantiate(tpe: DeclaredType): DeclaredType = tpe.instantiate(substitution)
          val instantiated = CallableTypeShape(callable.source,
            callable.paramLists.ne_map: params =>
              params.mapTypes(instantiate)
            , callable.result.map(instantiate), N, N, callable.declaration, callable.asyncResult)
          // Reentrant observations must find the view before supplied arguments
          // can publish candidates or trigger another observation of this call.
          rctx.state.instantiatedCallables(key) = instantiated
          callable.supplied.foreach: arguments =>
            val parameters: Ls[TypeShape.Parameter] = scheme.parameters.map: parameter =>
              val instance = substitution(parameter.parameter.symbol)
              TypeShape.Parameter(instance, instance.inferenceHost)
            bindTypeArguments(parameters, marks, arguments)
          constrainQuantifiedBounds(scheme.parameters, substitution)
          instantiated

  /** The body must satisfy its annotated result even if no value escapes or no
    * call inspects the implementation. In particular a returned closure receives
    * its declared domain before its member targets are completed.
    */
  def checkDeclaredResult(definition: TermDefinition)(using ResolutionContext): Unit =
    definition.body.foreach: body =>
      resultSignature(definition).foreach: sign =>
        val expected = declaredType(typeResolution(sign), Map.empty)
        listenResult(body): shape =>
          inferTypeArguments(expected.instantiate(rctx.instances), shape, Nil, S(body))

  def checkAscription(body: Term, sign: Term)(using ResolutionContext): Unit =
    val expected = declaredType(typeResolution(sign), Map.empty)
    listenTerm(body): shape =>
      inferTypeArguments(expected.instantiate(rctx.instances), shape, Nil, S(body))

  /** Keep both endpoints symbolic. Register before following either endpoint,
    * so recursive references reuse the relation even before any bound exists.
    */
  private[semantics] def constrainTypes(lower: ContextualType, upper: ContextualType, site: Opt[Term])(using ResolutionContext): Unit =
    if rctx.state.typeRelations.add((lower, upper)) then
      instanceShape(lower.tpe).exit(lower.marks).enter(upper.marks) match
        case value: TermShape => inferTypeArguments(upper.tpe, value, upper.marks, site)
        case NoShape => ()

  // Keep the first diagnostic use site outside the semantic constraint key, so
  // reporting provenance does not multiply identical edges in the inference graph.
  private def inferTypeArguments(tpe: DeclaredType, value: TermShape, marks: Ls[Marks],
      site: Opt[Term])(using ResolutionContext): Unit =
    if !rctx.addTypeConstraint(tpe, value, marks) then return
    val annotation = tpe.resolution.source
    def follow(tpe: DeclaredType, args: TypeApplication, captures: Ls[Marks],
        seen: Set[TypeResolution])(using ResolutionContext): Unit = if !seen(tpe.resolution) then
      val next = seen + tpe.resolution
      def observe(listener: Listener)(using ResolutionContext): Unit =
        listenConstraintViews(value): actual =>
          actual.enter(captures) match
            case actual: TermShape => listener(actual)
            case NoShape => ()
      tpe.resolution.listen:
        case TypeShape.Parameter(symbol, host) => tpe.bindings.get(symbol) match
          case S(bound) => follow(selectArgument(bound.instantiate(tpe.instances), tpe.positive), noTypeArguments, captures, next)
          case N =>
            val target = tpe.instances.get(symbol)
            val destination = target.fold(host)(_.inferenceHost)
            val lower = value.enter(captures)
            if rctx.hasExplicitTypeArgument(target.getOrElse(symbol)) then
              listenTypeArgument(destination): supplied =>
                // Compare in the caller's scope, retaining the supplied
                // reference's endpoint for any further parameter constraint.
                supplied.exit(captures).exit(marks) match
                  case Marked(instance: InstanceShape, context) =>
                    val endpoint = if context == NoMarks then Nil else context :: Nil
                    value.exit(marks).enter(context) match
                      case actual: TermShape => inferTypeArguments(instance.tpe, actual, endpoint, site)
                      case NoShape => ()
                  case _ => ()
            else publishParameter(destination, lower)
        case reference: TypeShape.Reference =>
          follow(referenceType(reference, tpe), args, captures, next)
        case TypeShape.Contextual(reference) =>
          follow(reference.tpe.instantiate(tpe.instances).withOrigin(tpe.origin), args.move(inverseMarks(reference.marks)),
            reference.marks ::: captures, next)
        case TypeShape.Applied(base, params) =>
          follow(declaredType(base, tpe), typeApplication(params, tpe), captures, next)
        case TypeShape.Alias(symbol, S(rhs)) =>
          follow(declaredType(rhs, aliasBindings(tpe, args, symbol.defn.get.tparams, tpe.positive), tpe.positive), noTypeArguments, captures, next)
        case TypeShape.Hole(host) => value.enter(captures) match
          case value: TermShape => host.publish(value)
          case NoShape => ()
        case TypeShape.Tuple(_) => observe(constrainTuple(tpe, _, marks, site))
        case TypeShape.Union(left, right) =>
          follow(declaredType(left, tpe), noTypeArguments, captures, next)
          follow(declaredType(right, tpe), noTypeArguments, captures, next)
        case TypeShape.Intersection(left, right) =>
          follow(declaredType(left, tpe), noTypeArguments, captures, next)
          follow(declaredType(right, tpe), noTypeArguments, captures, next)
        // Resolution approximates an upper union by constraining every component.
        // This supplies bounds without choosing branches or retaining alternative
        // constraint sets. Lower intersections likewise contribute independent
        // candidates through listenConstraintViews, avoiding candidate products.
        case TypeShape.Combined(formula) =>
          formula.orderedAtoms.foreach(atom => follow(atom.instantiate(tpe.instances), noTypeArguments, captures, next))
        case TypeShape.Record(_, fields) => observe(constrainRecord(fields.map((field, sign) => field -> declaredType(sign, tpe)), _, marks, site))
        case TypeShape.Function(_, _) => observe(constrainFunction(tpe, _, marks, site))
        case TypeShape.Polymorphic(_, _, body) =>
          follow(declaredType(body, tpe), args, captures, next)
        case TypeShape.Wildcard(input, _) => input.foreach(res => follow(declaredType(res, tpe.withPolarity(!tpe.positive)), args, captures, next))
        case TypeShape.Argument(parts) => follow(parts.input.instantiate(tpe.instances), args, captures, next)
        case TypeShape.SelectedArgument(argument, positive) =>
          listenArgumentParts(argument.instantiate(tpe.instances)): parts =>
            follow(if positive then parts.output else parts.input, args, captures, next)
        case TypeShape.Nominal(cls) => listenConstraintViews(value): value =>
          // Erasing a callback's signature must not erase the obligation to
          // check its implementation. Its unannotated inputs can receive any
          // value, independently of the calls observed through Function.
          listenTypeViews(tpe):
            case Marked(nominal: NominalInstanceView, _) if nominal.isInstanceOfClass(prelude.builtins.Function.defn.get) =>
              value.enter(captures) match
                case actual: TermShape =>
                  val provenance = ShapeProvenance(msg"The 'Function' type does not specify parameter types." -> N :: Nil)
                    .withTypeOrigin(annotation)
                  rctx.exposeValue(instantiateShape(actual, rctx.instances), provenance)
                case NoShape => ()
            case _ => ()
          val arguments = typeArguments(tpe, args, cls.tparams, tpe.positive).map(transportType(_, captures))
          def constrainNominal(value: TermShape)(using ResolutionContext): Unit =
            val ShapeParts(actual, instances, _) = shapeParts(value)
            val (head, context) = actual.applicationHead
            def constrain(param: TyParam, bound: DeclaredType, pattern: DeclaredType)(using ResolutionContext): Unit =
              listenArgumentParts(bound.instantiate(instances)): actual =>
                listenArgumentParts(argumentType(pattern, param)): expected =>
                  constrainTypes(ContextualType(actual.output, context), ContextualType(expected.output, Nil), site)
                  constrainTypes(ContextualType(expected.input, Nil), ContextualType(actual.input, context), site)
            def originalParameters()(using ResolutionContext): Unit = cls.tparams.zip(arguments).foreach: (param, pattern) =>
              val bound = parameterType(TypeShape.Parameter(param.sym, param.sym.inferenceHost))
              constrain(param, argumentType(bound, param), pattern)
            def parent(ext: TermShape)(using ResolutionContext): Unit =
              // Parent arguments live at the parent's endpoint, which can cross
              // both class and enclosing scopes. Preserve those marks together
              // with the child's substitution on every step of the ancestry.
              transportShape(instantiateShape(ext, instances), context) match
                case value: TermShape => constrainNominal(value)
                case NoShape => ()
            head match
              case _: UnknownValueShape =>
                cls.tparams.zip(arguments).foreach: (param, argument) =>
                  listenArgumentParts(argumentType(argument, param)): parts =>
                    inferTypeArguments(parts.output, value, marks, site)
              case ds: DefnShape =>
                if ds.clsDef.contains(cls) then originalParameters() else ds.ext.foreach(parent)
              case base: BaseShape =>
                if base.defn is cls then originalParameters() else base.ext.foreach(parent)
              case nominal: NominalInstanceView =>
                if nominal.defn is cls then cls.tparams.zip(arguments).foreach: (param, pattern) =>
                  nominal.bindings.get(param.sym).foreach(constrain(param, _, pattern))
                else nominalParent(nominal).foreach(parent)
              case tuple: TupleShape => parent(tuple.arrayParent)
              case _ => ()
          constrainNominal(value)
        case TypeShape.Top => ()
        case _ => value match
          // A concrete target stays fixed, but must receive bounds that arrive
          // through a symbolic source later. Concrete mismatch reporting is
          // separate from retaining this obligation in the graph.
          case Marked(_: InstanceShape, _) => listenConstraintViews(value)(inferTypeArguments(tpe, _, marks, site))
          case _ => ()
    // Alias expansion guards only unproductive cycles. Descending into a tuple,
    // nominal argument, or arrow installs another edge with its own cycle guard.
    withCanonicalType(tpe)(follow(_, noTypeArguments, Nil, Set.empty))

  /** Expand fixed tuple spreads before matching positions. Unknown-length
    * segments share the remaining middle elements, as with declared parameter
    * lists; their symbolic fields retain both input and output type arguments.
    */
  private def constrainTuple(expected: DeclaredType, actual: TermShape, marks: Ls[Marks],
      site: Opt[Term])(using ResolutionContext): Unit =
    listenTypeViews(expected, mergeIntersections = false):
      case Marked(tuple: TupleShape, context) =>
        def constrain(field: TupleShape.Fixed, value: TermShape)(using ResolutionContext): Unit =
          listenTupleField(field):
            case Marked(instance: InstanceShape, inner) =>
              inferTypeArguments(transportType(instance.tpe, inner :: context :: Nil), value, marks, site)
            case _ => ()
        val (leading, rest) = tuple.segments.span(_.isInstanceOf[TupleShape.Fixed])
        val (trailing, middle) = rest.reverse.span(_.isInstanceOf[TupleShape.Fixed])
        val positions = leading ::: trailing.reverse
        actual match
          case unknown @ Marked(_: UnknownValueShape, _) =>
            tuple.segments.foreach(segment => constrain(segment.element, unknown))
          case Marked(supplied: TupleShape, suppliedContext) =>
            val arity = Arity(leading.length, leading.length, middle.nonEmpty, trailing.length)
            zipTupleShapes(Nil, arity, supplied, suppliedContext): (index, shape) =>
              shape match
                case value: TermShape if arity.hasRest && index == leading.length =>
                  listenArrayElements(value): element =>
                    middle.foreach(segment => constrain(segment.element, element))
                case value: TermShape =>
                  val position = if arity.hasRest && index > leading.length then index - 1 else index
                  constrain(positions(position).element, value)
                case NoShape => ()
          case _ =>
            listenArrayElements(actual): element =>
              tuple.segments.foreach(segment => constrain(segment.element, element))
      case _ => ()

  /** Structural constraints follow declared fields only. This supplies generic
    * argument inference and callback checking without refining the annotation
    * with additional properties from an actual record.
    */
  private def constrainRecord(fields: Ls[(RcdField, DeclaredType)],
      actual: TermShape, marks: Ls[Marks], site: Opt[Term])(using ResolutionContext): Unit =
    fields.foreach: (field, expected) =>
      val flow = rctx.fieldProjectionSite(field.sym)
      def receive(value: TermShape)(using ResolutionContext): Unit = inferTypeArguments(expected, value, marks, site)

      actual match
        case Marked(_: UnknownValueShape, _) => receive(actual)
        // A structural interface only describes public members.
        case _ => listenMemberValue(actual.getMember(field.key.get).visibleFrom(_ => false, reportInaccessible = false),
          flow, field.rhs, TypeSubstitution.empty, () => ())(receive)

  /** Read a member using the same declaration and scope rules for ordinary
    * constraints and implicit protocol observations. The caller decides whether
    * a missing/opaque member contributes uncertainty or no new constraint.
    */
  private def listenMemberValue(info: MemberLookup, flow: FlowSymbol, source: Term,
      instances: TypeSubstitution, unresolved: () => ResolutionContext ?=> Unit)(receive: Listener)
      (using ResolutionContext): Unit = info match
    case MemberLookup.All(members) => members.foreach(listenMemberValue(_, flow, source, instances, unresolved)(receive))
    case MemberLookup.Contextual(nested, substitution) => listenMemberValue(nested, flow, source, instances.withOverrides(substitution), unresolved)(receive)
    case MemberLookup.Found(RecordMember(member, true), _) => receive(UnknownValueShape.at(member.rhs))
    case MemberLookup.Found(member, inner) =>
      fromBMS(member.memberSymbol, flow, inner, value => receive(instantiateShape(value, instances)), source, _ => (), false)(using rctx.withInstances(instances))
    case MemberLookup.Declared(member, bound, inner, annotation, positive) =>
      listenDeclaredMember(member, bound, flow, source, annotation, _ => (), false, positive, inner, N): value =>
        transportShape(instantiateShape(value, instances), inner) match
          case value: TermShape => receive(value)
          case NoShape => ()
    case MemberLookup.Typed(_, tpe, inner) =>
      receive(instanceShape(transportType(instantiateType(tpe, instances), inner)))
    case MemberLookup.Dynamic(inner) => DynShape().exit(inner) match
      case value: TermShape => receive(value)
      case NoShape => ()
    case MemberLookup.Indexed(fields, inner) => fields.foreach: field =>
      listenTupleField(field): value =>
        transportShape(instantiateShape(value, instances), inner) match
          case value: TermShape => receive(value)
          case NoShape => ()
    case _ => unresolved()

  /** Function constraints reverse the parameter flow and preserve result flow.
    * Read an implementation only while checking it against its declared interface;
    * calls through that interface continue to expose only the declared result.
    */
  private[semantics] def constrainFunction(expected: DeclaredType, source: TermShape, marks: Ls[Marks],
      site: Opt[Term])(using ResolutionContext): Unit =
    val ShapeParts(actual, instances, _) = shapeParts(source)
    def arityError(expected: DeclaredType)(using ResolutionContext): Unit =
      val messages =
        msg"Callback parameter list does not match its declared function type." -> actual.toLoc ::
        msg"The expected function type is declared here." -> expected.resolution.source.toLoc :: Nil
      site match
        case S(use) => resolError(use, messages)
        case N => rctx.report(ErrorReport(messages))
    actual match
      case Marked(_: InstanceShape, _) =>
        listenConstraintViews(actual)(constrainFunction(expected, _, marks, site))
        return
      case _ => ()
    val context = actual.applicationHead._2
    def results(listener: Listener)(using ResolutionContext): Unit = actual.applicationHead._1 match
      case intro: IntroShape => intro.trm match
        case Lam(_, body) => listenResult(body)(shape => listener(instantiateShape(shape, instances)))(using rctx.withInstances(instances))
        case _ => ()
      case ds: DefnShape => ds.defn match
        case td: TermDefinition => listenDefinitionResult(td, instances)(shape =>
          listener(instantiateShape(shape, instances)))(using rctx.withInstances(instances))
        case _ => ()
      case _ => ()
    def matchLists(expected: DeclaredType, remaining: Ls[(ParamList, Ls[Marks])])(using ResolutionContext): Unit =
      listenTypeViews(expected, mergeIntersections = false):
        case Marked(callable: CallableTypeShape, expectedContext) => remaining match
          case (params, _) :: tail =>
            val declared = callable.paramLists.head
            if callbackArityMismatch(Arity(params), declared) then
              arityError(expected)
            // Diagnostics must not disconnect parameter or result constraints.
            val allParams = params.allParams
            zipCallbackArguments(context, Arity(params), declared, callable.source, expectedContext)(
              (index, shape) => constrainParameterIn(allParams(index), shape, context, instances, site))
            callable.result.foreach: ret =>
              tail match
                case Nil => results: shape =>
                  shape.exit(context).enter(expectedContext) match
                    case value: TermShape => inferTypeArguments(ret, value, marks, site)
                    case NoShape => ()
                case _ => matchLists(ret, tail)
          case Nil => ()
        case Marked(record: RecordTypeShape, _) =>
          constrainRecord(record.fields.iterator.map((name, tpe) => record.declarations(name) -> tpe).toList,
            actual, marks, site)
        case _ => ()
    actual match
      case Marked(_: UnknownValueShape, _) =>
        listenTypeViews(expected, mergeIntersections = false):
          case Marked(callable: CallableTypeShape, _) =>
            callable.result.foreach(ret => inferTypeArguments(ret, actual, marks, site))
          case _ => ()
      case Marked(givenType: CallableTypeShape, actualContext) =>
        listenTypeViews(expected, mergeIntersections = false):
          case Marked(wanted: CallableTypeShape, expectedContext) =>
            val domain = givenType.paramLists.head
            val expectedDomain = wanted.paramLists.head
            if callbackArityMismatch(Arity(domain), expectedDomain) then
              arityError(expected)
            val allParams = domain.allParams
            zipCallbackArguments(actualContext :: Nil, Arity(domain), expectedDomain, wanted.source, expectedContext)(
              (index, shape) => allParams(index).tpe.foreach: tpe =>
                shape match
                  case value: TermShape => inferTypeArguments(tpe, value, context, site)
                  case NoShape => ()
              )
            wanted.result.foreach: ret =>
              def receive(shape: TermShape)(using ResolutionContext): Unit = shape.exit(actualContext).enter(expectedContext) match
                case value: TermShape => inferTypeArguments(ret, value, marks, site)
                case NoShape => ()
              listenCallableResult(givenType)(receive)
          case _ => ()
      case _ => matchLists(expected, actual.unappliedParams)

  /** Check obvious arity and droppability mismatches. Different variadic layouts
    * need not agree: a callback may collect trailing arguments in its rest parameter
    * or take fixed interface arguments from the end. More involved compatibility
    * questions belong to type checking, rather than a structural-equality check.
    * For fixed callbacks, diagnose trailing inputs that remain out of reach even
    * when callers omit all optional leading and variadic arguments.
    */
  private def callbackArityMismatch(actual: Arity, expected: DeclaredParams): Bool =
    val trailingCapacity = (actual.leading - expected.leadingRequired).max(0)
    actual.required > Arity(expected).required
      || !actual.hasRest && expected.variadic.exists(!_.param.flags.droppable)
      || !actual.hasRest && expected.params.drop(actual.leading).exists(!_.flags.droppable)
      || !actual.hasRest && expected.trailing.drop(trailingCapacity).exists(!_.flags.droppable)

  /** Approximate a declared argument list without choosing a compound signature's
    * branch or enumerating spread lengths. Equal layouts retain whole parameter
    * annotations. Otherwise align a guaranteed prefix and suffix, and join all
    * remaining flows at every possible middle position. In particular, an unknown
    * position must not erase a known element type or a symbolic inference endpoint.
    */
  private def zipDeclaredParameters(arity: Arity, declared: DeclaredParams)(
      publish: (Int, DeclaredType) => ResolutionContext ?=> Unit)(using ResolutionContext): Unit =
    def assign(index: Int, param: DeclaredParam): Unit = param.tpe.foreach(publish(index, _))
    if arity == Arity(declared) then
      declared.allParams.zipWithIndex.foreach((sign, index) => assign(index, sign))
    else
      val sharedTail = arity.trailing.min(declared.trailing.length)
      val alignedTail = arity.trailing == declared.trailing.length
      val prefix = if alignedTail then arity.leading.min(declared.params.length)
        else arity.leadingRequired.min(declared.leadingRequired)
      declared.params.take(prefix).zipWithIndex.foreach((sign, index) => assign(index, sign))
      declared.trailing.takeRight(sharedTail).zipWithIndex.foreach: (sign, index) =>
        assign(arity.leading + 1 + arity.trailing - sharedTail + index, sign)
      val positions = (prefix until arity.leading) ++
        (arity.leading + 1 until arity.leading + 1 + arity.trailing - sharedTail)
      val middle = declared.params.drop(prefix) ::: declared.trailing.dropRight(sharedTail)
      middle.foreach(sign => positions.foreach(assign(_, sign)))
      def restElement(element: DeclaredType, marks: Marks)(using ResolutionContext): Unit =
        val tpe = transportType(element, marks :: Nil)
        positions.foreach(index => publish(index, tpe))
        if arity.hasRest then publish(arity.leading, arrayType(tpe))
      declared.rest.foreach: rest =>
        listenTypeViews(rest, mergeIntersections = false):
          case Marked(array: NominalInstanceView, marks) =>
            arrayElementType(array).foreach(restElement(_, marks))
          case Marked(tuple: TupleShape, marks) =>
            tuple.segments.foreach: segment =>
              listenTupleField(segment.element):
                // Written tuple types retain their symbolic element endpoints.
                case Marked(instance: InstanceShape, inner) =>
                  restElement(transportType(instance.tpe, inner :: Nil), marks)
                case _ => arrayElementType(tuple.arrayParent).foreach(restElement(_, marks))
          case _ => ()
      if arity.hasRest then
        // Slicing can change a tuple-typed rest's length. Keep its element types
        // above, but widen the length to avoid false arity errors on forwarding.
        // Scalar middle inputs likewise contribute an Array of their declared type.
        middle.flatMap(_.tpe).foreach(tpe => publish(arity.leading, arrayType(tpe)))
        if middle.flatMap(_.tpe).isEmpty then
          // Even an empty or still-unresolved rest supplies the Array interface.
          publish(arity.leading, arrayType(extremeType(false)))

  private def arrayType(element: DeclaredType)(using ResolutionContext): DeclaredType =
    appliedType(prelude.builtins.Array, new ::(element, Nil))

  /** Synthesized applications need stable resolution identities: reference interning
    * cannot merge newly allocated TypeResolution nodes. Share the entire application
    * by constructor and symbolic arguments, rather than making a cache per builtin.
    * Combined atoms embed each argument's bindings, polarity, and scope transfers;
    * observing its current values here would lose later inference flows.
    */
  private def appliedType(symbol: ClassSymbol | TypeAliasSymbol, arguments: NELs[DeclaredType])
      (using ResolutionContext): DeclaredType =
    rctx.state.appliedTypes.getOrElseUpdate((symbol, arguments), {
      val source = arguments.head.resolution
      val member = symbol.defn.get.bsym
      // The constructor has no written identifier; its arguments retain their own source origins.
      val head = Term.MemberRef(member)(N, FlowSymbol.memSym(member))
      head.resolvedTargets = symbol :: Nil
      // This head is fully applied and has no lexical binders. Reusing an argument's
      // source would misclassify it as a bare generic use in that argument's scope.
      rctx.recordLexicalBinders(head, Set.empty)
      rctx.recordAppliedTypeArguments(head, arguments.length)
      val constructor = new TypeResolution(head, source.fail)
      softAssert(symbol.defn.get.tparams.length == arguments.length, "A synthesized type application must supply every parameter")
      symbol match
        case cls: ClassSymbol => constructor.publish(TypeShape.Nominal(cls.defn.get))
        case alias: TypeAliasSymbol =>
          constructor.publish(TypeShape.Alias(alias, alias.defn.get.rhs.map(typeResolution)))
      val args = arguments.map: argument =>
        val resolution = new TypeResolution(argument.resolution.source, argument.resolution.fail)
        resolution.publish(TypeShape.Combined(TypeFormula.atom(argument)))
        resolution
      val resolution = new TypeResolution(source.source, source.fail)
      resolution.publish(TypeShape.Applied(constructor, args))
      declaredType(resolution, Map.empty)
    })

  /** Fixed callback interfaces describe an ordinary argument tuple. Variable
    * layouts use the same flow approximation as separate signatures.
    */
  private def zipCallbackArguments(mss: Ls[Marks], arity: Arity, declared: DeclaredParams, source: Term, marks: Marks)(
      publish: (Int, TermShape | NoShape) => ResolutionContext ?=> Unit)(using ResolutionContext): Unit =
    def fields(params: Ls[DeclaredParam]): Ls[TupleShape.Fixed] = params.map: param =>
      param.tpe match
        case S(tpe) => TupleShape.TypedField(tpe, Nil)
        case N => TupleShape.UnknownField(source, Nil)
    if !declared.hasRest && declared.leadingRequired == declared.params.length && arity.required <= declared.params.length then
      zipTupleShapes(mss, arity, TupleShape(source, fields(declared.params))(this), marks)(publish)
    else
      zipDeclaredParameters(arity, declared): (index, tpe) =>
        listenTypeInstances(tpe)(shape => publish(index, shape.exit(marks).enter(mss)))
  
  private def listenSignatureResult(tpe: DeclaredType, count: Int)(listener: Listener)(using ResolutionContext): Unit =
    if count == 0 then listenTypeInstances(tpe)(listener)
    else listenTypeViews(tpe, mergeIntersections = false):
      case Marked(callable: CallableTypeShape, marks) =>
        callable.result.foreach(tpe => listenSignatureResult(transportType(tpe, marks :: Nil), count - 1)(listener))
      case _ => ()

  private def tupleArrayParents(using rs: ResolutionContext) = rs.state.tupleArrayParents
  /** A tuple is an Array whose element argument is the union of its field shapes.
    * Cache the parent before following fields: a recursive tuple can require its
    * own Array interface while one of those fields is still being resolved.
    */
  private[semantics] def tupleArrayParent(tuple: TupleShape)(using ResolutionContext): NominalInstanceView =
    tupleArrayParents.get(new Identity(tuple)) match
      case S(parent) => parent
      case N =>
        val cls = prelude.builtins.Array.defn.get
        softAssert(cls.tparams.length == 1, "The builtin Array must have one element type parameter")
        val elements = new TypeResolution(tuple.source, messages => resolError(tuple.source, messages))
        // The elements are the tuple's own contents, observed in its scope and
        // through the substitution the tuple retains.
        rctx.recordTemplateBinders(elements, shapeSupport(tuple))
        val parent = NominalInstanceView(cls, Map(cls.tparams.head.sym -> declaredType(elements, Map.empty)), implicitParent(cls))(N, ShapeProvenance.empty)(this)
        tupleArrayParents(new Identity(tuple)) = parent
        tuple.segments.foreach: segment =>
          listenTupleField(segment.element): value =>
            elements.publish(TypeShape.Inferred(value))
        parent

  /** Mutable literals share Array's existing element parameter, with an allocation
    * mark to keep distinct arrays and enclosing call activations independent.
    * Seed the interface before following elements so empty and recursive arrays
    * can receive writes. No positions or lengths survive this conversion.
    */
  private def mutableArray(source: Term.Mut, underlying: Tup)(using ResolutionContext): TermShape =
    rctx.state.mutableArrays.get(new Identity(source)) match
      case S(array) => array
      case N =>
        val cls = prelude.builtins.Array.defn.get
        softAssert(cls.tparams.length == 1, "The builtin Array must have one element type parameter")
        val param = cls.tparams.head.sym
        val site = FlowSymbol("mutable array")(using rctx.owner)
        val context = ExitMark(ResolutionBoundary(cls.sym), S(site), NoMarks)
        val elements = new TypeResolution(source, messages => resolError(source, messages))
        // The parameter host receives this allocation's elements as templates
        // written at the literal, distinguished from other allocations by marks.
        rctx.recordTemplateBinders(elements, lexicalBinders(underlying))
        elements.publish(TypeShape.Parameter(param, param.inferenceHost))
        // A nominal interface lives at the literal's use site. Its element
        // reference points back into the allocation; putting the allocation exit
        // on the whole interface would also exit a selected method's class scope
        // twice, once here and once in NominalInstanceView.getMemberImpl.
        val element = transportType(declaredType(elements, Map.empty), context :: Nil)
        val shape = NominalInstanceView(cls, Map(param -> element), implicitParent(cls))(N, ShapeProvenance.empty)(this)
        rctx.state.mutableArrays(new Identity(source)) = shape
        listenTerm(underlying): tuple =>
          listenArrayElements(tuple): element =>
            publishParameter(param, element.enter(context :: Nil))
        shape

  /** Member lookup on a declared nominal interface reached through `receiver`.
    *
    * A member's signature is interpreted at its class's definition: its Capture
    * nodes cross from the member into the class's enclosing scopes. The receiver
    * path, however, starts where the value was created or annotated, which can be
    * nested more deeply. For example, in
    * `fun mk(xs) = xs.map((x, ...) => mk([x]))`, the tuple `[x]` is created in
    * one activation of `mk` and passed to another, so its path is `↘mk ↗mk`,
    * whereas `mk([1])` passes a tuple with path `↘mk`. The innermost exits of
    * scopes that do not enclose the class's definition (here, the first `↗mk`,
    * since `Array` is global) are the value's provenance. They transport the
    * class's type-argument bindings, but do not move the member's scope.
    * Appending the whole path to the member instead places the scope of `map`
    * inside `mk` for one receiver and outside it for the other. Both receivers
    * share the `U` instance of the same `map` selection. Candidates published
    * through one path then cross the same scope twice when they are read
    * through the other path.
    */
  private[semantics] def nominalMember(view: NominalInstanceView, name: MemberKey, receiver: Marks)(using ResolutionContext): MemberLookup =
    val defn = view.defn
    // Module/object references introduce no value invocation boundary.
    val scope = defn.sym match
      case _: ModuleOrObjectSymbol => N
      case symbol => S(ResolutionBoundary(symbol))
    def inherited: MemberLookup =
      (MemberKey.index(name), arrayElementType(view)) match
        // An element's value keeps its whole path, including its provenance.
        case (S(index), S(element)) if index >= 0 =>
          MemberLookup.Indexed(TupleShape.TypedField(element, Nil) :: Nil, Nil).withMarks(receiver :: Nil)
        case _ =>
          // The parent is referenced inside the class, like its own members'
          // annotations: `class Int extends Num` captures `Num` into Int's
          // scope. An inherited member exits that scope before the receiver
          // path applies, just like an own member.
          val parentMember = nominalParent(view).fold[MemberLookup](MemberLookup.Missing): parent =>
            val Marked(parentView, inner) = parent
            markCarrier.exit(inner).exit(receiver) match
              case Marked(_, path) => parentView.getMemberThrough(name, path)
              // The parent interface is not reachable through this receiver;
              // applying these marks to its members yields no candidates.
              case NoShape => parentView.getMember(name).withMarks(inner :: receiver :: Nil)
          parentMember.withAnnotation(view.annotation)
    MemberKey.own(defn, name) match
      case S(member) =>
        val (location, provenance) = splitReceiverPath(defn, receiver)
        // Supplied arguments are outside the class; its parameter annotations
        // are inside. Enclosing binders keep their own lexical contexts and
        // enter the class through the annotation's explicit Capture nodes.
        val transported = view.bindings.map: (symbol, bound) =>
          val argument = provenance match
            case NoMarks => bound
            case provenance: ExitMark => transportType(bound, provenance :: Nil)
          symbol -> argument
        val local = captureNominalBindings(defn, transported)
        MemberLookup.own(defn, member,
          MemberLookup.Declared(member, local, scope.toList.map(ExitMark(_, N, NoMarks)), view.annotation, true)
            .withMarks(location match
              case NoMarks => Nil
              case location: SomeMarks => location :: Nil),
          inherited)
      case N => inherited

  /** Supplied class arguments are outside the instance scope. Both member and
    * parent annotations refer to those parameters from inside that scope.
    * Enclosing binders instead enter through their own explicit Capture nodes.
    */
  private def captureNominalBindings(defn: ClassLikeDef, bindings: Map[VarSymbol, DeclaredType])
      (using ResolutionContext): Map[VarSymbol, DeclaredType] =
    val parameters = defn.tparams.map(_.sym).toSet
    bindings.map: (symbol, bound) =>
      symbol -> (if parameters(symbol) && !defn.sym.isInstanceOf[ModuleOrObjectSymbol]
        then captureType(bound, defn.sym) else bound)

  /** A nominal value lives outside its class's instance scope, but its parent
    * annotation is resolved inside that scope. Leave it before applying the
    * value's caller path, both for inherited members and ancestor constraints.
    * Constructed shapes already carry this exit in their constructor context;
    * adding it to those shapes would cross the same boundary twice.
    */
  private def nominalParent(view: NominalInstanceView)(using ResolutionContext): Opt[TermShape] =
    view.parent.flatMap: parent =>
      val exited = view.defn.sym match
        case _: ModuleOrObjectSymbol => parent
        case symbol => transportShape(parent, ExitMark(ResolutionBoundary(symbol), N, NoMarks) :: Nil)
      exited match
        case parent: TermShape => S(parent)
        case NoShape => N

  /** Split a receiver path into the path from `defn`'s definition to the consumer,
    * and the innermost exits of scopes not enclosing that definition. Exits are
    * applied innermost first, so once a path leaves an enclosing scope of `defn`,
    * it cannot leave a scope that does not enclose `defn`.
    */
  private def splitReceiverPath(defn: ClassLikeDef, receiver: Marks)(using ResolutionContext): (Marks, ExitMarks) =
    val enclosing = defn.sym.getState.newResolverState.lexicalBoundaries.get(defn.sym)(using defn.sym.getState.newResolverState.context).getOrElse(
      lastWords(s"Nominal declaration ${defn.sym.nme} must record its enclosing resolution scopes"))
    def exits(path: ExitMarks): (ExitMarks, ExitMarks) = path match
      case ExitMark(boundary, id, rest) if enclosing(boundary) =>
        val (location, provenance) = exits(rest)
        (ExitMark(boundary, id, location), provenance)
      case provenance =>
        softAssert(!enclosing.exists(provenance.hasExit),
          "A receiver path cannot leave an enclosing scope of its class before a nested scope")
        (NoMarks, provenance)
    def go(path: Marks): (Marks, ExitMarks) = path match
      case EntryMark(boundary, id, rest) =>
        val (location, provenance) = go(rest)
        (EntryMark(boundary, id, location), provenance)
      case path: ExitMarks => exits(path)
    go(receiver)

  /** A checked index `prefix.[idx]` reads an element of an array. The index is
    * evaluated at runtime, so every element is a candidate, as for a spread.
    * Unlike a dynamic access `prefix![idx]`, it does not authorize dynamic
    * operations on the result: only a dynamic array has dynamic elements.
    */
  private def listenArrayIndex(sel: DynSel, prefix: Term)(listener: Listener)(using ResolutionContext): Unit =
    listenTermViews(prefix): receiver =>
      if !listenArrayElements(receiver)(listener) then receiver match
        case Marked(_: DynShape, _) => listener(receiver)
        case Marked(unknown: UnknownValueShape, marks) =>
          UnknownValueShape(sel, unknown.fromPublicInterface)(unknown.provenance.via(msg"This array index has no known element shape." -> sel.toLoc))
            .exit(marks) match
              case value: TermShape => listener(value)
              case NoShape => ()
        case _ =>
          if rctx.state.arrayIndexErrors.add(new Identity(sel)) then
            resolError(sel, receiver.diagnostic(msg"${receiver.describe.capitalize} does not support checked array indexing.") :::
              (msg"Use '![...]' for a dynamic access." -> N) :: Nil)

  private[semantics] def arrayElementType(array: NominalInstanceView): Opt[DeclaredType] =
    val cls = prelude.builtins.Array.defn.get
    array.ancestor(cls).flatMap(_.bindings.get(cls.tparams.head.sym))

  /** Element writes constrain the same declared parameter as Array's methods.
    * An annotated element type receives input constraints without exposing
    * additional members from the assigned value.
    */
  private[semantics] def assignArrayElement(lhs: Term, rhs: Term)(using ResolutionContext): Unit =
    val receiver = lhs match
      case NewSel(prefix, id, N) if id.name.toIntOption.exists(_ >= 0) => S(prefix)
      // Dynamic writes also reach the elements that checked indexing reads.
      case DynSel(prefix, _, true, _) => S(prefix)
      case _ => N
    receiver.foreach: prefix =>
      listenTermViews(prefix): array =>
        val (head, context) = array.applicationHead
        head match
          case nominal: NominalInstanceView => arrayElementType(nominal).foreach: element =>
            listenTerm(rhs): value =>
              value.enter(context) match
                case value: TermShape => inferTypeArguments(element, value, context, S(rhs))
                case NoShape => ()
          case _ => ()

  private[semantics] def listenTupleField(field: TupleShape.Fixed)(listener: Listener)(using ResolutionContext): Unit =
    def receive(shape: TermShape)(using ResolutionContext): Unit = transportShape(shape, field.marks) match
      case value: TermShape => listener(value)
      case NoShape => ()
    field match
      case TupleShape.Field(field, _) => listenTerm(field.term)(receive)
      case TupleShape.TypedField(tpe, _) => listenTypeInstances(tpe)(receive)
      case TupleShape.UnknownField(source, _) => receive(UnknownValueShape.at(source))
      case TupleShape.ValueField(value, _) => receive(value)
      case TupleShape.ViewedField(source, instances, _) =>
        listenTupleField(source)(value => receive(instantiateShape(value, instances)))(using rctx.withInstances(instances))

  /** Array patterns and rest-parameter constraints read Array's element bound.
    * Spreads instead observe the iteration protocol below. Never recover array
    * elements from constructor values: arrays are mutable, and the one-number
    * constructor creates empty slots.
    */
  private[semantics] def listenArrayElements(shape: TermShape)(listener: Listener)(using ResolutionContext): Bool =
    shape.applicationHead._1 match
      case tuple: TupleShape =>
        listenArrayElements(tuple.arrayParent)(element =>
          transportShape(element, shape.applicationHead._2) match
            case value: TermShape => listener(value)
            case NoShape => ())
      case _ => listenClassArgument(shape, prelude.builtins.Array.defn.get)(listener)

  /** Follow the actual iteration protocol. Each spread owns stable selection and
    * application sites; all operand alternatives contribute to one element host.
    * Unknown steps stay permissive and never replace already-known element flows.
    */
  private def iterationFlow(source: Term, scope: Opt[Set[VarSymbol]])(using ResolutionContext): IterationFlow =
    rctx.spreadFlow(source):
      def site(name: Str): FlowSymbol = FlowSymbol(name)(using rctx.owner)
      val empty = Tup(Nil)(Tree.Tup(Nil)).withLocOf(source)
      scope.foreach(rctx.recordLexicalBinders(empty, _))
      def call(name: Str): App =
        val tree = new Tree.App(Tree.Ident(name), Tree.Tup(Nil))
        tree.withLocOf(source)
        val result = new App(Term.Missing, empty)(tree, N, site(name))
        scope.foreach(rctx.recordLexicalBinders(result, _))
        result
      val elements = new TypeResolution(source, messages => resolError(source, messages))
      rctx.recordTemplateBinders(elements, scope)
      val flow = new IterationFlow(elements, call("iterator"), call("next"),
        site("iterator member"), site("next member"), site("iteration done"), site("iteration value"))
      def select(value: TermShape, key: MemberKey, site: FlowSymbol)(receive: Listener)(using ResolutionContext): Unit =
        listenInstanceViews(value): view =>
          listenMemberValue(view.getMember(key).visibleFrom(_ => false, reportInaccessible = false),
            site, source, TypeSubstitution.empty, () => receive(UnknownValueShape.spread(source, view)))(receive)
      listenTerm(flow.iterator): iterator =>
        select(iterator, "next", flow.nextMember)(applyShape(_, empty, flow.next, checked = false))
      listenTerm(flow.next): step =>
        select(step, "done", flow.doneMember): done =>
          val completed = done match
            case Marked(intro: IntroShape, _) => intro.trm match
              case Lit(Tree.BoolLit(true)) => true
              case _ => false
            case _ => false
          if !completed then
            select(step, "value", flow.valueMember)(value => elements.publish(TypeShape.Inferred(value)))
      flow

  private def listenIterableElements(value: TermShape, flow: IterationFlow)(using ResolutionContext): Unit =
    val symbols = prelude.builtins.SymbolModule
    // This expression is a diagnostic witness; lookup uses the canonical path.
    val module = Term.MemberRef(symbols.bms)(N, FlowSymbol.memSym(symbols.bms))
    val iterator = Term.NewSel(module, Tree.Ident("iterator"), N)(FlowSymbol.synthSel("iterator"))
    val iteratorKey = SymbolKey(symbols.module :: symbols.iterator :: Nil)(
      iterator)
    listenInstanceViews(value): view =>
      listenMemberValue(view.getMember(iteratorKey).visibleFrom(_ => false, reportInaccessible = false),
        flow.iteratorMember, flow.elements.source, TypeSubstitution.empty,
        () => flow.elements.publish(TypeShape.Inferred(UnknownValueShape.spread(flow.elements.source, view)))):
          method => applyShape(method, flow.iterator.rhs, flow.iterator, checked = false)

  private[semantics] def listenPromisePayload(shape: TermShape)(listener: Listener)(using ResolutionContext): Bool =
    listenClassArgument(shape, prelude.builtins.Promise.defn.get)(listener)

  /** Read the sole type argument of a nominal instance or an inferred construction.
    * Marks leave the allocation and enclosing scopes before the payload is observed.
    */
  private def listenClassArgument(shape: TermShape, cls: ClassLikeDef)(listener: Listener)(using ResolutionContext): Bool =
    softAssert(cls.tparams.length == 1, "The observed class must have one type parameter")
    val param = cls.tparams.head.sym
    val ShapeParts(source, instances, _) = shapeParts(shape)
    val head = source.applicationHead._1
    val context = source.applicationHead._2
    def receive(element: TermShape)(using ResolutionContext): Unit = transportShape(element, context) match
      case value: TermShape => listener(value)
      case NoShape => ()
    head match
      case nominal: NominalInstanceView => nominal.ancestor(cls) match
        case S(instance) =>
          instance.bindings.get(param) match
            case S(bound) =>
              listenTypeInstances(bound.instantiate(instances))(receive)
              true
            case N => false
        case N => false
      case defn: DefnShape if defn.clsDef.contains(cls) && source.isInstanceOfClass(cls) =>
        val parameter = instances.getOrElse(param, param)
        listenTypeArgument(parameter)(receive)
        true
      case _ => false

  /** Subscribe once to complete argument-tuple candidates. A pending spread is not
    * an argument, nor evidence of an arity mismatch; each resolved combination is.
    */
  def zipArgs(mss: Ls[Marks], ps: ParamList, args: Term, src: Term, funSh: TermShape)(using ResolutionContext): Unit =
    zipArgsIn(mss, ps, args, src, funSh, rctx.instances)

  private def zipArgsIn(mss: Ls[Marks], ps: ParamList, args: Term, src: Term, funSh: TermShape,
      instances: TypeSubstitution)(using ResolutionContext): Unit =
    val params = ps.allParams
    zipArgumentShapes(mss, Arity(ps), args, src, funSh)(
      (index, shape) => constrainParameterIn(params(index), shape, mss, instances, S(src)))

  private[semantics] def constrainParameter(p: Param, shape: TermShape | NoShape, marks: Ls[Marks])(using ResolutionContext): Unit =
    constrainParameterIn(p, shape, marks, rctx.instances, N)

  private def constrainParameterIn(p: Param, shape: TermShape | NoShape, marks: Ls[Marks],
      instances: TypeSubstitution, site: Opt[Term])(using ResolutionContext): Unit = shape match
    case NoShape => ()
    case sh: TermShape =>
      parameterSignature(p) match
        case S(tpe) => inferTypeArguments(tpe.instantiate(instances), sh, marks, site)
        case N => publishParameter(p.sym, sh)(using rctx.withInstances(instances))

  private[semantics] def parameterSignature(p: Param)(using ResolutionContext): Opt[DeclaredType] =
    p.sign.map(sign => declaredType(typeResolution(sign), Map.empty)).orElse(signatureParameters.get(p.sym))
      .orElse(p.sym.getState.newResolverState.signatureParameters.get(p.sym)(using p.sym.getState.newResolverState.context))

  /** The number of arguments a parameter list accepts, with `leading` parameters, of which
    * `leadingRequired` are required, and, if `hasRest`, a variadic parameter followed by `trailing` ones. */
  private case class Arity(leadingRequired: Int, leading: Int, hasRest: Bool, trailing: Int):
    require(hasRest || trailing == 0)
    def required: Int = leadingRequired + trailing
    def describe: Message =
      if hasRest then msg"at least ${required.toString} ${"argument".pluralized(required)}"
      else if required == leading then msg"${required.toString} ${"argument".pluralized(required)}"
      else msg"${required.toString} to ${leading.toString} arguments"
  private object Arity:
    def apply(ps: ParamList): Arity = Arity(ps.leadingRequiredCount, ps.params.length, ps.variadic.nonEmpty, ps.trailingParams.length)
    def apply(ps: DeclaredParams): Arity = Arity(ps.leadingRequired, ps.params.length, ps.hasRest, ps.trailing.length)
  
  /** Publish the shapes of the arguments matching each parameter position, where index
    * `arity.leading` denotes the variadic parameter and the following indices its trailing parameters,
    * as in `ParamList.allParams`. Optional parameters already include null at their declarations. */
  private def zipArgumentShapes(mss: Ls[Marks], arity: Arity,
      args: Term, src: Term, funSh: TermShape)(publish: (Int, TermShape | NoShape) => ResolutionContext ?=> Unit)(using ResolutionContext): Unit =
    checkArgumentArity(args, arity, src, funSh):
      case (tuple, marks) => zipTupleShapes(mss, arity, tuple, marks)(publish)

  /** Calls and tuple patterns match the same leading/rest/trailing layout.
    * Share position bounds and rest slicing so both preserve possible elements
    * without assigning them impossible positions or inventing minimum lengths.
    */
  private def zipTupleShapes(mss: Ls[Marks], arity: Arity, tuple: TupleShape, marks: Marks)(
      publish: (Int, TermShape | NoShape) => ResolutionContext ?=> Unit)(using ResolutionContext): Unit =
    val Arity(leadingRequired, expectedCount, hasRest, trailing) = arity
    val knownCount = tuple.segments.count(_.isInstanceOf[TupleShape.Fixed])
    val unknownCount = tuple.segments.length - knownCount
    val minExtra = (arity.required - knownCount).max(0)
    val extra = (expectedCount - knownCount).max(0)
    // Match leading positions from the left and trailing positions from the right.
    // A fixed field cannot cross the required parameters at the opposite end.
    // When all unknown segments precede it, they must supply any missing required
    // arguments. These bounds avoid enumerating spread lengths or their combinations.
    def assignPositions(segments: Ls[TupleShape.Segment], count: Int, reserved: Int, position: Int => Int): Unit =
      def assign(segment: TupleShape.Segment, positions: Range)(using ResolutionContext): Unit =
        positions.foreach: index =>
          listenTupleField(segment.element): sh =>
            publish(position(index), sh.exit(marks).enter(mss))
      def loop(rest: Ls[TupleShape.Segment], before: Int, unknownBefore: Int): Unit = rest match
        case Nil => ()
        case (field: TupleShape.Fixed) :: tail =>
          val unknownAfter = unknownCount - unknownBefore
          val after = knownCount - before - 1
          if unknownAfter > 0 || after >= reserved then
            val first = if unknownBefore > 0 && unknownAfter == 0 then before + minExtra else before
            val last = if unknownBefore == 0 then before
              else if hasRest then count - 1 else before + extra
            assign(field, first until (last + 1).min(count))
          loop(tail, before + 1, unknownBefore)
        case (unknown: TupleShape.Unknown) :: tail =>
          val end = if hasRest then count else (before + extra).min(count)
          assign(unknown, before until end)
          loop(tail, before, unknownBefore + 1)
      loop(segments, 0, 0)
    assignPositions(tuple.segments, expectedCount, trailing, identity)
    assignPositions(tuple.segments.reverse, trailing, leadingRequired, index => expectedCount + trailing - index)
    if hasRest then
      // If consumption reaches an unknown segment, some subsequent fields
      // may have been consumed too. Widen their lengths, keeping every field's
      // deferred element flow. Replacing them with an opaque unknown would lose
      // member targets and ambiguities; retaining them as fixed fields would
      // invent a minimum length when the rest is spread into another call.
      def drop(xs: Ls[TupleShape.Segment], count: Int, approximate: Bool)(using ResolutionContext): Ls[TupleShape.Segment] =
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
            if approximate then
              xs.take(xs.length - suffix.length).map(segment => TupleShape.Unknown(tuple.source, segment.element)) ::: suffix
            else suffix
      val remaining = drop(drop(tuple.segments, expectedCount, true).reverse, trailing, true).reverse
      val rest = if remaining == tuple.segments then tuple else TupleShape.restView(tuple, remaining)(this)
      publish(expectedCount, rest.exit(marks).enter(mss))
  
  private def checkArgumentArity(args: Term, arity: Arity, src: Term,
      callable: TermShape)(matched: ShapeListener[(TupleShape, Marks)])(using ResolutionContext): Unit =
    val reportKey = new Object
    listenTermViews(args):
      case Marked(tuple: TupleShape, marks) =>
        val known = tuple.segments.count(_.isInstanceOf[TupleShape.Fixed])
        val unknown = known != tuple.segments.length
        val mismatch = (!unknown && known < arity.required) || (!arity.hasRest && known > arity.leading)
        if mismatch then
          if rctx.state.reportedArities.getOrElseUpdate(reportKey, mutable.Set.empty).add(known) then
            val count = if unknown then msg"at least ${known}" else msg"${known}"
            resolError(src, callable.arityDiagnostic(msg"${callable.describe.capitalize} expected ${arity.describe}, but got ${count}"))
        else matched((tuple, marks))
      case _ => resolError(src, msg"Expected an argument tuple." -> args.toLoc :: Nil)
  
  /** Resolve every constructor pattern through the same symbolic interpretation.
    * A class overload takes precedence over its term companion in this context.
    * Keep every candidate so lowering can diagnose ambiguity independently of
    * the order in which definitions and receiver shapes become available. */
  def constructorPattern(res: Pattern.Constructor)(using ResolutionContext): Unit = if newResolution then
    val lhs = res.target
    def select(sym: DefinitionSymbol[?])(using ResolutionContext): Bool =
      lhs.withoutCaptures match
        case trm: NewResolvable =>
          rctx.recordResolution(trm, trm.resolvedTargets.contains(sym))(trm.resolvedTargets ::= sym)
        case _ => ()
      if res.resolvedTargets.contains(sym) then false
      else
        rctx.recordResolution(res, false)(res.resolvedTargets ::= sym)
        true
    def reject(sh: TermShape)(using ResolutionContext): Unit =
      rctx.markError(res)
      resolError(res, sh.diagnostic(msg"${sh.describe.capitalize} cannot be used as a constructor pattern."))
    def classPattern(cls: ClassDef | ModuleOrObjectDef)(using ResolutionContext): Unit = if select(cls.sym) then
      val assoc = res.arguments match
        case N => Nil
        case S(args) => cls.paramsOpt match
          case N =>
            if args.nonEmpty || cls.isInstanceOf[ClassDef] then
              rctx.markError(res)
              resolError(res, msg"${cls.describe.capitalize} does not take pattern arguments." -> cls.headerLoc :: Nil)
            Nil
          case S(ps) =>
            // Elaboration reports and removes rest parameters of class-like definitions,
            // so the arity of a constructor pattern is the number of plain parameters.
            softAssert(ps.variadic.isEmpty, "Unexected rest parameter in class-like definition")
            if args.sizeCompare(ps.params) =/= 0 then
              rctx.markError(res)
              resolError(res,
                msg"${cls.describe.capitalize} expected ${ps.params.length} ${
                  "pattern argument".pluralized(ps.params.length)}, but got ${args.length}" -> cls.headerLoc :: Nil)
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
                    rctx.markError(res)
                    Nil
                case _ =>
                  rctx.markError(res)
                  resolError(res, msg"Pattern argument requires an accessible constructor field." -> p.toLoc :: Nil)
                  Nil
      if !rctx.hasError(res) then
        // Field reads of the matched value can invoke by-name members here.
        val site = FlowSymbol.pat()(using rctx.owner)
        lexicalBinders(lhs).foreach(rctx.recordSiteBinders(site, _))
        def publish(marks: Ls[Marks])(using ResolutionContext): Unit =
          val psh = CtorPatternShape(cls, assoc, res, site, marks)
          if res.currentShapes.add(psh) then res.notifyShapeListeners(psh)
        cls match
          // An ambiguous lookup can publish several constructors. Pair each
          // declaration only with its own references; the lookup diagnoses
          // competing candidates independently of this shape subscription.
          // The pattern already selected its class target above; this subscription
          // recovers capture marks without adding the operand's term target.
          case _: ClassDef => listenClass(lhs, recordTargets = false)(ref =>
            if ref.definition eq cls then publish(ref.marks)
          , _ => ())
          case _: ModuleOrObjectDef => publish(Nil)
    def valuePattern(sh: TermShape)(using ResolutionContext): Unit = shapeParts(sh).value match
      case Marked(ds: DefnShape, _) => ds.defn match
        case cls: ClassDef => classPattern(cls)
        case obj: ModuleOrObjectDef if obj.sym.asObj.isDefined => classPattern(obj)
        case td: TermDefinition => td.tsym match
          case ctor: ClassCtorSymbol => classPattern(ctor.associatedCls.defn.get)
          case _ => reject(sh)
        case _ => reject(sh)
      case _ => reject(sh)
    lhs.withoutCaptures match
      case Term.Error() => rctx.markError(res)
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
                    case S(cls: (ClassDef | ModuleOrObjectDef)) => classPattern(cls)
                    case _ => softAssert(false, "Completed pattern member has no definition")
                case N =>
                  val site = FlowSymbol.pat()(using rctx.owner)
                  lexicalBinders(lhs).foreach(rctx.recordSiteBinders(site, _))
                  fromBMS(bms, site, sh.markss, valuePattern, lhs, _ => (), false)
          case sh: TermShape => valuePattern(sh)
  
  /** Pattern bodies are resolved before their runtime matching code is generated.
    * Check their bindings against an arbitrary input, so a local caller cannot
    * supply undeclared assumptions to guards or transformations.
    */
  def checkPatternDefinition(definition: PatternDef)(using ResolutionContext): Unit =
    val source = Term.MemberRef(definition.bsym)(N, FlowSymbol.pat()(using rctx.owner))
    val unknown = UnknownValueShape(source, fromPublicInterface = false)(ShapeProvenance(
      msg"Pattern '${definition.sym.nme}' accepts values of unknown shape." -> definition.headerLoc :: Nil))
    matchShapePat(unknown, definition.pattern)(_ => ())

  /** Propagate possible values to pattern bindings. Constructor tests filter by
    * nominal class; guards and literal tests may conservatively retain shapes.
    * Both scrutinee and constructor shapes can arrive after this registration. */
  def matchShapePat(shape: Shape, pattern: Pattern)(matched: ShapeListener[Shape])(using ResolutionContext): Unit =
    shape match
      case value @ Marked(_: InstanceShape, _) if pattern.isInstanceOf[Pattern.Constructor] || pattern.isInstanceOf[Pattern.Tuple] =>
        listenInstanceViews(value)(matchShapePat(_, pattern)(matched))
        return
      case _ => ()
    // Some pattern outputs (notably concatenations and rebuilt constructors)
    // need a separate output interface. Do not reuse the input's fields for them.
    def unknownOutput: UnknownValueShape = rctx.patternOutput(pattern):
      UnknownValueShape(Term.Error().withLocOf(pattern), fromPublicInterface = false)(ShapeProvenance(
        msg"The output shape of this pattern is not yet known." -> pattern.toLoc :: Nil))
    def isNominal(ctor: Pattern.Constructor): Bool =
      ctor.resolvedTargets.nonEmpty && ctor.resolvedTargets.forall:
        case _: ClassSymbol | _: ModuleOrObjectSymbol => true
        case _ => false
    def preservesInput(pat: Pattern): Bool = pat match
      case Pattern.Wildcard() | Pattern.Literal(_) | Pattern.Range(_, _, _) | Pattern.Negation(_) => true
      case Pattern.Alias(inner, _) => preservesInput(inner)
      case Pattern.Guarded(inner, _) => preservesInput(inner)
      case Pattern.Annotated(inner, _) => preservesInput(inner)
      case ctor: Pattern.Constructor =>
        isNominal(ctor) && ctor.arguments.forall(_.forall(preservesInput))
      case _ => false
    // Negation filters the input, never a transformed output. Only discard a
    // candidate when the whole shape must match the excluded pattern. In
    // particular, failing to prove membership in a class is not proof of its
    // complement: abstract and structural inputs may still contain instances.
    def exclude(input: Shape, pat: Pattern)(receive: ShapeListener[Shape])(using ResolutionContext): Unit =
      input match
        case value @ Marked(_: InstanceShape, _) =>
          listenInstanceViews(value)(exclude(_, pat)(receive))
        case symbol: SymShape => fromSymbol(symbol, exclude(_, pat)(receive),
          Term.Error().withLocOf(pat), _ => (), false)
        case value: TermShape => pat match
          case Pattern.Wildcard() => ()
          case Pattern.Literal(literal) => shapeParts(value).value match
            case Marked(intro: IntroShape, _) => intro.trm match
              case Lit(actual) if actual === literal => ()
              case _ => receive(value)
            case _ => receive(value)
          case Pattern.Alias(inner, _) => exclude(value, inner)(receive)
          case Pattern.Annotated(inner, _) => exclude(value, inner)(receive)
          case Pattern.Composition(true, left, right) =>
            // Not (left or right): exclude both alternatives from the input.
            exclude(value, left)(exclude(_, right)(receive))
          case Pattern.Composition(false, left, right) =>
            // Not (left and right): either failed test admits the input.
            exclude(value, left)(receive)
            exclude(value, right)(receive)
          case Pattern.Negation(inner) if preservesInput(inner) =>
            matchShapePat(value, inner)(receive)
          case ctor: Pattern.Constructor if isNominal(ctor) =>
            def unrestricted(pat: Pattern): Bool = pat match
              case Pattern.Wildcard() => true
              case Pattern.Alias(inner, _) => unrestricted(inner)
              case Pattern.Annotated(inner, _) => unrestricted(inner)
              case _ => false
            ctor.subscribeToShapes:
              case CtorPatternShape(cls, fields, _, _, _) =>
                // A nominal match alone cannot exclude C(p) when p tests a
                // field's value. Retain it unless every field accepts anything.
                if !value.isInstanceOfClass(cls) || !fields.forall((_, p) => unrestricted(p)) then receive(value)
          // Guards, extractors, and patterns with transformed intermediate
          // results may fail even on a matching nominal input. Retain their
          // input interfaces until those tests have a definite shape semantics.
          case _ => receive(value)
    pattern match
      case al @ Pattern.Alias(pat, _) =>
        matchShapePat(shape, pat): sh =>
          // Rejected duplicate/negated bindings have no allocated symbol. Pattern
          // validation already reports them; only valid bindings receive flow.
          al.symbolOption.foreach: symbol =>
            publishActivated(symbol, sh)
          matched(sh)
      case Pattern.Wildcard() | Pattern.Literal(_) | Pattern.Range(_, _, _) => matched(shape)
      case Pattern.Chain(left, right) =>
        matchShapePat(shape, left)(sh => matchShapePat(sh, right)(matched))
      case Pattern.Composition(false, left, right) =>
        // Conjunction tests both sides against the input and produces a pair;
        // only a chain feeds one pattern's output into the next pattern.
        matchShapePat(shape, left)(_ => ())
        matchShapePat(shape, right)(_ => ())
        matched(unknownOutput)
      case Pattern.Composition(true, left, right) =>
        matchShapePat(shape, left)(matched)
        matchShapePat(shape, right)(matched)
      case Pattern.Negation(pat) =>
        matchShapePat(shape, pat)(_ => ())
        exclude(shape, pat)(matched)
      case Pattern.Concatenation(left, right) =>
        // Prefix matching and concatenating transformed results need their own
        // shape rules. Still check nested bindings; no output interface is assumed.
        val unknown = unknownOutput
        matchShapePat(unknown, left)(_ => ())
        matchShapePat(unknown, right)(_ => ())
        matched(unknown)
      case Pattern.Record(fields) =>
        // A field-presence test supplies no field interface by itself. Nested
        // class tests can refine these unknowns before guards use their aliases.
        val unknown = unknownOutput
        fields.foreach((_, pat) => matchShapePat(unknown, pat)(_ => ()))
        matched(unknown)
      case Pattern.Transform(pat, parameters, transform) =>
        // The transform is lowered to a separate lambda. Its source references
        // already name these parameter symbols, not the aliases used by guards.
        parameters.foreach: (binding, parameter) =>
          pipeTerm(Term.SimpleRef(binding)(N), parameter)
        matchShapePat(shape, pat)(_ => ())
        listenTerm(transform)(matched)
      case Pattern.Guarded(pat, _) => matchShapePat(shape, pat)(matched)
      // Compilation-strategy annotations do not change the pattern's bindings.
      case Pattern.Annotated(pat, _) => matchShapePat(shape, pat)(matched)
      case ctor: Pattern.Constructor =>
        def listenConstructor(psh: PatternShape)(using ResolutionContext): Unit = psh match
          case CtorPatternShape(cls, fs, _, resSym, constructorMarks) =>
            // Nominal views already live outside the instance. Cancel the
            // constructor's own exit, retaining its enclosing lexical path.
            // A self-contained value such as unit would discard those outer
            // exits and lose the context of a class returned from a function.
            val context = cls match
              case _: ClassDef => MarkedShape.enter(markCarrier, ResolutionBoundary(cls.sym), N).exit(constructorMarks) match
                case Marked(_, marks) => marks :: Nil
                case NoShape => lastWords("A wildcard constructor entry cannot reject its own exit")
              case _: ModuleOrObjectDef => Nil
            def atPattern(tpe: DeclaredType)(receive: Listener)(using ResolutionContext): Unit =
              listenTypeViews(tpe): candidate =>
                transportShape(candidate, context) match
                  case value: TermShape => receive(value)
                  case NoShape => ()
            def check(sh: TermShape, unknown: Opt[TermShape])(using ResolutionContext): Unit =
              if sh.isInstanceOfClass(cls) then
                fs.foreach: (bms, pat) =>
                  def member(info: MemberLookup, instances: TypeSubstitution)(using ResolutionContext): Unit = info match
                    case MemberLookup.All(members) => members.foreach(member(_, instances))
                    case MemberLookup.Contextual(source, substitution) => member(source, instances.withOverrides(substitution))
                    case MemberLookup.Found(sym: BlockMemberSymbol, marks) =>
                      fromBMS(sym, resSym, marks,
                        field => matchShapePat(instantiateShape(field, instances), pat)(_ => ()), ctor.target, _ => (), false)
                    case MemberLookup.Declared(member, bindings, marks, annotation, positive) =>
                      listenDeclaredMember(member, bindings, resSym, ctor.target, annotation, _ => (), false, positive, marks, N): field =>
                        listenInstanceViews(instantiateShape(field, instances)): field =>
                          transportShape(field, marks) match
                            case value: TermShape =>
                              val field = (value.applicationHead._1, unknown) match
                                case (_: UnknownValueShape, S(Marked(origin: UnknownValueShape, marks))) =>
                                  UnknownValueShape(origin.source, origin.fromPublicInterface)(origin.provenance.via(
                                    msg"This constructor field may contain a value of unknown shape." -> member.toLoc)).exit(marks)
                                case _ => value
                              field match
                                case field: TermShape => matchShapePat(field, pat)(_ => ())
                                case NoShape => ()
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
                  // The pattern reads the field of `cls` even when it is private,
                  // ignoring the private members of the same name of `cls`'s subclasses.
                  member(sh.getMember(bms.nme).visibleFrom(_ is cls, reportInaccessible = false), TypeSubstitution.empty)
                matched(if fs.forall((_, pat) => preservesInput(pat)) then sh else unknownOutput)
            // A structural annotation describes possible class instances too.
            // A successful class test supplies the tested class's declared
            // interface even when the input did not have a nominal interface.
            // Interpret the constructor reference with its lexical captures:
            // inside C, testing against C must not place the refined value
            // outside C's scope before a subsequent field read leaves it.
            def testedClass(using ResolutionContext): DeclaredType =
              rctx.state.patternTypes.getOrElseUpdate((new Identity(ctor), cls.sym), {
                val resolution = new TypeResolution(ctor.target, messages => resolError(ctor.target, messages))
                resolution.publish(TypeShape.Nominal(cls))
                declaredType(resolution, Map.empty)
              })
            def subclass(base: ClassLikeDef)(using ResolutionContext): Unit =
              // A base-class annotation or self reference can denote a subclass
              // instance. The test exposes that subclass's declared fields even
              // when no constructor call supplies a concrete receiver shape.
              // Omitted subclass arguments remain abstract and share the cached
              // type, rather than borrowing types from unrelated allocations.
              atPattern(testedClass): candidate =>
                if candidate.isInstanceOfClass(base) then check(candidate, N)
            def narrow(sh: TermShape)(using ResolutionContext): Unit = shapeParts(sh).value match
              case Marked(_: RecordTypeShape, _) =>
                atPattern(testedClass)(check(_, N))
              case Marked(unknown: UnknownValueShape, _) =>
                // A class test can succeed for an external input. Its fields then
                // expose their declarations, not shapes observed in local calls.
                // Unknown type arguments retain the original diagnostic witness.
                // Refinement is a function of a static test and its input, not
                // an allocation on every delivery. A recursive callback can
                // feed the same unknown back to this test through Array[T].
                // Fresh argument hosts would make each otherwise identical
                // refined Array a new candidate and prevent a fixed point.
                val refined = rctx.state.patternRefinements.getOrElseUpdate((new Identity(ctor), cls.sym, context, ShapeIdentity.key(sh)), {
                  val base = testedClass.resolution
                  val arg = new TypeResolution(unknown.source, messages => resolError(unknown.source, messages))
                  // An unknown value has no dependencies.
                  rctx.recordTemplateBinders(arg, S(Set.empty))
                  val contextual = transportShape(sh, inverseMarks(context))
                  contextual match
                    case value: TermShape => arg.publish(TypeShape.Inferred(value))
                    case NoShape => ()
                  val applied = new TypeResolution(ctor.target, messages => resolError(ctor.target, messages))
                  applied.publish(TypeShape.Applied(base, cls.tparams.map(_ => arg)))
                  declaredType(applied, Map.empty)
                })
                atPattern(refined)(check(_, S(sh)))
              case Marked(opaque: OpaqueTypeShape, marks) =>
                UnknownValueShape(opaque.source, fromPublicInterface = false)(opaque.provenance).exit(marks) match
                  case value: TermShape => narrow(value)
                  case NoShape => ()
              case Marked(nominal: NominalInstanceView, _) if !nominal.isInstanceOfClass(cls) =>
                subclass(nominal.defn)
              case Marked(base: BaseShape, _) if !base.isInstanceOfClass(cls) =>
                subclass(base.defn)
              case _ => check(sh, N)
            shape match
              case sh: TermShape => narrow(sh)
              case sh: SymShape => fromSymbol(sh, narrow, ctor.target, _ => (), false)
        ctor.subscribeToShapes(listenConstructor)
      case Pattern.Tuple(leading, spread) =>
        val trailing = spread.fold(Nil)(_._3)
        val required = leading.length + trailing.length
        def tupleBindings(tuple: TupleShape, marks: Marks)(using ResolutionContext): Unit =
          val segments = tuple.segments
          val known = segments.count(_.isInstanceOf[TupleShape.Fixed])
          val uncertain = known != segments.length
          if (uncertain || known >= required) && (spread.nonEmpty || known <= required) then
            val patterns = leading ::: spread.toList.flatMap((_, rest, trailing) => rest :: trailing)
            val arity = Arity(leading.length, leading.length, spread.nonEmpty, trailing.length)
            zipTupleShapes(Nil, arity, tuple, marks): (index, value) =>
              value match
                case value: TermShape => matchShapePat(value, patterns(index))(_ => ())
                case NoShape => ()
            tuple.exit(marks) match
              case value: TermShape => matched(value)
              case NoShape => ()
        def narrow(value: TermShape)(using ResolutionContext): Unit = value match
          case Marked(tuple: TupleShape, marks) => tupleBindings(tuple, marks)
          case Marked(unknown: UnknownValueShape, marks) =>
            tupleBindings(TupleShape(unknown.source,
              TupleShape.Unknown(unknown.source, TupleShape.ValueField(unknown, Nil)) :: Nil)(this), marks)
          case Marked(nominal: NominalInstanceView, marks) =>
            // Bind the elements as instances of the declared element type:
            // binding a pattern variable does not request the type's interface,
            // which its uses observe on demand. Expanding the interface here
            // would bind a separate tuple for each candidate of a type parameter
            // such as FingerTreeList's `Deep[T]`, and each such tuple creates
            // further rest views and Array interfaces.
            arrayElementType(nominal).foreach: element =>
              tupleBindings(TupleShape(element.resolution.source,
                TupleShape.Unknown(element.resolution.source, TupleShape.TypedField(element, Nil)) :: Nil)(this), marks)
          case _ => ()
        shape match
          case value: TermShape => narrow(value)
          case sym: SymShape => fromSymbol(sym, narrow, Term.Missing, _ => (), false)
      case _ =>
        raise(ErrorReport(msg"This pattern is not supported during shape resolution." -> pattern.toLoc :: Nil))
  
  def matchScrutPat(scrutinee: Term, pattern: Pattern)(using ResolutionContext): Unit = if newResolution then
    listenTerm(scrutinee)(sh => matchShapePat(sh, pattern)(_ => ()))
  
  /** Both class interpretations use the original class as their scheme owner.
    * Instantiated views must never become new owners of the same source binders.
    */
  private def definitionParameters(definition: DefnShape): (AnyDefinitionSymbol, Ls[VarSymbol]) =
    definition.clsDef match
      case S(cls) => (cls.sym, cls.tparams.map(_.sym))
      case N => definition.defn match
        case td: TermDefinition => (td.tsym, definitionBinders(td))
        case _ => lastWords("A callable definition must have a class or term owner")

  private def instantiateDefinition(definition: DefnShape, site: FlowSymbol, siteBinders: Opt[Set[VarSymbol]], marks: Ls[Marks],
      captured: TypeSubstitution, supplied: Opt[Ls[DeclaredType]])
      (using ResolutionContext): TypeSubstitution =
    val (owner, parameters) = definitionParameters(definition)
    instantiateParameters(owner, parameters, site, siteBinders, marks, captured, supplied)

  private def instantiateParameters(owner: AnyDefinitionSymbol, parameters: Ls[VarSymbol], site: FlowSymbol,
      siteBinders: Opt[Set[VarSymbol]], marks: Ls[Marks], captured: TypeSubstitution,
      supplied: Opt[Ls[DeclaredType]])(using ResolutionContext): TypeSubstitution =
    val substitution = captured.withOverrides(rctx.instantiateTypeParameters(owner, site, parameters, siteBinders))
    supplied.foreach: arguments =>
      bindTypeArguments(parameters.map: parameter =>
        val instance = substitution(parameter)
        TypeShape.Parameter(instance, instance.inferenceHost)
      , marks, arguments)
    if parameters.nonEmpty && rctx.state.inferredInstantiations.add((owner, site, substitution, marks)) then
      parameters.foreach: parameter =>
        val instance = substitution(parameter)
        listenTypeArgument(parameter): bound =>
          bound.applicationHead._1 match
            case _: RigidTypeShape => ()
            case _ => inferTypeArguments(instanceType(instance), instantiateShape(bound, substitution), marks, N)
    substitution

  def appShape(source: TermShape, args: Term, res: App)(using ResolutionContext): Unit =
    applyShape(source, args, res, checked = true)

  private def applyShape(source: TermShape, args: Term, res: App, checked: Bool)(using ResolutionContext): Unit =
    val callerInstances = rctx.instances
    val ShapeParts(lhs, lexical, supplied) = shapeParts(source)
    val captured = callerInstances.withOverrides(lexical)
    val instances = lhs match
      case Marked(definition: DefnShape, _) if supplied.isEmpty =>
        instantiateDefinition(definition, res.resSym, lexicalBinders(res), lhs.applicationHead._2, captured, N)
      case Marked(construction: NewShape, _) if construction.argss.isEmpty && !construction.isSaturated && construction.supplied.isEmpty =>
        instantiateDefinition(construction.receiver, res.resSym, lexicalBinders(res), lhs.applicationHead._2, captured, N)
      case _ => captured
    def publish(value: TermShape)(using ResolutionContext): Unit =
      publishViewed(res, value, instances)(using rctx.withInstances(callerInstances))
    lhs match
      case Marked(view: IntersectionView, marks) =>
        view.values.foreach: value =>
          transportShape(value, marks :: Nil) match
            case value: TermShape => applyShape(value, args, res, checked)
            case NoShape => ()
        return
      case Marked(_: InstanceShape, _) =>
        listenInstanceViews(instantiateShape(lhs, instances), mergeIntersections = checked)(applyShape(_, args, res, checked))
        return
      case _ => ()
    // Explicit calls require a known interface or an explicitly dynamic value.
    // Implicit protocol observations instead retain unknown results below and
    // leave protocol compatibility to type checking.
    lhs match
      case Marked(_: DynShape, _) =>
        if checked then res.callableTargets.currentShapes.add(source)
        publish(lhs)
        return
      case _ => ()
    lhs match
      case Marked(nominal: NominalInstanceView, _) if nominal.isInstanceOfClass(prelude.builtins.Function.defn.get) =>
        if checked then res.callableTargets.currentShapes.add(source)
        // The builtin Function class guarantees callability, including through
        // aliases and subclasses, but supplies neither an arity nor a result
        // interface. Check the argument tuple and leave arity checks to runtime;
        // the result must remain unknown rather than acquiring dynamic access.
        if checked then checkArgumentArity(args, Arity(0, 0, true, 0), res, lhs)(_ => ())
        // The call identifies the result in the flow graph, while the annotation
        // explains its missing interface. Preserve that distinction so subsequent
        // selections and applications both diagnose the restricting type once.
        val provenance = ShapeProvenance(msg"The 'Function' type does not specify a return type." -> N :: Nil)
        publish(UnknownValueShape(res, fromPublicInterface = false)(nominal.annotation.fold(provenance)(provenance.withTypeOrigin)))
        return
      case Marked(original: CallableTypeShape, context) =>
        if checked then res.callableTargets.currentShapes.add(source)
        val viewed = instantiateShape(original, instances) match
          case callable: CallableTypeShape => callable
          case _ => lastWords("A callable view must remain callable")
        val callable = instantiateCallable(viewed, res.resSym, lexicalBinders(res), context :: Nil)
        val ps = callable.paramLists.head
        if checked then zipArgumentShapes(context :: Nil, Arity(ps), args, res, lhs)((index, value) =>
          ps.allParams(index).tpe.foreach: tpe =>
            value match
              case value: TermShape => inferTypeArguments(tpe, value, context :: Nil, S(res))
              case NoShape => ())
        def publish(shape: TermShape)(using ResolutionContext): Unit = transportShape(shape, context :: Nil) match
          case value: TermShape =>
            publishViewed(res, value, TypeSubstitution.empty)(using rctx.withInstances(callerInstances))
          case NoShape => ()
        listenCallableResult(callable)(publish)
        return
      case _ => ()
    val sh = appShapes.getOrElseUpdate((ShapeIdentity.key(lhs), res.resSym), {
      log(dbg"appShape: lhs = ${lhs.shwDbg}, args = ${args.showDbg}, res = ${res.showDbg}")
      new AppShape(lhs, args, res)
    })
    lhs.unappliedParams match
    case Nil => ()
    case (ps, mss) :: pss =>
      if checked then zipArgsIn(mss, ps, args, res, lhs, instances)
      else
        // Protocol observations supply no arguments, so a rest parameter is empty.
        ps.variadic.foreach(v => constrainParameterIn(v.param,
          TupleShape(args, Nil)(this), mss, instances, N))
    log(dbg"appShape isSaturated? ${sh.isSaturated}; head? ${sh.applicationHead._1.shwDbg}, ${sh.applicationHead._2.map(_.showDbg)}")
    def register(using ResolutionContext) = publish(sh)
    log(dbg"lhs ${lhs.isSaturated} ${lhs.unappliedParams.map(_.mapFirst(_.showDbg).mapSecond(_.map(_.showDbg)))}")
    if lhs.isSaturated then
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
      if checked then
        // Conditional and recursive flow can lose the correlation that selects
        // a callable branch. In lenient mode a known callable target suffices,
        // just as a known member target does; never discard the other flows.
        val exposed = lhs.applicationHead._1 match
          case unknown: UnknownValueShape => unknown.fromPublicInterface
          case _ => false
        rctx.resolutionProblem(res, config.language.eagerResolution || exposed)(lhs.diagnostic(message))
      publish(UnknownValueShape.at(res))
      return
    if checked then res.callableTargets.currentShapes.add(source)
    if sh.isSaturated then
      def go(body: Term, mss: Ls[Marks])(using ResolutionContext) =
        listenResult(body): sh =>
          transportShape(sh, mss) match
          case NoShape =>
          case sh: TermShape =>
            publish(sh)
      sh.applicationHead match
      case (ds: DefnShape, mss) =>
        ds.defn match
        case cd: ClassDef =>
          // TODO: resolve ctor?
          // TODO: handle `mss`
          register
        case td: TermDefinition =>
          td.tsym match
          case ccs: ClassCtorSymbol => // TOOD: to avoid the special case, give this the actual body?
            softAssert(td.body.isEmpty)
            // TODO: handle `mss`
            register
          case _ =>
            log(dbg"appShape: td.body = ${td.body}")
            listenDefinitionResult(td, instances): result =>
              transportShape(result, mss) match
                case value: TermShape => publish(value)
                case NoShape => ()
        case _ =>
          softAssert(rctx.hasError(res))
      case (sh: IntroShape, mss) =>
        sh.trm match
        case Lam(params, body) =>
          // Exit the same context that zipArgs enters, filtering results from other uses.
          go(body, mss)
        case _ =>
          softAssert(rctx.hasError(res))
      case _ =>
        softAssert(rctx.hasError(res))
    else register
  
  private def publishActivated(host: ShapeHost, source: Shape)(using ResolutionContext): Unit =
    val shape = if rctx.instances.isEmpty then source else ActivatedShapeEvent(source, rctx.instances)
    if host.currentShapes.add(shape) then host.notifyShapeListeners(shape)

  /** `instances` interprets references in the value; rctx.instances identifies
    * the receiving body activation. Preserve both: a recursive argument may still
    * refer to the caller's binder instance when delivered into a callee activation.
    */
  private def publishViewed(host: ShapeHost, source: Shape,
      instances: TypeSubstitution)(using ResolutionContext): Unit =
    val shape = source match
      case value: TermShape => instantiateShape(value, instances)
      case symbol: SymShape if instances.nonEmpty =>
        val (original, substitution) = symbol match
          case contextual: ContextualSymShape => (contextual.source, instances.withOverrides(contextual.instances))
          case core: CoreSymShape => (core, instances)
        rctx.state.contextualSymbols.getOrElseUpdate((original, substitution), ContextualSymShape(original, substitution))
      case _ => source
    publishActivated(host, shape)

  private def publishMember(host: NewResolvable & ShapeHost, member: BlockMemberSymbol | RecordMember,
      flow: FlowSymbol, marks: Ls[Marks], instances: TypeSubstitution)(using ResolutionContext): Unit =
    def publish(shape: Shape)(using ResolutionContext): Unit = publishViewed(host, shape, instances)
    def definition(sym: BlockMemberSymbol)(using ResolutionContext): Unit =
      publish(symShapes.getOrElseUpdate((sym, flow, marks), CoreSymShape(sym, flow, marks)))
    member match
      case member: BlockMemberSymbol => definition(member)
      case RecordMember(field, false) => definition(field.sym)
      case RecordMember(field, true) =>
        // Assignments can replace the stored value, so its initializer no longer
        // determines what a read returns. Publish the known property symbol for
        // selection/assignment, but an unknown shape for the value being read.
        rctx.recordResolution(host, host.resolvedTargets.contains(field.tsym))(host.resolvedTargets ::= field.tsym)
        publish(UnknownValueShape.at(field.rhs))

  private def publishDeclared(host: NewResolvable & ShapeHost, member: BlockMemberSymbol, flow: FlowSymbol,
      bindings: Map[VarSymbol, DeclaredType], marks: Ls[Marks], annotation: Opt[Term], positive: Bool,
      instances: TypeSubstitution)(using ResolutionContext): Unit =
    // Keep one diagnostic witness per semantic candidate, as for unknown values.
    // A different annotation location must not create additional inference flow.
    val shape = declaredSymShapes.getOrElseUpdate((member, flow, marks, bindings, positive),
      DeclaredSymShape(member, flow, marks, bindings, annotation, positive))
    publishViewed(host, shape, instances)

  private def publishTyped(host: NewResolvable & ShapeHost, field: RcdField, tpe: DeclaredType,
      marks: Ls[Marks], instances: TypeSubstitution)(using ResolutionContext): Unit =
    rctx.recordResolution(host, host.resolvedTargets.contains(field.tsym))(host.resolvedTargets ::= field.tsym)
    // Project before transporting: transportType interns its wrapper by the whole
    // type, so an unobservable binding would otherwise yield a distinct candidate.
    publishActivated(host, instanceShape(transportType(instantiateType(tpe, instances), marks)))

  private def publishDynamic(host: NewResolvable & ShapeHost, marks: Ls[Marks])(using ResolutionContext): Unit =
    DynShape().exit(marks) match
      case shape: TermShape =>
        publishActivated(host, shape)
      case NoShape => ()

  private def unknownMember(host: NewResolvable, name: Str, reason: MemberLookup.Uncertainty,
      fromPublicInterface: Bool, provenance: ShapeProvenance)(using ResolutionContext): Unit =
    val message = reason match
      case MemberLookup.Uncertainty.ValueShape =>
        msg"Cannot resolve member '$name' of a value with unknown shape."
      case MemberLookup.Uncertainty.RecordOverwrite =>
        msg"Cannot resolve member '$name' across a computed key or unknown record spread."
    host match
      case sel: NewSel =>
        rctx.resolutionProblem(sel, config.language.eagerResolution || fromPublicInterface):
          provenance.diagnostic(message, N)
      case _ if !rctx.hasError(host) =>
        rctx.markError(host)
        resolError(host, provenance.diagnostic(message, N))
      case _ => ()

  /** Like for imports in Scala, wildcard opens do not provide the members that are inaccessible
    * from `scope`, where `ref` is written: another opened definition may provide an accessible member.
    */
  def unresolvedRef(ref: UnresolvedRef, scope: SrcScope)(using ResolutionContext): Unit =
    ref.prefixes.foreach: prefix =>
      listenReceiver(prefix): shape =>
        def member(info: MemberLookup, instances: TypeSubstitution)(using ResolutionContext): Unit = info match
          case MemberLookup.All(members) => members.foreach(member(_, instances))
          case MemberLookup.Contextual(source, substitution) => member(source, instances.withOverrides(substitution))
          case MemberLookup.Found(member, marks) if rctx.canResolve(ref) || ref.resolvedMembers.contains(prefix -> member.memberSymbol) =>
            val candidate = prefix -> member.memberSymbol
            rctx.recordResolution(ref, ref.resolvedMembers.contains(candidate))(ref.resolvedMembers ::= candidate)
            publishMember(ref, member, ref.resSym, marks, instances)
          case MemberLookup.Declared(member, bindings, marks, annotation, positive) if rctx.canResolve(ref) || ref.resolvedMembers.contains(prefix -> member) =>
            val candidate = prefix -> member
            rctx.recordResolution(ref, ref.resolvedMembers.contains(candidate))(ref.resolvedMembers ::= candidate)
            publishDeclared(ref, member, ref.resSym, bindings, marks, annotation, positive, instances)
          case MemberLookup.Typed(field, tpe, marks) if rctx.canResolve(ref) || ref.resolvedMembers.contains(prefix -> field.sym) =>
            val candidate = prefix -> field.sym
            rctx.recordResolution(ref, ref.resolvedMembers.contains(candidate))(ref.resolvedMembers ::= candidate)
            publishTyped(ref, field, tpe, marks, instances)
          case MemberLookup.Indexed(_, _) if rctx.canResolve(ref) =>
            resolError(ref, msg"Tuple elements must be selected by index." -> ref.toLoc :: Nil)
          case MemberLookup.Dynamic(marks) if rctx.canResolve(ref) || ref.dynamicPrefixes.contains(prefix) =>
            rctx.recordResolution(ref, ref.dynamicPrefixes.contains(prefix))(ref.dynamicPrefixes ::= prefix)
            publishDynamic(ref, marks)
          case MemberLookup.Missing =>
            // A known miss in one wildcard source is not an error: another may
            // provide the name. Lowering diagnoses references with no candidates.
            ()
          case MemberLookup.Unknown(reason, fromPublicInterface, provenance) =>
            unknownMember(ref, ref.id.name, reason, fromPublicInterface, provenance)

          case _ => () // Completed references only route their selected members.
        member(shape.getMember(ref.id.name).visibleFrom(scope.canAccessPrivatesOf, reportInaccessible = false),
          TypeSubstitution.empty)

  /** Inspect an overload set only once its definitions have all been published. */
  private def completedClass(shape: SymShape)(selected: ShapeListener[ClassDef], absent: () => ResolutionContext ?=> Unit)(using ResolutionContext): Unit =
    shape.sym.onComplete: () =>
      shape.sym.asCls match
        case S(cls) => selected(cls.defn.get)
        case N => absent()

  /** Class interpretations wait for completed overload sets, independently of term
    * companions. Aliases can supply constructor shapes; applied instances cannot.
    * Capture marks are retained for subsequent instance-member lookup. */
  private case class ClassReference(target: ClassValueTarget, marks: Ls[Marks],
      instances: TypeSubstitution, supplied: Opt[Ls[DeclaredType]]):
    def definition: ClassDef = ClassValueShape.definitionOf(target)

  // Declaration references choose their class overload. Stored values instead
  // retain their runtime representation, whether a class or its constructor.
  private def listenClass(trm: Term, recordTargets: Bool)(selected: ShapeListener[ClassReference], reject: ShapeListener[TermShape])(using ResolutionContext): Unit =
    def select(ref: ClassReference)(using ResolutionContext): Unit =
      if recordTargets then recordValueTarget(trm.classHead, ref.definition.sym)
      selected(ref)
    def value(sh: TermShape)(using ResolutionContext): Unit =
      val ShapeParts(source, instances, supplied) = shapeParts(sh)
      val marks = source.applicationHead._2
      source match
        case Marked(ds: DefnShape, _) => ds.clsDef match
          case S(cls: ClassDef) =>
            val target: ClassValueTarget = ds.defn match
              case td: TermDefinition => td.tsym match
                case ctor: ClassCtorSymbol => ctor
                case _ => lastWords("Class shape without a class or constructor definition")
              case _: ClassDef => cls.sym
              case _ => lastWords("Class shape without a class or constructor definition")
            selected(ClassReference(target, marks, instances, supplied))
          case _ => reject(sh)
        case _ => reject(sh)
    trm match
      // Local variables store the term interpretation of their initializer, even
      // when their flow still contains its unconverted overload-set shape.
      case _: SimpleRef => listenTerm(trm)(value)
      case application @ TyApp(base, args) => listenClass(base, recordTargets)(ref =>
        val count = if ref.supplied.nonEmpty then 0 else ref.definition.tparams.length
        if count != args.length && rctx.state.typeArgumentArityErrors.add((new Identity(application), count)) then
          resolError(trm, msg"Class '${ref.definition.sym.nme}' expected ${count} type ${
            "argument".pluralized(count)}, but got ${args.length}" -> ref.definition.headerLoc :: Nil)
        val supplied = args.map(arg => declaredType(typeResolution(arg), Map.empty).instantiate(rctx.instances))
        if ref.supplied.nonEmpty then selected(ref)
        else
          val instances = instantiateParameters(ref.definition.sym, ref.definition.tparams.map(_.sym),
            rctx.typeApplicationSite(application), lexicalBinders(application), ref.marks,
            rctx.instances.withOverrides(ref.instances), S(supplied))
          selected(ref.copy(instances = instances, supplied = S(supplied)))
      , reject)
      case Capture(base, thru) =>
        listenClass(base, recordTargets)(ref => selected(ref.copy(marks =
          ref.marks ::: EntryMark(ResolutionBoundary(thru), N, NoMarks) :: Nil)), reject)
      case _ => listen(trm, discardMarks = false):
        case sh: SymShape =>
          completedClass(sh)(cls => select(ClassReference(cls.sym,
            ExitMark(ResolutionBoundary(cls.sym), S(sh.resSym), NoMarks) :: sh.markss,
            sh match
              case contextual: ContextualSymShape => contextual.instances
              case _ => TypeSubstitution.empty
            , N)),
            () => fromSymbol(sh, value, trm, sym => if recordTargets then recordValueTarget(trm, sym), false))
        case sh: TermShape => value(sh)

  /** Locate a projected declaration in the actual receiver's class ancestry.
    * Each parent shape carries the crossing from its class into the child, so
    * keep those crossings before adding the receiver's outer captures.
    */
  private def projectedMember(receiver: TermShape, cls: ClassDef, name: Str)(using ResolutionContext): Opt[MemberLookup] =
    val ShapeParts(source, instances, _) = shapeParts(receiver)
    val (head, marks) = source.applicationHead
    val member = head match
      case definition: DefnShape =>
        if definition.clsDef.contains(cls) then S(definition.getInstanceMember(name))
        else definition.ext.flatMap(projectedMember(_, cls, name))
      case base: BaseShape =>
        if base.defn is cls then S(base.getMember(name))
        else base.ext.flatMap(projectedMember(_, cls, name))
      case _ => N
    member.map(_.withMarks(marks).instantiate(instances))

  /** Class selections own their resolved class targets, including for aliases.
    * Projection qualifiers use this same representation without evaluating it.
    * The caller decides whether non-class values permit ordinary field selection.
    */
  private def classSelection(sel: NewSel)(selected: ShapeListener[ClassReference], reject: ShapeListener[TermShape])(using ResolutionContext): Unit =
    listenClass(sel.prefix, recordTargets = true)(ref =>
      val cls = ref.definition.sym
      rctx.recordResolution(sel, sel.resolvedTargets.contains(cls))(sel.resolvedTargets ::= cls)
      selected(ref)
    , reject)

  /** Super references expose every inherited candidate to inference, but never dispatch
    * through the overriding member. The parent shape retains generic arguments and scope marks.
    */
  def resolveSuper(sup: Super)(using ResolutionContext): Unit =
    def receive(info: MemberLookup, instances: TypeSubstitution)(using ResolutionContext): Unit = info match
      case MemberLookup.All(members) => members.foreach(receive(_, instances))
      case MemberLookup.Contextual(source, substitution) => receive(source, instances.withOverrides(substitution))
      case MemberLookup.Found(member, marks) => publishMember(sup, member, sup.resSym, marks, instances)
      case MemberLookup.Declared(member, bindings, marks, annotation, positive) =>
        publishDeclared(sup, member, sup.resSym, bindings, marks, annotation, positive, instances)
      case _ =>
        rctx.markError(sup)
        resolError(sup, msg"No inherited member '${sup.id.name}' is available through 'super'" -> sup.toLoc :: Nil)
    def completed(defn: ClassLikeDef)(using ResolutionContext): Unit =
      listenInheritedMember(defn, sup.id.name): info =>
        def captures(term: Term): Ls[Marks] = term match
          case Capture(base, thru) => EntryMark(ResolutionBoundary(thru), N, NoMarks) :: captures(base)
          case _ => Nil
        // Like in JavaScript, private members are not available through `super`, even where they are accessible:
        // `super` looks up the members inherited by the parent class (see also Lowering.superReference).
        receive(info.withMarks(captures(sup.receiver)).visibleFrom(_ => false, reportInaccessible = false),
          TypeSubstitution.empty)
    sup.owner.asDefnSym.defn match
      case S(defn) => completed(defn)
      case N => sup.owner.asDefnSym.defnListeners += completed

  /** `scope` is where `sel` is written, which determines the private members it can select. */
  def newSel(sel: NewSel, scope: SrcScope)(using ResolutionContext): Unit =
    log(dbg"newSel? sel = ${sel.showDbg}")
    def visible(info: MemberLookup): MemberLookup = info.visibleFrom(scope.canAccessPrivatesOf, reportInaccessible = true)
    def member(info: MemberLookup, description: Message, diagnostic: Message => Ls[(Message, Opt[Loc])],
        instances: TypeSubstitution)(using ResolutionContext): Unit = info match
      case MemberLookup.All(members) => members.foreach(member(_, description, diagnostic, instances))
      case MemberLookup.Contextual(source, substitution) => member(source, description, diagnostic, instances.withOverrides(substitution))
      case MemberLookup.Found(bms, marks) if rctx.canResolve(sel) || sel.resolvedMembers.contains(bms.memberSymbol) =>
        log(dbg"newSel member: bms = ${bms.memberSymbol.showDbg}, mss = ${marks.map(_.showDbg)}")
        rctx.recordResolution(sel, sel.resolvedMembers.contains(bms.memberSymbol))(sel.resolvedMembers ::= bms.memberSymbol)
        publishMember(sel, bms, sel.resSym, marks, instances)
      case MemberLookup.Declared(member, bindings, marks, annotation, positive) if rctx.canResolve(sel) || sel.resolvedMembers.contains(member) =>
        rctx.recordResolution(sel, sel.resolvedMembers.contains(member))(sel.resolvedMembers ::= member)
        publishDeclared(sel, member, sel.resSym, bindings, marks, annotation, positive, instances)
      case MemberLookup.Typed(field, tpe, marks) if rctx.canResolve(sel) || sel.resolvedMembers.contains(field.sym) =>
        rctx.recordResolution(sel, sel.resolvedMembers.contains(field.sym))(sel.resolvedMembers ::= field.sym)
        publishTyped(sel, field, tpe, marks, instances)
      case MemberLookup.Indexed(fields, marks) if rctx.canResolve(sel) || sel.tupleIndex == sel.id.name.toIntOption =>
        val index = sel.id.name.toIntOption
        softAssert(index.exists(_ >= 0), "Tuple lookup must identify a nonnegative index")
        rctx.recordResolution(sel, sel.tupleIndex == index)(sel.tupleIndex = index)
        fields.foreach: field =>
          listenTupleField(field): shape =>
            transportShape(shape, marks) match
              case value: TermShape =>
                publishViewed(sel, value, instances)
              case NoShape => ()
      case MemberLookup.Dynamic(marks) if rctx.canResolve(sel) || sel.hasDynamicTarget =>
        rctx.recordResolution(sel, sel.hasDynamicTarget)(sel.hasDynamicTarget = true)
        publishDynamic(sel, marks)
      case MemberLookup.Missing if rctx.canResolve(sel) =>
        rctx.resolutionProblem(sel, config.language.eagerResolution):
          diagnostic(msg"$description does not contain member '${sel.id.name}'")
      case MemberLookup.Unknown(reason, fromPublicInterface, provenance) =>
        unknownMember(sel, sel.id.name, reason, fromPublicInterface, provenance)
      // Later activations still transport field values through the compiled
      // selection, but cannot choose a different member for that old syntax.
      case _ => ()
    sel.cls match
      case N if sel.id.name == "class" =>
        classSelection(sel)(ref =>
          listenExt(ref.definition, ext =>
            val shape = ClassValueShape(ref.target, ext)
            assert(rctx.canResolve(sel) || ClassValueShape.targetsOf(sel).contains(ref.target),
              "Inference changed a completed class-value interpretation")
            val specialized = ref.supplied.fold[TermShape](shape)(args => SpecializedShape(shape, args, ref.instances))
            transportShape(specialized, ref.marks) match
              case value: TermShape => publishViewed(sel, value, ref.instances)
              case NoShape => ())
        , shape =>
          member(visible(shape.getMember(sel.id.name)), msg"${shape.describe.capitalize}", shape.diagnostic, TypeSubstitution.empty))
      case N => listenReceiver(sel.prefix): shape =>
        log(dbg"newSel: sel = ${sel.showDbg}, shape = ${shape.shwDbg}")
        member(visible(shape.getMember(sel.id.name)), msg"${shape.describe.capitalize}", shape.diagnostic, TypeSubstitution.empty)
      case S(cls) =>
        classSelection(cls)(ref =>
          val cd = ref.definition
          listenExt(cd, ext =>
            val info = visible(DefnShape(cd, ext).getInstanceMember(sel.id.name))
            info match
              case MemberLookup.Found(bms: BlockMemberSymbol, declarationMarks) =>
                // Resolve the projection target even in an unused function. Wait
                // for the receiver before deciding whether its result may expose
                // implementation flow or only the declared member signature.
                rctx.recordResolution(sel, sel.resolvedMembers.contains(bms))(sel.resolvedMembers ::= bms)
                bms.onComplete: () =>
                  bms.asModOrObj.orElse(bms.asTrm).orElse(bms.asCls).foreach: sym =>
                    rctx.recordResolution(sel, sel.resolvedTargets.contains(sym))(sel.resolvedTargets ::= sym)
                listenTermViews(sel.prefix): receiver =>
                  val selected = receiver match
                    case Marked(nominal: NominalInstanceView, context) =>
                      nominal.ancestor(cd) match
                        case S(view) => visible(view.getMember(sel.id.name)).withAnnotation(nominal.annotation).withMarks(context :: Nil)
                        case N =>
                          // An explicit projection can name a narrower class, but
                          // it cannot recover that class's implementation arguments.
                          val opaque = abstractType(new TypeResolution(sel, msgs => resolError(sel, msgs)))
                          MemberLookup.Declared(bms, cd.tparams.map(_.sym -> opaque).toMap, context :: Nil, nominal.annotation, true)
                    case _ =>
                      // C# selects a declaration, not an instance of C. Transport
                      // the member through the actual receiver, never the qualifier.
                      projectedMember(receiver, cd, sel.id.name).map(visible).getOrElse:
                        // Without a path into this class, only its declared
                        // interface is available; qualifier values add no evidence.
                        val opaque = abstractType(new TypeResolution(sel, msgs => resolError(sel, msgs)))
                        MemberLookup.Declared(bms, cd.tparams.map(_.sym -> opaque).toMap,
                          declarationMarks ::: ExitMark(ResolutionBoundary(cd.sym), N, NoMarks) :: Nil, N, true)
                  member(selected, msg"Class '${cd.sym.nme}'", message => (message -> cd.headerLoc) :: Nil, TypeSubstitution.empty)
              case _ => member(info, msg"Class '${cd.sym.nme}'", message => (message -> cd.headerLoc) :: Nil, TypeSubstitution.empty))
        , sh =>
          rctx.markError(sel)
          resolError(sel, sh.diagnostic(msg"${sh.describe.capitalize} cannot be used as a projection class."))
        )
  
  /** Both constructor references and explicit `new` use the same definition and
    * parameter lists, including auxiliary constructor(...) lists. A partial `new`
    * therefore retains the same callable head and contexts as a partial C(...).
    */
  private def constructorShape(cls: ClassDef, ext: Opt[TermShape])(using ResolutionContext): DefnShape =
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
      case S(base: BaseShape) => softAssert((base.defn is cls) && base.ext.map(ShapeIdentity.key) == ext.map(ShapeIdentity.key))
      case _ => softAssert(false, "Constructor shape is missing its class base")
    else softAssert(shape.ext.map(ShapeIdentity.key) == ext.map(ShapeIdentity.key))
    shape
  
  def resolveNew(nw: Term.New)(using ResolutionContext): Unit = nw.cls.classHead match
    case Term.Error() => rctx.markError(nw)
    // Class references resolve symbolically; variables must carry a class value.
    // Other expression forms require dynamic construction, even if they publish
    // no shapes (for example an unsupported reference in an extends clause).
    case _: NewResolvable | _: SimpleRef => resolveNewClass(nw)
    case _ =>
      rctx.markError(nw)
      resolError(nw, msg"Invalid class expression: ${nw.cls.describe}" -> nw.cls.toLoc :: Nil)
  
  private def resolveNewClass(nw: Term.New)(using ResolutionContext): Unit =
    // listenClass preserves captures and supplies the same class-body exit as a
    // constructor value. In particular, a captured constructor already carries
    // that exit; adding a second one here would duplicate its instance boundary.
    listenClass(nw.cls, recordTargets = true)(ref =>
      val cd = nw.rft.flatMap(_._1.defn).getOrElse(ref.definition)
      // Constructor arity is compiled from these shapes even when the runtime
      // operand is a variable with no resolved class symbol of its own.
      assert(rctx.canResolve(nw) || ClassValueShape.targetsOf(nw).contains(ref.target),
        "Inference changed a completed constructor target")
      val marks = nw.rft.fold(ref.marks): (symbol, _) =>
        ExitMark(ResolutionBoundary(symbol), S(nw.resSym), NoMarks) :: Nil
      val callerInstances = rctx.instances
      listenExt(cd, extsh =>
        val dsh = constructorShape(cd, extsh)
        val captured = callerInstances.withOverrides(ref.instances)
        // Explicit type arguments already consumed this scheme. Otherwise an
        // unapplied constructor waits for its first term application.
        val instances = if ref.supplied.nonEmpty || (nw.args.isEmpty && dsh.unappliedParams.nonEmpty) then captured
          else instantiateDefinition(dsh, nw.resSym, lexicalBinders(nw), marks, captured, N)
        val sh = newShapes.getOrElseUpdate((ref.target, marks, nw.resSym, ref.supplied),
          NewShape(dsh, ref.target, marks, nw.args, nw, ref.supplied))
        if rctx.state.constructorApplications.add((sh, instances)) then
          // A class without parameter lists still accepts one empty argument tuple.
          // Zipping alone would silently ignore that tuple, and any lists supplied
          // after a constructor is saturated. Anonymous refinements forward these
          // arguments through their synthetic parent New, which checks them there.
          if nw.rft.isEmpty then
            val paramCount = dsh.unappliedParams.length
            val maxLists = paramCount.max(1)
            if nw.args.length > maxLists then
              resolError(nw, dsh.arityDiagnostic(
                msg"Class '${cd.sym.nme}' expected at most ${maxLists} ${"argument list".pluralized(maxLists)}, but got ${nw.args.length}"))
            if paramCount == 0 then
              nw.args.headOption.foreach: args =>
                checkArgumentArity(args, Arity(0, 0, false, 0), nw, dsh)(_ => ())
          dsh.unappliedParams.lazyZip(nw.args).foreach:
            case ((ps, _), args) => zipArgsIn(marks, ps, args, nw, dsh, instances)
        publishViewed(nw, sh, instances)(using rctx.withInstances(callerInstances))
      )
    , shape =>
      if !rctx.hasError(nw) then
        rctx.markError(nw)
        resolError(nw, shape.diagnostic(msg"${shape.describe.capitalize} cannot be instantiated with keyword 'new'."))
    )
  
  /** Assignments return to the binding's lexical scope before contributing
    * candidates. Reads must see every assigned shape, including assignments
    * inside nested functions, without recording the RHS's symbol as their target.
    */
  private[semantics] def assignVariable(lhs: Term, rhs: Term)(using ResolutionContext): Unit =
    def assign(target: Term, shape: TermShape)(using ResolutionContext): Unit = target match
      case Capture(base, thru) =>
        MarkedShape.exit(shape, ResolutionBoundary(thru), N) match
          case value: TermShape => assign(base, value)
          case NoShape => ()
      case MemberRef(sym: TermSymbol) if sym.k is LetBind =>
        publishActivated(rctx.memberVariable(sym), shape)
      case SimpleRef(sym: LocalSymbol) => publishActivated(sym, shape)
      case Ref(sym: LocalSymbol) => publishActivated(sym, shape)
      case _ => ()
    listenTerm(rhs)(assign(lhs, _))

  def defineVar(sym: LocalSymbol | TermSymbol, rhs: Term)(loc: Opt[Loc])(using ResolutionContext): DefineVar =
    if newResolution then sym match
      case sym: TermSymbol =>
        listenTerm(rhs): sh =>
          publishActivated(rctx.memberVariable(sym), sh)
      case sym: LocalSymbol =>
        listen(rhs, discardMarks = false): sh =>
          publishActivated(sym, sh)
    DefineVar(sym, rhs)(loc)
  
  /** Close recursive getter dependencies before following the body. A cycle with
    * no normal result publishes nothing; a productive branch can still publish
    * later and propagate around the cycle until duplicate candidates stop it.
    * Results stay at the body's lexical endpoint: each reference applies its own
    * exit/capture marks after subscribing. Activation events retain substitutions
    * when a deferred body candidate arrives through an enclosing generic call.
    */
  private def listenByNameBody(td: TermDefinition, body: Term)(listener: Listener)(using ResolutionContext): Unit =
    assert(td.params.isEmpty)
    val key = (td.tsym, rctx.instances)
    rctx.state.byNameResults.get(key) match
      case S(host) => listenValueHost(host)(listener)
      case N =>
        val host = new Host[ShapeEvent]:
          def showDbg(using DebugPrinter): Str = s"result of ${td.tsym.nme}"
        rctx.state.byNameResults(key) = host
        listenValueHost(host)(listener)
        td.asyncAnnotation match
          case S(_) => listenDefinitionResult(td, rctx.instances)(publishActivated(host, _))
          case N => listenResult(body)(publishActivated(host, _))

  def pipeTerm(from: Term, to: ShapeHost)(using ResolutionContext): Unit =
    log(dbg"pipeTerm: from = ${from.showDbg}, to = ${to.showDbg}; ${to.currentShapes}")
    listenTerm(from): sh =>
      publishActivated(to, sh)
  
  /** The synthetic handler is an instance with real method definitions. Publish
    * it after building those definitions, so forward selections made while
    * elaborating the handled body resolve through ordinary member lookup. */
  def resolveAbortiveHandler(handle: Handle)(using ResolutionContext): Unit =
    assert(handle.isAbortive)
    val definition = handle.derivedClsSym.defn.get
    listenExt(definition, parent =>
      val receiver = selfShapes.getOrElseUpdate(handle.derivedClsSym, BaseShape(definition, parent))
      MarkedShape.exit(receiver, ResolutionBoundary(handle.derivedClsSym), N) match
        case value: TermShape => publishActivated(handle.lhs, value)
        case NoShape => lastWords("A new handler instance must be reachable outside its class"))

  // Classes without an explicit parent expose Object's declarations. Share this
  // root interface between inferred instances, nominal annotations, and this-values;
  // Object itself must terminate the chain. This does not add a runtime constructor call.
  private lazy val objectShape = NominalInstanceView(prelude.builtins.Object.defn.get, Map.empty, N)(N, ShapeProvenance.empty)(this)
  private def implicitParent(defn: ClassLikeDef): Opt[TermShape] =
    if defn.sym is prelude.builtins.Object then N else S(objectShape)

  /** Register declaration edges even for unused classes. Parent lookup waits for forward
    * definitions and follows inherited members using the same shapes as ordinary selection.
    */
  def registerInheritance(defn: ClassLikeDef)(using ResolutionContext): Unit =
    // Distinct source aliases cannot define the same JavaScript property twice.
    // Otherwise lookup could infer the first body while runtime keeps the last.
    defn.body.methods.filterNot(_.tsym.isPrivate).flatMap(td =>
      MemberKey.symbol(td).map(_ -> td)
    ).groupMap(_._1)(_._2).foreach:
      case (key, definitions) if definitions.map(_.tsym).distinct.sizeCompare(1) > 0 =>
        defn.isErroneous = true
        definitions.foreach(_.isErroneous = true)
        rctx.report:
          ErrorReport(msg"Duplicate definition of member '${key.name}'." -> N
          :: definitions.map: td =>
            msg"Member '${td.tsym.nme}' is defined here." -> td.toLoc)
      case _ => ()
    defn.body.members.valuesIterator.distinct.foreach: member =>
      member.asTrm.filterNot(sym => sym.isInstanceOf[ClassCtorSymbol] || sym.isPrivate).foreach: own =>
        // Bind this host to the defining unit before an importer can observe its edges.
        own.overrideLinks.inferenceHost
        MemberKey.symbol(member).foreach: key =>
          listenInheritedMember(defn, key): lookup =>
            def check(info: MemberLookup): Unit = info match
              case MemberLookup.All(members) => members.foreach(check)
              case MemberLookup.Contextual(source, _) => check(source)
              case MemberLookup.Found(base: BlockMemberSymbol, _) => collision(base)
              case MemberLookup.Declared(base, _, _, _, _) => collision(base)
              case _ => ()
            def collision(base: BlockMemberSymbol): Unit = if base.nme != member.nme then
              defn.isErroneous = true
              own.defn.foreach(_.isErroneous = true)
              rctx.report(ErrorReport(
                msg"Member '${member.nme}' uses the same @jsSymbol key as inherited member '${base.nme}'; overrides must keep the inherited name." -> own.toLoc ::
                msg"The inherited member is declared here." -> base.toLoc :: Nil))
            check(lookup.visibleFrom(_ => false, reportInaccessible = false))
        listenInheritedMember(defn, member.nme): lookup =>
          def record(info: MemberLookup): Unit = info match
            case MemberLookup.All(members) => members.foreach(record)
            case MemberLookup.Contextual(source, _) => record(source)
            case MemberLookup.Found(base: BlockMemberSymbol, _) => link(base)
            case MemberLookup.Declared(base, _, _, _, _) => link(base)
            case _ => ()
          def link(base: BlockMemberSymbol): Unit = base.onComplete: () =>
            base.asTrm.filterNot(_.isPrivate).foreach: target =>
              if target isnt own then
                if MemberKey.symbol(member) != MemberKey.symbol(base) then
                  // Source aliases must not silently redirect an override to a
                  // different runtime property. In particular, omitting jsSymbol
                  // on an override would leave the inherited protocol installed.
                  own.defn.foreach(_.isErroneous = true)
                  rctx.report(ErrorReport(
                    msg"Overriding member '${member.nme}' must use the same @jsSymbol annotation as its parent." -> own.toLoc ::
                    msg"The inherited member is declared here." -> target.toLoc :: Nil))
                own.overrideLinks.inferenceHost.publish(target)
          // Private members are not overridden, so they do not hide the inherited members they shadow.
          record(lookup.visibleFrom(_ => false, reportInaccessible = false))

  private def listenInheritedMember(defn: ClassLikeDef, name: MemberKey)
      (listener: ShapeListener[MemberLookup])(using ResolutionContext): Unit =
    // Legacy preludes may have no Object declaration or even an enclosing prelude context.
    // Their root classes have no implicit nominal parent in the legacy resolver.
    if !newResolution && defn.ext.isEmpty then listener(MemberLookup.Missing)
    else listenExt(defn, parent => listener(parent.fold[MemberLookup](MemberLookup.Missing)(_.getMember(name))))

  def listenExt(defn: ClassLikeDef, listener: ShapeListener[Opt[TermShape]])(using ResolutionContext): Unit =
    defn.ext match
    case S(trm) =>
      listenTerm(trm): sh =>
        listener(S(sh))
    case N =>
      listener(implicitParent(defn))
  
  /** Constructed receivers and nominal annotations share the same symbolic
    * parameter endpoints. Explicit arguments still receive input obligations;
    * observing only their output candidates would discard callback constraints.
    */
  private def instanceBindings(td: TermDefinition)(using ResolutionContext): Map[VarSymbol, DeclaredType] =
    td.tsym.owner.toList.flatMap(_.asDefnSym.defn.toList).flatMap(_.tparams).map: param =>
      val symbol = rctx.instances.getOrElse(param.sym, param.sym)
      param.sym -> parameterType(TypeShape.Parameter(symbol, symbol.inferenceHost))
    .toMap

  private def fromSymbol(shape: SymShape, listener: Listener, source: Term,
      selected: ShapeListener[DefinitionSymbol[?]], receiver: Bool)(using ResolutionContext): Unit =
    fromSymbolAt(shape, listener, source, selected, receiver, N)

  private def fromSymbolAt(shape: SymShape, listener: Listener, source: Term,
      selected: ShapeListener[DefinitionSymbol[?]], receiver: Bool,
      specialization: Opt[(FlowSymbol, Ls[DeclaredType])])(using ResolutionContext): Unit = shape match
    case contextual: ContextualSymShape =>
      fromSymbolAt(contextual.source, value => listener(instantiateShape(value, contextual.instances)),
        source, selected, receiver, specialization)(using rctx.withInstances(contextual.instances))
    case declared: DeclaredSymShape =>
      listenDeclaredMember(shape.sym, declared.bindings, shape.resSym, source, declared.annotation, selected, receiver, declared.positive, shape.markss, specialization): value =>
        transportShape(value, shape.markss) match
          case value: TermShape => listener(value)
          case NoShape => ()
    case _ => fromBMSAt(shape.sym, shape.resSym, shape.markss, listener, source, selected, receiver, specialization)

  def fromBMS(bms: BlockMemberSymbol, resSym: FlowSymbol, markss: Ls[Marks], listener: Listener,
      trm: Term, selected: ShapeListener[DefinitionSymbol[?]], receiver: Bool)(using ResolutionContext): Unit =
    fromBMSAt(bms, resSym, markss, listener, trm, selected, receiver, N)

  // External declarations with no written parameter lists derive their calling
  // convention from the signature. An ordinary parameterless function executes
  // at its reference, before any returned callable receives term arguments.
  private def isByName(td: TermDefinition): Bool =
    (td.k is syntax.Fun) && td.params.isEmpty && Annot.declareModifierOf(td.annotations).isEmpty

  /** A separate signature quantifies the definition. A quantified result
    * annotation instead belongs to the returned value and remains unconsumed.
    */
  private def definitionBinders(td: TermDefinition): Ls[VarSymbol] =
    td.tparams.toList.flatten.map(_.sym) ::: definitionQuantifiers(td).map(_.sym)

  private def definitionQuantifiers(td: TermDefinition): Ls[QuantVar] =
    def signatureQuantifiers(sign: Term): Ls[QuantVar] = sign match
      case Forall(parameters, _, body) => parameters ::: signatureQuantifiers(body)
      case _ => Nil
    if td.flags.hasResultAnnotation then Nil else td.sign.toList.flatMap(signatureQuantifiers)

  /** Instantiate a by-name definition at `site`: the reference, selection,
    * constructor pattern, or structural projection invoking it, unless an
    * explicit specialization supplies its own site. A symbol shape reaches its
    * listeners with the site of the selection that produced it, possibly far
    * from the term being observed (for `let m = MutMap.empty`, a later use of
    * `m`), so the instances' scope is the site's, which every such site records
    * (see NewResolverState.siteBinders).
    */
  private def instantiateByName(td: TermDefinition, site: FlowSymbol, marks: Ls[Marks],
      specialization: Opt[(FlowSymbol, Ls[DeclaredType])], bindings: Map[VarSymbol, DeclaredType])
      (using ResolutionContext): TypeSubstitution =
    val instantiationSite = specialization.fold(site)(_._1)
    val binders = definitionBinders(td)
    val siteBinders = rctx.siteBindersOf(instantiationSite)
    // An unknown scope retains every binding when the instances are read.
    softAssert(siteBinders.nonEmpty || binders.isEmpty,
      s"The site instantiating '${td.tsym.nme}' must record its enclosing type binders")
    val instances = instantiateParameters(td.tsym, binders, instantiationSite,
      siteBinders, marks, rctx.instances, specialization.map(_._2))
    val parameters = definitionQuantifiers(td).map: parameter =>
      DeclaredTypeParameter(TypeShape.Parameter(parameter.sym, parameter.sym.inferenceHost),
        parameter.lb.map(bound => declaredType(typeResolution(bound), bindings)),
        parameter.ub.map(bound => declaredType(typeResolution(bound), bindings)))
    constrainQuantifiedBounds(parameters, instances)
    instances

  private def fromBMSAt(bms: BlockMemberSymbol, resSym: FlowSymbol, markss: Ls[Marks], listener: Listener,
      trm: Term, selected: ShapeListener[DefinitionSymbol[?]], receiver: Bool,
      specialization: Opt[(FlowSymbol, Ls[DeclaredType])])(using ResolutionContext): Unit =
    log(dbg"listenBMS: bms = ${bms.describe}")
    bms.onComplete: () =>
      log(dbg"listenedBMS: bms = ${bms.describe}")
      valueTarget(bms, receiver) match
      case S(sym: (ModuleOrObjectSymbol | TermSymbol | ClassSymbol | PatternSymbol)) =>
        // Selection is independent of the selected value's shape. In particular,
        // an assignment needs its target even if the value has no inferred shape.
        // Pattern resolution supplies its own interpretation of the selected head.
        selected(sym)
        val wrappedListener: Listener = sh =>
          log(dbg"fromBMS: bms = ${bms.showDbg}, sh = ${sh.shwDbg}, flow = ${resSym.showDbg}, markss = ${markss.map(_.showDbg)}")
          val sh0 = sh
          // Modules, objects, and runtime pattern objects introduce no value
          // boundary. Pattern bodies have separate matching scopes; passing the
          // generated matcher object does not enter or leave those scopes.
          val exited = sym match
            case _: ModuleOrObjectSymbol | _: PatternSymbol => sh
            case sym: TermSymbol if sym.k is LetBind => sh
            case _ => MarkedShape.exit(sh, ResolutionBoundary(sym), S(resSym))
          (exited match
            case value: TermShape => transportShape(value, markss)
            case NoShape => NoShape) match
            case NoShape =>
              log(dbg"FILTER OUT ${sh.shwDbg} for ${sym.showDbg} % ${resSym.showDbg}")
            case sh: TermShape =>
              if sh0.isInstanceOf[MarkedShape[?]]
              then log(dbg"MATCH ${sh.shwDbg} for ${sym.showDbg} % ${resSym.showDbg}")
              else log(dbg"PUSH ${sh.shwDbg}")
              listener(sh)
        sym.defn match
        case S(td: TermDefinition) if td.params.isEmpty =>
          log(dbg"listenTerm: td.body = ${td.body.fold("N")(_.showDbg)}")
          val callerInstances = rctx.instances
          val instances = if isByName(td) then instantiateByName(td, resSym,
            ExitMark(ResolutionBoundary(td.tsym), S(resSym), NoMarks) :: markss, specialization, Map.empty)
            else callerInstances.without(td.tparams.toList.flatten.map(_.sym))
          def receive(shape: TermShape)(using ResolutionContext): Unit =
            wrappedListener(instantiateShape(shape, instances))(using rctx.withInstances(callerInstances))
          if td.asyncAnnotation.nonEmpty then listenDefinitionResult(td, instances)(receive)
          else resultSignature(td) match
            case S(sign) =>
              val result = declaredType(typeResolution(sign), Map.empty).instantiate(instances)
              val tpe = if isByName(td) then result else quantifiedType(result, td.tparams.toList.flatten.map(_.sym))
              listenTypeInstances(tpe): shape =>
                td.tsym.decl match
                  case S(_: Param) => receive(MarkedShape.enter(shape, ResolutionBoundary(td.tsym), N))
                  case _ => receive(shape)
            case N => td.body.foreach: body =>
              listenByNameBody(td, body)(shape =>
                // Legacy synthesized fields use a plain reference to their
                // constructor parameter. Supply the field capture explicitly;
                // new-resolution fields already carry it in their body syntax.
                val captured = (td.tsym.decl, body) match
                  case (S(_: Param), Ref(_: VarSymbol)) =>
                    MarkedShape.enter(shape, ResolutionBoundary(td.tsym), N)
                  case _ => shape
                receive(captured)
              )(using rctx.withInstances(instances))
        case S(d: TermDefinition) if !d.tsym.isInstanceOf[ClassCtorSymbol] &&
            ((d.sign.nonEmpty && (!d.flags.hasResultAnnotation || d.params.forall(ps =>
              ps.allParams.forall(_.sign.nonEmpty)))) ||
              (d.body.isEmpty && d.tsym.owner.exists(_.asDefnSym.defn.exists(_.tparams.nonEmpty)))) =>
          listenDeclaredMember(bms, instanceBindings(d), resSym, trm, N, selected, receiver, true, markss, specialization): value =>
            transportShape(value, markss) match
              case value: TermShape => listener(value)
              case NoShape => ()
        case S(d: TermDefinition) =>
          d.tsym match
          case ccs: ClassCtorSymbol =>
            val cls = ccs.associatedCls.defn.get
            listenExt(cls, extsh => wrappedListener(constructorShape(cls, extsh)))
          case _ =>
            wrappedListener(defnShapes.getOrElseUpdate(sym, DefnShape(d, N)))
        case S(d: ClassLikeDef) =>
          listenExt(d, extsh =>
            // defnShapes.get(sym).foreach: existing =>
            //   ??? // TODO error?
            wrappedListener(defnShapes.getOrElseUpdate(sym, DefnShape(d, extsh)))
          )
        case N if sym.asTrm.exists(_.k is LetBind) =>
          listenMemberVariable(sym.asTrm.get)(wrappedListener)
        case N =>
          softAssert(false, s"Symbol definition of ${sym} is not set upon completion of ${bms}")
      case _ =>
        def reportError(using ResolutionContext) = resolError(trm,
          msg"Expected a term; got ${bms.describe} '${bms.nme}'" -> N :: Nil)
        trm.withoutCaptures match
          case ref: NewResolvable =>
            if !rctx.hasError(ref) then
              rctx.markError(ref)
              reportError
          case _ => reportError
  
  /** Request the term interpretation of a reference without requiring a consumer
    * of its value shape. Direct definition references already identify the target;
    * overload sets need listeners, including when their definitions arrive later.
    */
  def requireTerm(trm: Term)(using ResolutionContext): Unit = trm.withoutCaptures match
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
  private def staticAnnotationSymbol(trm: Term): Opt[Symbol] = trm.withoutCaptures match
    case ref: NewRefImpl => S(ref.sym)
    case Ref(sym) => S(sym)
    case sel: NewSel => staticAnnotationSymbol(sel.prefix).flatMap(_.asMod).flatMap(_.tree.definedSymbols.get(sel.id.name))
    case sel: Sel => staticAnnotationSymbol(sel.prefix).flatMap(_.asMod).flatMap(_.tree.definedSymbols.get(sel.nme.name))
    case _ => N

  /** Only member identity is needed to interpret an annotation. In particular a
    * declared module has no runtime initializer to infer, and its syntax already
    * identifies its members before their definitions are elaborated. Ordinary
    * resolution still checks access and records targets for those selections.
    */
  def annotationSymbol(trm: Term)(using ResolutionContext): Opt[Symbol] = trm match
    case Capture(base, _) => annotationSymbol(base)
    case TyApp(base, _) => annotationSymbol(base)
    case App(base, _) => annotationSymbol(base)
    case ref: NewRefImpl => S(ref.sym)
    case _ if staticAnnotationSymbol(trm).nonEmpty =>
      requireTerm(trm)
      staticAnnotationSymbol(trm)
    case _: NewSel | _: UnresolvedRef =>
      val symbols = mutable.LinkedHashSet.empty[BlockMemberSymbol]
      var collecting = true
      var failed = false
      def fail()(using ResolutionContext): Unit = if !failed then
        failed = true
        resolError(trm, msg"An annotation's main symbol must be uniquely known when the annotation is elaborated." -> N :: Nil)
      // This listener validates an elaboration decision; it transports no values.
      // Keep checking late candidates in the defining block, but never mutate its
      // local bookkeeping when a completed block's listeners run in a consumer.
      listen(trm, discardMarks = false): shape =>
        if rctx.canResolve(trm) then shape match
          case sh: SymShape =>
            if symbols.add(sh.sym) && !collecting then fail()
          case _ => fail()
      collecting = false
      symbols.toList match
        case symbol :: Nil if !failed => S(symbol)
        case _ => fail(); N
    // Imported legacy annotations may still use Ref for builtin markers.
    case Ref(sym: BuiltinSymbol) => S(sym)
    case _ =>
      resolError(trm, msg"An annotation must have a known main symbol." -> N :: Nil)
      N

  /** Resolve the identity of a computed key, without checking its value's type.
    * `fresh` is a user contract: distinct marked vals denote distinct keys.
    * Modules and immutable vals make the path stable; calls and mutable bindings
    * cannot be used to identify a property at compile time. A forward val's marker
    * is checked when its definition completes, not by forcing its initializer.
    */
  def symbolKey(term: Term, required: Bool)(using ResolutionContext): Opt[SymbolKey] =
    def member(t: Term): Opt[Symbol] = staticAnnotationSymbol(t).orElse:
      if required then annotationSymbol(t)
      else
        val members = mutable.LinkedHashSet.empty[BlockMemberSymbol]
        listen(t, discardMarks = false):
          case sh: SymShape => members += sh.sym
          case _ => ()
        members.toList match
          case sym :: Nil => S(sym)
          case _ => N
    def stable(sym: Symbol): Bool = sym.asMod.nonEmpty || (sym match
      case bms: BlockMemberSymbol => bms.trmTree.exists(_.k is ImmutVal) || bms.asTrm.exists(_.k is ImmutVal)
      case tsym: TermSymbol => tsym.k is ImmutVal
      case _ => false)
    def canonicalPath(path: Ls[Symbol], seen: Set[Symbol]): Ls[Symbol] =
      path.foldLeft(Ls.empty[Symbol]): (prefix, sym) =>
        sym.asMod match
          case S(module) => prefix :+ module
          case N =>
            val base = sym.asTrm.flatMap(_.defn).map(_.sym).getOrElse(sym)
            val alias = if seen(base) then N else base.asTrm.flatMap(_.defn).flatMap(_.body).flatMap(stablePath)
            alias match
              // An immutable alias replaces the whole receiver path, not just
              // its last name: M.alias may refer to a val outside M. Only follow
              // stable references; calls and other initializers remain opaque.
              case S(target) => canonicalPath(target, seen + base)
              case N => prefix :+ base
    def stablePath(t: Term): Opt[Ls[Symbol]] = t.withoutCaptures match
      case ref: NewRefImpl => member(t).filter(stable).map(_ :: Nil)
      case Ref(sym) if stable(sym) => S(sym :: Nil)
      case sel: NewSel =>
        for
          prefix <- stablePath(sel.prefix)
          sym <- member(sel).filter(stable)
        yield prefix :+ sym
      case sel: Sel =>
        for
          prefix <- stablePath(sel.prefix)
          sym <- member(sel).filter(stable)
        yield prefix :+ sym
      case _ => N
    def fresh(sym: Symbol): Bool = sym.asTrm.flatMap(_.defn).exists(_.annotations.exists(_.isInstanceOf[Annot.Fresh]))
    stablePath(term) match
      case S(path) if path.last.asMod.isEmpty && (required || fresh(path.last)) =>
        if required then
          def check(): Unit = if !fresh(path.last) then
            resolError(term, msg"@jsSymbol requires a val marked @annotations.fresh." -> term.toLoc ::
              msg"The referenced member is declared here." -> path.last.toLoc :: Nil)
          path.last match
            case member: BlockMemberSymbol => member.onComplete(() => check())
            case _ => check()
        requireTerm(term)
        S(SymbolKey(canonicalPath(path.init, Set.empty) :+ path.last.asTrm.flatMap(_.defn).map(_.sym).getOrElse(path.last))(term))
      case _ =>
        if required then resolError(term,
          msg"@jsSymbol requires a stable path of modules and immutable vals ending in a val marked @annotations.fresh." -> term.toLoc :: Nil)
        N

  /** Values prefer the function/constructor overload; selection receivers prefer
    * the module overload. Keep that choice through captures so nested functions
    * and opened names use the same interpretation as direct references.
    */
  private[semantics] def valueTarget(member: BlockMemberSymbol, receiver: Bool): Opt[DefinitionSymbol[?]] =
    if receiver then member.asModOrObj.orElse(member.asTrm).orElse(member.asCls).orElse(member.asPat)
    else member.asTrm.orElse(member.asModOrObj).orElse(member.asCls).orElse(member.asPat)

  /** Syntactic control transfers within one evaluation scope. Calls may return,
    * but an explicit return/break/throw cannot also supply a normal value. Keep
    * exit operands at their lexical endpoint; the function or label observing
    * them applies the same shape transport as for its normal body result.
    */
  private case class ResultFlow(normal: Bool, exits: Map[Opt[LabelSymbol], Vector[Term]]):
    // None identifies the current function's return; Some(label) identifies a break.
    def or(that: ResultFlow): ResultFlow = ResultFlow(normal || that.normal,
      exits ++ that.exits.map((target, values) => target -> (exits.getOrElse(target, Vector.empty) ++ values)))
    def andThen(that: => ResultFlow): ResultFlow =
      if normal then copy(normal = false).or(that) else this
    def leave(target: Opt[LabelSymbol], value: Term): ResultFlow =
      andThen(ResultFlow(false, Map(target -> Vector.single(value))))

  private def resultFlow(term: Term): ResultFlow =
    val normal = ResultFlow(true, Map.empty)
    def sequence(terms: Iterable[Term]): ResultFlow =
      terms.foldLeft(normal)((flow, term) => flow.andThen(resultFlow(term)))
    def statement(stat: Statement): ResultFlow = stat match
      // A definition's body belongs to its own invocation, not to the enclosing
      // function. In particular, a nested getter's return must not escape here.
      case _: Definition => normal
      case term: Term => resultFlow(term)
      case _ => sequence(stat.subTerms)
    def split(branches: SimpleSplit, onEnd: ResultFlow): ResultFlow = branches match
      case SimpleSplit.Else(value) => resultFlow(value)
      case SimpleSplit.End => onEnd
      case SimpleSplit.Cons(SimpleSplit.Head.Let(_, value), tail) => resultFlow(value).andThen(split(tail, onEnd))
      case SimpleSplit.Cons(SimpleSplit.Head.Match(scrutinee, pattern, consequent), tail) =>
        // A failed pattern can skip its guards. Retain that path as well as
        // any control transfer from a guard which is evaluated.
        val guards = pattern.subTerms.foldLeft(normal)((flow, term) => flow.or(resultFlow(term)))
        resultFlow(scrutinee).andThen(guards.andThen(split(consequent, onEnd).or(split(tail, onEnd))))
    def quoted(term: Term, depth: Int): ResultFlow = term match
      // Only splices crossing back to the current stage execute now. Nested
      // quotations delay their own splices, including any returns they contain.
      case Unquoted(body) if depth == 1 => resultFlow(body)
      case Unquoted(body) => quoted(body, depth - 1)
      case Quoted(body) => quoted(body, depth + 1)
      case _ => term.subTerms.foldLeft(normal)((flow, term) => flow.andThen(quoted(term, depth)))
    term match
      case Ret(value) => resultFlow(value).leave(N, value)
      case Break(label, _, value) => value.fold(normal)(resultFlow).leave(S(label), value.getOrElse(unit))
      case Throw(value) => resultFlow(value).copy(normal = false)
      case _: Continue => ResultFlow(false, Map.empty)
      case Blk(stats, value) => stats.foldLeft(normal)((flow, stat) => flow.andThen(statement(stat))).andThen(resultFlow(value))
      case Label(label, _, body, _) =>
        val flow = resultFlow(body)
        ResultFlow(flow.normal || flow.exits.contains(S(label)), flow.exits - S(label))
      case Try(body, cleanup) =>
        val first = resultFlow(body)
        val last = resultFlow(cleanup)
        // An abrupt cleanup replaces the pending return/break as well as the
        // normal body value. A normally completing cleanup contributes no value.
        if last.normal then first.or(last.copy(normal = false)) else last
      case IfLike(_, form, branches) =>
        // Falling off an imperative split returns unit; falling off a returning
        // split throws a match error. A loop may finish without running its body.
        val flow = split(branches, if form.isImperative then normal else ResultFlow(false, Map.empty))
        if form == IfLikeForm.While then flow.or(normal) else flow
      case Quoted(body) => quoted(body, 1)
      case _: Lam | _: Unquoted | _: FunTy | _: Forall | _: Constrained | _: WildcardTy
          | _: CompType | _: Neg | _: DynTy => normal
      case Annotated(Annot.Async(), _) => normal
      case Annotated(_, target) => resultFlow(target)
      case Handle(_, rhs, args, _, _, _) => sequence(rhs :: args)
      case New(cls, args, _) => sequence(cls :: args)
      case Rcd(_, stats) => stats.foldLeft(normal)((flow, stat) => flow.andThen(statement(stat)))
      case Asc(value, _) => resultFlow(value)
      case TyApp(value, _) => resultFlow(value)
      case _ => sequence(term.subTerms)

  /** Function results include explicit returns, whereas listenTerm observes only
    * normal completion. Share this rule between calls, result checking, getters,
    * and interface exposure so a returned closure is checked even when no caller
    * observes it locally.
    */
  private[semantics] def listenResult(body: Term)(listener: Listener)(using ResolutionContext): Unit =
    val flow = resultFlow(body)
    if flow.normal then listenTerm(body)(listener)
    flow.exits.getOrElse(N, Vector.empty).foreach(value => listenTerm(value)(listener))

  def listenTerm(trm: Term)(listener: Listener)(using ResolutionContext): Unit =
    log(dbg"listenTerm: trm = ${trm.showDbg}")
    listenValue(trm, false)(listener)

  def listenReceiver(trm: Term)(listener: Listener)(using ResolutionContext): Unit =
    listenValue(trm, true)(shape => listenInstanceViews(shape)(listener))

  private def listenValue(trm: Term, receiver: Bool)(listener: Listener)(using ResolutionContext): Unit = trm match
    case Capture(base, thru) =>
      listenValue(base, receiver): shape =>
        listener(MarkedShape.enter(shape, ResolutionBoundary(thru), N))
    case _ => listen(trm, discardMarks = false):
      case sh: TermShape => listener(sh)
      case ss: SymShape =>
        fromSymbol(ss, listener, trm, recordValueTarget(trm, _), receiver)

  private def recordValueTarget(term: Term, symbol: DefinitionSymbol[?])(using ResolutionContext): Unit =
    term.withoutCaptures match
      case ref: NewResolvable =>
        rctx.recordResolution(ref, ref.resolvedTargets.contains(symbol))(ref.resolvedTargets ::= symbol)
      case _ => ()
  
  /** Subscribe to spread operands once for each tuple or record AST node. Record
    * the node before calling start: a recursive spread can call listen on the same
    * node before start returns. Testing shapes.isEmpty would not prevent duplicate
    * subscriptions while the node is waiting for a forward definition. Deliver
    * cached shapes to each listener, which is already registered for future shapes.
    */
  private def listenAggregate(aggregate: Tup | CtxTup | Rcd, listener: ShapeListener[ShapeEvent])
      (start: (Listener) => Unit)(using ResolutionContext): Unit =
    val first = aggregateProducers.add(new Identity(aggregate))
    // An imported definition can already have shapes computed by its own elaborator.
    // Send those shapes to this listener even if first is true; recomputing the same
    // shapes below will not notify it, because shapes.add rejects duplicates.
    aggregate.replayShapes(listener)
    if first then
      start: shape =>
        if aggregate.currentShapes.add(shape) then aggregate.notifyShapeListeners(shape)

  private def activationListener(receive: ShapeListener[Shape])(using ResolutionContext): ShapeListener[ShapeEvent] =
    // A request and event are compatible when their activation maps agree on
    // shared keys; an empty source request accepts all activations. Unwrap the
    // event and supply that activation to the receiving operation, without
    // replacing the enclosed value's independent caller-side substitution.
    val requestedInstances = rctx.instances
    def compatible(instances: TypeSubstitution): Bool =
      requestedInstances.forall((parameter, instance) => instances.get(parameter).forall(_ eq instance))
    event => event match
      case ActivatedShapeEvent(value, instances) =>
        if compatible(instances) then receive(value)(using rctx.withInstances(requestedInstances.withOverrides(instances)))
      case value: TermShape => receive(instantiateShape(value, rctx.instances))
      case symbol: SymShape => receive(symbol)

  private def listenValueHost(host: ShapeHost)(receive: Listener)(using ResolutionContext): Unit =
    host.subscribeToShapes(activationListener:
      case value: TermShape => receive(value)
      case _: SymShape => softAssert(false, "Value hosts contain only term shapes")
    )

  private def listenMemberVariable(sym: TermSymbol)(receive: Listener)(using ResolutionContext): Unit =
    listenValueHost(rctx.memberVariable(sym))(receive)

  private def listen(trm: Term, discardMarks: Bool)(receive: ShapeListener[Shape])(using ResolutionContext): Unit =
    val listener = activationListener(receive)
    log(dbg"listen: trm = ${trm.showDbg}")
    trm.addShapeListener(listener)
    trm match
    case _: SynthSel =>
      lastWords("Synthetic selections must not enter new resolution")
    case Asc(_, sign) => listenTypeInstances(sign)(listener)
    case sel @ DynSel(prefix, _, true, true) => listenArrayIndex(sel, prefix)(listener)
    case _: DynSel | _: DynNew => listener(DynShape())
    case application @ TyApp(underlying, args) =>
      def checkArity(callee: TermShape, count: Int)(using ResolutionContext): Unit =
        if count != args.length && rctx.state.typeArgumentArityErrors.add((new Identity(application), count)) then
          resolError(trm, callee.diagnostic(msg"${callee.describe.capitalize} expected ${count} type ${
            "argument".pluralized(count)}, but got ${args.length}"))
      def instantiate(value: TermShape)(receive: Listener)(using ResolutionContext): Unit = listenInstanceViews(value): viewed =>
        val ShapeParts(actual, captured, supplied) = shapeParts(viewed)
        if supplied.nonEmpty then
          checkArity(actual, 0)
          receive(value)
        else actual.applicationHead match
          case (callable: CallableTypeShape, marks) =>
            checkArity(callable, callable.tparams.length)
            val supplied = args.map(arg => declaredType(typeResolution(arg), Map.empty).instantiate(rctx.instances))
            instantiateCallable(callable.copy(supplied = S(supplied)),
              rctx.typeApplicationSite(application), lexicalBinders(application), marks).exit(marks) match
              case value: TermShape => receive(value)
              case NoShape => ()
          case (callee: DefnShape, marks) =>
            val (_, parameters) = definitionParameters(callee)
            // The first consumed parameter list has already bound this scheme.
            // Looking through an application's head must not turn its result
            // (especially a constructed object) back into a generic function.
            val unapplied = actual match
              case Marked(_: DefnShape, _) => true
              case Marked(construction: NewShape, _) => construction.argss.isEmpty && !construction.isSaturated
              case _ => false
            checkArity(callee, if unapplied then parameters.length else 0)
            if !unapplied then receive(value)
            else
              val supplied = args.map(arg => declaredType(typeResolution(arg), Map.empty).instantiate(rctx.instances))
              val instances = instantiateDefinition(callee, rctx.typeApplicationSite(application),
                lexicalBinders(application), marks, rctx.instances.withOverrides(captured), S(supplied))
              SpecializedShape(callee, supplied, instances).exit(marks) match
                case specialized: TermShape => receive(specialized)
                case NoShape => ()
          case _ => receive(value)
      // A value specialization binds its arguments in the type application's
      // scope, after the reference has crossed all intervening captures. By-name
      // definitions execute at the reference itself: supply their arguments there,
      // rebasing from the application scope with the ordinary mark operations.
      // Their result may have an independent scheme and must not be specialized
      // again with the arguments belonging to the by-name definition.
      def observe(base: Term, captures: Ls[Marks])
          (receive: (TermShape, Bool) => ResolutionContext ?=> Unit)(using ResolutionContext): Unit = base match
        case Capture(inner, thru) =>
          val crossing = EntryMark(ResolutionBoundary(thru), N, NoMarks)
          observe(inner, crossing :: captures): (shape, invoked) =>
            receive(if discardMarks then shape else MarkedShape.enter(shape, ResolutionBoundary(thru), N), invoked)
        case _ => listen(base, discardMarks):
          case sym: SymShape => sym.sym.onComplete: () =>
            valueTarget(sym.sym, false).flatMap(_.defn) match
              case S(td: TermDefinition) if isByName(td) =>
                val definition = defnShapes.getOrElseUpdate(td.tsym, DefnShape(td, N))
                checkArity(definition, definitionBinders(td).length)
                val arguments = args.map: arg =>
                  val caller = declaredType(typeResolution(arg), Map.empty).instantiate(rctx.instances)
                  transportType(caller, inverseMarks(captures))
                fromSymbolAt(sym, value => receive(value, true), base, recordValueTarget(base, _), false,
                  S((rctx.typeApplicationSite(application), arguments)))
              case _ => fromSymbol(sym, value => receive(value, false), base, recordValueTarget(base, _), false)
          case value: TermShape => receive(value, false)
      observe(underlying, Nil): (value, invoked) =>
        if invoked then listener(value) else instantiate(value)(listener)
    case mut @ Mut(underlying: Tup) => listener(mutableArray(mut, underlying))
    case Mut(underlying) => listenTerm(underlying)(listener)
    case tuple: (Tup | CtxTup) => listenAggregate(tuple, listener): publish =>
        val elements = tuple match
          case Tup(fields) => fields
          case CtxTup(fields) => fields
        val fields = elements.collect { case Fld(_, key, S(value)) => (key, value) }
        val named = if fields.isEmpty then Nil else
          // Reuse the defining graph's property symbols when an imported tuple
          // is observed directly, as well as when its copied listeners fire.
          val graph = tuple.originalData.owner
          assert(graph != null, "A tuple producer must have an inference owner")
          val defining = rctx.inGraph(graph.nn.context)
          val record = defining.state.namedTupleRecords.getOrElseUpdate(new Identity(tuple), {
            val record: Rcd = Rcd(false, fields.map((key, value) => RcdField(key, value)(using rctx.owner)))
            record.withLocOf(tuple)
            // The record's fields are the tuple's own field expressions, so its
            // lexical scope is the tuple's.
            lexicalBinders(tuple).foreach(defining.recordLexicalBinders(record, _))
            record
          })(using defining)
          // The synthesized record has no owning graph of its own; share the
          // defining graph's canonical shape for it, like its property symbols.
          TupleShape.ValueField(RecordShape(record, record.stats.collect {
            case field: RcdField => RecordShape.Field(field)
          })(using defining), Nil) :: Nil
        def expand(elems: Ls[Elem], reversed: Ls[TupleShape.Element])(using ResolutionContext): Unit = elems match
          case Nil =>
            // A sole spread preserves its operand's shape and context exactly.
            // Besides avoiding wrappers, this lets recursive rest forwarding
            // reach the same fixed point as forwarding an ordinary parameter.
            val shape = (reversed, named) match
              case (TupleShape.Spread(shape, NoMarks) :: Nil, Nil) => shape
              case (TupleShape.Spread(shape, marks: SomeMarks) :: Nil, Nil) => MarkedShape(shape, marks)
              case _ => TupleShape(tuple, reversed.reverse ::: named)(this)
            publish(shape)
          // Lowering evaluates fields in source order, but packs all named
          // fields into one trailing record. Shape positions must match that layout.
          case Fld(_, _, S(_)) :: rest => expand(rest, reversed)
          case (field: Fld) :: rest => expand(rest, TupleShape.Field(field, Nil) :: reversed)
          case Spd(_, term, _) :: rest =>
            val spreadKey = new Object
            listenTermViews(term): sh =>
              if rctx.state.spreadInputs.getOrElseUpdate(spreadKey, mutable.Set.empty).add(ShapeIdentity.key(sh)) then sh match
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
                  val spread = TupleShape(term, TupleShape.Unknown(term, TupleShape.ValueField(DynShape(), Nil)) :: Nil)(this)
                  expand(rest, TupleShape.Spread(spread, marks) :: reversed)
                case shape =>
                  // An iterable spread contributes an unknown number of elements,
                  // so its candidates would differ only in their element values.
                  // Distinct element types (e.g. one annotation observed through
                  // different activations) must not each become an operand: a
                  // literal enumerates every combination of its operands, and
                  // with several spreads this product makes resolution of
                  // recursive code such as FingerTreeList's `concatMiddle`
                  // intractable. Instead, all elements of this spread flow into
                  // one inferred element type, as for a tuple's Array interface.
                  // Combinations of independent operands carry no correlation
                  // between their element values, so no information is lost.
                  val flow = iterationFlow(term, lexicalBinders(tuple))
                  listenIterableElements(shape, flow)
                  val element = TupleShape.TypedField(declaredType(flow.elements, Map.empty), Nil)
                  val spread = TupleShape(term, TupleShape.Unknown(term, element) :: Nil)(this)
                  if rctx.state.spreadInputs.getOrElseUpdate(spreadKey, mutable.Set.empty).add(ShapeIdentity.key(spread)) then
                    expand(rest, TupleShape.Spread(spread, NoMarks) :: reversed)
        expand(elements, Nil)
    case record: Rcd => listenAggregate(record, listener): publish =>
        def expand(stats: Ls[Statement], reversed: Ls[RecordShape.Element])(using ResolutionContext): Unit = stats match
          case Nil =>
            val shape = RecordShape(record, reversed.reverse)
            publish(shape)
          case (field: RcdField) :: rest => expand(rest, RecordShape.Field(field) :: reversed)
          case RcdSpread(term) :: rest =>
            val spreadKey = new Object
            listenTermViews(term): shape =>
              if rctx.state.spreadInputs.getOrElseUpdate(spreadKey, mutable.Set.empty).add(ShapeIdentity.key(shape)) then shape match
                case Marked(shape: RecordShape, marks) =>
                  // Bound recursive record producers just as for tuple spreads.
                  // Keep surrounding explicit fields even when the spread widens.
                  val spread = if shape.containsSpread(shape.source, marks)
                    then RecordShape(shape.source, RecordShape.Unknown(UnknownValueShape.spread(term, shape)) :: Nil)
                    else shape
                  expand(rest, RecordShape.Spread(spread, marks) :: reversed)
                case Marked(_: DynShape, marks) => expand(rest, RecordShape.Dynamic(marks :: Nil) :: reversed)
                case _ => expand(rest, RecordShape.Unknown(UnknownValueShape.spread(term, shape)) :: reversed)
          case _ :: rest => expand(rest, reversed)
        expand(record.stats, Nil)
    // Ignore undefined during resolution. Runtime literals and pattern tests
    // are compiled from the term itself and do not need a shape.
    case Lit(Tree.UnitLit(false)) => ()
    case intro: IntroTerm =>
      // Literals and lambdas have the declared interface of their builtin class,
      // including inherited members. Retain their own shape for calls, pattern
      // tests, and provenance.
      val primitive = intro match
        case Lit(_: Tree.StrLit) => S(prelude.builtins.Str)
        case Lit(_: Tree.IntLit) => S(prelude.builtins.Int)
        case Lit(_: Tree.DecLit) => S(prelude.builtins.Num)
        case Lit(_: Tree.BoolLit) => S(prelude.builtins.Bool)
        case _: Lam => S(prelude.builtins.Function)
        case _ => N
      def publish(parent: Opt[NominalInstanceView])(using ResolutionContext): Unit =
        listener(introShapes.getOrElseUpdate(new Identity(intro), {
          log(dbg"introShape: intro = $intro")
          IntroShape(intro, parent)
        }))
      primitive match
        case N => publish(N)
        case S(cls) =>
          val tpe = rctx.state.primitiveTypes.getOrElseUpdate(cls, {
            val resolution = new TypeResolution(intro, messages => resolError(intro, messages))
            resolution.publish(TypeShape.Nominal(cls.defn.get))
            declaredType(resolution, Map.empty)
          })
          listenTypeViews(tpe):
            case nominal: NominalInstanceView => publish(S(nominal))
            case _ => softAssert(false, "Primitive class must expose a nominal interface")
    case Ref(sym) if sym is sym.getState.globalThisSymbol => listener(DynShape())
    case SelfRef(sym) if sym is sym.getState.globalThisSymbol => listener(DynShape())
    case ref @ Ref(loc: LocalSymbol) =>
      loc.subscribeToShapes(listener)
    case ref @ SimpleRef(sym) =>
      sym match
      case loc: LocalSymbol =>
        loc.subscribeToShapes(listener)
      // Primitive operations are handled directly by lowering; they do not
      // introduce member-resolution candidates.
      case _: BuiltinSymbol => ()
    case SelfRef(sym) =>
      // A receiver can be referenced before its body is complete or after its
      // definition has already been published. The definition listener handles both.
      def completed(defn: ClassLikeDef)(using ResolutionContext): Unit =
        listenExt(defn, ext =>
          // Each inner symbol has one self shape; repeated notifications must agree.
          val shape = selfShapes.getOrElseUpdate(sym, BaseShape(defn, ext))
          softAssert(shape.defn is defn)
          softAssert(shape.ext.map(ShapeIdentity.key) == ext.map(ShapeIdentity.key))
          listener(shape))
      val symbol = sym.asDefnSym
      symbol.defn match
        case S(defn) => completed(defn)
        case N => symbol.defnListeners += completed
    case ref @ MemberRef(sym: TermSymbol) if sym.k is LetBind =>
      // A let-binding has no evaluation boundary of its own. Surrounding
      // function/class captures still enter and exit through Capture normally.
      recordValueTarget(ref, sym)
      rctx.memberVariable(sym).subscribeToShapes(listener)
    case MemberRef(_: TermSymbol) =>
      // Ctx.RefElem only refers to let-bound term symbols directly. Other definitions,
      // including class parameter fields, are referenced through their BlockMemberSymbol.
      lastWords("Only let-bound term symbols can be referenced directly")
    case ref @ MemberRef(sym: BlockMemberSymbol) =>
      val fs = ref.resSym
      val sh = symShapes.getOrElseUpdate((sym, fs, Nil), CoreSymShape(sym, fs, Nil))
      listener(sh)
    case ref @ MemberRef(_: ErrorSymbol) => rctx.markError(ref)
    case ref @ MemberRef(sym: TypeAliasSymbol) =>
      rctx.markError(ref)
      resolError(ref, msg"Type alias '${sym.nme}' cannot be used as a runtime value." -> sym.toLoc :: Nil)
    case MemberRef(_: InnerSymbol) =>
      // Ctx.RefElem uses SelfRef for class/module receivers, not MemberRef.
      lastWords("Direct inner-symbol references must use SelfRef")
    case Capture(base, thru) =>
      if discardMarks then
        listen(base, discardMarks = true)(listener)
      else listenTerm(base): sh =>
        listener(MarkedShape.enter(sh, ResolutionBoundary(thru), N))
    case ref @ Ref(sym: InnerSymbol) => // TODO: remove remaining occurrences of such refs
      sym.addShapeListener(listener)
    case ref @ Ref(bsym: BlockMemberSymbol) =>
      lastWords("Legacy block member references must not enter new resolution")
    case res: (App | New | Ref | Sel | SelProj | Resolved | LeadingDotSel) =>
      res.replayShapes(listener)
    case sh: (NewSel | UnresolvedRef | Super | IfLike) =>
      sh.replayShapes(listener)
    case block @ Blk(_, result) =>
      if resultFlow(block).normal then listen(result, discardMarks)(listener)
    case cleanup @ Try(body, _) =>
      // Finally is evaluated for effects; normal completion returns the body's
      // value. Its cleanup value must not contribute candidates to this result.
      if resultFlow(cleanup).normal then listen(body, discardMarks)(listener)
    case Label(label, _, body, hasContinueDispatch) =>
      val flow = resultFlow(body)
      if flow.normal then listen(body, discardMarks):
        // Lowering uses runtime.Continue to re-enter the label. Only normal
        // results and non-local break values flow out of the label.
        case value: TermShape if hasContinueDispatch && value.isInstanceOfClass(State.continueSymbol.defn.get) => ()
        case value => listener(value)
      flow.exits.getOrElse(S(label), Vector.empty).foreach(value => listen(value, discardMarks)(listener))
    case annotated @ Annotated(annotation @ Annot.Async(), body) =>
      listener(promiseShape(annotation, resultType(body, lexicalBinders(annotated), rctx.instances)(listenResult(body))))
    case Annotated(_, target) => listen(target, discardMarks)(listener)
    case _: Assgn | _: Drop => listener(unitResultShape)
    case _: Ret | _: Break | _: Throw | _: Continue => () // These expressions do not complete normally.
    case _: Quoted | _: Unquoted =>
      // Quotation constructs a runtime syntax value; splicing supplies syntax
      // for a different stage. Neither has the value interface of its operand.
      listener(UnknownValueShape.at(trm))
    case handle: Handle if handle.isAbortive =>
      resolveAbortiveHandler(handle)
      listenResult(handle.body)(listener)
      handle.defs.foreach: method =>
        // Parameters arrive through the method and handler-instance boundaries.
        // The result leaves both boundaries, joining every invocation at the
        // handler site rather than returning to the abandoned continuation.
        listenDefinitionResult(method.td, rctx.instances): result =>
          result.exit(ExitMark(ResolutionBoundary(method.td.tsym), N, NoMarks))
            .exit(ExitMark(ResolutionBoundary(handle.derivedClsSym), N, NoMarks)) match
              case value: TermShape => listener(value)
              case NoShape => ()
    case _: Handle =>
      // An effect handler can abort or replace the continuation's result. The
      // normal body's interface alone therefore cannot describe this value.
      listener(UnknownValueShape(trm, fromPublicInterface = false)(ShapeProvenance(
        msg"An effect handler can replace the handled body's result." -> trm.toLoc :: Nil)))
    case _: DynTy | _: FunTy | _: Forall | _: Constrained | _: WildcardTy | _: CompType | _: Neg =>
      resolError(trm, msg"A type cannot be used as a runtime value." -> N :: Nil)
    case Error() => () // Elaboration has already reported the error; it supplies no candidate.
    case Missing => () // A body skipped by lightweight elaboration (`Mode.Light`) supplies no candidate.
    case _: SynthIf | _: SynthWhile =>
      lastWords("Lowering-generated control flow must not enter resolution")
    case _: Region | _: RegRef | _: Deref | _: SetRef =>
      lastWords("InvalML reference operations require legacy resolution")
  
end NewResolver
