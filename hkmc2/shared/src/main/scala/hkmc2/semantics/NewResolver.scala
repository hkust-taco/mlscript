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
  // These results carry no value flow or lexical context. Reuse one immutable
  // shape so repeated subscriptions do not manufacture distinct unit candidates.
  private lazy val unitResultShape = IntroShape(unit, N)
  
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
            case alias: TypeDef =>
              result.publish(TypeShape.Alias(alias.sym, alias.rhs.map(typeResolution)))
              // Validate unused annotations too, once their forward source graph
              // is complete. Interface observation uses the same gate below.
              withCanonicalType(DeclaredType(result, Map.empty, Map.empty, true))(_ => ())
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
          case Capture(base, thru) => result.publish(TypeShape.Captured(typeResolution(base), thru))
          case TyApp(base, args) => result.publish(TypeShape.Applied(typeResolution(base), args.map(typeResolution)))
          case Forall(params, outer, body) =>
            result.publish(TypeShape.Polymorphic(params.map: param =>
              TypeQuantifier(TypeShape.Parameter(param.sym, param.sym.inferenceHost),
                param.lb.map(typeResolution), param.ub.map(typeResolution))
            , outer, typeResolution(body)))
          case CompType(left, right, union) =>
            val l = typeResolution(left)
            val r = typeResolution(right)
            result.publish(if union then TypeShape.Union(l, r) else TypeShape.Intersection(l, r))
          case DynTy() => result.publish(TypeShape.Dynamic)
          case FunTy(params, ret, _) => result.publish(TypeShape.Function(params, typeResolution(ret)))
          case UnitVal() => result.publish(TypeShape.Unit)
          case WildcardTy(input, output) => result.publish(TypeShape.Wildcard(input.map(typeResolution), output.map(typeResolution)))
          case SimpleRef(sym: VarSymbol) if sym.decl.exists(_.isInstanceOf[TyParam]) =>
            result.publish(TypeShape.Parameter(sym, sym.inferenceHost))
          case Ref(sym: VarSymbol) if sym.decl.exists(_.isInstanceOf[TyParam]) =>
            result.publish(TypeShape.Parameter(sym, sym.inferenceHost))
          case Tup(fields) if fields.forall(_.isInstanceOf[Fld]) =>
            result.publish(TypeShape.Tuple(fields.collect { case Fld(_, sign, _) => typeResolution(sign) }))
          case record: Rcd =>
            val fields = record.stats.collect { case field: RcdField => field }
            if fields.length != record.stats.length || fields.exists(field => field.field match
              case Lit(_: Tree.StrLit) => false
              case _ => true)
            then
              result.fail(msg"A record type requires statically named fields." -> record.toLoc :: Nil)
              result.publish(TypeShape.Abstract)
            else result.publish(TypeShape.Record(record,
              fields.reverse.distinctBy(_.sym.nme).reverse.map(field => field -> typeResolution(field.rhs))))
          // Signed numeric literals use operator applications in the syntax tree.
          // Like unsigned singleton types, they have no member interface here.
          case App(Ref(op: BuiltinSymbol), Tup(Fld(_, Lit(_: Tree.IntLit | _: Tree.DecLit), _) :: Nil))
              if op.nme === "-" || op.nme === "+" =>
            result.publish(TypeShape.Abstract)
          case _: Neg | _: Tup | _: Lit | Missing | Error() =>
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

  /** Compute free binders on the finite source graph, not on substituted types.
    * Each edge can hide binders introduced by an alias or quantifier. Iterating
    * finite binder sets reaches a fixed point even for mutually recursive types.
    * An unresolved target is a dependency still to discover, never a closed type.
    * Valid written types have one target (validation rejects ambiguity). The
    * synthetic nodes that can receive more candidates use no ambient bindings.
    */
  private def typeDependencies(resolution: TypeResolution)(using NewResolverState)
      : Either[Set[TypeResolution], Set[VarSymbol]] = rstate.typeDependencies.get(resolution) match
    case S(binders) => R(binders)
    case N =>
      val graph = mutable.LinkedHashMap.empty[TypeResolution, (Set[VarSymbol], Ls[(TypeResolution, Set[VarSymbol])])]
      val argumentUses = mutable.Map.empty[TypeResolution, Ls[(TypeResolution, VarSymbol, TypeResolution)]]
      val pending = mutable.Set.empty[TypeResolution]
      def visit(res: TypeResolution): Unit = if !graph.contains(res) then
        graph(res) = (Set.empty, Nil)
        rstate.typeDependencies.get(res) match
          case S(binders) => graph(res) = (binders, Nil)
          case N =>
            val shapes = res.currentShapes.toList
            if shapes.isEmpty then pending += res
            var direct = Set.empty[VarSymbol]
            var edges = List.empty[(TypeResolution, Set[VarSymbol])]
            def edge(child: TypeResolution, hidden: Set[VarSymbol]): Unit =
              edges ::= child -> hidden
              visit(child)
            def child(res: TypeResolution): Unit = edge(res, Set.empty)
            def reference(tpe: DeclaredType): Unit =
              visit(tpe.resolution)
              tpe.bindings.values.foreach(reference)
            shapes.foreach:
              case TypeShape.Parameter(symbol, _) => direct += symbol
              case TypeShape.Nominal(defn) =>
                // This immutable declaration metadata belongs to the original
                // graph, even when the type was reached through an imported AST.
                direct ++= defn.sym.getState.newResolverState.lexicalTypeBinders.get(defn.sym).getOrElse(
                  lastWords(s"Nominal declaration ${defn.sym.nme} must record its enclosing type binders"))
              case TypeShape.Alias(symbol, rhs) =>
                val bound = symbol.defn.get.tparams.map(_.sym).toSet
                rhs.foreach(edge(_, bound))
              case TypeShape.Captured(base, _) => child(base)
              case TypeShape.Applied(base, args) =>
                child(base)
                // An alias argument contributes dependencies only if the body
                // uses its formal. Solve this with the other equations: a cycle
                // such as Loop[A] = {next: Loop[Array[A]]} has no use of A.
                def arguments(base: TypeResolution, seen: Set[TypeResolution]): Unit =
                  if seen(base) then args.foreach(child) else base.currentShapes.toList match
                    case TypeShape.Captured(inner, _) :: Nil => arguments(inner, seen + base)
                    case TypeShape.Alias(symbol, S(rhs)) :: Nil =>
                      visit(rhs)
                      val formals = symbol.defn.get.tparams
                      args.zipWithIndex.foreach: (arg, index) =>
                        formals.lift(index) match
                          case S(formal) =>
                            visit(arg)
                            argumentUses(res) = (rhs, formal.sym, arg) :: argumentUses.getOrElse(res, Nil)
                          case N => child(arg)
                    case _ => args.foreach(child)
                arguments(base, Set.empty)
              case TypeShape.Tuple(fields) => fields.foreach(child)
              case TypeShape.Record(_, fields) => fields.foreach((_, field) => child(field))
              case TypeShape.Function(params, result) => child(typeResolution(params)); child(result)
              case TypeShape.Polymorphic(params, _, body) =>
                val bound = params.map(_.parameter.symbol).toSet
                params.foreach: param =>
                  param.lower.foreach(edge(_, bound))
                  param.upper.foreach(edge(_, bound))
                edge(body, bound)
              case TypeShape.Union(left, right) => child(left); child(right)
              case TypeShape.Intersection(left, right) => child(left); child(right)
              case TypeShape.Wildcard(input, output) => input.foreach(child); output.foreach(child)
              // These synthesized nodes retain their own interpreted references
              // or inference hosts; none reads the surrounding binding map.
              case TypeShape.Combined(formula) => formula.orderedAtoms.foreach(reference)
              case TypeShape.Argument(parts) => reference(parts.input); reference(parts.output)
              case TypeShape.SelectedArgument(argument, _) => reference(argument)
              case TypeShape.Contextual(context) => reference(context.tpe)
              case TypeShape.Inferred(_) | TypeShape.Hole(_) | TypeShape.Unit | TypeShape.Dynamic | TypeShape.Abstract |
                  TypeShape.Top | TypeShape.Bottom => ()
            graph(res) = (direct, edges)
      visit(resolution)
      if pending.nonEmpty then L(pending.toSet) else
        val dependencies = mutable.Map.from(graph.iterator.map((res, node) => res -> node._1))
        var changed = true
        while changed do
          changed = false
          graph.foreach: (res, node) =>
            val direct = argumentUses.getOrElse(res, Nil).foldLeft(node._1): (acc, use) =>
              if dependencies(use._1)(use._2) then acc ++ dependencies(use._3) else acc
            val next = node._2.foldLeft(direct): (acc, edge) =>
              acc ++ (dependencies(edge._1) -- edge._2)
            if next != dependencies(res) then
              dependencies(res) = next
              changed = true
        dependencies.foreach((res, binders) => rstate.typeDependencies(res) = binders)
        R(dependencies(resolution))

  /** Check recursive substitutions on the finite source graph, before observing
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
  private def regularType(root: TypeResolution)(using NewResolverState): Bool = rstate.regularTypes.get(root) match
    case S(result) => result
    case N =>
      val visited = mutable.Set.empty[TypeResolution]
      val applications = mutable.ArrayBuffer.empty[(TypeResolution, TypeAliasSymbol, TypeResolution, Ls[TypeResolution])]
      def alias(base: TypeResolution, seen: Set[TypeResolution]): Opt[(TypeAliasSymbol, TypeResolution)] =
        if seen(base) then N else base.currentShapes.toList match
          case TypeShape.Alias(symbol, S(rhs)) :: Nil => S(symbol -> rhs)
          case TypeShape.Captured(inner, _) :: Nil => alias(inner, seen + base)
          case _ => N
      def visit(res: TypeResolution): Unit = if visited.add(res) then
        res.currentShapes.foreach:
          case TypeShape.Alias(_, rhs) => rhs.foreach(visit)
          case TypeShape.Captured(base, _) => visit(base)
          case TypeShape.Applied(base, args) =>
            alias(base, Set.empty).foreach: (symbol, rhs) =>
              applications += ((res, symbol, rhs, args))
            visit(base)
            args.foreach(visit)
          case TypeShape.Tuple(fields) => fields.foreach(visit)
          case TypeShape.Record(_, fields) => fields.foreach((_, field) => visit(field))
          case TypeShape.Function(params, result) => visit(typeResolution(params)); visit(result)
          case TypeShape.Polymorphic(params, _, body) =>
            params.foreach: param =>
              param.lower.foreach(visit)
              param.upper.foreach(visit)
            visit(body)
          case TypeShape.Union(left, right) => visit(left); visit(right)
          case TypeShape.Intersection(left, right) => visit(left); visit(right)
          case TypeShape.Wildcard(input, output) => input.foreach(visit); output.foreach(visit)
          case TypeShape.Combined(formula) => formula.orderedAtoms.foreach(atom => visit(atom.resolution))
          case TypeShape.Argument(parts) => visit(parts.input.resolution); visit(parts.output.resolution)
          case TypeShape.SelectedArgument(argument, _) => visit(argument.resolution)
          case TypeShape.Contextual(reference) => visit(reference.tpe.resolution)
          case _ => ()
      visit(root)
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
            case TypeShape.Argument(parts) :: Nil => uses(parts.input, wrapped, next, aliases) ++ uses(parts.output, wrapped, next, aliases)
            case TypeShape.SelectedArgument(argument, _) :: Nil => uses(argument, wrapped, next, aliases)
            case TypeShape.Applied(base, args) :: Nil => alias(base, Set.empty) match
              case S((symbol, rhs)) if !aliases(symbol) =>
                // Constructor analysis ignores scope crossings, but still follows
                // the alias's substitution. The guard bounds body expansion;
                // substitution values are finite immutable reference DAGs.
                val substitutions = symbol.defn.get.tparams.zip(args).map: (formal, argument) =>
                  formal.sym -> argumentType(declaredType(argument, tpe), formal.vce)
                uses(declaredType(rhs, tpe.bindings ++ substitutions, tpe.positive), wrapped, next, aliases + symbol)
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
      rstate.regularTypes(root) = result
      result

  /** Wait for the source graph before observing a substituted interface. The
    * retained environment is projected only after every forward dependency has
    * a target. Subscriptions and completed summaries are shared by source node;
    * callbacks and their hosts remain private to each consuming inference graph.
    */
  private def withCanonicalType(tpe: DeclaredType)(listener: ShapeListener[DeclaredType])(using NewResolverState): Unit =
    def publish(binders: Set[VarSymbol])(using NewResolverState): Unit =
      if regularType(tpe.resolution) then
        listener(declaredType(tpe.resolution, tpe.bindings.filter((symbol, _) => binders(symbol)), tpe.positive)
          .instantiate(tpe.instances))
    typeDependencies(tpe.resolution) match
      case R(binders) => publish(binders)
      case L(_) =>
        rstate.pendingTypeDependencies.get(tpe.resolution) match
          case S(host) => host.listen(publish)
          case N =>
            val host = new TypeDependencyHost
            rstate.pendingTypeDependencies(tpe.resolution) = host
            host.listen(publish)
            def retry()(using NewResolverState): Unit = typeDependencies(tpe.resolution) match
              case R(binders) => host.publish(binders)
              case L(pending) => pending.foreach: unresolved =>
                if rstate.dependencySubscriptions.add((tpe.resolution, unresolved)) then
                  unresolved.listen(_ => retry())
            retry()

  /** Substitute a bound parameter before storing an argument. Otherwise recursive
    * interfaces such as Tree[A] = Node[A] | Empty would accumulate equivalent
    * A-to-A environments every time a recursive field is selected.
    */
  private[semantics] def declaredType(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType])(using NewResolverState): DeclaredType =
    declaredType(resolution, bindings, true)

  private def declaredType(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType], positive: Bool)
      (using NewResolverState): DeclaredType =
    def loop(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType], aliases: Set[TypeAliasSymbol]): DeclaredType =
      def retain: DeclaredType =
        val relevant = if bindings.isEmpty then bindings else typeDependencies(resolution) match
          case R(binders) => bindings.filter((symbol, _) => binders(symbol))
          case L(_) => bindings
        DeclaredType(resolution, relevant, Map.empty, positive)
      resolution.currentShapes.toList match
        case TypeShape.Parameter(symbol, _) :: Nil if bindings.contains(symbol) => selectArgument(bindings(symbol), positive)
        case TypeShape.Captured(base, thru) :: Nil => captureType(loop(base, bindings, aliases), thru)
        case TypeShape.Union(left, right) :: Nil =>
          combinedType(resolution, typeFormula(loop(left, bindings, aliases)).union(typeFormula(loop(right, bindings, aliases))))
        case TypeShape.Intersection(left, right) :: Nil =>
          combinedType(resolution, typeFormula(loop(left, bindings, aliases)).intersection(typeFormula(loop(right, bindings, aliases))))
        case TypeShape.Applied(base, arguments) :: Nil =>
          def applyAlias(base: DeclaredType, supplied: Ls[DeclaredType], seen: Set[TypeResolution]): Opt[DeclaredType] =
            if seen(base.resolution) then N else base.resolution.currentShapes.toList match
              case TypeShape.Alias(symbol, S(rhs)) :: Nil if !aliases(symbol) =>
                val parameters = symbol.defn.get.tparams
                if parameters.length != supplied.length then N else
                  val substitutions = parameters.zip(supplied).map: (parameter, argument) =>
                    parameter.sym -> argumentType(argument, parameter.vce)
                  S(loop(rhs, effectiveBindings(base) ++ substitutions, aliases + symbol))
              case TypeShape.Contextual(reference) :: Nil =>
                // Use exactly the interpreter's application rule: move caller
                // arguments to the template endpoint, substitute there, then
                // transport the result back. A wildcard exit followed by entry
                // is not cancelled; transportType retains its ordinary marks.
                applyAlias(reference.tpe.instantiate(base.instances),
                  supplied.map(transportType(_, inverseMarks(reference.marks))), seen + base.resolution)
                  .map(transportType(_, reference.marks))
              case _ => N
          // Reduce arguments in their caller environment before binding formals.
          // The alias guard grows only on body expansion, so nested Identity
          // applications reduce while unproductive recursive aliases stop.
          applyAlias(loop(base, bindings, aliases), arguments.map(loop(_, bindings, aliases)), Set.empty).getOrElse(retain)
        case _ => retain
    loop(resolution, bindings, Set.empty)

  /** Normalize Boolean combinations without observing an atom's candidates.
    * Transport distributes over components using the ordinary transportType
    * operation; no exit/entry cancellation is introduced by normalization.
    */
  private def typeFormula(tpe: DeclaredType)(using NewResolverState): TypeFormula[DeclaredType] =
    tpe.resolution.currentShapes.toList match
      case (parameter: TypeShape.Parameter) :: Nil if !tpe.bindings.contains(parameter.symbol) =>
        // Different written occurrences of A are the same lattice atom. Limit
        // this canonicalization to combinations, so ordinary annotation and
        // storage references retain their precise diagnostic source location.
        TypeFormula.atom(parameterType(parameter).copy(positive = tpe.positive).instantiate(tpe.instances))
      case TypeShape.Combined(formula) :: Nil => formula.map(_.instantiate(tpe.instances))
      case TypeShape.Contextual(reference) :: Nil =>
        typeFormula(reference.tpe.instantiate(tpe.instances)).map(transportType(_, reference.marks))
      case TypeShape.Top :: Nil => TypeFormula.top
      case TypeShape.Bottom :: Nil => TypeFormula.bottom
      case _ => TypeFormula.atom(tpe)

  private def combinedType(source: TypeResolution, formula: TypeFormula[DeclaredType])(using NewResolverState): DeclaredType =
    if formula.clauses.isEmpty then extremeType(false)
    else if formula.clauses.contains(Set.empty) then extremeType(true)
    else if formula.clauses.size == 1 && formula.atoms.size == 1 then formula.atoms.head
    else rstate.combinedTypes.getOrElseUpdate(formula, {
      val resolution = new TypeResolution(source.source, source.fail)
      resolution.publish(TypeShape.Combined(formula))
      DeclaredType(resolution, Map.empty, Map.empty, true)
    })

  private def declaredType(resolution: TypeResolution, context: DeclaredType)(using NewResolverState): DeclaredType =
    declaredType(resolution, context.bindings, context.positive).instantiate(context.instances)

  /** A substituted argument denotes one type at this occurrence. Freeze its
    * selected part before it becomes an invariant nominal argument; later input
    * and output uses must not select different parts of the original wildcard.
    * Only delayed/captured pairs need a node, and selecting a selection is inert.
    */
  private[semantics] def selectArgument(argument: DeclaredType, positive: Bool)(using NewResolverState): DeclaredType =
    def deferred(using NewResolverState): DeclaredType =
      rstate.selectedArguments.getOrElseUpdate((argument, positive), {
        val resolution = new TypeResolution(argument.resolution.source, argument.resolution.fail)
        resolution.publish(TypeShape.SelectedArgument(argument, positive))
        declaredType(resolution, Map.empty)
      })
    rstate.selectedArguments.get((argument, positive)).getOrElse:
      argument.resolution.currentShapes.toList match
        case TypeShape.SelectedArgument(_, _) :: Nil => argument
        case TypeShape.Argument(parts) :: Nil =>
          (if positive then parts.output else parts.input).instantiate(argument.instances)
        case TypeShape.Wildcard(input, output) :: Nil =>
          // Keep the wildcard's source for a missing part's diagnostics; the
          // shared extreme node itself has no source location.
          (if positive then output else input).fold(deferred): part =>
            declaredType(part, argument.copy(positive = if positive then argument.positive else !argument.positive))
        case TypeShape.Contextual(reference) :: Nil =>
          transportType(selectArgument(reference.tpe.instantiate(argument.instances), positive), reference.marks)
        case Nil | TypeShape.Captured(_, _) :: Nil => deferred
        case _ => argument

  private def instanceType(instance: TypeParameterInstance)(using NewResolverState): DeclaredType =
    declaredType(typeResolution(instance.reference), Map.empty)

  private def parameterType(parameter: TypeShape.Parameter)(using NewResolverState): DeclaredType =
    rstate.parameterTypes.getOrElseUpdate(parameter, {
      val source = SimpleRef(parameter.symbol)(parameter.symbol.id)
      val resolution = new TypeResolution(source, messages => resolError(source, messages))
      resolution.publish(parameter)
      declaredType(resolution, Map.empty)
    })

  private def extremeType(top: Bool)(using NewResolverState): DeclaredType =
    rstate.extremeTypes.getOrElseUpdate(top, {
      val resolution = new TypeResolution(Term.Missing, _ => lastWords("A synthesized extreme type cannot be invalid"))
      resolution.publish(if top then TypeShape.Top else TypeShape.Bottom)
      declaredType(resolution, Map.empty)
    })

  /** Written wildcards override declaration variance. Unqualified arguments use
    * the declared variance; an invariant argument supplies both identical parts.
    */
  private def argumentType(tpe: DeclaredType, variance: Opt[Bool])(using NewResolverState): DeclaredType =
    val selected = tpe.resolution.currentShapes.exists:
      case TypeShape.SelectedArgument(_, _) => true
      case _ => false
    if variance.isEmpty || (!selected && tpe.resolution.source.withoutCaptures.isInstanceOf[WildcardTy]) then tpe else
      // Apply declaration variance to the interpreted type, not another pair.
      // Reusing a synthesized argument must select it first, so recursive
      // substitutions cannot accumulate repeated variance wrappers.
      tpe.resolution.currentShapes.toList match
        case TypeShape.Argument(_) :: Nil => argumentType(selectArgument(tpe, tpe.positive), variance)
        case _ => rstate.variantTypes.getOrElseUpdate((tpe, variance.get), {
          val resolution = new TypeResolution(tpe.resolution.source, tpe.resolution.fail)
          val parts = if variance.get then TypeArgument(extremeType(false), tpe)
            else TypeArgument(tpe, extremeType(true))
          resolution.publish(TypeShape.Argument(parts))
          declaredType(resolution, Map.empty)
        })

  private def listenArgumentParts(tpe: DeclaredType)(listener: ShapeListener[TypeArgument])(using NewResolverState): Unit =
    tpe.resolution.listen:
      case TypeShape.Wildcard(input, output) =>
        listener(TypeArgument(input.fold(extremeType(false))(declaredType(_, tpe.copy(positive = !tpe.positive))),
          output.fold(extremeType(true))(declaredType(_, tpe))))
      case TypeShape.Argument(parts) =>
        listener(TypeArgument(parts.input.instantiate(tpe.instances), parts.output.instantiate(tpe.instances)))
      case TypeShape.Captured(base, thru) =>
        listenArgumentParts(declaredType(base, tpe)): parts =>
          listener(TypeArgument(captureType(parts.input, thru), captureType(parts.output, thru)))
      case TypeShape.Contextual(reference) =>
        listenArgumentParts(reference.tpe.instantiate(tpe.instances)): parts =>
          listener(TypeArgument(transportType(parts.input, reference.marks), transportType(parts.output, reference.marks)))
      case TypeShape.Parameter(symbol, _) if tpe.bindings.contains(symbol) =>
        val selected = selectArgument(tpe.bindings(symbol).instantiate(tpe.instances), tpe.positive)
        listener(TypeArgument(selected, selected))
      case _ => listener(TypeArgument(tpe, tpe))

  private def effectiveBindings(tpe: DeclaredType)(using NewResolverState): Map[VarSymbol, DeclaredType] =
    tpe.instances.map((parameter, instance) => parameter -> instanceType(instance)) ++
      tpe.bindings.map((parameter, bound) => parameter -> bound.instantiate(tpe.instances))

  /** A parameterless generic declaration returns a polymorphic value. Keep its
    * binders around the annotation until the value's interface is observed.
    */
  private def quantifiedType(tpe: DeclaredType, parameters: Ls[VarSymbol])(using NewResolverState): DeclaredType =
    if parameters.isEmpty then tpe else
      val resolution = rstate.quantifiedTypes.getOrElseUpdate((tpe.resolution, parameters), {
        val result = new TypeResolution(tpe.resolution.source, tpe.resolution.fail)
        result.publish(TypeShape.Polymorphic(parameters.map: parameter =>
          TypeQuantifier(TypeShape.Parameter(parameter, parameter.inferenceHost), N, N)
        , N, tpe.resolution))
        result
      })
      declaredType(resolution, tpe)

  private def typeViews(using rs: NewResolverState) = rs.typeViews
  /** Each missing formal position belongs to its source type use. Keeping one
    * live host preserves late bounds without allocating a quantified parameter.
    */
  private[semantics] def omittedType(source: TypeResolution, parameter: VarSymbol)(using NewResolverState): DeclaredType =
    rstate.omittedTypes.getOrElseUpdate((source, parameter), {
      val resolution = new TypeResolution(source.source, source.fail)
      val bounds = new TermShapeHost
      resolution.publish(TypeShape.Hole(bounds.inferenceHost))
      declaredType(resolution, Map.empty)
    })

  /** Supplied arguments and omitted positions belong to the application scope.
    * Moving a template must rebase both, even before an omitted host is needed.
    */
  private case class TypeApplication(arguments: Ls[DeclaredType], context: Ls[Marks]):
    def move(marks: Ls[Marks])(using NewResolverState): TypeApplication =
      TypeApplication(arguments.map(transportType(_, marks)), context ::: marks)
  private val noTypeArguments = TypeApplication(Nil, Nil)

  private def typeArguments(source: DeclaredType, application: TypeApplication, parameters: Ls[TyParam])
      (using NewResolverState): Ls[DeclaredType] =
    parameters.zipWithIndex.map: (parameter, index) =>
      application.arguments.lift(index).getOrElse(
        transportType(omittedType(source.resolution, parameter.sym).instantiate(source.instances), application.context))

  private def typeBindings(source: DeclaredType, arguments: TypeApplication, parameters: Ls[TyParam])
      (using NewResolverState): Map[VarSymbol, DeclaredType] =
    effectiveBindings(source) ++ parameters.zip(typeArguments(source, arguments, parameters)).map: (parameter, argument) =>
      parameter.sym -> argumentType(argument, parameter.vce)

  /** External inputs contribute unknowns only to missing annotation parts.
    * A written binder still denotes its declared type, including after a partial
    * application fixes it; exposure must not add arbitrary values to that binder.
    */
  private[semantics] def exposeTypeHoles(tpe: DeclaredType, unknown: TermShape, marks: Ls[Marks])
      (using NewResolverState): Unit =
    if !rstate.exposedTypeHoles.add((tpe, unknown, marks)) then return
    def follow(current: DeclaredType, args: TypeApplication, captures: Ls[Marks], seen: Set[TypeResolution])
        (using NewResolverState): Unit = if !seen(current.resolution) then
      val next = seen + current.resolution
      def descend(child: DeclaredType)(using NewResolverState): Unit = unknown.enter(captures) match
        case value: TermShape => exposeTypeHoles(child, value, marks)
        case NoShape => ()
      current.resolution.listen:
        case TypeShape.Hole(host) => unknown.enter(captures) match
          case value: TermShape => host.publish(value)
          case NoShape => ()
        case TypeShape.Parameter(symbol, _) =>
          current.bindings.get(symbol).foreach(bound => follow(selectArgument(bound.instantiate(current.instances), current.positive), noTypeArguments, captures, next))
        case TypeShape.Captured(base, thru) =>
          follow(captureType(declaredType(base, current), thru), args, captures, next)
        case TypeShape.Contextual(reference) =>
          follow(reference.tpe.instantiate(current.instances), args.move(inverseMarks(reference.marks)),
            reference.marks ::: captures, next)
        case TypeShape.Applied(base, arguments) =>
          follow(declaredType(base, current), TypeApplication(arguments.map(declaredType(_, current)), Nil), captures, next)
        case TypeShape.Alias(symbol, S(rhs)) =>
          follow(declaredType(rhs, typeBindings(current, args, symbol.defn.get.tparams), current.positive), noTypeArguments, captures, next)
        case TypeShape.Nominal(cls) =>
          cls.tparams.zip(typeArguments(current, args, cls.tparams)).foreach: (param, argument) =>
            listenArgumentParts(argumentType(argument, param.vce)): parts =>
              exposeTypeHoles(transportType(parts.output, captures), unknown, marks)
        case TypeShape.Tuple(fields) => fields.foreach(field => descend(declaredType(field, current)))
        case TypeShape.Record(_, fields) => fields.foreach((_, field) => descend(declaredType(field, current)))
        case TypeShape.Function(_, result) => descend(declaredType(result, current))
        case TypeShape.Polymorphic(parameters, _, body) =>
          val symbols = parameters.map(_.parameter.symbol)
          val lexical = current.copy(bindings = current.bindings -- symbols, instances = current.instances -- symbols)
          follow(declaredType(body, lexical), args, captures, next)
        case TypeShape.Wildcard(_, output) => output.foreach(res => follow(declaredType(res, current), args, captures, next))
        case TypeShape.Argument(parts) => follow(parts.output.instantiate(current.instances), args, captures, next)
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

  private def abstractTypes(using rs: NewResolverState) = rs.abstractTypes
  // Narrowing a nominal receiver by projection does not infer the narrower
  // class's arguments. This abstract interface is distinct from an inference hole.
  private def abstractType(source: TypeResolution)(using NewResolverState): DeclaredType = abstractTypes.getOrElseUpdate(source, {
    val resolution = new TypeResolution(source.source, source.fail)
    resolution.publish(TypeShape.Abstract)
    declaredType(resolution, Map.empty)
  })

  /** An annotation is an abstraction boundary, even when its implementation is
    * available. Subscribe to the type graph, never to values flowing into it.
    * Shared hosts retain subscriptions for forward and recursive type references.
    */
  def listenTypeInstances(sign: Term)(listener: Listener)(using NewResolverState): Unit =
    listenTypeInstances(declaredType(typeResolution(sign), Map.empty))(listener)

  private[semantics] def listenTypeInstances(tpe: DeclaredType)(listener: Listener)(using NewResolverState): Unit =
    listener(InstanceShape(tpe.instantiate(rstate.instances)))

  /** Expanding a type is an observation, not a type-argument constraint. Cache
    * observations before following parameters so recursive interfaces reach the
    * same graph nodes instead of allocating fresh inference variables.
    */
  private[semantics] def listenInstanceViews(value: TermShape)(listener: Listener)(using NewResolverState): Unit = value match
    case Marked(instance: InstanceShape, marks) =>
      listenTypeViews(transportType(instance.tpe, marks :: Nil))(listener)
    case _ => listener(value)

  private def listenTermViews(term: Term)(listener: Listener)(using NewResolverState): Unit =
    listenTerm(term)(shape => listenInstanceViews(shape)(listener))

  /** Substitution changes a deferred observation, not its source graph. Compound
    * children inherit the same flat map when they are subsequently observed.
    */
  private[semantics] def instantiateShape(value: TermShape, instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): TermShape =
    if instances.isEmpty then value else rstate.shapeViews.getOrElseUpdate((value, instances), {
      val Marked(source, marks) = value
      val instantiated: NonMarkedShape = source match
        case instance: InstanceShape => InstanceShape(instance.tpe.instantiate(instances))
        case rigid: RigidTypeShape => instances.get(rigid.parameter).fold[NonMarkedShape](rigid)(p => InstanceShape(instanceType(p)))
        case tuple: TupleShape => tuple.copy(instances = instances ++ tuple.instances)(this)
        case record: RecordShape => record.copy(instances = instances ++ record.instances)
        case nominal: NominalInstanceView =>
          val bindings = instances.map((parameter, instance) => parameter -> instanceType(instance)) ++
            nominal.bindings.map((parameter, bound) => parameter -> bound.instantiate(instances))
          nominal.copy(bindings = bindings, parent = nominal.parent.map(instantiateShape(_, instances)))(nominal.annotation)(this)
        case record: RecordTypeShape =>
          val bindings = instances.map((parameter, instance) => parameter -> instanceType(instance)) ++
            record.bindings.map((parameter, bound) => parameter -> bound.instantiate(instances))
          record.copy(bindings = bindings)
        case contextual: ContextualShape => contextual.copy(instances = instances ++ contextual.instances)
        case specialized: SpecializedShape => specialized.copy(
          arguments = specialized.arguments.map(_.instantiate(instances)), instances = instances ++ specialized.instances)
        case callable: CallableTypeShape =>
          val captured = instances -- callable.tparams.map(_.parameter.symbol)
          callable.copy(paramLists = callable.paramLists.map: params =>
            DeclaredParams(params.params.map(_.map(_.instantiate(captured))), params.hasRest, params.rest.map(_.instantiate(captured)))
          , result = callable.result.map(_.instantiate(captured)))
        case literal: IntroShape if !literal.trm.isInstanceOf[Lam] => literal
        case _: (UnknownValueShape | DynShape | OpaqueTypeShape | ErrShape) => source
        case _ => ContextualShape(source, instances)
      marks match
        case NoMarks => instantiated
        case marks: SomeMarks => MarkedShape(instantiated, marks)
    })

  private def contextualParts(value: TermShape): (TermShape, Map[VarSymbol, TypeParameterInstance]) = value match
    case Marked(ContextualShape(source, instances), marks) =>
      (marks match
        case NoMarks => source
        case marks: SomeMarks => MarkedShape(source, marks)
      , instances)
    case _ => (value, Map.empty)

  /** Operations on a specialized declaration reuse its consumed binder group.
    * Keep that distinction separate from lexical captures of an open scheme.
    */
  private def callableParts(value: TermShape): (TermShape, Map[VarSymbol, TypeParameterInstance], Bool) =
    val (original, captured) = contextualParts(value)
    original match
      case Marked(specialized: SpecializedShape, marks) =>
        val declaration = marks match
          case NoMarks => specialized.declaration
          case marks: SomeMarks => MarkedShape(specialized.declaration, marks)
        (declaration, captured ++ specialized.instances, true)
      case _ => (original, captured, false)

  private def listenTypeViews(tpe: DeclaredType)(listener: Listener)(using NewResolverState): Unit =
    typeViews.get(tpe) match
      case S(host) => host.listen(listener)
      case N =>
        val host = new TermShapeHost
        typeViews(tpe) = host
        host.listen(listener)
        def follow(current: DeclaredType, args: TypeApplication, aliases: Set[TypeResolution], publish: Listener)(using NewResolverState): Unit =
          current.resolution.listen: shape =>
            def bind(params: Ls[TyParam])(using NewResolverState): Map[VarSymbol, DeclaredType] =
              typeBindings(current, args, params)
            def next(res: TypeResolution)(using NewResolverState): Unit = follow(declaredType(res, current), noTypeArguments, aliases, publish)
            shape match
              case TypeShape.Dynamic => publish(DynShape())
              case TypeShape.Top => publish(OpaqueTypeShape(tpe.resolution.source))
              case TypeShape.Bottom => ()
              case TypeShape.Wildcard(_, output) =>
                output.fold(publish(OpaqueTypeShape(tpe.resolution.source)))(next)
              case TypeShape.Argument(parts) => follow(parts.output.instantiate(current.instances), noTypeArguments, aliases, publish)
              case TypeShape.SelectedArgument(argument, positive) =>
                // An argument cycle can forward this selection without exposing
                // an interface. Keep the subscription for later parts, but stop
                // traversing the same unproductive reference in this observation.
                if !aliases(current.resolution) then
                  listenArgumentParts(argument.instantiate(current.instances)): parts =>
                    follow(if positive then parts.output else parts.input, args, aliases + current.resolution, publish)
              case TypeShape.Inferred(value) => listenInstanceViews(instantiateShape(value, current.instances))(publish)
              case TypeShape.Hole(host) => host.subscribe: value =>
                listenInstanceViews(instantiateShape(value, current.instances))(publish)
              case TypeShape.Nominal(defn) =>
                val bindings = bind(defn.tparams)
                defn.ext match
                  case N => publish(NominalInstanceView(defn, bindings, implicitParent(defn))(S(tpe.resolution.source))(this))
                  case S(parent) =>
                    // Only the parent's declared type is relevant here. Evaluating
                    // its constructor arguments would reintroduce implementation flow.
                    listenTypeViews(declaredType(typeResolution(parent.cls), bindings)): ext =>
                      publish(NominalInstanceView(defn, bindings, S(ext))(S(tpe.resolution.source))(this))
              case TypeShape.Alias(symbol, rhs) =>
                // Revisiting the same alias reference without reaching an outer
                // nominal/function shape supplies no additional interface. Track
                // references, not symbols: Id[Id[T]] has two distinct references.
                // This also terminates aliases that recursively grow their arguments.
                if aliases(current.resolution) then publish(OpaqueTypeShape(tpe.resolution.source))
                else rhs match
                  case S(rhs) => follow(declaredType(rhs, bind(symbol.defn.get.tparams), current.positive), noTypeArguments,
                    aliases + current.resolution, publish)
                  case N => publish(OpaqueTypeShape(tpe.resolution.source))
              case TypeShape.Applied(base, params) =>
                follow(declaredType(base, current), TypeApplication(params.map(declaredType(_, current)), Nil), aliases, publish)
              case TypeShape.Parameter(symbol, host) => current.bindings.get(symbol) match
                case S(bound) => follow(selectArgument(bound.instantiate(current.instances), current.positive), noTypeArguments, aliases, publish)
                case N =>
                  val target = current.instances.get(symbol).fold(host)(_.inferenceHost)
                  listenTypeArgument(target): value =>
                    // Report the use of an abstract parameter in a signature, not
                    // just its declaration. This survives substitution through
                    // generic members and nested tuple or function annotations.
                    val annotated = value match
                      case Marked(rigid: RigidTypeShape, marks) =>
                        UnknownValueShape(rigid.source)(rigid.provenance.via(
                          msg"This type annotation supplies the value's shape." -> tpe.resolution.source.toLoc)).exit(marks)
                      case Marked(unknown: UnknownValueShape, marks) =>
                        UnknownValueShape(unknown.source)(unknown.provenance.via(
                          msg"This type annotation supplies the value's shape." -> tpe.resolution.source.toLoc)).exit(marks)
                      case _ => value
                    annotated match
                      case value: TermShape => listenInstanceViews(instantiateShape(value, current.instances))(publish)
                      case NoShape => ()
              case TypeShape.Captured(base, thru) =>
                follow(captureType(declaredType(base, current), thru), args, aliases, publish)
              case TypeShape.Contextual(reference) =>
                // Arguments belong to the application scope, whereas the
                // template belongs to the reference's source scope. Move the
                // arguments back before substitution, then transport the result.
                follow(reference.tpe.instantiate(current.instances), args.move(inverseMarks(reference.marks)), aliases,
                  shape => shape.exit(reference.marks) match
                    case value: TermShape => publish(value)
                    case NoShape => ())
              case TypeShape.Function(params, ret) =>
                val ps = params match
                  case Tup(fields) => DeclaredParams(fields.collect:
                    case Fld(_, sign, _) => S(declaredType(typeResolution(sign), current.copy(positive = !current.positive)))
                  , fields.exists(!_.isInstanceOf[Fld]), N)
                  case single => DeclaredParams(S(declaredType(typeResolution(single), current.copy(positive = !current.positive))) :: Nil, false, N)
                publish(CallableTypeShape(tpe.resolution.source, ps :: Nil,
                  S(declaredType(ret, current)), N, N, N))
              case TypeShape.Polymorphic(params, _, body) =>
                val symbols = params.map(_.parameter.symbol)
                val lexical = current.copy(bindings = current.bindings -- symbols, instances = current.instances -- symbols)
                val binders = params.map: param =>
                  DeclaredTypeParameter(param.parameter,
                    param.lower.map(declaredType(_, lexical)),
                    param.upper.map(declaredType(_, lexical)))
                follow(declaredType(body, lexical), args, aliases, shape => shape match
                  case Marked(callable: CallableTypeShape, marks) =>
                    callable.copy(scheme = S(TypeScheme(current.resolution, binders ::: callable.tparams))).exit(marks) match
                      case value: TermShape => publish(value)
                      case NoShape => ()
                  case _ => publish(shape))
              case TypeShape.Tuple(fields) =>
                publish(TupleShape(current.resolution.source,
                  fields.map(field => TupleShape.TypedField(declaredType(field, current), Nil)))(this))
              case TypeShape.Record(source, fields) => publish(RecordTypeShape(source, fields, effectiveBindings(current), current.positive))
              case TypeShape.Union(left, right) => next(left); next(right)
              case TypeShape.Intersection(left, right) => next(left); next(right)
              case TypeShape.Combined(formula) => formula.orderedAtoms.foreach: atom =>
                follow(atom.instantiate(current.instances), noTypeArguments, aliases, publish)
              case TypeShape.Unit | TypeShape.Abstract => publish(OpaqueTypeShape(tpe.resolution.source))
        withCanonicalType(tpe)(follow(_, noTypeArguments, Set.empty, host.publish))

  // A separate full signature also annotates the implementation's parameters.
  // Register these before its body is elaborated, so observed calls can never
  // publish inferred alternatives for parameters behind this boundary.
  private def signatureParameters(using rs: NewResolverState) = rs.signatureParameters
  def registerParameterSignature(paramLists: Ls[ParamList], sign: Term)(using NewResolverState): Unit =
    def bind(paramLists: Ls[ParamList], tpe: DeclaredType)(using NewResolverState): Unit = paramLists match
      case Nil => ()
      case ps :: tail => listenTypeViews(tpe):
        case Marked(callable: CallableTypeShape, marks) =>
          val declared = callable.paramLists.head
          if !declared.hasRest then ps.params.zip(declared.params).foreach: (param, sign) =>
            if param.sign.isEmpty then sign.foreach: tpe =>
              val contextual = transportType(tpe, marks :: Nil)
              signatureParameters(param.sym) = contextual
              listenTypeInstances(contextual): shape =>
                if param.sym.currentShapes.add(shape) then param.sym.notifyShapeListeners(shape)
          callable.result.foreach(tpe => bind(tail, transportType(tpe, marks :: Nil)))
        case _ => ()
    bind(paramLists, declaredType(typeResolution(sign), Map.empty))

  /** Synthesized constructor fields retain their source declaration on the symbol. */
  private[semantics] def resultSignature(td: TermDefinition)(using NewResolverState): Opt[Term] = td.tsym.decl match
    case S(p: Param) => p.sign
    case _ => td.resultSignature

  /** Retain a scope transfer on the reference, including deferred fields and
    * both argument parts. Flatten existing transfers before interning, so a
    * recursive projection cannot build a tower of transport wrappers.
    */
  private[semantics] def transportType(bound: DeclaredType, marks: Ls[Marks])(using NewResolverState): DeclaredType =
    val (base, previous) = bound.resolution.currentShapes.toList match
      case TypeShape.Contextual(reference) :: Nil => (reference.tpe.instantiate(bound.instances), reference.marks)
      case _ => (bound, Nil)
    softAssert(!base.resolution.currentShapes.exists:
      case TypeShape.Contextual(_) => true
      case _ => false
    , "Contextual references must be flattened before they are interned")
    // A wildcard exit followed by an entry is not an identity: the exit
    // consumes a candidate's entry site and the new entry supplies its own.
    // Deferred references use exactly the same transport as ordinary values.
    InstanceShape(base).exit(previous).exit(marks) match
      case Marked(_, NoMarks) => base
      case Marked(_, path: SomeMarks) =>
        val reference = ContextualType(base, path :: Nil)
        rstate.contextualTypes.getOrElseUpdate(reference, {
          val resolution = new TypeResolution(base.resolution.source, base.resolution.fail)
          resolution.publish(TypeShape.Contextual(reference))
          declaredType(resolution, Map.empty)
        })
      case NoShape => extremeType(false)

  private def inverseMarks(marks: Ls[Marks])(using NewResolverState): Ls[Marks] =
    // Reverse directions using ordinary mark operations, not a reordered list
    // of scopes. This is not an inverse on candidates: a wildcard exit can lose
    // a call-site ID, which the reversed path cannot reconstruct.
    InstanceShape(extremeType(false)).enter(marks) match
      case Marked(_, NoMarks) => Nil
      case Marked(_, path: SomeMarks) => path :: Nil
      case NoShape => lastWords("Inverting a scope path cannot reject a candidate")

  private[semantics] def captureType(bound: DeclaredType, scope: AnyDefinitionSymbol)(using NewResolverState): DeclaredType =
    transportType(bound, EntryMark(ResolutionBoundary(scope), N, NoMarks) :: Nil)

  /** Finish a projection on the deferred reference before delivering it to a
    * caller. Leaving a wildcard entry outside InstanceShape would let a later
    * call exit cancel it before the reference's own path had been composed.
    */
  private def transportShape(value: TermShape, marks: Ls[Marks])(using NewResolverState): TermShape | NoShape = value match
    case Marked(instance: InstanceShape, inner) =>
      InstanceShape(transportType(instance.tpe, inner :: marks))
    case _ => value.exit(marks)

  private def listenDeclaredMember(member: BlockMemberSymbol, bindings: Map[VarSymbol, DeclaredType], flow: FlowSymbol,
      source: Term, annotation: Opt[Term], selected: ShapeListener[DefinitionSymbol[?]], receiver: Bool, positive: Bool,
      receiverMarks: Ls[Marks], specialization: Opt[(FlowSymbol, Ls[DeclaredType])])(listener: Listener)(using NewResolverState): Unit =
    member.onComplete: () =>
      valueTarget(member, receiver) match
        case S(symbol: TermSymbol) if !symbol.isInstanceOf[ClassCtorSymbol] =>
          selected(symbol)
          val td = symbol.defn.get
          val crossesValueScope = !(td.k is syntax.RecordField) && !td.tsym.decl.exists(_.isInstanceOf[Param])
          val callerInstances = rstate.instances
          val instances = if isByName(td) then instantiateByName(td, flow,
            ExitMark(ResolutionBoundary(td.tsym), S(flow), NoMarks) :: receiverMarks, specialization) else callerInstances
          // A selected generic method binds its own parameters anew. Receiver
          // bindings can mention an earlier call of that same source method in
          // their values, but cannot bind the new method's local names.
          val capturedBindings = bindings -- definitionBinders(td)
          def publish(shape: TermShape)(using NewResolverState): Unit =
            val Marked(interface, context) = shape
            val generic = interface match
              case callable: CallableTypeShape if !isByName(td) =>
                val parameters = td.tparams.toList.flatten.map(p => declaredParameter(p.sym)) ::: callable.tparams
                callable.copy(scheme = if parameters.isEmpty then N else S(TypeScheme(td.tsym, parameters)), declaration = S(td))
              case instance: InstanceShape if !isByName(td) =>
                InstanceShape(quantifiedType(instance.tpe, td.tparams.toList.flatten.map(_.sym)))
              case _ => interface
            // Constructor fields keep their parameter scope; structural fields
            // follow their written type directly. Other members leave their own
            // definition scope when their declared interface is selected.
            val path = context :: (if crossesValueScope then
              ExitMark(ResolutionBoundary(td.tsym), S(flow), NoMarks) :: Nil else Nil)
            val exited = transportShape(generic, path)
            exited match
              case value: TermShape => listener(instantiateShape(value, instances))(using rstate.withInstances(callerInstances))
              case NoShape => ()
          def signature(sign: Term, polarity: Bool)(using NewResolverState): DeclaredType =
            val tpe = declaredType(typeResolution(sign), capturedBindings, polarity)
            if isByName(td) then tpe.instantiate(instances) else tpe
          val result = resultSignature(td).map(signature(_, positive))
          if td.sign.nonEmpty && (td.k is syntax.Fun) && !td.flags.hasResultAnnotation && !isByName(td) then
            listenTypeViews(signature(td.sign.get, positive))(publish)
          else if td.params.nonEmpty then
            publish(CallableTypeShape(source,
              td.params.map(ps => DeclaredParams(ps.params.map(_.sign.map(signature(_, !positive))),
                ps.restParam.nonEmpty, ps.restParam.flatMap(_.sign).map(signature(_, !positive)))), result, N, N, S(td)))
          else result match
            case S(tpe) => listenTypeInstances(tpe)(publish)
            case N =>
              // Keep the missing constructor annotation on the unknown value so
              // later selections and calls can explain why argument flow is hidden.
              val unknown = td.tsym.decl match
                case S(param: Param) => UnknownValueShape(source)(ShapeProvenance(
                  (msg"Constructor parameter '${param.sym.nme}' has no type annotation." -> param.toLoc) ::
                  annotation.toList.map(sign =>
                    msg"This type annotation does not provide a type for field '${member.nme}'." -> sign.toLoc)))
                case _ => UnknownValueShape.at(source)
              publish(unknown)
        case _ =>
          // A nested nominal declaration denotes its statically selected symbol;
          // selecting it does not inspect an instance field or method body.
          fromBMSAt(member, flow, Nil, listener, source, selected, receiver, specialization)

  def resolError(src: Term | Pattern, msgs: Ls[(Message, Opt[Loc])])(using rs: NewResolverState): Unit = rs.report:
    ErrorReport(msg"Resolution error in ${src.describe}" -> src.toLoc ::msgs, source = Diagnostic.Source.Compilation)
  
  def registerTypeParameters(owner: AnyDefinitionSymbol, params: Ls[VarSymbol])(using State, NewResolverState): Unit =
    if params.nonEmpty then
      // Check every generic body under an abstract activation, including private
      // definitions and non-strict worksheets. Its fresh entry site cannot match
      // a real caller's exit, so identity-like results still substitute the actual
      // type argument without leaking this abstract candidate into the caller.
      val site = FlowSymbol("generic interface")
      params.foreach: param =>
        val ref = SimpleRef(param)(param.id)
        val unknown = RigidTypeShape(param, ref)
        publishParameter(param, MarkedShape.enter(unknown, ResolutionBoundary(owner), S(site)))

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

  private[semantics] def publishParameter(symbol: VarSymbol, shape: TermShape | NoShape)(using NewResolverState): Unit =
    shape match
      case value: TermShape if !symbol.decl.exists(_.isInstanceOf[TyParam]) => publishActivated(symbol, value)
      case _ => publishParameter(symbol.inferenceHost, shape)

  private[semantics] def publishParameter(host: Publisher.Data[Shape], shape: TermShape | NoShape)(using NewResolverState): Unit = shape match
    case value: TermShape => host.publish(value)
    case _ => ()

  private def declaredParameter(symbol: VarSymbol)(using NewResolverState): DeclaredTypeParameter =
    DeclaredTypeParameter(TypeShape.Parameter(symbol, symbol.inferenceHost), N, N)

  private def bindTypeArguments(parameters: Ls[TypeShape.Parameter], marks: Ls[Marks], arguments: Ls[DeclaredType])
      (using NewResolverState): Unit =
    // Establish every supplied position before publication can replay body
    // constraints or trigger observations of a mutually dependent parameter.
    parameters.zip(arguments).foreach((p, _) => rstate.markExplicitTypeArgument(p.symbol))
    parameters.zip(arguments).foreach: (parameter, argument) =>
      publishParameter(parameter.host, InstanceShape(argument).enter(marks))

  /** Consume the scheme at its authoritative site. Specialized values and curried
    * tails carry instantiated references and no scheme, so later calls reuse it.
    */
  private def instantiateCallable(callable: CallableTypeShape, site: FlowSymbol,
      marks: Ls[Marks])(using NewResolverState): CallableTypeShape = callable.scheme match
    case N => callable
    case S(scheme) =>
      val key = (callable, site, marks)
      rstate.instantiatedCallables.get(key) match
        case S(instantiated) => instantiated
        case N =>
          val substitution = rstate.instantiateTypeParameters(scheme.owner, site, scheme.parameters.map(_.parameter.symbol))
          def instantiate(tpe: DeclaredType): DeclaredType = tpe.instantiate(substitution)
          val instantiated = callable.copy(
            paramLists = callable.paramLists.map: params =>
              DeclaredParams(params.params.map(_.map(instantiate)), params.hasRest, params.rest.map(instantiate))
            , result = callable.result.map(instantiate), scheme = N, supplied = N)
          // Reentrant observations must find the view before supplied arguments
          // can publish candidates or trigger another observation of this call.
          rstate.instantiatedCallables(key) = instantiated
          callable.supplied.foreach: arguments =>
            val parameters: Ls[TypeShape.Parameter] = scheme.parameters.map: parameter =>
              val instance = substitution(parameter.parameter.symbol)
              TypeShape.Parameter(instance, instance.inferenceHost)
            bindTypeArguments(parameters, marks, arguments)
          instantiated

  /** The body must satisfy its annotated result even if no value escapes or no
    * call inspects the implementation. In particular a returned closure receives
    * its declared domain before its member targets are completed.
    */
  def checkDeclaredResult(definition: TermDefinition)(using NewResolverState): Unit =
    definition.body.foreach: body =>
      resultSignature(definition).foreach: sign =>
        checkAscription(body, sign)

  def checkAscription(body: Term, sign: Term)(using NewResolverState): Unit =
    val expected = declaredType(typeResolution(sign), Map.empty)
    listenTerm(body): shape =>
      inferTypeArguments(expected.instantiate(rstate.instances), shape, Nil)

  // Install each constraint edge before subscribing: callback parameter/result
  // flow can revisit it immediately. Distinct instantiations retain their marks.
  private def typeConstraints(using rs: NewResolverState) = rs.typeConstraints
  /** Keep both endpoints symbolic. Register before following either endpoint,
    * so recursive references reuse the relation even before any bound exists.
    */
  private[semantics] def constrainTypes(lower: ContextualType, upper: ContextualType)(using NewResolverState): Unit =
    if rstate.typeRelations.add((lower, upper)) then
      InstanceShape(lower.tpe).exit(lower.marks).enter(upper.marks) match
        case value: TermShape => inferTypeArguments(upper.tpe, value, upper.marks)
        case NoShape => ()

  private def inferTypeArguments(tpe: DeclaredType, value: TermShape, marks: Ls[Marks])(using NewResolverState): Unit =
    if !typeConstraints.add((tpe, value, marks)) then return
    def follow(tpe: DeclaredType, args: TypeApplication, captures: Ls[Marks],
        seen: Set[TypeResolution])(using NewResolverState): Unit = if !seen(tpe.resolution) then
      val next = seen + tpe.resolution
      def observe(listener: Listener)(using NewResolverState): Unit =
        listenInstanceViews(value): actual =>
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
            if rstate.hasExplicitTypeArgument(target.getOrElse(symbol)) then
              listenTypeArgument(destination): supplied =>
                // Compare in the caller's scope, retaining the supplied
                // reference's endpoint for any further parameter constraint.
                supplied.exit(captures).exit(marks) match
                  case Marked(instance: InstanceShape, context) =>
                    val endpoint = if context == NoMarks then Nil else context :: Nil
                    value.exit(marks).enter(context) match
                      case actual: TermShape => inferTypeArguments(instance.tpe, actual, endpoint)
                      case NoShape => ()
                  case _ => ()
            else publishParameter(destination, lower)
        case TypeShape.Captured(base, thru) =>
          follow(captureType(declaredType(base, tpe), thru), args, captures, next)
        case TypeShape.Contextual(reference) =>
          follow(reference.tpe.instantiate(tpe.instances), args.move(inverseMarks(reference.marks)),
            reference.marks ::: captures, next)
        case TypeShape.Applied(base, params) =>
          follow(declaredType(base, tpe), TypeApplication(params.map(declaredType(_, tpe)), Nil), captures, next)
        case TypeShape.Alias(symbol, S(rhs)) =>
          follow(declaredType(rhs, typeBindings(tpe, args, symbol.defn.get.tparams), tpe.positive), noTypeArguments, captures, next)
        case TypeShape.Hole(host) => value.enter(captures) match
          case value: TermShape => host.publish(value)
          case NoShape => ()
        case TypeShape.Tuple(fields) => observe:
          case unknown @ Marked(_: UnknownValueShape, _) =>
            fields.foreach(field => inferTypeArguments(declaredType(field, tpe), unknown, marks))
          case Marked(tuple: TupleShape, context) =>
            fields.zipWithIndex.foreach: (field, index) =>
              tuple.getMember(index.toString) match
                case MemberLookup.Indexed(actual, inner) => listenTupleField(actual): shape =>
                  shape.exit(inner).exit(context) match
                    case value: TermShape =>
                      inferTypeArguments(declaredType(field, tpe), value, marks)
                    case NoShape => ()
                case _ => ()
          case _ => ()
        case TypeShape.Record(_, fields) => observe(constrainRecord(fields, effectiveBindings(tpe), tpe.positive, _, marks))
        case TypeShape.Function(_, _) => observe(constrainFunction(tpe, _, marks))
        case TypeShape.Polymorphic(_, _, body) =>
          follow(declaredType(body, tpe), args, captures, next)
        case TypeShape.Wildcard(input, _) => input.foreach(res => follow(declaredType(res, tpe.copy(positive = !tpe.positive)), args, captures, next))
        case TypeShape.Argument(parts) => follow(parts.input.instantiate(tpe.instances), args, captures, next)
        case TypeShape.SelectedArgument(argument, positive) =>
          listenArgumentParts(argument.instantiate(tpe.instances)): parts =>
            follow(if positive then parts.output else parts.input, args, captures, next)
        case TypeShape.Nominal(cls) => listenInstanceViews(value): value =>
          val arguments = typeArguments(tpe, args, cls.tparams).map(transportType(_, captures))
          val (actual, instances) = contextualParts(value)
          val (head, context) = actual.applicationHead
          def constrain(param: TyParam, bound: DeclaredType, pattern: DeclaredType)(using NewResolverState): Unit =
            listenArgumentParts(bound.instantiate(instances)): actual =>
              listenArgumentParts(argumentType(pattern, param.vce)): expected =>
                constrainTypes(ContextualType(actual.output, context), ContextualType(expected.output, Nil))
                constrainTypes(ContextualType(expected.input, Nil), ContextualType(actual.input, context))
          def constrainNominal(nominal: NominalInstanceView)(using NewResolverState): Unit =
            if nominal.defn is cls then cls.tparams.zip(arguments).foreach: (param, pattern) =>
              nominal.bindings.get(param.sym).foreach(constrain(param, _, pattern))
          head match
            case _: UnknownValueShape =>
              cls.tparams.zip(arguments).foreach: (param, argument) =>
                listenArgumentParts(argumentType(argument, param.vce)): parts =>
                  inferTypeArguments(parts.output, value, marks)
            case ds: DefnShape if ds.clsDef.contains(cls) => cls.tparams.zip(arguments).foreach: (param, pattern) =>
              val bound = parameterType(TypeShape.Parameter(param.sym, param.sym.inferenceHost))
              constrain(param, argumentType(bound, param.vce), pattern)
            case nominal: NominalInstanceView => constrainNominal(nominal)
            case tuple: TupleShape => constrainNominal(tuple.arrayParent)
            case _ => ()
        case TypeShape.Top => ()
        case _ => value match
          // A concrete target stays fixed, but must receive bounds that arrive
          // through a symbolic source later. Concrete mismatch reporting is
          // separate from retaining this obligation in the graph.
          case Marked(_: InstanceShape, _) => listenInstanceViews(value)(inferTypeArguments(tpe, _, marks))
          case _ => ()
    // Alias expansion guards only unproductive cycles. Descending into a tuple,
    // nominal argument, or arrow installs another edge with its own cycle guard.
    withCanonicalType(tpe)(follow(_, noTypeArguments, Nil, Set.empty))

  /** Structural constraints follow declared fields only. This supplies generic
    * argument inference and callback checking without refining the annotation
    * with additional properties from an actual record.
    */
  private def constrainRecord(fields: Ls[(RcdField, TypeResolution)], bindings: Map[VarSymbol, DeclaredType], positive: Bool,
      actual: TermShape, marks: Ls[Marks])(using NewResolverState): Unit =
    fields.foreach: (field, sign) =>
      val expected = declaredType(sign, bindings, positive)
      val flow = FlowSymbol.memSym(field.sym)(using rstate.owner)
      def receive(value: TermShape)(using NewResolverState): Unit = inferTypeArguments(expected, value, marks)
      def member(info: MemberLookup, instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit = info match
        case MemberLookup.Contextual(source, substitution) => member(source, instances ++ substitution)
        case MemberLookup.Found(RecordMember(member, true), _) => receive(UnknownValueShape.at(member.rhs))
        case MemberLookup.Found(member, inner) =>
          fromBMS(member.memberSymbol, flow, inner, value => receive(instantiateShape(value, instances)), field.rhs, _ => (), false)(using rstate.withInstances(instances))
        case MemberLookup.Declared(member, bound, inner, annotation, positive) =>
          listenDeclaredMember(member, bound, flow, field.rhs, annotation, _ => (), false, positive, inner, N): value =>
            transportShape(instantiateShape(value, instances), inner) match
              case value: TermShape => receive(value)
              case NoShape => ()
        case MemberLookup.Dynamic(inner) => DynShape().exit(inner) match
          case value: TermShape => receive(value)
          case NoShape => ()
        case _ => ()
      actual match
        case Marked(_: UnknownValueShape, _) => receive(actual)
        case _ => member(actual.getMember(field.sym.nme), Map.empty)

  /** Function constraints reverse the parameter flow and preserve result flow.
    * Read an implementation only while checking it against its declared interface;
    * calls through that interface continue to expose only the declared result.
    */
  private[semantics] def constrainFunction(expected: DeclaredType, source: TermShape, marks: Ls[Marks])(using NewResolverState): Unit =
    val (actual, instances, _) = callableParts(source)
    actual match
      case Marked(_: InstanceShape, _) =>
        listenInstanceViews(actual)(constrainFunction(expected, _, marks))
        return
      case _ => ()
    val context = actual.applicationHead._2
    def results(listener: Listener)(using NewResolverState): Unit = actual.applicationHead._1 match
      case intro: IntroShape => intro.trm match
        case Lam(_, body) => listenTerm(body)(shape => listener(instantiateShape(shape, instances)))(using rstate.withInstances(instances))
        case _ => ()
      case ds: DefnShape => ds.defn match
        case td: TermDefinition => td.sign match
          case S(sign) => listenSignatureResult(declaredType(typeResolution(sign), Map.empty).instantiate(instances),
            if td.flags.hasResultAnnotation then 0 else td.params.length)(listener)
          case N => td.body.foreach(body => listenTerm(body)(shape => listener(instantiateShape(shape, instances)))(using rstate.withInstances(instances)))
        case _ => ()
      case _ => ()
    def matchLists(expected: DeclaredType, remaining: Ls[(ParamList, Ls[Marks])])(using NewResolverState): Unit =
      listenTypeViews(expected):
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
                  listenTypeInstances(tpe): shape =>
                    constrainParameterIn(param, shape.exit(expectedContext).enter(context), context, instances)
              params.restParam.foreach: rest =>
                val fields = declared.params.drop(params.params.length).map:
                  case S(tpe) => TupleShape.TypedField(tpe, Nil)
                  case N => TupleShape.UnknownField(callable.source, Nil)
                val suffix = if declared.hasRest
                  then TupleShape.Unknown(callable.source, Nil, UnknownValueShape.at(callable.source)) :: Nil
                  else Nil
                val tuple = TupleShape(callable.source, fields ::: suffix)(this)
                constrainParameterIn(rest, tuple.exit(expectedContext).enter(context), context, instances)
              callable.result.foreach: ret =>
                tail match
                  case Nil => results: shape =>
                    shape.exit(context).enter(expectedContext) match
                      case value: TermShape => inferTypeArguments(ret, value, marks)
                      case NoShape => ()
                  case _ => matchLists(ret, tail)
          case Nil => ()
        case Marked(record: RecordTypeShape, _) =>
          constrainRecord(record.fields, record.bindings, record.positive, actual, marks)
        case _ => ()
    actual match
      case Marked(_: UnknownValueShape, _) =>
        listenTypeViews(expected):
          case Marked(callable: CallableTypeShape, _) =>
            callable.result.foreach(ret => inferTypeArguments(ret, actual, marks))
          case _ => ()
      case Marked(givenType: CallableTypeShape, actualContext) =>
        listenTypeViews(expected):
          case Marked(wanted: CallableTypeShape, expectedContext) =>
            val domain = givenType.paramLists.head
            val expectedDomain = wanted.paramLists.head
            if domain.params.length != expectedDomain.params.length || domain.hasRest != expectedDomain.hasRest then
              resolError(expected.resolution.source, msg"Callback parameter list does not match its declared function type." -> actual.toLoc :: Nil)
            else
              domain.params.zip(expectedDomain.params).foreach:
                case (S(givenParam), S(wantedParam)) =>
                  listenTypeInstances(wantedParam): shape =>
                    shape.exit(expectedContext).enter(actualContext) match
                      case value: TermShape => inferTypeArguments(givenParam, value, context)
                      case NoShape => ()
                case _ => ()
              wanted.result.foreach: ret =>
                def receive(shape: TermShape)(using NewResolverState): Unit = shape.exit(actualContext).enter(expectedContext) match
                  case value: TermShape => inferTypeArguments(ret, value, marks)
                  case NoShape => ()
                givenType.paramLists.tail match
                  case Nil => givenType.result.foreach(listenTypeInstances(_)(receive))
                  case tail => receive(givenType.copy(paramLists = tail))
          case _ => ()
      case _ => matchLists(expected, actual.unappliedParams)

  private def listenSignatureResult(tpe: DeclaredType, count: Int)(listener: Listener)(using NewResolverState): Unit =
    if count == 0 then listenTypeInstances(tpe)(listener)
    else listenTypeViews(tpe):
      case Marked(callable: CallableTypeShape, marks) =>
        callable.result.foreach(tpe => listenSignatureResult(transportType(tpe, marks :: Nil), count - 1)(listener))
      case _ => ()

  private def tupleArrayParents(using rs: NewResolverState) = rs.tupleArrayParents
  /** A tuple is an Array whose element argument is the union of its field shapes.
    * Cache the parent before following fields: a recursive tuple can require its
    * own Array interface while one of those fields is still being resolved.
    */
  private[semantics] def tupleArrayParent(tuple: TupleShape)(using NewResolverState): NominalInstanceView =
    tupleArrayParents.get(new Identity(tuple)) match
      case S(parent) => parent
      case N =>
        val cls = prelude.builtins.Array.defn.get
        softAssert(cls.tparams.length == 1, "The builtin Array must have one element type parameter")
        val elements = new TypeResolution(tuple.source, messages => resolError(tuple.source, messages))
        val parent = NominalInstanceView(cls, Map(cls.tparams.head.sym -> declaredType(elements, Map.empty)), implicitParent(cls))(N)(this)
        tupleArrayParents(new Identity(tuple)) = parent
        tuple.segments.foreach:
          case field: TupleShape.Fixed => listenTupleField(field): value =>
            elements.publish(TypeShape.Inferred(value))
          case TupleShape.Unknown(_, marks, value) => value.exit(marks) match
            case value: TermShape => elements.publish(TypeShape.Inferred(value))
            case NoShape => ()
        parent

  /** Mutable literals share Array's existing element parameter, with an allocation
    * mark to keep distinct arrays and enclosing call activations independent.
    * Seed the interface before following elements so empty and recursive arrays
    * can receive writes. No positions or lengths survive this conversion.
    */
  private def mutableArray(source: Term.Mut, underlying: Tup)(using NewResolverState): TermShape =
    rstate.mutableArrays.get(new Identity(source)) match
      case S(array) => array
      case N =>
        val cls = prelude.builtins.Array.defn.get
        softAssert(cls.tparams.length == 1, "The builtin Array must have one element type parameter")
        val param = cls.tparams.head.sym
        val site = FlowSymbol("mutable array")(using rstate.owner)
        val context = ExitMark(ResolutionBoundary(cls.sym), S(site), NoMarks)
        val elements = new TypeResolution(source, messages => resolError(source, messages))
        elements.publish(TypeShape.Parameter(param, param.inferenceHost))
        // A nominal interface lives at the literal's use site. Its element
        // reference points back into the allocation; putting the allocation exit
        // on the whole interface would also exit a selected method's class scope
        // twice, once here and once in NominalInstanceView.getMemberImpl.
        val element = transportType(declaredType(elements, Map.empty), context :: Nil)
        val shape = NominalInstanceView(cls, Map(param -> element), implicitParent(cls))(N)(this)
        rstate.mutableArrays(new Identity(source)) = shape
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
  private[semantics] def nominalMember(view: NominalInstanceView, name: Str, receiver: Marks)(using NewResolverState): MemberLookup =
    val defn = view.defn
    // Module/object references introduce no value invocation boundary.
    val scope = defn.sym match
      case _: ModuleOrObjectSymbol => N
      case symbol => S(ResolutionBoundary(symbol))
    defn.body.members.get(name) match
      case S(member) =>
        val (location, provenance) = splitReceiverPath(defn, receiver)
        // Supplied arguments are outside the class; its parameter annotations
        // are inside. Enclosing binders keep their own lexical contexts and
        // enter the class through the annotation's explicit Capture nodes.
        val parameters = defn.tparams.map(_.sym).toSet
        val local = view.bindings.map: (symbol, bound) =>
          val transported = provenance match
            case NoMarks => bound
            case provenance: ExitMark => transportType(bound, provenance :: Nil)
          symbol -> (if parameters(symbol) && scope.nonEmpty then captureType(transported, defn.sym) else transported)
        MemberLookup.Declared(member, local, scope.toList.map(ExitMark(_, N, NoMarks)), view.annotation, true)
          .withMarks(location match
            case NoMarks => Nil
            case location: SomeMarks => location :: Nil)
      case N =>
        (name.toIntOption, arrayElementType(view)) match
          // An element's value keeps its whole path, including its provenance.
          case (S(index), S(element)) if index >= 0 =>
            MemberLookup.Indexed(TupleShape.TypedField(element, Nil), Nil).withMarks(receiver :: Nil)
          case _ =>
            // The parent is referenced inside the class, like its own members'
            // annotations: `class Int extends Num` captures `Num` into Int's
            // scope. An inherited member exits that scope before the receiver
            // path applies, just like an own member.
            val exit = scope.fold[Marks](NoMarks)(ExitMark(_, N, NoMarks))
            val inherited = view.parent.fold[MemberLookup](MemberLookup.Missing): parent =>
              val Marked(parentView, inner) = parent
              InstanceShape(extremeType(false)).exit(inner).exit(exit).exit(receiver) match
                case Marked(_, path) => parentView.getMemberThrough(name, path)
                // The parent interface is not reachable through this receiver;
                // applying these marks to its members yields no candidates.
                case NoShape => parentView.getMember(name).withMarks(inner :: exit :: receiver :: Nil)
            inherited.withAnnotation(view.annotation)

  /** Split a receiver path into the path from `defn`'s definition to the consumer,
    * and the innermost exits of scopes not enclosing that definition. Exits are
    * applied innermost first, so once a path leaves an enclosing scope of `defn`,
    * it cannot leave a scope that does not enclose `defn`.
    */
  private def splitReceiverPath(defn: ClassLikeDef, receiver: Marks)(using NewResolverState): (Marks, ExitMarks) =
    val enclosing = defn.sym.getState.newResolverState.lexicalBoundaries.get(defn.sym).getOrElse(
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

  private[semantics] def arrayElementType(array: NominalInstanceView): Opt[DeclaredType] =
    val cls = prelude.builtins.Array.defn.get
    array.ancestor(cls).flatMap(_.bindings.get(cls.tparams.head.sym))

  /** Element writes constrain the same declared parameter as Array's methods.
    * An annotated element type receives input constraints without exposing
    * additional members from the assigned value.
    */
  private[semantics] def assignArrayElement(lhs: Term, rhs: Term)(using NewResolverState): Unit =
    val receiver = lhs match
      case NewSel(prefix, id, N) if id.name.toIntOption.exists(_ >= 0) => S(prefix)
      case DynSel(prefix, _, true) => S(prefix)
      case _ => N
    receiver.foreach: prefix =>
      listenTermViews(prefix): array =>
        val (head, context) = array.applicationHead
        head match
          case nominal: NominalInstanceView => arrayElementType(nominal).foreach: element =>
            listenTerm(rhs): value =>
              value.enter(context) match
                case value: TermShape => inferTypeArguments(element, value, context)
                case NoShape => ()
          case _ => ()

  private[semantics] def listenTupleField(field: TupleShape.Fixed)(listener: Listener)(using NewResolverState): Unit =
    def receive(shape: TermShape)(using NewResolverState): Unit = transportShape(shape, field.marks) match
      case value: TermShape => listener(value)
      case NoShape => ()
    field match
      case TupleShape.Field(field, _) => listenTerm(field.term)(receive)
      case TupleShape.TypedField(tpe, _) => listenTypeInstances(tpe)(receive)
      case TupleShape.UnknownField(source, _) => receive(UnknownValueShape.at(source))
      case TupleShape.ValueField(value, _) => receive(value)
      case TupleShape.ViewedField(source, instances, _) =>
        listenTupleField(source)(value => receive(instantiateShape(value, instances)))(using rstate.withInstances(instances))

  /** Array spreads have unknown length, but their declared element type still
    * constrains every element. Never recover elements from constructor values:
    * Arrays are mutable, and the one-number constructor creates empty slots.
    */
  private[semantics] def listenArrayElements(shape: TermShape)(listener: Listener)(using NewResolverState): Bool =
    val cls = prelude.builtins.Array.defn.get
    softAssert(cls.tparams.length == 1, "The builtin Array must have one element type parameter")
    val param = cls.tparams.head.sym
    val (source, instances) = contextualParts(shape)
    val Marked(value, _) = source
    // Supplied and inferred element types share the allocation's parameter.
    // Outer marks transport its bounds through callers without changing which
    // parameter instance the allocation selected.
    val head = value.applicationHead._1
    val context = source.applicationHead._2
    def receive(element: TermShape)(using NewResolverState): Unit = transportShape(element, context) match
      case value: TermShape => listener(value)
      case NoShape => ()
    head match
      case tuple: TupleShape =>
        listenArrayElements(tuple.arrayParent)(receive)
      case nominal: NominalInstanceView => nominal.ancestor(cls) match
        case S(array) =>
          array.bindings.get(param) match
            case S(bound) =>
              listenTypeInstances(bound)(receive)
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
  def zipArgs(mss: Ls[Marks], ps: Ls[Param], r: Opt[Param], args: Term, src: Term, funSh: TermShape)(using NewResolverState): Unit =
    zipArgsIn(mss, ps, r, args, src, funSh, rstate.instances)

  private def zipArgsIn(mss: Ls[Marks], ps: Ls[Param], r: Opt[Param], args: Term, src: Term, funSh: TermShape,
      instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit =
    val params = ps ::: r.toList
    zipArgumentShapes(mss, ps.length, r.nonEmpty, args, src, funSh): (index, shape) =>
      constrainParameterIn(params(index), shape, mss, instances)

  private[semantics] def constrainParameter(p: Param, shape: TermShape | NoShape, marks: Ls[Marks])(using NewResolverState): Unit =
    constrainParameterIn(p, shape, marks, rstate.instances)

  private def constrainParameterIn(p: Param, shape: TermShape | NoShape, marks: Ls[Marks],
      instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit =
    shape match
      case NoShape => ()
      case sh: TermShape =>
        parameterSignature(p) match
          case S(tpe) => inferTypeArguments(tpe.instantiate(instances), sh, marks)
          case N => publishParameter(p.sym, sh)(using rstate.withInstances(instances))

  private[semantics] def parameterSignature(p: Param)(using NewResolverState): Opt[DeclaredType] =
    p.sign.map(sign => declaredType(typeResolution(sign), Map.empty)).orElse(signatureParameters.get(p.sym))
      .orElse(p.sym.getState.newResolverState.signatureParameters.get(p.sym))

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
              if approximate then TupleShape.Unknown(tuple.source, Nil, UnknownValueShape.at(tuple.source)) :: suffix else suffix
        val remaining = drop(segments, expectedCount, true)
        val rest = if expectedCount == 0 then tuple else TupleShape.restView(tuple, remaining)(this)
        publish(expectedCount, rest.exit(marks).enter(mss))
    checkArgumentArity(args, expectedCount, hasRest, src, funSh):
      case (tuple, marks) => matchSegments(tuple, marks)
  
  private def checkArgumentArity(args: Term, expected: Int, rest: Bool, src: Term,
      callable: TermShape)(matched: ShapeListener[(TupleShape, Marks)])(using NewResolverState): Unit =
    val reportKey = new Object
    listenTermViews(args):
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
                  fromBMS(bms, FlowSymbol.pat()(using rstate.owner), sh.markss, valuePattern, lhs, _ => (), false)
          case sh: TermShape => valuePattern(sh)
  
  /** Propagate possible values to pattern bindings. Constructor tests filter by
    * nominal class; guards and literal tests may conservatively retain shapes.
    * Both scrutinee and constructor shapes can arrive after this registration. */
  def matchShapePat(shape: Shape, pattern: Pattern)(matched: ShapeListener[Shape])(using NewResolverState): Unit =
    shape match
      case value @ Marked(_: InstanceShape, _) if pattern.isInstanceOf[Pattern.Constructor] || pattern.isInstanceOf[Pattern.Tuple] =>
        listenInstanceViews(value)(matchShapePat(_, pattern)(matched))
        return
      case _ => ()
    pattern match
      case al @ Pattern.Alias(pat, _) =>
        matchShapePat(shape, pat): sh =>
          // Rejected duplicate/negated bindings have no allocated symbol. Pattern
          // validation already reports them; only valid bindings receive flow.
          al.symbolOption.foreach: symbol =>
            publishActivated(symbol, sh)
          matched(sh)
      case Pattern.Wildcard() | Pattern.Literal(_) => matched(shape)
      case Pattern.Chain(left, right) =>
        matchShapePat(shape, left)(sh => matchShapePat(sh, right)(matched))
      case Pattern.Composition(false, left, right) =>
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
            def check(sh: TermShape, unknown: Opt[TermShape])(using NewResolverState): Unit =
              if sh.isInstanceOfClass(cls) then
                fs.foreach: (bms, pat) =>
                  def member(info: MemberLookup, instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit = info match
                    case MemberLookup.Contextual(source, substitution) => member(source, instances ++ substitution)
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
                                  UnknownValueShape(origin.source)(origin.provenance.via(
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
                  member(sh.getMember(bms.nme), Map.empty)
                matched(sh)
            def narrow(sh: TermShape)(using NewResolverState): Unit = sh match
              case Marked(unknown: UnknownValueShape, _) =>
                // A class test can succeed for an external input. Its fields then
                // expose their declarations, not shapes observed in local calls.
                // Unknown type arguments retain the original diagnostic witness.
                val base = new TypeResolution(ctor.target, messages => resolError(ctor.target, messages))
                base.publish(TypeShape.Nominal(cls))
                val arg = new TypeResolution(unknown.source, messages => resolError(unknown.source, messages))
                arg.publish(TypeShape.Inferred(sh))
                val applied = new TypeResolution(ctor.target, messages => resolError(ctor.target, messages))
                applied.publish(TypeShape.Applied(base, cls.tparams.map(_ => arg)))
                listenTypeViews(declaredType(applied, Map.empty))(check(_, S(sh)))
              case Marked(opaque: OpaqueTypeShape, marks) =>
                UnknownValueShape.at(opaque.source).exit(marks) match
                  case value: TermShape => narrow(value)
                  case NoShape => ()
              case Marked(nominal: NominalInstanceView, _) if !nominal.isInstanceOfClass(cls) =>
                // A base-class annotation can contain a subclass instance. Its
                // constructor test exposes that subclass's declarations; omitted
                // subclass type arguments remain abstract, never inferred from
                // unrelated constructor calls elsewhere in the unit.
                // Reuse the abstract instantiation when recursive flow reaches
                // this test again, so its omitted arguments have stable identities.
                val tested = rstate.patternTypes.getOrElseUpdate((new Identity(ctor), cls.sym), {
                  val resolution = new TypeResolution(ctor.target, messages => resolError(ctor.target, messages))
                  resolution.publish(TypeShape.Nominal(cls))
                  declaredType(resolution, Map.empty)
                })
                listenTypeViews(tested): candidate =>
                  if candidate.isInstanceOfClass(nominal.defn) then check(candidate, N)
              case _ => check(sh, N)
            shape match
              case sh: TermShape => narrow(sh)
              case sh: SymShape => fromSymbol(sh, narrow, ctor.target, _ => (), false)
        ctor.subscribeToShapes(listenConstructor)
      case Pattern.Tuple(leading, spread) =>
        val trailing = spread.fold(Nil)(_._3)
        val required = leading.length + trailing.length
        def tupleBindings(tuple: TupleShape, marks: Marks)(using NewResolverState): Unit =
          val segments = tuple.segments
          val known = segments.count(_.isInstanceOf[TupleShape.Fixed])
          val uncertain = known != segments.length
          if (uncertain || known >= required) && (spread.nonEmpty || known <= required) then
            def bind(segment: TupleShape.Segment, p: Pattern)(using NewResolverState): Unit =
              def receive(value: TermShape)(using NewResolverState): Unit = value.exit(marks) match
                case value: TermShape => matchShapePat(value, p)(_ => ())
                case NoShape => ()
              segment match
                case field: TupleShape.Fixed => listenTupleField(field)(receive)
                case TupleShape.Unknown(_, inner, value) => value.exit(inner) match
                  case value: TermShape => receive(value)
                  case NoShape => ()
            // A spread can move subsequent fields. Retain every possible position
            // rather than treating the first unknown segment as the only candidate.
            def positions(xs: Ls[TupleShape.Segment], ps: Ls[Pattern])(using NewResolverState): Unit =
              var before = 0
              var unknownBefore = false
              xs.foreach:
                case field: TupleShape.Fixed =>
                  ps.iterator.zipWithIndex.foreach: (p, index) =>
                    if index >= before && (if !unknownBefore then index == before
                        else spread.nonEmpty || index <= before + required - known) then bind(field, p)
                  before += 1
                case unknown: TupleShape.Unknown =>
                  ps.drop(before).foreach(bind(unknown, _))
                  unknownBefore = true
            positions(segments, leading)
            positions(segments.reverse, trailing.reverse)
            spread.foreach: (_, p, _) =>
              // Stop trimming at an unknown segment: its possible lengths include
              // consuming the remaining prefix/suffix, so all later values may remain.
              def trim(xs: Ls[TupleShape.Segment], count: Int): Ls[TupleShape.Segment] =
                if count == 0 then xs else xs match
                  case (_: TupleShape.Fixed) :: tail => trim(tail, count - 1)
                  case _ => xs
              val middle = trim(trim(segments, leading.length).reverse, trailing.length).reverse
              // Reusing an unchanged view also bounds recursive tail matching on
              // arrays with unknown length; wrapping it again would grow forever.
              val rest = if middle == segments then tuple
                else TupleShape.restView(tuple, middle)(this)
              rest.exit(marks) match
                case value: TermShape => matchShapePat(value, p)(_ => ())
                case NoShape => ()
            tuple.exit(marks) match
              case value: TermShape => matched(value)
              case NoShape => ()
        def narrow(value: TermShape)(using NewResolverState): Unit = value match
          case Marked(tuple: TupleShape, marks) => tupleBindings(tuple, marks)
          case Marked(unknown: UnknownValueShape, marks) =>
            tupleBindings(TupleShape(unknown.source,
              TupleShape.Unknown(unknown.source, Nil, unknown) :: Nil)(this), marks)
          case Marked(nominal: NominalInstanceView, marks) =>
            nominal.ancestor(prelude.builtins.Array.defn.get).foreach: array =>
              array.bindings.get(prelude.builtins.Array.defn.get.tparams.head.sym).foreach: element =>
                listenTypeViews(element):
                  case Marked(shape, inner) =>
                    tupleBindings(TupleShape(element.resolution.source,
                      TupleShape.Unknown(element.resolution.source, inner :: Nil, shape) :: Nil)(this), marks)
          case _ => ()
        shape match
          case value: TermShape => narrow(value)
          case sym: SymShape => fromSymbol(sym, narrow, Term.Missing, _ => (), false)
      case _ =>
        raise(ErrorReport(msg"This pattern is not supported during shape resolution." -> pattern.toLoc :: Nil))
  
  def matchScrutPat(scrutinee: Term.Ref, pattern: Pattern)(using NewResolverState): Unit = if newResolution then
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

  private def instantiateDefinition(definition: DefnShape, site: FlowSymbol, marks: Ls[Marks],
      captured: Map[VarSymbol, TypeParameterInstance], supplied: Opt[Ls[DeclaredType]])
      (using NewResolverState): Map[VarSymbol, TypeParameterInstance] =
    val (owner, parameters) = definitionParameters(definition)
    instantiateParameters(owner, parameters, site, marks, captured, supplied)

  private def instantiateParameters(owner: AnyDefinitionSymbol, parameters: Ls[VarSymbol], site: FlowSymbol,
      marks: Ls[Marks], captured: Map[VarSymbol, TypeParameterInstance], supplied: Opt[Ls[DeclaredType]])
      (using NewResolverState): Map[VarSymbol, TypeParameterInstance] =
    val substitution = captured ++ rstate.instantiateTypeParameters(owner, site, parameters)
    supplied.foreach: arguments =>
      bindTypeArguments(parameters.map: parameter =>
        val instance = substitution(parameter)
        TypeShape.Parameter(instance, instance.inferenceHost)
      , marks, arguments)
    if parameters.nonEmpty && rstate.inferredInstantiations.add((owner, site, substitution, marks)) then
      parameters.foreach: parameter =>
        val instance = substitution(parameter)
        listenTypeArgument(parameter): bound =>
          bound.applicationHead._1 match
            case _: RigidTypeShape => ()
            case _ => inferTypeArguments(instanceType(instance), instantiateShape(bound, substitution), marks)
    substitution

  def appShape(source: TermShape, args: Term, res: App)(using NewResolverState): Unit =
    val callerInstances = rstate.instances
    val (lhs, lexical, specialized) = callableParts(source)
    val captured = callerInstances ++ lexical
    val instances = lhs match
      case Marked(definition: DefnShape, _) if !specialized =>
        instantiateDefinition(definition, res.resSym, lhs.applicationHead._2, captured, N)
      case Marked(construction: NewShape, _) if construction.argss.isEmpty && !construction.isSaturated && construction.supplied.isEmpty =>
        instantiateDefinition(construction.receiver, res.resSym, lhs.applicationHead._2, captured, N)
      case _ => captured
    def publish(value: TermShape)(using NewResolverState): Unit =
      publishViewed(res, value, instances)(using rstate.withInstances(callerInstances))
    lhs match
      case Marked(_: InstanceShape, _) =>
        listenInstanceViews(instantiateShape(lhs, instances))(appShape(_, args, res))
        return
      case _ => ()
    // Only explicit dynamic values authorize calls without a known interface.
    // An unknown alternative must invalidate the call even if other candidates
    // happen to be callable in this compilation unit.
    lhs match
      case Marked(_: DynShape, _) =>
        publish(lhs)
        return
      case _ => ()
    lhs match
      case Marked(original: CallableTypeShape, context) =>
        val viewed = instantiateShape(original, instances) match
          case callable: CallableTypeShape => callable
          case _ => lastWords("A callable view must remain callable")
        val callable = instantiateCallable(viewed, res.resSym, context :: Nil)
        val ps = callable.paramLists.head
        zipArgumentShapes(context :: Nil, ps.params.length, ps.hasRest, args, res, lhs): (index, value) =>
          (if index < ps.params.length then ps.params(index) else ps.rest).foreach: tpe =>
            value match
              case value: TermShape => inferTypeArguments(tpe, value, context :: Nil)
              case NoShape => ()
        def publish(shape: TermShape)(using NewResolverState): Unit = transportShape(shape, context :: Nil) match
          case value: TermShape =>
            publishViewed(res, value, Map.empty)(using rstate.withInstances(callerInstances))
          case NoShape => ()
        callable.paramLists.tail match
          case Nil => callable.result match
            case S(tpe) => listenTypeInstances(tpe)(publish)
            case N => publish(UnknownValueShape.at(callable.source))
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
      zipArgsIn(mss, ps.params, ps.restParam, args, res, lhs, instances)
    log(s"appShape isSaturated? ${sh.isSaturated}; head? ${sh.applicationHead}")
    def register(using NewResolverState) = publish(sh)
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
      val notes = lhs.applicationHead._1 match
        case unknown: UnknownValueShape => unknown.provenance.diagnosticNotes
        case _ => Nil
      resolError(res, (message -> lhs.toLoc) :: notes)
    if sh.isSaturated then
      def go(body: Term, mss: Ls[Marks])(using NewResolverState) =
        listenTerm(body): sh =>
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
                listenSignatureResult(declaredType(typeResolution(sign), Map.empty).instantiate(instances), count): result =>
                  transportShape(result, mss) match
                    case value: TermShape =>
                      publish(value)
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
  
  private def publishActivated(host: ShapeHost, source: Shape)(using NewResolverState): Unit =
    val shape = if rstate.instances.isEmpty then source else source match
      case value: TermShape => ActivatedShape(value, rstate.instances)
      case symbol: SymShape =>
        rstate.activatedSymbols.getOrElseUpdate((symbol, rstate.instances), ActivatedSymShape(symbol, rstate.instances))
    if host.currentShapes.add(shape) then host.notifyShapeListeners(shape)

  private def publishViewed(host: ShapeHost, source: Shape,
      instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit =
    val shape = source match
      case value: TermShape => instantiateShape(value, instances)
      case symbol: SymShape if instances.nonEmpty =>
        val (original, substitution) = symbol match
          case contextual: ContextualSymShape => (contextual.source, instances ++ contextual.instances)
          case _ => (symbol, instances)
        rstate.contextualSymbols.getOrElseUpdate((original, substitution), ContextualSymShape(original, substitution))
      case _ => source
    publishActivated(host, shape)

  private def publishMember(host: NewResolvable & ShapeHost, member: BlockMemberSymbol | RecordMember,
      flow: FlowSymbol, marks: Ls[Marks], instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit =
    def publish(shape: Shape)(using NewResolverState): Unit = publishViewed(host, shape, instances)
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
        publish(UnknownValueShape.at(field.rhs))

  private def publishDeclared(host: NewResolvable & ShapeHost, member: BlockMemberSymbol, flow: FlowSymbol,
      bindings: Map[VarSymbol, DeclaredType], marks: Ls[Marks], annotation: Opt[Term], positive: Bool,
      instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit =
    // Keep one diagnostic witness per semantic candidate, as for unknown values.
    // A different annotation location must not create additional inference flow.
    val shape = declaredSymShapes.getOrElseUpdate((member, flow, marks, bindings, positive),
      DeclaredSymShape(member, flow, marks, bindings, annotation, positive))
    publishViewed(host, shape, instances)

  private def publishDynamic(host: NewResolvable & ShapeHost, marks: Ls[Marks])(using NewResolverState): Unit =
    DynShape().exit(marks) match
      case shape: TermShape =>
        publishActivated(host, shape)
      case NoShape => ()

  private def unknownMember(host: NewResolvable, name: Str, reason: MemberLookup.Uncertainty, provenance: ShapeProvenance)(using NewResolverState): Unit = if !rstate.hasError(host) then
    rstate.markError(host)
    val message = reason match
      case MemberLookup.Uncertainty.ValueShape =>
        msg"Cannot resolve member '$name' of a value with unknown shape."
      case MemberLookup.Uncertainty.RecordOverwrite =>
        msg"Cannot resolve member '$name' across a computed key or unknown record spread."
    resolError(host, (message -> N) :: provenance.diagnosticNotes)

  def unresolvedRef(ref: UnresolvedRef)(using NewResolverState): Unit =
    ref.prefixes.foreach: prefix =>
      listenReceiver(prefix): shape =>
        def member(info: MemberLookup, instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit = info match
          case MemberLookup.Contextual(source, substitution) => member(source, instances ++ substitution)
          case MemberLookup.Found(member, marks) if rstate.canResolve(ref) || ref.resolvedMembers.contains(prefix -> member.memberSymbol) =>
            val candidate = prefix -> member.memberSymbol
            rstate.recordResolution(ref, ref.resolvedMembers.contains(candidate))(ref.resolvedMembers ::= candidate)
            publishMember(ref, member, ref.resSym, marks, instances)
          case MemberLookup.Declared(member, bindings, marks, annotation, positive) if rstate.canResolve(ref) || ref.resolvedMembers.contains(prefix -> member) =>
            val candidate = prefix -> member
            rstate.recordResolution(ref, ref.resolvedMembers.contains(candidate))(ref.resolvedMembers ::= candidate)
            publishDeclared(ref, member, ref.resSym, bindings, marks, annotation, positive, instances)
          case MemberLookup.Indexed(_, _) if rstate.canResolve(ref) =>
            resolError(ref, msg"Tuple elements must be selected by index." -> ref.toLoc :: Nil)
          case MemberLookup.Dynamic(marks) if rstate.canResolve(ref) || ref.dynamicPrefixes.contains(prefix) =>
            rstate.recordResolution(ref, ref.dynamicPrefixes.contains(prefix))(ref.dynamicPrefixes ::= prefix)
            publishDynamic(ref, marks)
          case MemberLookup.Missing =>
            // A known miss in one wildcard source is not an error: another may
            // provide the name. Lowering diagnoses references with no candidates.
            ()
          case MemberLookup.Unknown(reason, provenance) => unknownMember(ref, ref.id.name, reason, provenance)

          case _ => () // Completed references only route their selected members.
        member(shape.getMember(ref.id.name), Map.empty)

  /** Inspect an overload set only once its definitions have all been published. */
  private def completedClass(shape: SymShape)(selected: ShapeListener[ClassDef], absent: () => NewResolverState ?=> Unit)(using NewResolverState): Unit =
    shape.sym.onComplete: () =>
      shape.sym.asCls match
        case S(cls) => selected(cls.defn.get)
        case N => absent()

  /** Class interpretations wait for completed overload sets, independently of term
    * companions. Aliases can supply constructor shapes; applied instances cannot.
    * Capture marks are retained for subsequent instance-member lookup. */
  private case class ClassReference(definition: ClassDef, marks: Ls[Marks],
      instances: Map[VarSymbol, TypeParameterInstance], supplied: Opt[Ls[DeclaredType]])

  private def listenClass(trm: Term)(selected: ShapeListener[ClassReference], reject: ShapeListener[Shape])(using NewResolverState): Unit =
    def select(ref: ClassReference)(using NewResolverState): Unit =
      trm.classHead match
        case target: NewResolvable =>
          rstate.recordResolution(target, target.resolvedTargets.contains(ref.definition.sym))(
            target.resolvedTargets ::= ref.definition.sym)
        case _ => ()
      selected(ref)
    def value(sh: TermShape)(using NewResolverState): Unit =
      val (source, instances) = contextualParts(sh)
      val marks = source.applicationHead._2
      def fromDefinition(ds: DefnShape, supplied: Opt[Ls[DeclaredType]], captured: Map[VarSymbol, TypeParameterInstance]): Unit =
        ds.clsDef match
          case S(cls: ClassDef) => select(ClassReference(cls, marks, instances ++ captured, supplied))
          case _ => reject(sh)
      source match
        case Marked(ds: DefnShape, _) => fromDefinition(ds, N, Map.empty)
        case Marked(specialized: SpecializedShape, _) =>
          fromDefinition(specialized.declaration, S(specialized.arguments), specialized.instances)
        case _ => reject(sh)
    trm match
      case application @ TyApp(base, args) => listenClass(base)(ref =>
        val count = if ref.supplied.nonEmpty then 0 else ref.definition.tparams.length
        if count != args.length && rstate.typeArgumentArityErrors.add((new Identity(application), count)) then
          resolError(trm, msg"Class '${ref.definition.sym.nme}' expected ${count} type ${
            "argument".pluralized(count)}, but got ${args.length}" -> ref.definition.toLoc :: Nil)
        val supplied = args.map(arg => declaredType(typeResolution(arg), Map.empty).instantiate(rstate.instances))
        if ref.supplied.nonEmpty then select(ref)
        else
          val instances = instantiateParameters(ref.definition.sym, ref.definition.tparams.map(_.sym),
            rstate.typeApplicationSite(application), ref.marks, rstate.instances ++ ref.instances, S(supplied))
          select(ref.copy(instances = instances, supplied = S(supplied)))
      , reject)
      case Capture(base, thru) =>
        listenClass(base)(ref => select(ref.copy(marks =
          ref.marks ::: EntryMark(ResolutionBoundary(thru), N, NoMarks) :: Nil)), reject)
      case _ => listen(trm):
        case sh: SymShape =>
          completedClass(sh)(cls => select(ClassReference(cls,
            ExitMark(ResolutionBoundary(cls.sym), S(sh.resSym), NoMarks) :: sh.markss,
            sh match
              case contextual: ContextualSymShape => contextual.instances
              case _ => Map.empty
            , N)),
            () => fromSymbol(sh, value, trm, _ => (), false))
        case sh: TermShape => value(sh)

  def newSel(sel: NewSel)(using NewResolverState): Unit =
    log(s"newSel? sel = ${sel.showDbg}")
    def member(info: MemberLookup, description: Message, loc: Opt[Loc],
        instances: Map[VarSymbol, TypeParameterInstance])(using NewResolverState): Unit = info match
      case MemberLookup.Contextual(source, substitution) => member(source, description, loc, instances ++ substitution)
      case MemberLookup.Found(bms, marks) if rstate.canResolve(sel) || sel.resolvedMembers.contains(bms.memberSymbol) =>
        log(s"newSel member: bms = ${bms.memberSymbol.showDbg}, mss = ${marks.map(_.showDbg)}")
        rstate.recordResolution(sel, sel.resolvedMembers.contains(bms.memberSymbol))(sel.resolvedMembers ::= bms.memberSymbol)
        publishMember(sel, bms, sel.resSym, marks, instances)
      case MemberLookup.Declared(member, bindings, marks, annotation, positive) if rstate.canResolve(sel) || sel.resolvedMembers.contains(member) =>
        rstate.recordResolution(sel, sel.resolvedMembers.contains(member))(sel.resolvedMembers ::= member)
        publishDeclared(sel, member, sel.resSym, bindings, marks, annotation, positive, instances)
      case MemberLookup.Indexed(field, marks) if rstate.canResolve(sel) || sel.tupleIndex == sel.id.name.toIntOption =>
        val index = sel.id.name.toIntOption
        softAssert(index.exists(_ >= 0), "Tuple lookup must identify a nonnegative index")
        rstate.recordResolution(sel, sel.tupleIndex == index)(sel.tupleIndex = index)
        listenTupleField(field): shape =>
          transportShape(shape, marks) match
            case value: TermShape =>
              publishViewed(sel, value, instances)
            case NoShape => ()
      case MemberLookup.Dynamic(marks) if rstate.canResolve(sel) || sel.hasDynamicTarget =>
        rstate.recordResolution(sel, sel.hasDynamicTarget)(sel.hasDynamicTarget = true)
        publishDynamic(sel, marks)
      case MemberLookup.Missing if rstate.canResolve(sel) =>
        rstate.markError(sel)
        resolError(sel, msg"$description does not contain member '${sel.id.name}'" -> loc :: Nil)
      case MemberLookup.Unknown(reason, provenance) => unknownMember(sel, sel.id.name, reason, provenance)
      // Later activations still transport field values through the compiled
      // selection, but cannot choose a different member for that old syntax.
      case _ => ()
    sel.cls match
      case N => listenReceiver(sel.prefix): shape =>
        log(s"newSel: sel = ${sel.showDbg}, shape = ${shape.shwDbg}")
        member(shape.getMember(sel.id.name), msg"${shape.describe.capitalize}", shape.toLoc, Map.empty)
      case S(cls) =>
        listenClass(cls)(ref =>
          val cd = ref.definition
          val marks = ref.marks
          val candidate = cd.sym -> marks
          rstate.recordResolution(sel, sel.resolvedClasses.contains(candidate))(sel.resolvedClasses ::= candidate)
          listenExt(cd, ext =>
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
                listenTermViews(sel.prefix): receiver =>
                  val selected = receiver match
                    case Marked(nominal: NominalInstanceView, context) =>
                      nominal.ancestor(cd) match
                        case S(view) => view.getMember(sel.id.name).withAnnotation(nominal.annotation).withMarks(context :: Nil)
                        case N =>
                          // An explicit projection can name a narrower class, but
                          // it cannot recover that class's implementation arguments.
                          val opaque = abstractType(new TypeResolution(sel, msgs => resolError(sel, msgs)))
                          MemberLookup.Declared(bms, cd.tparams.map(_.sym -> opaque).toMap, context :: Nil, nominal.annotation, true)
                    case _ => info
                  member(selected, msg"Class '${cd.sym.nme}'", cd.toLoc, Map.empty)
              case _ => member(info, msg"Class '${cd.sym.nme}'", cd.toLoc, Map.empty))
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
    listenClass(nw.cls)(ref =>
      val cd = ref.definition
      val marks = ref.marks
      val callerInstances = rstate.instances
      listenExt(cd, extsh =>
        val dsh = constructorShape(cd, extsh)
        val captured = callerInstances ++ ref.instances
        // Explicit type arguments already consumed this scheme. Otherwise an
        // unapplied constructor waits for its first term application.
        val instances = if ref.supplied.nonEmpty || (nw.args.isEmpty && dsh.unappliedParams.nonEmpty) then captured
          else instantiateDefinition(dsh, nw.resSym, marks, captured, N)
        val sh = newShapes.getOrElseUpdate((cd.sym, marks, nw.resSym, ref.supplied),
          NewShape(dsh, cd.sym, marks, nw.args, nw, ref.supplied))
        if rstate.constructorApplications.add((sh, instances)) then
          dsh.unappliedParams.lazyZip(nw.args).foreach:
            case ((ps, _), args) => zipArgsIn(marks, ps.params, ps.restParam, args, nw, dsh, instances)
        publishViewed(nw, sh, instances)(using rstate.withInstances(callerInstances))
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
          publishActivated(sym, sh)
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
      publishActivated(to, sh)
  
  // Classes without an explicit parent expose Object's declarations. Share this
  // root interface between inferred instances, nominal annotations, and this-values;
  // Object itself must terminate the chain. This does not add a runtime constructor call.
  private lazy val objectShape = NominalInstanceView(prelude.builtins.Object.defn.get, Map.empty, N)(N)(this)
  private def implicitParent(defn: ClassLikeDef): Opt[TermShape] =
    if defn.sym is prelude.builtins.Object then N else S(objectShape)

  def listenExt(defn: ClassLikeDef, listener: ShapeListener[Opt[TermShape]])(using NewResolverState): Unit =
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
  private def instanceBindings(td: TermDefinition)(using NewResolverState): Map[VarSymbol, DeclaredType] =
    td.tsym.owner.toList.flatMap(_.asDefnSym.defn.toList).flatMap(_.tparams).map: param =>
      val symbol = rstate.instances.getOrElse(param.sym, param.sym)
      param.sym -> parameterType(TypeShape.Parameter(symbol, symbol.inferenceHost))
    .toMap

  private def fromSymbol(shape: SymShape, listener: Listener, source: Term,
      selected: ShapeListener[DefinitionSymbol[?]], receiver: Bool)(using NewResolverState): Unit =
    fromSymbolAt(shape, listener, source, selected, receiver, N)

  private def fromSymbolAt(shape: SymShape, listener: Listener, source: Term,
      selected: ShapeListener[DefinitionSymbol[?]], receiver: Bool,
      specialization: Opt[(FlowSymbol, Ls[DeclaredType])])(using NewResolverState): Unit = shape match
    case contextual: ContextualSymShape =>
      fromSymbolAt(contextual.source, value => listener(instantiateShape(value, contextual.instances)),
        source, selected, receiver, specialization)(using rstate.withInstances(contextual.instances))
    case declared: DeclaredSymShape =>
      listenDeclaredMember(shape.sym, declared.bindings, shape.resSym, source, declared.annotation, selected, receiver, declared.positive, shape.markss, specialization): value =>
        transportShape(value, shape.markss) match
          case value: TermShape => listener(value)
          case NoShape => ()
    case _ => fromBMSAt(shape.sym, shape.resSym, shape.markss, listener, source, selected, receiver, specialization)

  def fromBMS(bms: BlockMemberSymbol, resSym: FlowSymbol, markss: Ls[Marks], listener: Listener,
      trm: Term, selected: ShapeListener[DefinitionSymbol[?]], receiver: Bool)(using NewResolverState): Unit =
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
    def signatureBinders(sign: Term): Ls[VarSymbol] = sign match
      case Forall(parameters, _, body) => parameters.map(_.sym) ::: signatureBinders(body)
      case _ => Nil
    td.tparams.toList.flatten.map(_.sym) :::
      (if td.flags.hasResultAnnotation then Nil else td.sign.toList.flatMap(signatureBinders))

  private def instantiateByName(td: TermDefinition, site: FlowSymbol, marks: Ls[Marks],
      specialization: Opt[(FlowSymbol, Ls[DeclaredType])])(using NewResolverState): Map[VarSymbol, TypeParameterInstance] =
    instantiateParameters(td.tsym, definitionBinders(td), specialization.fold(site)(_._1),
      marks, rstate.instances, specialization.map(_._2))

  private def fromBMSAt(bms: BlockMemberSymbol, resSym: FlowSymbol, markss: Ls[Marks], listener: Listener,
      trm: Term, selected: ShapeListener[DefinitionSymbol[?]], receiver: Bool,
      specialization: Opt[(FlowSymbol, Ls[DeclaredType])])(using NewResolverState): Unit =
    log(s"listenBMS: bms = ${bms.describe}")
    bms.onComplete: () =>
      log(s"listenedBMS: bms = ${bms.describe}")
      valueTarget(bms, receiver) match
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
          (exited match
            case value: TermShape => transportShape(value, markss)
            case NoShape => NoShape) match
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
          val callerInstances = rstate.instances
          val instances = if isByName(td) then instantiateByName(td, resSym,
            ExitMark(ResolutionBoundary(td.tsym), S(resSym), NoMarks) :: markss, specialization)
            else callerInstances -- td.tparams.toList.flatten.map(_.sym)
          def receive(shape: TermShape)(using NewResolverState): Unit =
            wrappedListener(instantiateShape(shape, instances))(using rstate.withInstances(callerInstances))
          resultSignature(td) match
            case S(sign) =>
              val result = declaredType(typeResolution(sign), Map.empty).instantiate(instances)
              val tpe = if isByName(td) then result else quantifiedType(result, td.tparams.toList.flatten.map(_.sym))
              listenTypeInstances(tpe): shape =>
                td.tsym.decl match
                  case S(_: Param) => receive(MarkedShape.enter(shape, ResolutionBoundary(td.tsym), N))
                  case _ => receive(shape)
            case N => td.body.foreach: body =>
              listenTerm(body)(shape =>
                // Legacy synthesized fields use a plain reference to their
                // constructor parameter. Supply the field capture explicitly;
                // new-resolution fields already carry it in their body syntax.
                val captured = (td.tsym.decl, body) match
                  case (S(_: Param), Ref(_: VarSymbol)) =>
                    MarkedShape.enter(shape, ResolutionBoundary(td.tsym), N)
                  case _ => shape
                receive(captured)
              )(using rstate.withInstances(instances))
        case S(d: TermDefinition) if !d.tsym.isInstanceOf[ClassCtorSymbol] &&
            ((d.sign.nonEmpty && (!d.flags.hasResultAnnotation || d.params.forall(ps =>
              (ps.params ::: ps.restParam.toList).forall(_.sign.nonEmpty)))) ||
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

  /** Values prefer the function/constructor overload; selection receivers prefer
    * the module overload. Keep that choice through captures so nested functions
    * and opened names use the same interpretation as direct references.
    */
  private def valueTarget(member: BlockMemberSymbol, receiver: Bool): Opt[DefinitionSymbol[?]] =
    if receiver then member.asModOrObj.orElse(member.asTrm).orElse(member.asCls)
    else member.asTrm.orElse(member.asModOrObj).orElse(member.asCls)

  def listenTerm(trm: Term)(listener: Listener)(using NewResolverState): Unit =
    log(s"listenTerm: trm = ${trm.showDbg}")
    listenValue(trm, false)(listener)

  def listenReceiver(trm: Term)(listener: Listener)(using NewResolverState): Unit =
    listenValue(trm, true)(shape => listenInstanceViews(shape)(listener))

  private def listenValue(trm: Term, receiver: Bool)(listener: Listener)(using NewResolverState): Unit = trm match
    case Capture(base, thru) =>
      listenValue(base, receiver): shape =>
        listener(MarkedShape.enter(shape, ResolutionBoundary(thru), N))
    case _ => listen(trm):
      case sh: TermShape => listener(sh)
      case ss: SymShape =>
        fromSymbol(ss, listener, trm, recordValueTarget(trm, _), receiver)

  private def recordValueTarget(term: Term, symbol: DefinitionSymbol[?])(using NewResolverState): Unit =
    term.withoutCaptures match
      case ref: NewResolvable =>
        rstate.recordResolution(ref, ref.resolvedTargets.contains(symbol))(ref.resolvedTargets ::= symbol)
      case _ => ()
  
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

  def listen(trm: Term, discardMarks: Bool = false)(receive: ShapeListener[Shape])(using NewResolverState): Unit =
    // Source listeners process all activations. A deferred observation with a
    // chosen substitution accepts only compatible activations of that source;
    // the delivered value still keeps its independent caller-side references.
    val requestedInstances = rstate.instances
    def compatible(instances: Map[VarSymbol, TypeParameterInstance]): Bool =
      requestedInstances.forall((parameter, instance) => instances.get(parameter).forall(_ eq instance))
    val listener: ShapeListener[Shape] = shape => shape match
      case ActivatedShape(value, instances) =>
        if compatible(instances) then receive(value)(using rstate.withInstances(requestedInstances ++ instances))
      case activated: ActivatedSymShape =>
        if compatible(activated.instances) then
          receive(activated.source)(using rstate.withInstances(requestedInstances ++ activated.instances))
      case value: TermShape => receive(instantiateShape(value, rstate.instances))
      case _ => receive(shape)
    log(s"listen: trm = ${trm.showDbg}")
    trm.addShapeListener(listener)
    trm match
    case _: SynthSel =>
      lastWords("Synthetic selections must not enter new resolution")
    case Asc(_, sign) => listenTypeInstances(sign)(listener)
    case _: DynSel | _: DynNew => listener(DynShape())
    case application @ TyApp(underlying, args) =>
      def checkArity(callee: TermShape, count: Int)(using NewResolverState): Unit =
        if count != args.length && rstate.typeArgumentArityErrors.add((new Identity(application), count)) then
          resolError(trm, msg"${callee.describe.capitalize} expected ${count} type ${
            "argument".pluralized(count)}, but got ${args.length}" -> callee.toLoc :: Nil)
      def instantiate(value: TermShape)(receive: Listener)(using NewResolverState): Unit = listenInstanceViews(value): viewed =>
        val (actual, captured) = contextualParts(viewed)
        actual.applicationHead match
          case (specialized: SpecializedShape, _) =>
            checkArity(specialized, 0)
            receive(value)
          case (callable: CallableTypeShape, marks) =>
            checkArity(callable, callable.tparams.length)
            val supplied = args.map(arg => declaredType(typeResolution(arg), Map.empty).instantiate(rstate.instances))
            instantiateCallable(callable.copy(supplied = S(supplied)),
              rstate.typeApplicationSite(application), marks).exit(marks) match
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
              val supplied = args.map(arg => declaredType(typeResolution(arg), Map.empty).instantiate(rstate.instances))
              val instances = instantiateDefinition(callee, rstate.typeApplicationSite(application), marks,
                rstate.instances ++ captured, S(supplied))
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
          (receive: (TermShape, Bool) => NewResolverState ?=> Unit)(using NewResolverState): Unit = base match
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
                  val caller = declaredType(typeResolution(arg), Map.empty).instantiate(rstate.instances)
                  transportType(caller, inverseMarks(captures))
                fromSymbolAt(sym, value => receive(value, true), base, recordValueTarget(base, _), false,
                  S((rstate.typeApplicationSite(application), arguments)))
              case _ => fromSymbol(sym, value => receive(value, false), base, recordValueTarget(base, _), false)
          case value: TermShape => receive(value, false)
      observe(underlying, Nil): (value, invoked) =>
        if invoked then listener(value) else instantiate(value)(listener)
    case mut @ Mut(underlying: Tup) => listener(mutableArray(mut, underlying))
    case Mut(underlying) => listenTerm(underlying)(listener)
    case tuple: Tup => listenAggregate(tuple, listener): publish =>
        val fields = tuple.fields.collect { case Fld(_, key, S(value)) => (key, value) }
        val named = if fields.isEmpty then Nil else
          // Reuse the defining graph's property symbols when an imported tuple
          // is observed directly, as well as when its copied listeners fire.
          val graph = tuple.originalData.owner
          assert(graph != null, "A tuple producer must have an inference owner")
          val record = rstate.inGraph(graph.nn).namedTupleRecords.getOrElseUpdate(new Identity(tuple), {
            val record: Rcd = Rcd(false, fields.map((key, value) => RcdField(key, value)(using rstate.owner)))
            record.withLocOf(tuple)
            record
          })
          TupleShape.ValueField(RecordShape(record, record.stats.collect {
            case field: RcdField => RecordShape.Field(field)
          }), Nil) :: Nil
        def expand(elems: Ls[Elem], reversed: Ls[TupleShape.Element])(using NewResolverState): Unit = elems match
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
          case Spd(_, term) :: rest =>
            val spreadKey = new Object
            listenTermViews(term): sh =>
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
                case shape @ Marked(_, marks) =>
                  val typed = listenArrayElements(shape):
                    case Marked(element, context) =>
                      val spread = TupleShape(term, TupleShape.Unknown(term, context :: Nil, element) :: Nil)(this)
                      expand(rest, TupleShape.Spread(spread, NoMarks) :: reversed)
                  if !typed then
                    // Other opaque iterables have no known element type. Their
                    // runtime spread remains permitted without authorizing calls.
                    val unknown = TupleShape(term, TupleShape.Unknown(term, Nil, UnknownValueShape.spread(term, shape)) :: Nil)(this)
                    expand(rest, TupleShape.Spread(unknown, marks) :: reversed)
        expand(tuple.fields, Nil)
    case record: Rcd => listenAggregate(record, listener): publish =>
        def expand(stats: Ls[Statement], reversed: Ls[RecordShape.Element])(using NewResolverState): Unit = stats match
          case Nil =>
            val shape = RecordShape(record, reversed.reverse)
            publish(shape)
          case (field: RcdField) :: rest => expand(rest, RecordShape.Field(field) :: reversed)
          case RcdSpread(term) :: rest =>
            val spreadKey = new Object
            listenTermViews(term): shape =>
              if rstate.spreadInputs.getOrElseUpdate(spreadKey, mutable.Set.empty).add(shape) then shape match
                case Marked(shape: RecordShape, marks) =>
                  // Bound recursive record producers just as for tuple spreads.
                  // Keep surrounding explicit fields even when the spread widens.
                  val spread = if shape.containsSpread(shape.source, marks)
                    then RecordShape(shape.source, RecordShape.Unknown(term)(UnknownValueShape.spread(term, shape).provenance) :: Nil)
                    else shape
                  expand(rest, RecordShape.Spread(spread, marks) :: reversed)
                case Marked(_: DynShape, marks) => expand(rest, RecordShape.Dynamic(marks :: Nil) :: reversed)
                case _ => expand(rest, RecordShape.Unknown(term)(UnknownValueShape.spread(term, shape).provenance) :: reversed)
          case _ :: rest => expand(rest, reversed)
        expand(record.stats, Nil)
    case intro: IntroTerm =>
      // Literals have the declared primitive interface, including inherited
      // members. Retain their literal shape for pattern tests and provenance.
      val primitive = intro match
        case Lit(_: Tree.StrLit) => S(prelude.builtins.Str)
        case Lit(_: Tree.IntLit) => S(prelude.builtins.Int)
        case Lit(_: Tree.DecLit) => S(prelude.builtins.Num)
        case Lit(_: Tree.BoolLit) => S(prelude.builtins.Bool)
        case _ => N
      def publish(parent: Opt[NominalInstanceView])(using NewResolverState): Unit =
        listener(introShapes.getOrElseUpdate(new Identity(intro), {
          log(s"introShape: intro = $intro")
          IntroShape(intro, parent)
        }))
      primitive match
        case N => publish(N)
        case S(cls) =>
          val tpe = rstate.primitiveTypes.getOrElseUpdate(cls, {
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
      case _: BuiltinSymbol =>
        lastWords("Builtin symbols must not enter new resolution as SimpleRef")
    case SelfRef(sym) =>
      // A receiver can be referenced before its body is complete or after its
      // definition has already been published. The definition listener handles both.
      def completed(defn: ClassLikeDef)(using NewResolverState): Unit =
        listenExt(defn, ext =>
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
      listenDefn(sym, sh =>
        MarkedShape.exit(sh, ResolutionBoundary(sym), S(ref.resSym)) match
          case sh: TermShape => listener(sh)
          case NoShape => ())
    case ref @ MemberRef(sym: BlockMemberSymbol) =>
      val fs = ref.resSym
      val sh = symShapes.getOrElseUpdate((sym, fs, Nil), SymShape(sym, fs, Nil))
      listener(sh)
    case Capture(base, thru) =>
      if discardMarks then
        listen(base, discardMarks = true)(listener)
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
    case Try(body, _) =>
      // Finally is evaluated for effects; normal completion returns the body's
      // value. Its cleanup value must not contribute candidates to this result.
      listen(body)(listener)
    case _: Assgn | _: Drop => listener(unitResultShape)
    case _: Throw | _: Continue => () // These expressions do not complete normally.
    // case u: UnitVal =>
    case Missing =>
      () // FIXME: Currently get this from light-elaborated Predef import
    case _ =>
      println(s"TODO: listen for ${trm.describe} (${trm.getClass})")
      ()
  
end NewResolver
