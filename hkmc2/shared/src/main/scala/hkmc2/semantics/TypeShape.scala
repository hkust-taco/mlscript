package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import codegen.Erasure

/** A type interpretation, separate from the value shapes of the same reference syntax.
  * Compound types retain links to their operands so forward aliases need not be expanded eagerly.
  */
enum TypeShape:
  case Nominal(defn: ClassLikeDef)
  case Alias(symbol: TypeAliasSymbol, rhs: Opt[TypeResolution])
  case Union(left: TypeResolution, right: TypeResolution)
  case Intersection(left: TypeResolution, right: TypeResolution)
  // Negated interfaces remain opaque, but their dependencies must participate
  // in source validation, including the rejection of unguarded alias cycles.
  case Negation(base: TypeResolution)
  // Substituted unions/intersections retain whole interpreted endpoints. Keeping
  // their lattice normal form prevents repeated Boolean substitutions from
  // nesting environments, without expanding bounds or changing endpoint marks.
  case Combined(formula: TypeFormula[DeclaredType])
  case Tuple(fields: Ls[TypeResolution])
  case Record(source: Term.Rcd, fields: Ls[(RcdField, TypeResolution)])
  case Function(params: Term, result: TypeResolution)
  case Polymorphic(params: Ls[TypeQuantifier], outer: Opt[VarSymbol], body: TypeResolution)
  case Applied(base: TypeResolution, args: Ls[TypeResolution])
  case Wildcard(input: Opt[TypeResolution], output: Opt[TypeResolution])
  // Synthesized declaration variance retains the argument's lexical environment.
  case Argument(parts: TypeArgument)
  // Substitution selects one part before the type is used in further constraints.
  // The argument stays in its own lexical environment, including delayed parts.
  case SelectedArgument(argument: DeclaredType, positive: Bool)
  // A transported reference retains its context before any deferred component
  // is observed. The resolver flattens these nodes and normalizes their marks.
  case Contextual(reference: ContextualType)
  // The same third-party symbol can have different inference in two exporters.
  // Retain its originating host so importing a result needs no whole-state copy.
  case Parameter(symbol: VarSymbol, host: Publisher.Data[ShapeEvent])
  // An omitted argument owns one source inference node. It is not a quantified
  // binder and is never instantiated at a call site; marks distinguish its flows.
  case Hole(host: Publisher.Data[TermShape])
  // Synthesized generic arguments can retain inferred value shapes, for example
  // the element union of the Array supertype of a tuple. Written annotations
  // never introduce this case by inspecting their implementation.
  case Inferred(value: TermShape)
  case Captured(base: TypeResolution, thru: AnyDefinitionSymbol)
  case Unit
  case Dynamic
  case Abstract
  case Top
  case Bottom

/** Candidates are published during elaboration. Erasure reads the resulting graph; it
  * never performs lookup or resolves an alias by inspecting an elaborated definition.
  */
final class TypeResolution(val source: Term, report: Ls[(Message, Opt[Loc])] => Unit) extends Host[TypeShape]:
  private var reported = false
  def hasErrors: Bool = reported
  def showDbg(using DebugPrinter): Str = s"type of ${source.showDbg}"
  def publish(shape: TypeShape)(using NewResolverState): Unit =
    if currentShapes.add(shape) then notifyShapeListeners(shape)
  def listen(listener: ShapeListener[TypeShape])(using NewResolverState): Unit =
    subscribeToShapes(listener)
  def fail(messages: Ls[(Message, Opt[Loc])]): Unit = if !reported then
    reported = true
    report(messages)
  def validate(seen: Set[TypeResolution])(using Erasure): Unit = if !seen(this) then
    import TypeShape.*
    import Message.MessageContext
    val next = seen + this
    val ambiguousReceiver = source.withoutCaptures match
      case ref: Term.UnresolvedRef => ref.resolvedMembers.distinct.sizeCompare(1) > 0
      case sel: Term.NewSel => sel.hasAmbiguousClass
      case _ => false
    if shapes.isEmpty then fail(msg"This type has no resolved target" -> source.toLoc :: Nil)
    else if ambiguousReceiver || shapes.sizeCompare(1) > 0 then
      val candidates = source.withoutCaptures match
        case ref: Term.UnresolvedRef => ref.resolvedMembers.distinct.map: (prefix, member) =>
          msg"candidate: ${member.describe}" -> member.toLoc
        case _ => shapes.toList.flatMap:
          case Nominal(defn) => msg"candidate: ${defn.sym.describeKind}" -> defn.toLoc :: Nil
          case Alias(symbol, _) => msg"candidate: ${symbol.describeKind}" -> symbol.toLoc :: Nil
          case _ => Nil
      fail(msg"This type is ambiguous, as it has multiple resolved targets" -> source.toLoc :: candidates)
    shapes.foreach:
      case Alias(_, rhs) => rhs.foreach(_.validate(next))
      case Captured(base, _) => base.validate(next)
      case Applied(base, args) =>
        base.validate(next)
        args.foreach(_.validate(next))
        def checkArity(base: TypeResolution, seen: Set[TypeResolution]): Unit = if !seen(base) then
          def check(name: Str, count: Int, loc: Opt[Loc]): Unit = if args.length > count then
            fail(msg"Type '$name' accepts at most $count type ${"argument".pluralized(count)}, but got ${args.length}." ->
              source.toLoc :: (msg"The type parameters are declared here." -> loc) :: Nil)
          base.shapes.toList match
            case Nominal(defn) :: Nil => check(defn.sym.nme, defn.tparams.length, defn.toLoc)
            case Alias(symbol, _) :: Nil => symbol.defn.foreach(d => check(symbol.nme, d.tparams.length, d.toLoc))
            case Captured(inner, _) :: Nil => checkArity(inner, seen + base)
            case _ => ()
        checkArity(base, Set.empty)
      case Wildcard(input, output) => input.foreach(_.validate(next)); output.foreach(_.validate(next))
      case Argument(parts) => parts.input.resolution.validate(next); parts.output.resolution.validate(next)
      case SelectedArgument(argument, _) => argument.resolution.validate(next)
      case Contextual(reference) => reference.tpe.resolution.validate(next)
      case Function(_, result) => result.validate(next)
      case Polymorphic(params, _, body) =>
        params.foreach: param =>
          param.lower.foreach(_.validate(next))
          param.upper.foreach(_.validate(next))
        body.validate(next)
      case Tuple(fields) => fields.foreach(_.validate(next))
      case Record(_, fields) => fields.foreach(_._2.validate(next))
      case Union(left, right) => left.validate(next); right.validate(next)
      case Intersection(left, right) => left.validate(next); right.validate(next)
      case Negation(base) => base.validate(next)
      case Combined(formula) => formula.orderedAtoms.foreach(_.resolution.validate(next))
      case _ => ()

/** A type with its lexical type-parameter bindings. These bindings describe declared
  * interfaces, not constructor arguments or value-flow capture paths.
  */
final case class DeclaredType(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType],
    instances: Map[VarSymbol, TypeParameterInstance], positive: Bool):
  // This polarity interprets substitutions in the source expression; it is not
  // the direction of a constraint subsequently applied to the interpreted type.
  require(instances.forall((source, instance) => instance.origin eq source),
    "A substitution must map original binders to their call-site instances")
  /** Instantiation changes references to source binders, never expands their bounds.
    * A reference already interpreted in another call retains that interpretation.
    * The finite map contains original binders and canonical site instances only.
    */
  def instantiate(substitution: Map[VarSymbol, TypeParameterInstance]): DeclaredType =
    copy(instances = substitution ++ instances)

/** A type reference observed from a common comparison scope. The marks belong
  * to this endpoint: reversing a constraint swaps endpoints, not an expanded
  * candidate's already-normalized path.
  */
final case class ContextualType(tpe: DeclaredType, marks: Ls[Marks])

/** Invariant S has S in both positions. Missing wildcard parts are represented
  * by Nothing on input and Any on output, never by inference holes.
  */
final case class TypeArgument(input: DeclaredType, output: DeclaredType)

/** A quantified binder belongs to the source scheme; its bounds retain graph links
  * so mutually dependent bounds do not require expanding or copying their types.
  */
final case class TypeQuantifier(parameter: TypeShape.Parameter,
    lower: Opt[TypeResolution], upper: Opt[TypeResolution])

/** A callable's binder and bounds interpreted in the surrounding lexical bindings. */
final case class DeclaredTypeParameter(parameter: TypeShape.Parameter,
    lower: Opt[DeclaredType], upper: Opt[DeclaredType])

/** The owner is the original declaration, or a quantified annotation for an
  * anonymous callable. Applied and imported views retain this identity.
  */
final case class TypeScheme(owner: AnyDefinitionSymbol | TypeResolution, parameters: Ls[DeclaredTypeParameter])
