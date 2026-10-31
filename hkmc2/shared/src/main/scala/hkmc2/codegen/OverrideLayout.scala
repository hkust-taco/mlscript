package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import semantics.*
import hkmc2.Message.MessageContext


/** Checks whether an overriding member preserves its inherited member's argument bindings, and
  * computes which parameters correspond. Every inherited parameter that the override retains must
  * have a counterpart receiving the same argument, omitted-argument default, or rest slice on every
  * call permitted by the inherited signature. Only an inherited `drop` flag permits omitting a parameter.
  *
  * [[signature]] derives a source parameter layout from each member declaration.
  * [[correspondingParameters]] compares two such layouts and returns the matching parameter pairs
  * or a failure explaining why the override changes the bindings. [[Erasure]] uses these pairs to
  * inherit parameter representations; [[OverrideChecks]] then checks representation compatibility.
  * Layout comparison itself depends on argument positions and parameter flags, not names or types.
  * It runs before lowering replaces optional and trailing parameters with argument extraction code.
  */
object OverrideLayout:
  /** A reason and source location for rejecting a declaration's layout or an override's correspondence. */
  final case class Failure(message: Message, toLoc: Opt[Loc])
  
  /** One parameter in a source layout, with its binding flags and diagnostic information.
    *
    * A written parameter retains its [[Param]] in `parameter`, so erasure can inherit its representation
    * once correspondence is known. An input recovered from a declared arrow has no bound variable,
    * so `representation` stores its erased type directly. Exactly one of these fields is present.
    * `label` identifies the parameter by name or position in diagnostics.
    */
  final case class Input(flags: FldFlags, parameter: Opt[Param], representation: Opt[ErasedValueType], label: Str, toLoc: Opt[Loc]):
    assert(parameter.isDefined != representation.isDefined, "An override input has exactly one representation source")
  /** The binding layout of one parameter list. `params` contains the leading required and optional
    * inputs; `variadic` contains the rest input and any required trailing inputs. `flags` records
    * whether the list is contextual, which an override must preserve.
    */
  final case class Parameters(flags: ParamListFlags, params: Ls[Input], variadic: Opt[Variadic[Input]], toLoc: Opt[Loc]):
    /** Inputs that bind arguments from the end of a call, after the rest slice. */
    def trailingParams: Ls[Input] = variadic.fold(Nil)(_.trailing)
    /** Minimum accepted argument count, including both required leading and trailing inputs. */
    def paramCountLB: Int = FldFlags.requiredPrefixLength(params.map(_.flags)) + trailingParams.length
    /** Maximum accepted argument count when `variadic` is absent; a variadic list has no finite maximum. */
    def paramCountMax: Int = params.length
    /** All inputs in binding order: leading inputs, the rest input if present, then trailing inputs. */
    def allParams: Ls[Input] = params ::: variadic.toList.flatMap(_.allParams)
  /** A member's source parameter lists and any result representation recovered from declared arrows.
    * Written definitions leave `result` absent; their erased symbols supply the result separately.
    * An empty `params` denotes a member with no source parameter lists, such as a getter.
    */
  final case class Signature(params: Ls[Parameters], result: Opt[ErasedValueType])
  
  /** Build a written parameter list's layout without reading its parameters' erased types. */
  private def written(ps: ParamList): Parameters =
    def input(p: Param): Input = Input(p.flags, S(p), N, s"parameter '${p.sym.nme}'", p.toLoc)
    Parameters(ps.flags, ps.params.map(input), ps.variadic.map(_.map(input)), ps.toLoc)
  
  /** Compute the source signature used to compare `td` with an overriding or inherited member.
    *
    * A definition with written parameters contributes those lists, including their optional, rest,
    * trailing, and contextual flags. An explicitly declared `fun` with no written parameters takes
    * its lists from its callable type: `declare fun f: (Int, Str?) -> Bool` contributes one list with
    * two inputs. An ordinary getter returning a function contributes no lists of its own.
    *
    * Return `Right` with the layout and any result representation recovered from declared arrows,
    * or `Left` when a callable declaration does not determine a supported, unambiguous layout.
    * Follow completed type interpretations and aliases; imported legacy declarations can supply
    * written arrows without interpretations. Resolution must be complete, but written parameter
    * symbols need not have erased types yet. This operation does not assign those types.
    */
  def signature(td: TermDefinition)(using erasure: Erasure, cfg: Config)(using Raise): Either[Failure, Signature] =
    /** Convert an arrow's input type to one list, retaining tuple-field flags and any rest/trailing inputs. */
    def domain(term: Term, eraseInput: Term => Opt[ErasedValueType]): Either[Failure, Parameters] =
      def input(term: Term, flags: FldFlags, index: Int): Input =
        Input(flags, N, S(eraseInput(term).getOrElse(ErasedType.Unknown)), s"parameter $index", term.toLoc)
      term match
        case Term.Tup(fields) =>
          val (leading, remainder) = fields.span(_.isInstanceOf[Fld])
          val prefix = leading.zipWithIndex.collect:
            case (fld: Fld, index) => input(fld.term, fld.flags, index + 1)
          remainder match
            case Nil => Right(Parameters(ParamListFlags.empty, prefix, N, term.toLoc))
            case (spread: Spd) :: trailing if trailing.forall(_.isInstanceOf[Fld]) =>
              val rest = input(spread.term, FldFlags.empty.copy(droppable = spread.droppable), prefix.length + 1)
              val suffix = trailing.zipWithIndex.collect:
                case (fld: Fld, index) => input(fld.term, fld.flags, prefix.length + index + 2)
              Right(Parameters(ParamListFlags.empty, prefix, S(Variadic(rest, suffix)), term.toLoc))
            case _ => Left(Failure(msg"has an unsupported parameter layout in its declared function type", term.toLoc))
        case _ => Right(Parameters(ParamListFlags.empty, input(term, FldFlags.empty, 1) :: Nil, N, term.toLoc))
    /** Whether the written type may describe callable parameters. Aliases require further inspection
      * before the declaration can be classified as a getter.
      */
    def writtenCallable(term: Term): Bool = term match
      case Term.FunTy(_, _, _) => true
      case Term.Capture(base, _) => writtenCallable(base)
      case Term.Forall(_, _, body) => writtenCallable(body)
      case Term.CompType(left, right, _) => writtenCallable(left) || writtenCallable(right)
      case _ => term.resolvedSym.flatMap(_.asAls).nonEmpty
    /** Look for another function arrow behind the outer aliases of a legacy result type.
      * An alias cycle or an alias ending at a type parameter also counts as potentially callable,
      * since this fallback cannot substitute the alias's arguments.
      */
    def legacyCallableHead(term: Term, seen: Set[TypeAliasSymbol], followingAlias: Bool): Bool = term match
      case Term.Capture(base, _) => legacyCallableHead(base, seen, followingAlias)
      case Term.Forall(_, _, body) => legacyCallableHead(body, seen, followingAlias)
      case Term.FunTy(_, _, _) => true
      case _ => term.resolvedSym match
        // The legacy fallback has no argument environment. An alias ending in a parameter
        // could be Id[Callable], so only a known non-callable head may terminate that alias.
        case S(parameter: VarSymbol) if parameter.decl.exists(_.isInstanceOf[TyParam]) => followingAlias
        case S(symbol) => symbol.asAls.exists: alias =>
          // Legacy references may retain the block member containing the alias declaration.
          seen(alias) || alias.defn.flatMap(_.rhs).exists(legacyCallableHead(_, seen + alias, true))
        case N => false
    /** Recover parameter lists and the terminal result from written legacy arrows.
      * `hasParameters` distinguishes the initial callable declaration from its result type.
      * Read imported syntax without registering listeners or changing its stored interpretations.
      */
    def arrows(term: Term, hasParameters: Bool): Either[Failure, Signature] = term match
      case Term.Capture(base, _) => arrows(base, hasParameters)
      case Term.Forall(_, _, body) => arrows(body, hasParameters)
      case Term.FunTy(lhs, rhs, _) =>
        for
          ps <- domain(lhs, ErasedType.eraseSign)
          rest <- arrows(rhs, true)
        yield Signature(ps :: rest.params, rest.result)
      case _ if (!hasParameters && writtenCallable(term)) || (hasParameters && legacyCallableHead(term, Set.empty, false)) =>
        Left(Failure(msg"has a callable type whose parameter layout cannot be determined from its declaration", term.toLoc))
      case _ => Right(Signature(Nil, ErasedType.eraseSign(term)))
    /** Look for a function shape through aliases, wrappers, and compound types at the type's head.
      * This identifies compound callable declarations that have no single parameter layout and
      * must not be classified as getters. Visit shared nodes once; stop at function shapes without
      * searching their inputs or results.
      */
    def containsCallable(resolution: TypeResolution): Bool =
      val visited = scala.collection.mutable.Set.empty[TypeResolution]
      def visit(res: TypeResolution): Bool = visited.add(res) && res.shapes.exists:
        case _: TypeShape.Function => true
        case TypeShape.Alias(_, rhs) => rhs.exists(visit)
        case TypeShape.Reference(base, _, _, _) => visit(base)
        case TypeShape.Applied(base, _) => visit(base)
        case TypeShape.Polymorphic(_, _, body) => visit(body)
        case TypeShape.Contextual(reference) => visit(reference.tpe.resolution)
        case TypeShape.Union(left, right) => visit(left) || visit(right)
        case TypeShape.Intersection(left, right) => visit(left) || visit(right)
        case TypeShape.Combined(formula) => formula.orderedAtoms.exists(atom => visit(atom.resolution))
        case _ => false
      visit(resolution)
    /** A type resolution together with the type arguments bound where it occurs.
      * These bindings let us detect a further callable result hidden behind a parameter, such as
      * `Return[(A, B?) -> C]` where `Return[R] = X -> R`. They serve layout discovery only;
      * generic inputs and results keep their existing erasures.
      */
    final case class Argument(resolution: TypeResolution, bindings: Map[VarSymbol, Argument])
    def argument(res: TypeResolution, bindings: Map[VarSymbol, Argument]): Argument = res.shapes.toList match
      case TypeShape.Parameter(symbol, _) :: Nil => bindings.getOrElse(symbol, Argument(res, bindings))
      case _ => Argument(res, bindings)
    // DeclaredType binding maps contain already-constructed immutable references, so they form
    // a DAG. Recursive types point through TypeResolution, where callableHead checks cycles.
    val capturedArguments = scala.collection.mutable.Map.empty[DeclaredType, Argument]
    /** Convert a declared type and its captured arguments to the `Argument` view, sharing repeated views. */
    def captured(tpe: DeclaredType): Argument = capturedArguments.getOrElseUpdate(tpe,
      argument(tpe.resolution, tpe.bindings.map((symbol, bound) => symbol -> captured(bound))))
    def bind(parameters: Ls[VarSymbol], args: Ls[Argument], bindings: Map[VarSymbol, Argument]): Map[VarSymbol, Argument] =
      bindings ++ parameters.zip(args)
    /** Whether a supplied result type can expose another function arrow through aliases and bindings.
      * `args` supplies arguments to the next alias or polymorphic binder; `positive` chooses the
      * relevant bound of a wildcard. A cyclic head conservatively counts as callable. `resolved`
      * uses this check to reject specialized callable results whose additional lists it cannot normalize.
      */
    def callableHead(current: Argument, args: Ls[Argument], seen: Set[TypeResolution], positive: Bool): Bool =
      val res = current.resolution
      // A repeated unresolved head cannot establish that the result is non-callable. The guard
      // bounds recursive aliases; substituting a bound parameter first also handles Id[Id[T]].
      if seen(res) then true
      else
        val next = seen + res
        val bindings = current.bindings
        res.shapes.toList match
          case TypeShape.Function(_, _) :: Nil => true
          case TypeShape.Applied(base, supplied) :: Nil =>
            callableHead(argument(base, bindings), supplied.map(argument(_, bindings)), next, positive)
          case TypeShape.Alias(symbol, S(rhs)) :: Nil =>
            val parameters = symbol.defn.toList.flatMap(_.tparams.map(_.sym))
            callableHead(argument(rhs, bind(parameters, args, bindings)), Nil, next, positive)
          case TypeShape.Polymorphic(parameters, _, body) :: Nil =>
            callableHead(argument(body, bind(parameters.map(_.parameter.symbol), args, bindings)), Nil, next, positive)
          case TypeShape.Reference(base, _, supplied, _) :: Nil =>
            callableHead(argument(base, bindings ++ supplied.map((symbol, bound) => symbol -> captured(bound))), args, next, positive)
          case TypeShape.Contextual(reference) :: Nil =>
            callableHead(captured(reference.tpe), args, next, reference.tpe.positive)
          case TypeShape.Parameter(symbol, _) :: Nil =>
            bindings.get(symbol).exists(callableHead(_, Nil, next, positive))
          case TypeShape.Wildcard(input, output) :: Nil =>
            (if positive then output else input).exists(res => callableHead(argument(res, bindings), args, next, positive))
          case TypeShape.Argument(parts) :: Nil =>
            callableHead(captured(if positive then parts.output else parts.input), args, next, positive)
          case TypeShape.SelectedArgument(bound, selectedPositive) :: Nil =>
            callableHead(captured(bound), args, next, selectedPositive)
          // These are result values, not additional physical lists. In particular a compound
          // callback value and an abstract/unbound result do not establish one callable head.
          case (TypeShape.Alias(_, N) | TypeShape.Unit | TypeShape.Dynamic | TypeShape.Abstract |
              TypeShape.Top | TypeShape.Bottom | _: TypeShape.Nominal | _: TypeShape.Tuple |
              _: TypeShape.Record | _: TypeShape.Union | _: TypeShape.Intersection | _: TypeShape.Combined |
              _: TypeShape.Negation | _: TypeShape.Hole | _: TypeShape.Inferred) :: Nil => false
          case _ => true
    /** Recover parameter lists and a terminal result representation from a completed type interpretation.
      * Follow aliases and wrappers, collecting one list per arrow. `bindings` and pending `args`
      * retain supplied type arguments so a callable result cannot hide a further parameter list.
      * `applied` records whether the path supplied type arguments; `hasParameters` records whether
      * it already consumed an arrow, after which an ordinary compound type denotes the result value.
      * Return a failure when cycles, errors, or an unsupported callable head prevent recovery.
      */
    def resolved(res: TypeResolution, seen: Set[TypeResolution], applied: Bool,
        hasParameters: Bool, bindings: Map[VarSymbol, Argument], args: Ls[Argument]): Either[Failure, Signature] =
      def unsupported = Left(Failure(msg"has a declared callable type whose parameter layout cannot be determined", res.source.toLoc))
      if seen(res) || res.hasErrors then unsupported
      else
        val next = seen + res
        res.shapes.toList match
          case TypeShape.Alias(_, S(rhs)) :: Nil if rhs.source.typeInterpretation.isEmpty && containsCallable(rhs) =>
            // A callable alias can hide further curried lists even after the first arrow.
            // Without its operand metadata, treating it as a result would skip those bindings.
            Left(Failure(msg"has an aliased callable type whose parameter layout cannot be determined from its declaration", res.source.toLoc))
          case TypeShape.Alias(symbol, S(rhs)) :: Nil =>
            val parameters = symbol.defn.toList.flatMap(_.tparams.map(_.sym))
            resolved(rhs, next, applied, hasParameters, bind(parameters, args, bindings), Nil)
          case TypeShape.Reference(base, _, supplied, _) :: Nil =>
            resolved(base, next, applied || supplied.nonEmpty, hasParameters,
              bindings ++ supplied.map((symbol, bound) => symbol -> captured(bound)), args)
          case TypeShape.Applied(base, supplied) :: Nil =>
            resolved(base, next, true, hasParameters, bindings, supplied.map(argument(_, bindings)))
          case TypeShape.Polymorphic(parameters, _, body) :: Nil =>
            resolved(body, next, applied, hasParameters, bind(parameters.map(_.parameter.symbol), args, bindings), Nil)
          case TypeShape.Contextual(reference) :: Nil =>
            val context = captured(reference.tpe)
            resolved(context.resolution, next, applied || context.bindings.nonEmpty, hasParameters, context.bindings, args)
          case TypeShape.Function(lhs, rhs) :: Nil =>
            for
              ps <- domain(lhs, erasure.eraseSignature)
              rest <- resolved(rhs, next, applied, true, bindings, Nil)
            yield Signature(ps :: rest.params, rest.result)
          case TypeShape.Parameter(symbol, _) :: Nil if bindings.get(symbol).exists(callableHead(_, Nil, Set.empty, true)) => unsupported
          // A parameter at the initial applied head cannot establish a layout either. A result
          // parameter whose supplied argument is non-callable keeps ordinary generic erasure.
          case TypeShape.Parameter(_, _) :: Nil if applied && !hasParameters => unsupported
          case TypeShape.Alias(_, N) :: Nil if hasParameters => Right(Signature(Nil, S(erasure.eraseResolved(res))))
          case TypeShape.Alias(_, N) :: Nil => unsupported
          case _ :: Nil if hasParameters || !containsCallable(res) => Right(Signature(Nil, S(erasure.eraseResolved(res))))
          case _ => unsupported
    if (td.k is syntax.Fun) && td.params.isEmpty && td.hasDeclareModifier.nonEmpty then
      td.sign.fold[Either[Failure, Signature]](Right(Signature(Nil, N))): sign =>
        val normalized = if !cfg.language.useNewResolution then arrows(sign, false)
        else sign.typeInterpretation match
          case S(resolution) => resolved(resolution, Set.empty, false, false, Map.empty, Nil)
          case N if td.tsym.isErased => arrows(sign, false)
          case N =>
            softAssert(false, "A current-source declared callable signature must have a completed interpretation")
            Left(Failure(msg"has an unresolved declared callable type", sign.toLoc))
        normalized.map:
          case Signature(Nil, _) => Signature(Nil, N)
          case signature => signature
    else Right(Signature(td.params.map(written), N))
  
  /** Describes where a parameter's value comes from for a particular argument count.
    * Argument indices are zero-based and slice ends are exclusive. The symbolic variants describe
    * arbitrarily large calls: `ArgumentFromEnd(1)` is the last argument, and an unbounded slice
    * ends before the given number of trailing arguments.
    */
  private enum Binding:
    case Argument(index: Int)
    case Default
    case Slice(start: Int, end: Int)
    case EmptySlice
    // These describe every sufficiently large argument count n, rather than one sampled count.
    case ArgumentFromEnd(distance: Int)
    case UnboundedSlice(start: Int, trailing: Int)
  
  /** Compute the argument or default bound to each input, in the order of `ps.allParams`.
    * `S(n)` describes a call with exactly `n` arguments; `N` describes the symbolic large-count
    * case used by `correspondingList`, where every leading and trailing input has an argument.
    * For example, `(x?, ...xs, y)` at count one gives `Default`, `EmptySlice`, and `Argument(0)`.
    */
  private def bindings(ps: Parameters, count: Opt[Int]): Ls[Binding] =
    import Binding.*
    val leading = ps.params.length
    val trailing = ps.trailingParams.length
    val prefix = ps.params.indices.map: index =>
      if count.exists(index >= _ - trailing) then Default else Argument(index)
    val rest = ps.variadic.toList.map: _ =>
      count match
        case S(n) if n - trailing <= leading => EmptySlice
        case S(n) => Slice(leading, n - trailing)
        case N => UnboundedSlice(leading, trailing)
    val suffix = ps.trailingParams.indices.map: index =>
      count match
        case S(n) => Argument(n - trailing + index)
        case N => ArgumentFromEnd(trailing - index)
    prefix.toList ::: rest ::: suffix.toList
  
  /** Match the inputs of two parameter lists by their bindings over every inherited argument count.
    * Return `(overriding, inherited)` pairs in inherited input order, or the first layout failure.
    * A missing inherited input must allow `drop`; an unmatched overriding input must receive only
    * defaults or an empty rest slice on inherited calls. Variadic lists require finitely many
    * concrete counts plus a symbolic comparison covering all larger counts.
    */
  private def correspondingList(overriding: Parameters, inherited: Parameters): Either[Failure, Ls[(Input, Input)]] =
    def fail(message: Message): Left[Failure, Nothing] = Left(Failure(message, overriding.toLoc))
    if overriding.flags != inherited.flags then
      fail(msg"must preserve contextual parameter lists")
    else if overriding.paramCountLB > inherited.paramCountLB then
      fail(msg"requires at least ${overriding.paramCountLB.toString} ${"argument".pluralized(overriding.paramCountLB)}, but the overridden member permits ${inherited.paramCountLB.toString}")
    else
      // All optional slots are filled once n reaches leading + trailing. Above both such
      // boundaries, prefixes are constant indices, suffixes are n-relative indices, and rest
      // slices have constant starts and n-relative ends. Comparing that symbolic region plus
      // every smaller permitted count is therefore exact, including unknown-length spreads.
      val boundary = (overriding.params.length + overriding.trailingParams.length)
        .max(inherited.params.length + inherited.trailingParams.length)
      val last = if inherited.variadic.isDefined then boundary else inherited.paramCountMax
      val counts = (inherited.paramCountLB to last).toList.map(S(_)) :::
        (if inherited.variadic.isDefined then N :: Nil else Nil)
      val actual = counts.map(bindings(overriding, _)).transpose
      val expected = counts.map(bindings(inherited, _)).transpose
      val actualPositions = actual.zipWithIndex.toMap
      val matches = expected.map(binding => actualPositions.getOrElse(binding, -1))
      val missing = inherited.allParams.zip(matches).collectFirst:
        case (param, -1) if !param.flags.droppable =>
          Failure(msg"must preserve the arguments bound to inherited ${param.label}", overriding.toLoc)
      missing match
        case S(failure) => Left(failure)
        case N =>
          val matched = matches.filter(_ >= 0).toSet
          val extra = overriding.allParams.zip(actual).zipWithIndex.collectFirst:
            case ((param, binding), index) if !matched(index) && binding.exists {
              case Binding.Default | Binding.EmptySlice => false
              case _ => true
            } => Failure(msg"${param.label} would receive arguments assigned to a different inherited parameter", param.toLoc)
          extra match
            case S(failure) => Left(failure)
            case N => Right(inherited.allParams.zip(matches).collect:
              case (param, index) if index >= 0 => overriding.allParams(index) -> param)
  
  /** Compute the parameter correspondence for an override that preserves every permitted base call.
    * Return `Right` with `(overriding, inherited)` pairs in inherited list/input order, or `Left`
    * with the first incompatibility. Paired inputs must receive the same arguments or defaults for
    * every argument count accepted by the inherited list. Names and representations do not affect
    * this comparison; list boundaries and contextual flags must match.
    *
    * For example, overriding `(x, y?)` with `(a, b?, extra?)` pairs `a` with `x` and `b` with `y`;
    * `extra` receives a default on every base call and needs no pair. Missing inherited inputs must
    * allow `drop`. Unmatched overriding inputs must receive only defaults or an empty rest slice,
    * so an added optional input before an inherited rest slice must not consume that slice's arguments.
    * Callers use the returned pairs to inherit and check representations in a separate step.
    */
  def correspondingParameters(overriding: Ls[Parameters], inherited: Ls[Parameters]): Either[Failure, Ls[(Input, Input)]] =
    if overriding.length != inherited.length then
      Left(Failure(msg"must preserve the number of parameter lists", overriding.headOption.flatMap(_.toLoc)))
    else overriding.zip(inherited).foldLeft[Either[Failure, Ls[(Input, Input)]]](Right(Nil)):
      case (Left(failure), _) => Left(failure)
      case (Right(pairs), (actual, expected)) => correspondingList(actual, expected).map(pairs ::: _)
