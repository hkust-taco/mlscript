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
  * A member's parameter lists are its written ones; arrows in its type annotation describe the value
  * it returns and never add lists. For example, `declare fun f: (Int) -> Int` and an abstract
  * `fun f: (Int) -> Int` both have no parameter lists, while `declare fun f(x: Int): Int` has one.
  *
  * [[correspondingParameters]] compares two members' written parameter lists and returns the
  * matching parameter pairs or a failure explaining why the override changes the bindings.
  * [[Erasure]] uses these pairs to inherit parameter representations; [[OverrideChecks]] then checks
  * representation compatibility. The comparison depends on argument positions and parameter flags,
  * not names or types. It runs before lowering replaces optional and trailing parameters with
  * argument extraction code.
  */
object OverrideLayout:
  /** A reason and source location for rejecting an override's argument correspondence. */
  final case class Failure(message: Message, toLoc: Opt[Loc])
  
  /** How diagnostics refer to a parameter. */
  def label(param: Param): Str = s"parameter '${param.sym.nme}'"
  
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
  
  /** Compute the argument or default bound to each parameter, in the order of `ps.allParams`.
    * `S(n)` describes a call with exactly `n` arguments; `N` describes the symbolic large-count
    * case used by `correspondingList`, where every leading and trailing parameter has an argument.
    * For example, `(x?, ...xs, y)` at count one gives `Default`, `EmptySlice`, and `Argument(0)`.
    */
  private def bindings(ps: ParamList, count: Opt[Int]): Ls[Binding] =
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
  
  /** Match the parameters of two lists by their bindings over every inherited argument count.
    * Return `(overriding, inherited)` pairs in inherited parameter order, or the first layout failure.
    * A missing inherited parameter must allow `drop`; an unmatched overriding parameter must receive
    * only defaults or an empty rest slice on inherited calls. Variadic lists require finitely many
    * concrete counts plus a symbolic comparison covering all larger counts.
    */
  private def correspondingList(overriding: ParamList, inherited: ParamList): Either[Failure, Ls[(Param, Param)]] =
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
          Failure(msg"must preserve the arguments bound to inherited ${label(param)}", overriding.toLoc)
      missing match
        case S(failure) => Left(failure)
        case N =>
          val matched = matches.filter(_ >= 0).toSet
          val extra = overriding.allParams.zip(actual).zipWithIndex.collectFirst:
            case ((param, binding), index) if !matched(index) && binding.exists {
              case Binding.Default | Binding.EmptySlice => false
              case _ => true
            } => Failure(msg"${label(param)} would receive arguments assigned to a different inherited parameter", param.toLoc)
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
    * `extra` receives a default on every base call and needs no pair. Missing inherited parameters
    * must allow `drop`. Unmatched overriding parameters must receive only defaults or an empty rest
    * slice, so an added optional parameter before an inherited rest slice must not consume that
    * slice's arguments. Callers use the returned pairs to inherit and check representations in a
    * separate step.
    */
  def correspondingParameters(overriding: Ls[ParamList], inherited: Ls[ParamList]): Either[Failure, Ls[(Param, Param)]] =
    if overriding.length != inherited.length then
      Left(Failure(msg"must preserve the number of parameter lists", overriding.headOption.flatMap(_.toLoc)))
    else overriding.zip(inherited).foldLeft[Either[Failure, Ls[(Param, Param)]]](Right(Nil)):
      case (Left(failure), _) => Left(failure)
      case (Right(pairs), (actual, expected)) => correspondingList(actual, expected).map(pairs ::: _)
