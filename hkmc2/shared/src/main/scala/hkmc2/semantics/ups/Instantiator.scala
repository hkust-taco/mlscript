package hkmc2
package semantics
package ups

import hkmc2.utils.*, shorthands.*
import Elaborator.{Ctx, State, ctx}
import Message.MessageContext, ucs.{error, warn}
import semantics.Pattern as SP, Pattern.*
import syntax.Tree, Tree.{StrLit, Ident, IntLit}
import collection.mutable.{Map as MutMap, Queue as MutQueue}
import utils.TL
import scala.collection.immutable.SeqMap

object Instantiator:
  type Subst = Map[VarSymbol, Pat]

class Instantiator(using tl: TL)(using Ctx, State, Raise):
  import tl.*
  
  /** The map contains all instantiated patterns. The key is a pattern symbol
   *  paired with fully instantiated patterns as arguments. The value is the
   *  pattern symbol's definition with all parameters have been substituted.
   *  If the value is `None`, the pattern has not been instantiated yet. */
  val progress: MutMap[Instantiation, Opt[Pat]] = MutMap.empty
  
  /** We instantiate patterns in a breadth-first manner. The queue contains all
   *  patterns that need to be instantiated. */
  val worklist: MutQueue[Instantiation] = MutQueue.empty
  
  /** Instantiate an anonymous pattern. */
  def apply(pattern: SP): (Pat, Context) = scoped("ucs:instantiation"):
    val entryPoint = instantiate(pattern)(using Map.empty)
    (entryPoint, runInstantiationLoop)
  
  /** Run the loop to recursively instantiate needed patterns. */
  private def runInstantiationLoop: Context =
    while worklist.nonEmpty do
      val instantiation = worklist.dequeue()
      val defn = instantiation.symbol.defn.get
      // Check if the number of pattern parameters and pattern arguments match.
      if defn.patternParams.size != instantiation.arguments.size then
        val parameterCount = "pattern parameter" countBy defn.patternParams.size
        val argumentCount = "pattern argument" countBy instantiation.arguments.size
        error(msg"Pattern `${instantiation.symbol.nme}` has $parameterCount." -> Loc(defn.patternParams),
          msg"But $argumentCount were provided." -> instantiation.toLoc)
        // The entire pattern will not be instantiated. Use never instead.
        progress += (instantiation -> S(Pattern.Never))
      else
        val subst = defn.patternParams.iterator.map(_.sym).zip(instantiation.arguments).toMap
        log("Instantiating " + instantiation.showDbg)
        val instantiated = instantiate(defn.pattern)(using subst)
        log(s"Instantiated ${instantiation.showDbg}\n" +
          s"arity = ${instantiation.symbol.defn.get.patternParams.size}\n" +
          s"arguments = ${instantiation.arguments.iterator.map(_.showDbg).mkString(", ")}\n" +
          s"instantiated = ${instantiated.showDbg}")
        // Add the instantiated pattern to the progress map.
        progress += (instantiation -> S(instantiated))
    // Finally, return the synonym representing the entry point pattern and all
    // instantiated pattern definitions.
    val definitions = progress.view.mapValues:
      _.getOrElse(lastWords("The pattern is expected to be instantiated."))
    .toMap
    new Context(definitions)
  
  /** Add the instantiation to the queue if it has not been instantiated yet. */
  def schedule(instantiation: Instantiation): Instantiation =
    if !progress.contains(instantiation) then
      progress += (instantiation -> N)
      worklist.enqueue(instantiation)
    else
      log(s"Already instantiated ${instantiation.showDbg}")
    progress(instantiation)
    instantiation
  
  /** Instantiate the given pattern with a substitution map. */
  def instantiate(pattern: SP)(using subst: Map[VarSymbol, Pat]): Pat = pattern match
    case SP.Constructor(target, arguments) => target.symbol match
      // Look up the corresponding pattern from the substitution.
      case S(symbol: VarSymbol) => subst(symbol)
      // Recursively instantiate the arguments of constructor patterns.
      case S(symbol) => symbol.asClsLike match
        case S(symbol: ClassSymbol) =>
          symbol.defn.get.paramsOpt match
            case S(ParamList(_, params, _)) => arguments match
              case S(arguments) =>
                if params.size != arguments.size then
                  error(msg"Class `${symbol.nme}` has ${params.size} parameters." -> Loc(params),
                    msg"But ${arguments.size} arguments were provided." -> Loc(arguments))
                ClassLike(symbol, S(params.iterator.zip(arguments).flatMap:
                  case (param, argument) if param.flags.isVal =>
                    // The names are not from the source and are retrieved from
                    // parameters in class definitions. Therefore, no `Loc`
                    // should be attached.
                    S(new Ident(param.sym.id.name) -> instantiate(argument))
                  case (param, argument) =>
                    error(msg"Parameter `${param.sym.nme}` is not accessible." -> param.toLoc)
                    N
                .to(SeqMap)))
              // The class has parameters but no arguments are provided.
              case N => ClassLike(symbol, N)
            case N => arguments match
              case N => ClassLike(symbol, N) // No arguments are provided.
              case S(arguments) =>
                // An erroneous pattern must not match anything: bare
                // `ClassLike(symbol, N)` would make `Str("x")` behave like
                // plain `Str` — i.e. match every string — after the error.
                error(msg"Class `${symbol.nme}` has no parameters." -> Loc(arguments))
                Never
        case S(symbol: ModuleOrObjectSymbol) =>
          arguments match
            case N => ClassLike(symbol, N)
            case S(arguments) =>
              // Same rationale as above: do not match after the error.
              error(
                msg"`${symbol.nme}` is a module, thus it cannot have arguments." -> Loc(arguments))
              Never
        case S(symbol: PatternSymbol) =>
          // TODO(after we defined the semantics of pattern parameters): We need
          // to partition the arguments into pattern arguments and extraction
          // arguments here.
          val patternArguments = arguments.getOrElse(Nil).map(instantiate(_))
          val instantiation = Instantiation(symbol, patternArguments)(pattern.toLoc)
          Synonym(schedule(instantiation))
        case N => lastWords(s"Expected target symbol to be a Class-like Symbol, got ${symbol.getClass.getSimpleName}")
      case N => lastWords(s"Missing symbol for constructor pattern `${target.showAsTree}`")
    // The source location is pinned explicitly on the nodes built here:
    // their auto-computed location spans their children, and a `Synonym`
    // child locates the referenced *definition*, so a junction over
    // definitions from different source blocks would mix origins (which
    // `AutoLocated` asserts against) as soon as a diagnostic asks for it.
    case SP.Composition(true, left, right) =>
      (instantiate(left) or instantiate(right)).withLocOf(pattern)
    case SP.Composition(false, left, right) =>
      (instantiate(left) and instantiate(right)).withLocOf(pattern)
    case SP.Negation(pattern2) => Not(instantiate(pattern2)).withLocOf(pattern)
    case SP.Wildcard() => Wildcard
    case SP.Literal(literal) => Literal(literal)
    case SP.Range(lower, upper, rightInclusive) =>
      (lower, upper) match
        case (StrLit(lower), StrLit(upper)) if lower.nonEmpty && upper.nonEmpty =>
          // Character ranges span the code points between their two bounds
          // (the elaborator has checked that each bound is one code point).
          // Keeping ranges symbolic lets the string pattern compiler emit
          // compact character-class transitions instead of wide disjunctions;
          // ranges reaching beyond the Basic Multilingual Plane additionally
          // decompose into surrogate-pair sequences (see `codePointRange`).
          //
          // Note that the upper bound must be lowered by one for an exclusive
          // range: the original expansion `(lower.head to upper.head)` ignored
          // `rightInclusive` altogether, which silently turned `"a" ..< "z"`
          // into `"a" ..= "z"`. An empty range matches nothing.
          val lo = lower.codePointAt(0)
          val included = upper.codePointAt(0)
          val hi = if rightInclusive then included else included - 1
          codePointRange(lo, hi).withLocOf(pattern)
        case (IntLit(lower), IntLit(upper)) =>
          // Integer ranges are still expanded into a list of literals. After
          // the `where` clause or chain patterns are implemented, we could
          // directly expand the range pattern into a range test. An empty
          // range (`5 ..< 5`, or reversed bounds) expands to the empty
          // disjunction, which is `Never`.
          val range = if rightInclusive then lower to upper else lower until upper
          Or(range.map(i => Literal(IntLit(i))).toList)
        case _ =>
          error(msg"Range patterns are not supported in pattern compilation." -> pattern.toLoc)
          Never
    case SP.Concatenation(left, right) =>
      // Nested concatenations are deliberately NOT flattened into the parent
      // sequence: the output of a sequence is the left fold of its elements'
      // outputs under JS `+`, which is not associative across mixed operand
      // types, so re-associating `a ~ (b ~ c)` would change the value a
      // grouped sub-pattern produces — and flattening happened *after*
      // substitution, so the same sub-pattern used to produce one value when
      // referenced through a synonym and another when passed as a pattern
      // argument. `StringCompiler.build` recurses through nested `Concat`s.
      Concat(instantiate(left) :: instantiate(right) :: Nil).withLocOf(pattern)
    case SP.Tuple(leading, spread) =>
      val instantiatedSpread = spread.map:
        case (spreadKind, middle, trailing) =>
          (spreadKind, instantiate(middle), trailing.map(instantiate(_)))
      Tuple(leading.map(instantiate(_)), instantiatedSpread)
    case SP.Record(fields) => Record:
      fields.iterator.map((id, pattern) => (id, instantiate(pattern))).to(SeqMap)
    case SP.Chain(first, second) =>
      error(msg"Pattern chaining is not supported in pattern compilation." -> pattern.toLoc)
      Never
    case alias @ SP.Alias(pattern, id) => alias.symbolOption match
      case N => instantiate(pattern)
      case S(symbol) => Rename(instantiate(pattern), symbol)
    // Pattern arguments are accessible throughout the pattern.
    case SP.Transform(pattern, parameters, transform) =>
      Extract(instantiate(pattern), parameters.toMap, transform)
    case SP.Annotated(pattern, annotations) =>
      // Currently, we only support `@compile` annotation, so here we only
      // check whether this annotation exists, and report an error for all
      // other annotations.
      val shouldCompile = annotations.foldLeft(true): (acc, termOrLoc) =>
        val res = termOrLoc match
          case R(term) => term.resolvedSym match
            case S(symbol) if symbol.asBlkMember.exists(_ is ctx.builtins.annotations.compile) => N
            case S(_) | N => S(term.toLoc)
          case L(loc) => S(loc)
        res match
          case S(loc) =>
            warn(msg"This annotation is not supported here." -> loc,
              msg"Note: Patterns only support the `@compile` annotation." -> pattern.toLoc)
            acc
          case N => true
      instantiate(pattern)
    case _: SP.Guarded =>
      // Guards may fail after consumption based on information the automaton
      // cannot track, which would reintroduce backtracking; they are excluded
      // from compiled patterns for now.
      error(msg"Guarded patterns are not supported in pattern compilation." -> pattern.toLoc)
      Never

  /** The inclusive code-point range `lo` to `hi` as a pattern over UTF-16
    * code units. A range within the Basic Multilingual Plane is a single
    * character class; a range of astral code points becomes high-surrogate/
    * low-surrogate pairs, split into at most three alternatives (a partial
    * first high surrogate, the full middle high surrogates, and a partial
    * last high surrogate) — the standard decomposition used by regular
    * expression engines. A range spanning both planes is the disjunction of
    * its two halves.
    */
  private def codePointRange(lo: Int, hi: Int): Pat =
    def surrogates(cp: Int): (Int, Int) =
      (0xD800 + ((cp - 0x10000) >> 10), 0xDC00 + ((cp - 0x10000) & 0x3FF))
    def pairRange(highLo: Int, highHi: Int, lowLo: Int, lowHi: Int): Pat =
      Concat(CharClass(highLo, highHi) :: CharClass(lowLo, lowHi) :: Nil)
    // An empty range matches nothing. This must be a fresh node (not the
    // shared `Never` singleton) because the caller attaches a location to it.
    if hi < lo then Or(Nil)
    else if hi <= 0xFFFF then CharClass(lo, hi)
    else if lo <= 0xFFFF then
      CharClass(lo, 0xFFFF) or codePointRange(0x10000, hi)
    else
      val (loHigh, loLow) = surrogates(lo)
      val (hiHigh, hiLow) = surrogates(hi)
      if loHigh == hiHigh then pairRange(loHigh, loHigh, loLow, hiLow)
      else
        val first = pairRange(loHigh, loHigh, loLow, 0xDFFF)
        val middle =
          if hiHigh > loHigh + 1
          then pairRange(loHigh + 1, hiHigh - 1, 0xDC00, 0xDFFF) :: Nil
          else Nil
        val last = pairRange(hiHigh, hiHigh, 0xDC00, hiLow)
        Or(first :: middle ::: last :: Nil)
