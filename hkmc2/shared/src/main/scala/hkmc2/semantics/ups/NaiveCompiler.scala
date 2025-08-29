package hkmc2
package semantics
package ups

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import ucs.{TermSynthesizer, FlatPattern, error, safeRef}, ucs.extractors.*
import syntax.{Fun, Keyword, Tree}, Tree.{Ident, StrLit}, Keyword.{`as`, `=>`}
import scala.collection.mutable.Buffer
import Elaborator.{Ctx, State, ctx}, utils.TL
import semantics.Pattern as SP // "SP" is short for "semantic patterns"

object NaiveCompiler:
  /** String range bounds must be single characters. */
  def isInvalidStringBounds(lo: StrLit, hi: StrLit)(using Raise): Bool =
    val ds = Buffer.empty[(Message, Option[Loc])]
    if lo.value.length != 1 then
      ds += msg"The lower bound of character ranges must be a single character." -> lo.toLoc
    if hi.value.length != 1 then
      ds += msg"The upper bound of character ranges must be a single character." -> hi.toLoc
    if ds.nonEmpty then error(ds.toSeq*)
    ds.nonEmpty
  
  /** Each scrutinee is represented by a function that creates a reference to
   *  the scrutinee symbol. It is sufficient for current implementation.
   */
  type Scrut = () => Term.Ref
  
  extension (symbol: BlockLocalSymbol)
    def toScrut: Scrut = () => symbol.safeRef
  
  type BindingMap = Map[VarSymbol, Scrut]
  
  type SplitSequel[Output] = (makeConsequent: (Output, BindingMap) => Split, alternative: Split) => Split
  
  extension [Output](sequel: SplitSequel[Output])
    def map[Result](f: Output => Result): SplitSequel[Result] = (makeConsequent, alternative) =>
      sequel((output, bindings) => makeConsequent(f(output), bindings), alternative)
  
  type MakeConsequent = (output: Scrut, bindings: BindingMap) => Split
  
  /** The continuation function returned by `makeMatchSplit`.
   *  Note that `alternative` does not serve as the fallback split. It means the
   *  next split we should try when the current split fails.
   *  
   *  Note: I realized that it would make more sense to let `output` be a term.
   *  Because in some cases, the output is not used in the consequent split.
   *  For example, the output of the `negation` pattern is discarded.
   *  
   *  The `bindings` parameter is used to denote the variables that are bound
   *  during the matching process. The key is the pattern's variable symbol and
   *  the value is the local symbol that represents the matched values.
   */
  type MakeSplit = (makeConsequent: MakeConsequent, alternative: Split) => Split
  
  extension (first: MakeSplit)
    def | (second: MakeSplit): MakeSplit = (makeConsequent, alternative) =>
      first(makeConsequent, second(makeConsequent, alternative))
    def & (second: MakeSplit): SplitSequel[(Scrut, Scrut)] = (makeConsequent, alternative) =>
      first(
        (firstOutput, firstBindings) => second(
          (secondOutput, secondBindings) => makeConsequent(
            (firstOutput, secondOutput),
            firstBindings ++ secondBindings // Do we need to duplicate the bindings?
          ),
          alternative),
        alternative)
  
  type MakePrefixConsequent = (consumedOutput: Scrut, remainingOutput: Scrut, bindings: BindingMap) => Split
  
  /** The continuation function returned by `makeStringPrefixMatchSplit`. */
  type MakePrefixSplit = (makeConsequent: MakePrefixConsequent, alternative: Split) => Split
  
  val rejectPrefixSplit: MakePrefixSplit = (_, alternative) => alternative

import NaiveCompiler.*

/** This class compiles a tree describing a pattern into functions that can
 *  perform pattern matching on terms described by the pattern. */
class NaiveCompiler(using tl: TL)(using State, Ctx, Raise) extends TermSynthesizer:
  import tl.*, FlatPattern.MatchMode, SP.*
  
  private lazy val lteq = State.builtinOpsMap("<=")
  private lazy val lt = State.builtinOpsMap("<")
  
  private def makeRangeTest(scrut: Scrut, lo: syntax.Literal, hi: syntax.Literal, rightInclusive: Bool, innerSplit: Split) =
    def scrutFld = fld(scrut())
    val test1 = app(lteq.safeRef, tup(fld(Term.Lit(lo)), scrutFld), "isGreaterThanLower")
    val upperOp = if rightInclusive then lteq else lt
    val test2 = app(upperOp.safeRef, tup(scrutFld, fld(Term.Lit(hi))), "isLessThanUpper")
    plainTest(test1, "isGreaterThanLower")(plainTest(test2, "isLessThanUpper")(innerSplit))
  
  extension (patterns: Ls[SP])
    def folded(z: (Ls[TempSymbol], MakeConsequent))(makeSubScrutineeSymbol: Int => TempSymbol) =
      patterns.iterator.zipWithIndex.foldRight(z):
        case ((element, index), (subScrutinees, makeInnerSplit)) =>
          val subScrutinee = makeSubScrutineeSymbol(index)
          val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
            makeMatchSplit(subScrutinee.toScrut, element)(
              (elementOutput, elementBindings) => makeInnerSplit(
                elementOutput, // TODO: Combine `outerOutput` and `elementOutput`
                outerBindings ++ elementBindings),
              Split.End)
          (subScrutinee :: subScrutinees, makeThisSplit)
  
  /** Make a UCS split that matches the entire scrutinee against the pattern.
   *  Since each pattern has an output, the split is responsible for creating
   *  a binding that holds the output value and pass it to the continuation
   *  function that makes the conseuqent split.
   */
  private def makeMatchSplit(scrutinee: Scrut, pattern: SP): MakeSplit =
    pattern match
      case Constructor(target, patternArguments, arguments) => (makeConsequent, alternative) =>
        // If we treat a constructor pattern as the intersection of constructor
        // instance pattern and argument patterns, the output value should be
        // a tuple made of the input value and values of each argument.
        // This is the sub-scrutinees for arguments.
        
        // The pattern arguments for destructing the constructor's arguments.
        val (arguments1, makeChainedConsequent) = arguments.fold((N, makeConsequent)):
          _.iterator.zipWithIndex.foldRight(Nil: Ls[FlatPattern.Argument], makeConsequent):
            case ((argument, index), (theArguments, makeInnerSplit)) =>
              val subScrutinee = TempSymbol(N, s"argument$index$$")
              val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
                makeMatchSplit(subScrutinee.toScrut, argument)(
                  (argumentOutput, argumentBindings) => makeInnerSplit(
                    argumentOutput, // TODO: Combine `outerOutput` and `argumentOutput`
                    outerBindings ++ argumentBindings),
                  Split.End)
              val theArgument = FlatPattern.Argument(subScrutinee, Tree.Empty().withLocOf(argument))
              (theArgument :: theArguments, makeThisSplit)
          .mapFirst(S(_))
        // For pattern arguments for higher-order patterns, we generate the
        // inline objects with `unapply` and `unapplyStringPrefix` methods.
        val arguments0 = patternArguments.iterator.zipWithIndex.map: (pattern, index) =>
          FlatPattern.Argument(TempSymbol(N, s"patternArgument$index$$"), pattern)
        .toList
        val theArguments = arguments1.fold(if arguments0.isEmpty then N else S(arguments0)):
          case arguments => S(arguments0 ::: arguments)
        scoped("ucs:translation"):
          log(s"the arguments of ${pattern.showDbg}:\n${theArguments.showAsTree}")
        // Here, passing `scrutinee` as the output is not always correct. When
        // `target` is a class or object, the output should be the scrutinee.
        // When `target` is a pattern, the output should be the pattern's output.
        // But it is until the normalization we can tell whether `target` is a
        // pattern or not.
        val outputSymbol = TempSymbol(N, "output")
        val consequent = makeChainedConsequent(outputSymbol.toScrut, Map.empty)
        Branch(scrutinee(), FlatPattern.ClassLike(target, theArguments, outputSymbol :: Nil), consequent) ~: alternative
      case Composition(true, left, right) =>
        makeMatchSplit(scrutinee, left) | makeMatchSplit(scrutinee, right)
      case Composition(false, left, right) => (makeConsequent, alternative) =>
        makeMatchSplit(scrutinee, left)(
          (leftOutput, leftBindings) => makeMatchSplit(scrutinee, right)(
            (rightOutput, rightBindings) => 
              val tupleIdent = Ident("tupledResults")
              val tupleSymbol = TempSymbol(N, "tupledResults")
              val tupleTerm = tup(leftOutput() |> fld, rightOutput() |> fld)
              Split.Let(tupleSymbol, tupleTerm, makeConsequent(() => tupleSymbol.safeRef, leftBindings ++ rightBindings) ~~: alternative),
            alternative),
          alternative)
      case Negation(pattern) => (makeConsequent, alternative) =>
        // Currently, the negation pattern produces the original value. In the
        // future, we would include diagnostic information about why the pattern
        // failed. Note that this feature requires the `alternative` parameter
        // to be a function that takes a diagnostic information generation
        // function.
        val outputSymbol = TempSymbol(N, "negationOutput")
        // The place where the diagnostic information should be stored.
        val outputTerm = scrutinee()
        makeMatchSplit(scrutinee, pattern)(
          (_output, _bindings) => alternative, // The output and bindings are discarded.
          Split.Let(outputSymbol, outputTerm, makeConsequent(() => outputSymbol.safeRef, Map.empty) ~~: alternative)
        )
      // Because a wildcard pattern always matches, `alternative` is not used.
      case Wildcard() => (makeConsequent, _) => makeConsequent(scrutinee, Map.empty)
      case Literal(literal) => (makeConsequent, alternative) =>
        Branch(scrutinee(), FlatPattern.Lit(literal)(Nil), makeConsequent(scrutinee, Map.empty)) ~: alternative
      case Range(lower, upper, rightInclusive) => (makeConsequent, alternative) =>
        makeRangeTest(scrutinee, lower, upper, rightInclusive, makeConsequent(scrutinee, Map.empty)) ~~: alternative
      case Concatenation(left, right) => (makeConsequent, alternative) =>
        log(s"Concatenation")
        makeStringPrefixMatchSplit(scrutinee, left)(
          (consumedOutput, remainingOutput, bindingsFromConsumed) =>
            makeMatchSplit(remainingOutput, right)(
              // Here we discard the postfix output because I still haven't
              // figured out the semantics of string concatenation.
              (_postfixOutput, bindingsFromRemaining) => makeConsequent(
                  scrutinee, bindingsFromConsumed ++ bindingsFromRemaining
                ) ~~: alternative,
              alternative
            ),
          alternative
        )
      case Tuple(elements, N, _) => (makeConsequent, alternative) =>
        // Fixed-length tuple patterns are similar to constructor patterns.
        val z = (Nil: Ls[TempSymbol], makeConsequent)
        // TODO: Deduplicate the code with the `Constructor` case.
        val (subScrutinees, makeChainedConsequent) = elements.iterator.zipWithIndex.foldRight(z):
          case ((element, index), (subScrutinees, makeInnerSplit)) =>
            val subScrutinee = TempSymbol(N, s"element$index$$")
            val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
              makeMatchSplit(subScrutinee.toScrut, element)(
                (elementOutput, elementBindings) => makeInnerSplit(
                  elementOutput, // TODO: Combine `outerOutput` and `elementOutput`
                  outerBindings ++ elementBindings),
                Split.End)
            (subScrutinee :: subScrutinees, makeThisSplit)
        // END TODO
        makeTupleBranch(scrutinee(), subScrutinees, makeChainedConsequent(scrutinee, Map.empty), alternative)
      case Tuple(leading, S(spread), trailing) => (makeConsequent, alternative) =>
        val (trailSubScrutinees, makeConsequent0) = trailing.folded((Nil, makeConsequent)):
          index => TempSymbol(N, s"lastElement$index$$")
        val spreadSubScrutinee = TempSymbol(N, "middleElements")
        val makeConsequent1: MakeConsequent = (outerOutput, outerBindings) =>
          makeMatchSplit(spreadSubScrutinee.toScrut, spread)(
            (spreadOutput, spreadBindings) => makeConsequent0(
              spreadOutput, // TODO: Combine `outerOutput` and `spreadOutput`
              outerBindings ++ spreadBindings),
            Split.End)
        val (leadingSubScrutinees, makeConsequent2) = leading.folded((Nil, makeConsequent1)):
          index => TempSymbol(N, s"firstElement$index$$")
        makeTupleBranch(scrutinee(), leadingSubScrutinees, spreadSubScrutinee, trailSubScrutinees, makeConsequent2(scrutinee, Map.empty), alternative)
      case Record(fields) => (makeConsequent, alternative) =>
        // This case is similar to the `Constructor` case.
        val z = (Nil: Ls[(Ident, TempSymbol)], makeConsequent)
        // TODO: Deduplicate the code with the `Constructor` case.
        val (entries, makeChainedConsequent) = fields.iterator.zipWithIndex.foldRight(z):
          case (((key, pattern), index), (fields, makeInnerSplit)) =>
            val subScrutinee = TempSymbol(N, s"field_${key.name}$$")
            val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
              makeMatchSplit(subScrutinee.toScrut, pattern)(
                (fieldOutput, fieldBindings) => makeInnerSplit(
                  fieldOutput, // TODO: Combine `outerOutput` and `fieldOutput`
                  outerBindings ++ fieldBindings),
                alternative) // We fill in the alternative here. This is
                             // different from the `Constructor` case.
            ((key, subScrutinee) :: fields, makeThisSplit)
        // END TODO
        val consequent = makeChainedConsequent(scrutinee, Map.empty)
        Branch(scrutinee(), FlatPattern.Record(entries)(Nil), consequent) ~: alternative
      case Chain(first, second) => (makeConsequent, alternative) =>
        makeMatchSplit(scrutinee, first)(
          (firstOutput, firstBindings) => makeMatchSplit(firstOutput, second)(
            (secondOutput, secondBindings) => makeConsequent(secondOutput, firstBindings ++ secondBindings),
            alternative),
          alternative)
      case alias @ Alias(pattern, id) => alias.symbolOption match
        // Ignore those who don't have symbols. `Elaborator` should have
        // reported errors.
        case N =>
          log(s"pattern ${pattern.showDbg} doesn't have an alias symbol: ${id.name}")
          makeMatchSplit(scrutinee, pattern)
        case S(symbol) => (makeConsequent, alternative) =>
          makeMatchSplit(scrutinee, pattern)(
            (output, bindings) =>
              makeConsequent(output, bindings + (symbol -> output)),
            alternative)
      case Transform(pattern, transform) =>
        // We should first create a local function that transforms the captured
        // values. So far, `pattern`'s variables should be bound to symbols.
        // Thus, we can make a parameter list from the symbols. Then, we make
        // a lambda term from the parameter list and the transform term. Because
        // `pattern` might be translated to many branches, making a lambda term
        // in advance reduces code duplication.
        val symbols = pattern.variables.symbols
        val params = symbols.map:
          Param(FldFlags.empty, _, N, Modulefulness.none)
        val lambdaSymbol = new TempSymbol(N, "transform")
        // Next, we need to elaborate the pattern into a split. Note that
        // `makeMatchSplit` returns a function that takes a split as the
        // consequence. `makeMatchSplit` also takes a list of symbols so that
        // it needs to make sure that those bindings are available in the
        // consequence split.
        (makeConsequent, alternative) => Split.Let(
          sym = lambdaSymbol,
          term = Term.Lam(PlainParamList(params), transform),
          // Declare the lambda function at the outermost level. Even if there
          // are multiple disjunctions in the consequent, we will not need to
          // repeat the `transform` term.
          tail = makeMatchSplit(scrutinee, pattern)(
            // Note that the output is not used. Semantically, the `transform`
            // term can only access the matched values by bindings.
            (_output, bindings) =>
              log(s"we are handling pattern ${pattern.showDbg}")
              log(s"produced bindings are ${bindings.keys.map(_.nme).mkString(", ")}")
              val arguments = symbols.iterator.map(bindings).map(_() |> fld).toSeq
              val resultTerm = app(lambdaSymbol.safeRef, tup(arguments*), "the transform's result")
              val resultSymbol = TempSymbol(N, "transformResult")
              Split.Let(resultSymbol, resultTerm, makeConsequent(resultSymbol.toScrut, Map.empty)),
            alternative))
  
  /** Construct a UCS split to match the prefix of the given scrutinee.
   * 
   *  @return The return value is a function that builds the split. */
  private def makeStringPrefixMatchSplit(
      scrutinee: Scrut,
      pattern: SP,
  )(using Raise): MakePrefixSplit = pattern match
    case Constructor(target, patternArguments, arguments) => target.symbol match
      // The case when the target refers to a pattern parameter.
      case S(symbol: VarSymbol) => symbol.decl match
        case S(param @ Param(flags = FldFlags(pat = true))) =>
          (makeConsequent, alternative) =>
            val outputSymbol = TempSymbol(N, "output") // Denotes the pattern's output.
            val remainingSymbol = TempSymbol(N, "remaining") // Denotes the remaining value.
            val mode = MatchMode.StringPrefix(outputSymbol, remainingSymbol)
            val thePattern = FlatPattern.ClassLike(target, N, mode, false)(Tree.Dummy, Nil)
            val consequent = makeConsequent(outputSymbol.toScrut, remainingSymbol.toScrut, Map.empty)
            Branch(scrutinee(), thePattern, consequent) ~: alternative
        case S(_) | N => rejectPrefixSplit
      case S(symbol) => symbol.asPat match
        // The case when the target refers to a pattern symbol.
        case S(symbol: PatternSymbol) =>
          (makeConsequent, alternative) =>
            val defn = symbol.defn.getOrElse(die)
            val outputSymbol = TempSymbol(N, "output") // Denotes the pattern's output.
            val remainingSymbol = TempSymbol(N, "remaining") // Denotes the remaining value.
            // Unfold extraction parameters and create symbols for sub-scrutinees.
            val (theExtractionArguments, makeChainedConsequent) = arguments.fold((N, makeConsequent)):
              _.iterator.zipWithIndex.foldRight(Nil: Ls[FlatPattern.Argument], makeConsequent):
                case ((argument, index), (theArguments, makeInnerSplit)) =>
                  val subScrutinee = TempSymbol(N, s"argument$index$$")
                  val makeThisSplit: MakePrefixConsequent = (outerConsumedOutput, outerRemainingOutput, outerBindings) =>
                    makeStringPrefixMatchSplit(subScrutinee.toScrut, argument)(
                      (consumedOutput, remainingOutput, bindings) => makeInnerSplit(
                        // TODO: Combine `outerConsumedOutput` and `consumedOutput`
                        consumedOutput,
                        // TODO: Combine `outerRemainingOutput` and `remainingOutput`
                        remainingOutput,
                        outerBindings ++ bindings),
                      Split.End)
                  val theArgument = FlatPattern.Argument(subScrutinee, Tree.Empty().withLocOf(argument))
                  (theArgument :: theArguments, makeThisSplit)
              .mapFirst(S(_))
            val thePatternArguments = patternArguments.iterator.zipWithIndex.map: (pattern, index) =>
              FlatPattern.Argument(TempSymbol(N, s"patternArgument$index$$"), pattern)
            .toList
            val allArguments = theExtractionArguments.fold(
              if thePatternArguments.isEmpty then N else S(thePatternArguments)
            ):
              case arguments => S(thePatternArguments ::: arguments)
            val consequent = makeChainedConsequent(outputSymbol.toScrut, remainingSymbol.toScrut, Map.empty)
            val mode = MatchMode.StringPrefix(outputSymbol, remainingSymbol)
            val thePattern = FlatPattern.ClassLike(target, allArguments, mode, false)(Tree.Dummy, Nil)
            Branch(scrutinee(), thePattern, consequent) ~: alternative
        case N => rejectPrefixSplit
      // The other possibilities do not match strings.
      case S(_) | N => rejectPrefixSplit
    case Composition(true, left, right) =>
      val makeLeft = makeStringPrefixMatchSplit(scrutinee, left)
      val makeRight = makeStringPrefixMatchSplit(scrutinee, right)
      (makeConsequent, alternative) =>
        makeLeft(makeConsequent, makeRight(makeConsequent, alternative))
    case Composition(false, left, right) => (makeConsequent, alternative) =>
      // This case is different, as the left pattern should be matched in prefix
      // mode, but the `right` pattern should be matched in full mode. If the
      // `right` pattern fails, we should check if `left` can match a different
      // prefix and retry `right`.
      // TODO: Implement the correct backtracking behavior.
      makeStringPrefixMatchSplit(scrutinee, left)(
        (leftOutput, leftRemains, leftBindings) => makeMatchSplit(scrutinee, right)(
          (rightOutput, rightBindings) => 
            val productSymbol = TempSymbol(N, "product")
            val productTerm = tup(leftOutput() |> fld, rightOutput() |> fld)
            Split.Let(productSymbol, productTerm, makeConsequent(
              productSymbol.toScrut, leftRemains, leftBindings ++ rightBindings)),
          alternative),
        alternative)
    case Negation(pattern) =>
      // This case is tricky. The question is how many of characters should be
      // left to the continuation? For example, to match string "match is over"
      // against pattern `~"game" ~ " is over"`. The first step is to match
      // pattern `"game"` as a prefix of the input. After we found it doesn't
      // not match, how many characters should we consume in this step? From a
      // global perspective, we know that we should consume the prefix
      // `"match is "``, but with backtracking, we have to try every
      // combinations before we can make a conclusion.
      rejectPrefixSplit
    case Wildcard() => (makeConsequent, alternative) => 
      // Because the wildcard pattern always matches, we can match the entire
      // string and returns an empty string as the remaining value.
      val emptyStringSymbol = TempSymbol(N, "emptyString")
      makeConsequent(scrutinee, emptyStringSymbol.toScrut, Map.empty)
      Branch(scrutinee(), FlatPattern.ClassLike(ctx.builtins.Str.safeRef, N, Nil),
        Split.Let(emptyStringSymbol, str(""),
          makeConsequent(scrutinee, emptyStringSymbol.toScrut, Map.empty))
      ) ~: alternative
    case Literal(prefix: StrLit) => (makeConsequent, alternative) =>
      // Check if the scrutinee is the same as the literal. If so, we return
      // an empty string as the remaining value.
      val isLeadingSymbol = TempSymbol(N, "isLeading")
      val isLeadingTerm = callStringStartsWith(
        scrutinee(), Term.Lit(prefix), "the result of startsWith")
      val outputSymbol = TempSymbol(N, "consumed")
      val outputTerm = callStringTake(scrutinee(), prefix.value.length, "the consumed part of input")
      val remainsSymbol = TempSymbol(N, "remains")
      val remainsTerm = callStringDrop(scrutinee(), prefix.value.length, "the remaining input")
      Split.Let(isLeadingSymbol, isLeadingTerm,
        Branch(isLeadingSymbol.safeRef,
          Split.Let(outputSymbol, outputTerm,
            Split.Let(remainsSymbol, remainsTerm,
              makeConsequent(outputSymbol.toScrut, remainsSymbol.toScrut, Map.empty)))
        ) ~: alternative)
    // Non-string literal patterns are directly discarded.
    case Literal(_) => rejectPrefixSplit
    case Range(lower: StrLit, upper: StrLit, rightInclusive) => (makeConsequent, alternative) =>
      // Check if the string is not empty. Then 
      val stringHeadSymbol = TempSymbol(N, "stringHead")
      val stringTailSymbol = TempSymbol(N, "stringTail")
      val nonEmptySymbol = TempSymbol(N, "nonEmpty")
      val nonEmptyTerm = app(this.lt.safeRef, tup(fld(int(0)), fld(sel(scrutinee(), "length"))), "string is not empty")
      Split.Let(nonEmptySymbol, nonEmptyTerm, // `0 < string.length`
        Branch(nonEmptySymbol.safeRef,
          Split.Let(stringHeadSymbol, callStringGet(scrutinee(), 0, "head"),
            Split.Let(stringTailSymbol, callStringDrop(scrutinee(), 1, "tail"),
              makeRangeTest(stringHeadSymbol.toScrut, lower, upper, rightInclusive,
                makeConsequent(stringHeadSymbol.toScrut, stringTailSymbol.toScrut, Map.empty))))
        ) ~: alternative)
    // Other range patterns cannot be string prefixes.
    case Range(_, _, _) => rejectPrefixSplit
    case Concatenation(left, right) => (makeConsequent, alternative) =>
      makeStringPrefixMatchSplit(scrutinee, left)(
        (leftConsumedOutput, leftRemainingOutput, leftBindings) =>
          makeStringPrefixMatchSplit(leftRemainingOutput, right)(
            (rightConsumedOutput, rightRemainingOutput, rightBindings) =>
              makeConsequent(leftConsumedOutput, rightRemainingOutput, leftBindings ++ rightBindings),
            alternative),
        alternative)
    // Tuples and records cannot be string prefixes.
    case Tuple(_, _, _) => rejectPrefixSplit
    case Record(_) => rejectPrefixSplit
    case Chain(first, second) => (makeConsequent, alternative) =>
      // This case is different because the first pattern might haven
      // non-string output. So, we should apply `makeMatchSplit` to the second
      // pattern, and finally pass the remains from the first pattern to the
      // continuation.
      makeStringPrefixMatchSplit(scrutinee, first)(
        (firstOutput, firstRemains, firstBindings) =>
          makeMatchSplit(firstOutput, second)(
            (secondOutput, secondBindings) =>
              makeConsequent(secondOutput, firstRemains, firstBindings ++ secondBindings),
            alternative),
        alternative)
    case alias @ Alias(pattern, id) =>
      alias.symbolOption match
        // Ignore those who don't have symbols. `Elaborator` should have
        // reported errors.
        case N =>
          log(s"pattern ${pattern.showDbg} doesn't have an alias symbol: ${id.name}")
          makeStringPrefixMatchSplit(scrutinee, pattern)
        case S(symbol) => (makeConsequent, alternative) =>
          makeStringPrefixMatchSplit(scrutinee, pattern)(
            (output, remains, bindings) =>
              makeConsequent(output, remains, bindings + (symbol -> output)),
            alternative)
    case Transform(pattern, transform) =>
      // TODO: Duplicate code with the `Transform` case in `makeMatchSplit`.
      val symbols = pattern.variables.symbols
      val params = symbols.map(Param(FldFlags.empty, _, N, Modulefulness.none))
      val lambdaSymbol = new TempSymbol(N, "transform")
      (makeConsequent, alternative) => Split.Let(
        sym = lambdaSymbol,
        term = Term.Lam(PlainParamList(params), transform),
        // Declare the lambda function at the outermost level. Even if there
        // are multiple disjunctions in the consequent, we will not need to
        // repeat the `transform` term.
        tail = makeStringPrefixMatchSplit(scrutinee, pattern)(
          // Note that the output is not used. Semantically, the `transform`
          // term can only access the matched values by bindings.
          (_output, remains, bindings) =>
            val arguments = symbols.iterator.map(bindings).map(_() |> fld).toSeq
            val resultTerm = app(lambdaSymbol.safeRef, tup(arguments*), "the transform's result")
            val resultSymbol = TempSymbol(N, "transformResult")
            Split.Let(resultSymbol, resultTerm, makeConsequent(resultSymbol.toScrut, remains, Map.empty)),
          alternative))
  
  /** Make a term like `MatchFailure(null)`. We will synthesize detailed
   *  error messages and pass them to the function. */
  private def failure: Split = Split.Else(makeMatchFailure())
  
  /** Create a method from the given UCS splits.
   *  The function has a parameter list that contains the pattern parameters and
   *  a parameter that represents the input value.
   */
  private def makeMethod(
      owner: Opt[PatternSymbol],
      name: Str,
      patternParameters: List[Param],
      scrut: VarSymbol,
      topmost: Split
  ): TermDefinition =
    val sym = BlockMemberSymbol(name, Nil)
    val tsym = TermSymbol(Fun, owner, Ident(name))
    // Pattern parameters are passed as objects.
    val patternInputs = patternParameters.map(_.copy(flags = FldFlags.empty))
    // The last parameter is the scrutinee.
    val scrutParam = Param(FldFlags.empty, scrut, N, Modulefulness.none)
    val ps = PlainParamList(patternInputs :+ scrutParam)
    TermDefinition(Fun, sym, tsym, ps :: Nil, N, N,
      S(Term.IfLike(Keyword.`if`, topmost)), FlowSymbol(s"‹unapply-result›"),
      TermDefFlags.empty, Modulefulness.none, Nil, N)
  
  /** Translate a list of extractor/matching functions for the given pattern.
   *  There are currently two functions: `unapply` and `unapplyStringPrefix`.
   *  
   *  - `unapply` is used for matching the entire scrutinee. It returns the
   *    captured/extracted values.
   *  - `unapplyStringPrefix` is used for matching the string prefix of the
   *    scrutinee. It returns the remaining string and the captured/extracted
   *    values. If the given tree does not represent a string pattern, this
   *    function will not be generated.
   *  
   *  @param pattern We will eventually generate methods from the omnipotent
   *                 `Pattern` class. Now the new `pattern` parameter and the
   *                 old `body` parameter are mixed.
   */
  def compilePattern(pd: PatternDef): Ls[TermDefinition] = trace(
    pre = s"compilePattern <<< ${pd.showDbg}", 
    post = (blk: Ls[TermDefinition]) => s"compilePattern >>> $blk"
  ):
    // TODO: Use `pd.extractionParams`.
    val unapply = scoped("ucs:translation"):
      val inputSymbol = VarSymbol(Ident("input"))
      val topmost = makeMatchSplit(inputSymbol.toScrut, pd.pattern)
        ((output, bindings) => Split.Else(makeMatchResult(output())), failure)
      log(s"Translated `unapply`: ${topmost.prettyPrint}")
      makeMethod(N, "unapply", pd.patternParams, inputSymbol, topmost)
    // TODO: Use `pd.extractionParams`.
    val unapplyStringPrefix = scoped("ucs:cp"):
      // We don't report errors here because they have been already reported in
      // the translation of `unapply` function.
      given Raise = Function.const(())
      val inputSymbol = VarSymbol(Ident("input"))
      val topmost = makeStringPrefixMatchSplit(inputSymbol.toScrut, pd.pattern)
        ((consumedOutput, remainingOutput, bindings) => Split.Else:
          makeMatchResult(tup(fld(consumedOutput()), fld(remainingOutput()))), failure)
      log(s"Translated `unapplyStringPrefix`: ${topmost.prettyPrint}")
      makeMethod(N, "unapplyStringPrefix", pd.patternParams, inputSymbol, topmost)
    unapply :: unapplyStringPrefix :: Nil
  
  /** Generate the record statements of `unapply` methods that can be used in
   *  objects for anonymous patterns. */
  def makeUnapplyRecordStatements(
      name: Str,
      patternParameters: List[Param],
      scrut: VarSymbol,
      topmost: Split
  ): Ls[Statement] =
    val fieldSymbol = TempSymbol(N, name)
    val decl = LetDecl(fieldSymbol, Nil)
    val param = Param(FldFlags.empty, scrut, N, Modulefulness.none)
    val paramList = PlainParamList(param :: Nil)
    val lambda = Term.Lam(paramList, Term.IfLike(Keyword.`if`, topmost))
    val defineVar = DefineVar(fieldSymbol, lambda)
    val field = RcdField(Term.Lit(StrLit(name)), fieldSymbol.safeRef)
    decl :: defineVar :: field :: Nil
  
  /** Translate an anonymous pattern. They are usually pattern arguments. */
  def compileAnonymousPattern(patternParams: Ls[Param], params: Ls[Param], pattern: SP): Term = trace(
    pre = s"compileAnonymousPattern <<< $pattern", 
    post = (blk: Term) => s"compileAnonymousPattern >>> $blk"
  ):
    // If the `target` refers to a pattern symbol, we can reference the pattern.
    val term = pattern match
      case Constructor(target, Nil, N) =>
        log(s"target.symbol: ${target.symbol}")
        log(s"target.symbol.flatMap(_.asPat): ${target.symbol.flatMap(_.asPat)}")
        target.symbol.flatMap(_.asPat).flatMap(Compiler.reference(_, target.toLoc))
      case _ => N
    log(s"term: ${term}")
    term.getOrElse:
      val unapply = scoped("ucs:translation"):
        val inputSymbol = VarSymbol(Ident("input"))
        val topmost = makeMatchSplit(inputSymbol.toScrut, pattern)
          ((output, bindings) => Split.Else(makeMatchResult(output())), failure)
        log(s"Translated `unapply`: ${topmost.prettyPrint}")
        makeUnapplyRecordStatements("unapply", patternParams, inputSymbol, topmost)
      val unapplyStringPrefix = scoped("ucs:cp"):
        // We don't report errors here because they have been already reported in
        // the translation of `unapply` function.
        given Raise = Function.const(())
        val inputSymbol = VarSymbol(Ident("input"))
        val topmost = makeStringPrefixMatchSplit(inputSymbol.toScrut, pattern)
          ((consumedOutput, remainingOutput, bindings) => Split.Else:
            makeMatchResult(tup(fld(consumedOutput()), fld(remainingOutput()))), failure)
        log(s"Translated `unapplyStringPrefix`: ${topmost.prettyPrint}")
        makeUnapplyRecordStatements("unapplyStringPrefix", patternParams, inputSymbol, topmost)
      Term.Rcd(false, unapply ::: unapplyStringPrefix)
