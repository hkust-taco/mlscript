package hkmc2
package semantics
package ups

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import ucs.{TermSynthesizer, FlatPattern, error, warn, safeRef}, ucs.extractors.*
import syntax.{Fun, Keyword, Tree}, Tree.{Ident, StrLit}, Keyword.{`as`, `=>`}
import collection.mutable.{Buffer, HashMap}, collection.immutable.SeqMap
import Elaborator.{Ctx, State, ctx}, utils.TL
import semantics.Pattern as SP // "SP" is short for "semantic patterns"
import Term.Ref

object SplitCompiler:
  /** String range bounds must be single characters. */
  def isInvalidStringBounds(lo: StrLit, hi: StrLit)(using Raise): Bool =
    val ds = Buffer.empty[(Message, Option[Loc])]
    if lo.value.length != 1 then
      ds += msg"The lower bound of character ranges must be a single character." -> lo.toLoc
    if hi.value.length != 1 then
      ds += msg"The upper bound of character ranges must be a single character." -> hi.toLoc
    if ds.nonEmpty then error(ds.toSeq*)
    ds.nonEmpty
  
  /** A class that can generate `Ref` to the scrutinee. It also comes with a few
   *  mutable maps to reuse sub-scrutinees. Memoization of sub-scrutinees help
   *  the normalization to merge let bindings from different branches.
   */
  sealed abstract class Scrut:
    private val subScrutinees: Buffer[SymbolScrut] = Buffer.empty
    private val fields: HashMap[Ident, SymbolScrut] = HashMap.empty
    private val tupleLead: HashMap[Int, SymbolScrut] = HashMap.empty
    private val tupleLast: HashMap[Int, SymbolScrut] = HashMap.empty
    
    def apply(): Term.Ref
    def getSubScrutinee(index: Int)(using State): SymbolScrut =
      while subScrutinees.size <= index do
        subScrutinees += TempSymbol(N, s"argument${subScrutinees.size}$$").toScrut
      subScrutinees(index)
    def getTupleLeadSubScrutinee(index: Int)(using State): SymbolScrut =
      tupleLead.getOrElseUpdate(index, TempSymbol(N, s"element$index$$").toScrut)
    def getTupleLastSubScrutinee(index: Int)(using State): SymbolScrut =
      tupleLast.getOrElseUpdate(index, TempSymbol(N, s"lastElement$index$$").toScrut)
    def getFieldScrutinee(fieldName: Ident)(using State): SymbolScrut =
      fields.getOrElseUpdate(fieldName, TempSymbol(N, s"field_${fieldName.name}$$").toScrut)
  
  object Scrut:
    def from(ref: Term.Ref): RefScrut = RefScrut(() => ref)
  
  class RefScrut(make: () => Term.Ref) extends Scrut:
    def apply(): Ref = make()
  
  class SymbolScrut(val symbol: BlockLocalSymbol) extends Scrut:
    def apply(): Ref = symbol.ref()
  
  extension (symbol: BlockLocalSymbol)
    def toScrut: SymbolScrut = SymbolScrut(symbol)
  
  type BindingMap = SeqMap[VarSymbol, Scrut]
  
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
  
  /** The continuation function returned by `makeStringPrefixMatchSplit`. It
   *  represents functions making splits that match any given string's prefix.
   */
  type MakePrefixSplit = (makeConsequent: MakePrefixConsequent, alternative: Split) => Split
  
  object RejectPrefix extends ((MakePrefixConsequent, Split) => Split):
    def apply(makeConsequent: MakePrefixConsequent, alternative: Split): Split = alternative
    
  extension (makePrefixSplit: MakePrefixSplit)
    /** Build another `MakePrefixSplit` if the function does not reject. */
    transparent inline def whenAccept(derivedFunction: => MakePrefixSplit): MakePrefixSplit =
      if makePrefixSplit is RejectPrefix then RejectPrefix else derivedFunction
  
  /** A lazily created scrutinee. */
  class LazyScrut(nameHint: Opt[Str] = N)(using State) extends Scrut:
    private var _hasBeenUsed = false
    private lazy val symbol =
      _hasBeenUsed = true
      TempSymbol(N, nameHint.getOrElse("output"))
    def apply(): Ref = symbol.safeRef
    def toList: Ls[TempSymbol] = if _hasBeenUsed then symbol :: Nil else Nil
    def toLet(term: => Term, tail: Split): Split =
      if _hasBeenUsed then Split.Let(symbol, term, tail) else tail

import SplitCompiler.*

/** This class compiles a pattern to a split that matches the pattern. */
class SplitCompiler(using tl: TL)(using State, Ctx, Raise) extends TermSynthesizer:
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
    def folded(z: (Ls[SymbolScrut], MakeConsequent))(makeSubScrutineeSymbol: Int => SymbolScrut) =
      patterns.iterator.zipWithIndex.foldRight(z):
        case ((element, index), (subScrutinees, makeInnerSplit)) =>
          val subScrutinee = makeSubScrutineeSymbol(index)
          val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
            makeMatchSplit(subScrutinee, element)(
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
  def makeMatchSplit(scrutinee: Scrut, pattern: SP): MakeSplit =
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
              val subScrutinee = scrutinee.getSubScrutinee(index)
              val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
                makeMatchSplit(subScrutinee, argument)(
                  (_argumentOutput, argumentBindings) => makeInnerSplit(
                    // Note that we discard the argument pattern's output becuase
                    // we can't synthesize a valid term if the argument pattern
                    // produce some output.
                    outerOutput, // TODO: Combine `outerOutput` with `argumentOutput`.
                    outerBindings ++ argumentBindings),
                  Split.End)
              // TODO: We should check the arguments right here, rather than in
              // `Normalization`. Please fix this in the next commit.
              val tree = if argument.isInstanceOf[Wildcard] then Tree.Under() else Tree.Empty()
              val theArgument = FlatPattern.Argument(subScrutinee.symbol, tree.withLocOf(argument))
              (theArgument :: theArguments, makeThisSplit)
          .mapFirst(S(_))
        // For pattern arguments for higher-order patterns, we generate the
        // inline objects with `unapply` and `unapplyStringPrefix` methods.
        val arguments0 = patternArguments.iterator.zipWithIndex.map: (pattern, index) =>
          FlatPattern.Argument(TempSymbol(N, s"patternArgument$index$$"), pattern)
        .toList
        val theArguments = arguments1.fold(if arguments0.isEmpty then N else S(arguments0)):
          case arguments => S(arguments0 ::: arguments)
        // Here, passing `scrutinee` as the output is not always correct. When
        // `target` is a class or object, the output should be the scrutinee.
        // When `target` is a pattern, the output should be the pattern's output.
        // But it is until the normalization we can tell whether `target` is a
        // pattern or not.
        val outputSymbol = new LazyScrut()
        val consequent = makeChainedConsequent(outputSymbol, SeqMap.empty)
        Branch(scrutinee(), FlatPattern.ClassLike(target, theArguments, outputSymbol.toList), outputSymbol.toLet(scrutinee(), consequent)) ~: alternative
      case Composition(true, left, right) =>
        makeMatchSplit(scrutinee, left) | makeMatchSplit(scrutinee, right)
      case Composition(false, left, right) => (makeConsequent, alternative) =>
        makeMatchSplit(scrutinee, left)(
          (leftOutput, leftBindings) => makeMatchSplit(scrutinee, right)(
            (rightOutput, rightBindings) => 
              val outputScrut = new LazyScrut()
              outputScrut.toLet(
                tup(leftOutput() |> fld, rightOutput() |> fld),
                makeConsequent(outputScrut, leftBindings ++ rightBindings) ~~: alternative),
            alternative),
          alternative)
      case Negation(pattern) => (makeConsequent, alternative) =>
        // Currently, the negation pattern produces the original value. In the
        // future, we would include diagnostic information about why the pattern
        // failed. Note that this feature requires the `alternative` parameter
        // to be a function that takes a diagnostic information generation
        // function.
        val outputSymbol = new LazyScrut()
        makeMatchSplit(scrutinee, pattern)(
          (_output, _bindings) => alternative, // The output and bindings are discarded.
          // The place where the diagnostic information should be stored.
          outputSymbol.toLet(scrutinee(), makeConsequent(outputSymbol, SeqMap.empty) ~~: alternative)
        )
      // Note that we might duplicate the alternative split here.
      case Wildcard() => (makeConsequent, alternative) => makeConsequent(scrutinee, SeqMap.empty) ~~: alternative
      case Literal(literal) => (makeConsequent, alternative) =>
        Branch(scrutinee(), FlatPattern.Lit(literal)(Nil), makeConsequent(scrutinee, SeqMap.empty)) ~: alternative
      case Range(lower, upper, rightInclusive) => (makeConsequent, alternative) =>
        makeRangeTest(scrutinee, lower, upper, rightInclusive, makeConsequent(scrutinee, SeqMap.empty)) ~~: alternative
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
      case Tuple(elements, N) => (makeConsequent, alternative) =>
        // Fixed-length tuple patterns are similar to constructor patterns.
        val z = (Nil: Ls[BlockLocalSymbol], makeConsequent)
        // TODO: Deduplicate the code with the `Constructor` case.
        val (subScrutinees, makeChainedConsequent) = elements.iterator.zipWithIndex.foldRight(z):
          case ((element, index), (subScrutinees, makeInnerSplit)) =>
            val subScrutinee = scrutinee.getTupleLeadSubScrutinee(index)
            val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
              makeMatchSplit(subScrutinee, element)(
                (_elementOutput, elementBindings) =>
                  val bindings = outerBindings ++ elementBindings
                  makeInnerSplit(
                  outerOutput, // TODO: Combine `outerOutput` and `elementOutput`
                  bindings),
                Split.End)
            (subScrutinee.symbol :: subScrutinees, makeThisSplit)
        // END TODO
        makeTupleBranch(scrutinee(), subScrutinees, makeChainedConsequent(scrutinee, SeqMap.empty), alternative)
      case Tuple(leading, S((_, spread, trailing))) => (makeConsequent, alternative) =>
        val (trailSubScrutinees, makeConsequent0) = trailing.folded((Nil, makeConsequent)):
          index => scrutinee.getTupleLastSubScrutinee(index)
        val spreadSubScrutinee = TempSymbol(N, "middleElements")
        val makeConsequent1: MakeConsequent = (outerOutput, outerBindings) =>
          makeMatchSplit(spreadSubScrutinee.toScrut, spread)(
            (spreadOutput, spreadBindings) => makeConsequent0(
              spreadOutput, // TODO: Combine `outerOutput` and `spreadOutput`
              outerBindings ++ spreadBindings),
            Split.End)
        val (leadingSubScrutinees, makeConsequent2) = leading.folded((Nil, makeConsequent1)):
          index => scrutinee.getTupleLeadSubScrutinee(index)
        makeTupleBranch(
          scrutinee(),
          leadingSubScrutinees.map(_.symbol),
          spreadSubScrutinee,
          trailSubScrutinees.map(_.symbol),
          makeConsequent2(scrutinee, SeqMap.empty),
          alternative)
      case Record(fields) => (makeConsequent, alternative) =>
        // This case is similar to the `Constructor` case.
        val z = (Nil: Ls[(Ident, BlockLocalSymbol)], makeConsequent)
        // TODO: Deduplicate the code with the `Constructor` case.
        val (entries, makeChainedConsequent) = fields.iterator.zipWithIndex.foldRight(z):
          case (((key, pattern), index), (fields, makeInnerSplit)) =>
            val subScrutinee = scrutinee.getFieldScrutinee(key)
            val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
              makeMatchSplit(subScrutinee, pattern)(
                (fieldOutput, fieldBindings) => makeInnerSplit(
                  fieldOutput, // TODO: Combine `outerOutput` and `fieldOutput`
                  outerBindings ++ fieldBindings),
                alternative) // We fill in the alternative here. This is
                             // different from the `Constructor` case.
            ((key, subScrutinee.symbol) :: fields, makeThisSplit)
        // END TODO
        val consequent = makeChainedConsequent(scrutinee, SeqMap.empty)
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
        case N => makeMatchSplit(scrutinee, pattern)
        case S(symbol) => (makeConsequent, alternative) =>
          makeMatchSplit(scrutinee, pattern)(
            (output, bindings) =>
              makeConsequent(output, bindings + (symbol -> output)),
            alternative)
      case Transform(pattern, parameters, transform) =>
        // We should first create a local function that transforms the captured
        // values. So far, `pattern`'s variables should be bound to symbols.
        // Thus, we can make a parameter list from the symbols. Then, we make
        // a lambda term from the parameter list and the transform term. Because
        // `pattern` might be translated to many branches, making a lambda term
        // in advance reduces code duplication.
        val symbols = pattern.variables.symbols
        val params = parameters.map:
          case (_, parameterSymbol) =>
            Param(FldFlags.empty, parameterSymbol, N, Modulefulness.none)
        val lambdaSymbol = new TempSymbol(N, "transform")
        // Next, we need to elaborate the pattern into a split. Note that
        // `makeMatchSplit` returns a function that takes a split as the
        // consequence. `makeMatchSplit` also takes a list of symbols so that
        // it needs to make sure that those bindings are available in the
        // consequence split.
        (makeConsequent, alternative) => Split.Let(
          sym = lambdaSymbol,
          term = Term.Lam(PlainParamList(params), transform.mkClone),
          // Declare the lambda function at the outermost level. Even if there
          // are multiple disjunctions in the consequent, we will not need to
          // repeat the `transform` term.
          tail = makeMatchSplit(scrutinee, pattern)(
            // Note that the output is not used. Semantically, the `transform`
            // term can only access the matched values by bindings.
            (_output, bindings) =>
              val arguments = symbols.iterator.map(bindings).map(_() |> fld).toSeq
              val resultTerm = app(lambdaSymbol.safeRef, tup(arguments*), "the transform's result")
              val resultSymbol = TempSymbol(N, "transformResult")
              Split.Let(resultSymbol, resultTerm, makeConsequent(resultSymbol.toScrut, SeqMap.empty)),
            alternative))
      case Annotated(pattern, annotations) =>
        // Currently, we only support `@compile` annotation, so here we only
        // check whether this annotation exists, and report an error for all
        // other annotations.
        val shouldCompile = annotations.foldLeft(true): (acc, term) =>
          term.symbol match
            case S(symbol) if symbol === ctx.builtins.annotations.compile => true
            case S(_) | N =>
              warn(msg"This annotation is not supported here." -> term.toLoc,
                msg"Note: Patterns only support the `@compile` annotation." -> pattern.toLoc)
              acc
        if shouldCompile then compilePattern(scrutinee, pattern) else makeMatchSplit(scrutinee, pattern)
      case Guarded(pattern, guard) => (makeConsequent, alternative) =>
        makeMatchSplit(scrutinee, pattern)(
          (output, bindings) =>
            val guardSymbol = TempSymbol(N, "guardResult")
            val branch = Branch(guardSymbol.ref(), makeConsequent(output, bindings))
            val innermost = Split.Let(guardSymbol, guard, branch ~: Split.End)
            // The creation of bindings here is repeated with the creation of
            // bindings during desugaring. We can add a piece of information
            // to the `bindings` map. See tests in `where.mls`.
            bindings.iterator.foldLeft(innermost):
              case (innerSplit, (symbol, mkTerm)) => Split.Let(symbol, mkTerm(), innerSplit),
          alternative)
  
  /** Construct a UCS split to match the prefix of the given scrutinee.
   * 
   *  @return The return value is a function that builds the split. */
  protected def makeStringPrefixMatchSplit(
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
            val consequent = makeConsequent(outputSymbol.toScrut, remainingSymbol.toScrut, SeqMap.empty)
            Branch(scrutinee(), thePattern, consequent) ~: alternative
        case S(_) | N => RejectPrefix
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
            val consequent = makeChainedConsequent(outputSymbol.toScrut, remainingSymbol.toScrut, SeqMap.empty)
            val mode = MatchMode.StringPrefix(outputSymbol, remainingSymbol)
            val thePattern = FlatPattern.ClassLike(target, allArguments, mode, false)(Tree.Dummy, Nil)
            Branch(scrutinee(), thePattern, consequent) ~: alternative
        case N => RejectPrefix
      // The other possibilities do not match strings.
      case S(_) | N => RejectPrefix
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
      RejectPrefix
    case Wildcard() => (makeConsequent, alternative) => 
      // Because the wildcard pattern always matches, we can match the entire
      // string and returns an empty string as the remaining value.
      val emptyStringSymbol = TempSymbol(N, "emptyString")
      makeConsequent(scrutinee, emptyStringSymbol.toScrut, SeqMap.empty)
      Branch(scrutinee(), FlatPattern.ClassLike(ctx.builtins.Str.safeRef, N, Nil),
        Split.Let(emptyStringSymbol, str(""),
          makeConsequent(scrutinee, emptyStringSymbol.toScrut, SeqMap.empty))
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
              makeConsequent(outputSymbol.toScrut, remainsSymbol.toScrut, SeqMap.empty)))
        ) ~: alternative)
    // Non-string literal patterns are directly discarded.
    case Literal(_) => RejectPrefix
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
                makeConsequent(stringHeadSymbol.toScrut, stringTailSymbol.toScrut, SeqMap.empty))))
        ) ~: alternative)
    // Other range patterns cannot be string prefixes.
    case Range(_, _, _) => RejectPrefix
    case Concatenation(left, right) => (makeConsequent, alternative) =>
      makeStringPrefixMatchSplit(scrutinee, left)(
        (leftConsumedOutput, leftRemainingOutput, leftBindings) =>
          makeStringPrefixMatchSplit(leftRemainingOutput, right)(
            (rightConsumedOutput, rightRemainingOutput, rightBindings) =>
              makeConsequent(leftConsumedOutput, rightRemainingOutput, leftBindings ++ rightBindings),
            alternative),
        alternative)
    // Tuples and records cannot be string prefixes.
    case Tuple(_, _) => RejectPrefix
    case Record(_) => RejectPrefix
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
        case N => makeStringPrefixMatchSplit(scrutinee, pattern)
        case S(symbol) =>
          val make = makeStringPrefixMatchSplit(scrutinee, pattern)
          make.whenAccept:
            (makeConsequent, alternative) => make(
              (output, remains, bindings) =>
                makeConsequent(output, remains, bindings + (symbol -> output)),
              alternative)
    case Transform(pattern, parameters, transform) =>
      val make = makeStringPrefixMatchSplit(scrutinee, pattern)
      make.whenAccept:
        // Declare the lambda function at the outermost level. Even if there are
        // multiple disjunctions in the consequent, we will not need to repeat
        // the `transform` term.
        val symbols = pattern.variables.symbols
        val params = parameters.map:
          case (_, parameterSymbol) =>
            Param(FldFlags.empty, parameterSymbol, N, Modulefulness.none)
        val lambdaSymbol = new TempSymbol(N, "transform")
        (makeConsequent, alternative) => Split.Let(
          sym = lambdaSymbol,
          term = Term.Lam(PlainParamList(params), transform),
          tail = make(
            // Note that the output is not used. Semantically, the `transform`
            // term can only access the matched values by bindings.
            (_output, remains, bindings) =>
              val arguments = symbols.iterator.map(bindings).map(_() |> fld).toSeq
              val resultTerm = app(lambdaSymbol.safeRef, tup(arguments*), "the transform's result")
              val resultSymbol = TempSymbol(N, "transformResult")
              Split.Let(resultSymbol, resultTerm, makeConsequent(resultSymbol.toScrut, remains, SeqMap.empty)),
            alternative))
    case Guarded(pattern, guard) =>
      val make = makeStringPrefixMatchSplit(scrutinee, pattern)
      make.whenAccept:
        (makeConsequent, alternative) => make(
          (output, remains, bindings) =>
            val guardSymbol = TempSymbol(N, "guardResult")
            val branch = Branch(guardSymbol.ref(), makeConsequent(output, remains, bindings))
            val innermost = Split.Let(guardSymbol, guard, branch ~: Split.End)
            // The creation of bindings here is repeated with the creation of
            // bindings during desugaring. We can add a piece of information
            // to the `bindings` map. See tests in `where.mls`.
            bindings.iterator.foldLeft(innermost):
              case (innerSplit, (symbol, mkTerm)) => Split.Let(symbol, mkTerm(), innerSplit),
          alternative)
  
  /** This method handles the efficient and non-backtracking pattern compilation. 
    * Note that we still have not supported accessing pattern parameters in the
    * naive pattern declaration in the efficient pattern compilation. */
  def compilePattern(scrutinee: Scrut, pattern: SP): MakeSplit =
  (makeConsequent, alternative) => scoped("ucs:ups:compilation"):
    // Instantiate the pattern and all patterns used in it.
    val instantiator = new Instantiator
    val (synonym, context) = instantiator(pattern)
    // Initate the compilation.
    val compiler = new Compiler(using context)
    val ((matcherSymbol, fieldName), implementations) = compiler.buildMatcher(synonym)
    val innermostSplit =
      // 1. Bind the call result to a variable.
      val recordSymbol = TempSymbol(N, "matchRecord")
      val recordTerm = app(matcherSymbol.safeRef, tup(fld(scrutinee())), "result of matcher function")
      val f1 = Split.Let(recordSymbol, recordTerm, _)
      // 2. Select the selection field to the result.
      val matchResultSymbol = TempSymbol(N, "matchResult")
      val matchResultTerm = sel(recordSymbol.safeRef, fieldName)
      val f2 = Split.Let(matchResultSymbol, matchResultTerm, _)
      // 3. Check if the field value is a `MatchResult` and bind the output.
      val outputSymbol = TempSymbol(N, "patternOutput")
      val bindingsSymbol = TempSymbol(N, "bindings") // TODO: This is useless.
      // val consequent = aliasOutputSymbols(outputSymbol.safeRef, outputSymbols, consequent)
      // TODO: How to forward the bindings from the pattern compilation to here?
      val consequent = makeConsequent(outputSymbol.toScrut, SeqMap.empty)
      val pattern = matchResultPattern(S(outputSymbol :: bindingsSymbol :: Nil))
      val branch = Branch(matchResultSymbol.safeRef, pattern, consequent)
      f1(f2(branch ~: alternative))
    implementations.iterator.foldRight(innermostSplit):
      case ((symbol, paramList, term), innerSplit) =>
        log(term.showDbg)
        Split.Let(symbol, Term.Lam(paramList, term), innerSplit)
