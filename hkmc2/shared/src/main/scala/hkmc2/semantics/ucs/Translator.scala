package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import Split.display, ucs.Normalization
import syntax.{Fun, Keyword, ParamBind, Tree}, Tree.*, Keyword.{`as`, `=>`}
import scala.collection.mutable.{Buffer, Set as MutSet}
import Elaborator.{Ctx, State, ctx}
import Desugarer.unapply

object Translator:
  /** String range bounds must be single characters. */
  def isInvalidStringBounds(lo: StrLit, hi: StrLit)(using Raise): Bool =
    val ds = Buffer.empty[(Message, Option[Loc])]
    if lo.value.length != 1 then
      ds += msg"String range bounds must have only one character." -> lo.toLoc
    if hi.value.length != 1 then
      ds += msg"String range bounds must have only one character." -> hi.toLoc
    if ds.nonEmpty then error(ds.toSeq*)
    ds.nonEmpty
  
  /** Each scrutinee is represented by a function that creates a reference to
   *  the scrutinee symbol. It is sufficient for current implementation.
   */
  type Scrut = () => Term.Ref
  
  extension (symbol: BlockLocalSymbol)
    def toScrut: Scrut = () => symbol.ref().withIArgs(Nil)
  
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

import Translator.*

/** This class translates a tree describing a pattern into functions that can
 *  perform pattern matching on terms described by the pattern.
 */
class Translator(val elaborator: Elaborator)(using State, Ctx, Raise) extends DesugaringBase:
  import elaborator.term, elaborator.tl.*, HelperExtractors.*, FlatPattern.MatchMode
  import Pattern.*
  
  private type CaptureMap = Map[Param, Term.Ref]
  
  private type Inner = CaptureMap => Split
  
  private type PrefixInner = (CaptureMap, Scrut) => Split
  
  private lazy val lteq = State.builtinOpsMap("<=")
  private lazy val lt = State.builtinOpsMap("<")
  private lazy val eq = State.builtinOpsMap("===")
  
  private def makeRangeTest(scrut: Scrut, lo: syntax.Literal, hi: syntax.Literal, rightInclusive: Bool, innerSplit: Split) =
    def scrutFld = fld(scrut())
    val test1 = app(lteq.ref(), tup(fld(Term.Lit(lo)), scrutFld), "isGreaterThanLower")
    val upperOp = if rightInclusive then lteq else lt
    val test2 = app(upperOp.ref(), tup(scrutFld, fld(Term.Lit(hi))), "isLessThanUpper")
    plainTest(test1, "isGreaterThanLower")(plainTest(test2, "isLessThanUpper")(innerSplit))
  
  @deprecated("Remove after we finished the new pattern translation.")
  private def makeRange(scrut: Scrut, lo: syntax.Literal, hi: syntax.Literal, rightInclusive: Bool, inner: Inner) =
    def scrutFld = fld(scrut())
    val test1 = app(lteq.ref(), tup(fld(Term.Lit(lo)), scrutFld), "gtLo")
    val upperOp = if rightInclusive then lteq else lt
    val test2 = app(upperOp.ref(), tup(scrutFld, fld(Term.Lit(hi))), "ltHi")
    plainTest(test1, "gtLo")(plainTest(test2, "ltHi")(inner(Map.empty)))
  
  /** Create a pattern object that contains the given pattern. */
  def makeAnonymousPatternObject(
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
    val field = RcdField(Term.Lit(StrLit(name)), fieldSymbol.ref())
    decl :: defineVar :: field :: Nil
  
  extension (patterns: Ls[Pattern])
    def folded(z: (Ls[TempSymbol], MakeConsequent))(makeSubScrutineeSymbol: Int => TempSymbol) =
      patterns.iterator.zipWithIndex.foldRight(z):
        case ((element, index), (subScrutinees, makeInnerSplit)) =>
          val subScrutinee = makeSubScrutineeSymbol(index)
          val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
            makeMatchSplit(subScrutinee.toScrut, element, Nil /* TODO */)(
              (elementOutput, elementBindings) => makeInnerSplit(
                elementOutput, // TODO: Combine `outerOutput` and `elementOutput`
                outerBindings ++ elementBindings),
              Split.End)
          (subScrutinee :: subScrutinees, makeThisSplit)
  
  /** Make a UCS split that matches the entire scrutinee against the pattern.
   *  Since each pattern has an output, the split is responsible for creating
   *  a binding that holds the output value and pass it to the continuation
   *  function that makes the conseuqent split.
   * 
   *  @param bindings Variables that can be bound in this pattern. Currently,
   *                  when we encounter an `Alias` pattern, we check whether
   *                  its symbol exists in this list before binding it. But I'm
   *                  not sure whether this check is redundant.
   */
  private def makeMatchSplit(
      scrutinee: Scrut,
      pattern: Pattern,
      allowedBindings: Ls[VarSymbol]
  ): MakeSplit =
    import Pattern.*
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
                makeMatchSplit(subScrutinee.toScrut, argument, allowedBindings)(
                  (argumentOutput, argumentBindings) => makeInnerSplit(
                    argumentOutput, // TODO: Combine `outerOutput` and `argumentOutput`
                    outerBindings ++ argumentBindings),
                  Split.End)
              val theArgument = FlatPattern.Argument(subScrutinee, Tree.Empty().withLocOf(argument), N, N)
              (theArgument :: theArguments, makeThisSplit)
          .mapFirst(S(_))
        // For pattern arguments for higher-order patterns, we generate the
        // inline objects with `unapply` and `unapplyStringPrefix` methods.
        val arguments0 = patternArguments.iterator.zipWithIndex.map: (pattern, index) =>
          val patternSymbol = TempSymbol(N, s"patternArgument$index$$")
          val patternObject = translateAnonymousPattern(Nil, Nil, pattern)
          FlatPattern.Argument(patternSymbol, Tree.Empty().withLocOf(pattern), N, S(patternObject))
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
        Branch(scrutinee(), FlatPattern.ClassLike(target, theArguments, MatchMode.Default, false)(Tree.Dummy, outputSymbol :: Nil), consequent) ~: alternative
      case Composition(true, left, right) =>
        makeMatchSplit(scrutinee, left, allowedBindings) | makeMatchSplit(scrutinee, right, allowedBindings)
      case Composition(false, left, right) => (makeConsequent, alternative) =>
        makeMatchSplit(scrutinee, left, allowedBindings)(
          (leftOutput, leftBindings) => makeMatchSplit(scrutinee, right, allowedBindings)(
            (rightOutput, rightBindings) => 
              val tupleIdent = Ident("tupledResults")
              val tupleSymbol = TempSymbol(N, "tupledResults")
              val tupleTerm = tup(leftOutput() |> fld, rightOutput() |> fld)
              Split.Let(tupleSymbol, tupleTerm, makeConsequent(() => tupleSymbol.ref(), leftBindings ++ rightBindings) ~~: alternative),
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
        makeMatchSplit(scrutinee, pattern, allowedBindings)(
          (_output, _bindings) => alternative, // The output and bindings are discarded.
          Split.Let(outputSymbol, outputTerm, makeConsequent(() => outputSymbol.ref(), Map.empty) ~~: alternative)
        )
      // Because a wildcard pattern always matches, `alternative` is not used.
      case Wildcard() => (makeConsequent, _) => makeConsequent(scrutinee, Map.empty)
      case Literal(literal) => (makeConsequent, alternative) =>
        Branch(scrutinee(), FlatPattern.Lit(literal)(Nil), makeConsequent(scrutinee, Map.empty)) ~: alternative
      case Range(lower, upper, rightInclusive) => (makeConsequent, alternative) =>
        makeRangeTest(scrutinee, lower, upper, rightInclusive, makeConsequent(scrutinee, Map.empty)) ~~: alternative
      case Concatenation(left, right) => (makeConsequent, alternative) =>
        makeStringPrefixMatchSplit(scrutinee, left)(
          (consumedOutput, remainingOutput, bindings) =>
            makeMatchSplit(remainingOutput, right, allowedBindings)(
              // Here we discard the postfix output because I still haven't
              // figured out the semantics of string concatenation.
              (_postfixOutput, bindings) => makeConsequent(scrutinee, bindings) ~~: alternative,
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
              makeMatchSplit(subScrutinee.toScrut, element, allowedBindings)(
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
          makeMatchSplit(spreadSubScrutinee.toScrut, spread, allowedBindings)(
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
              makeMatchSplit(subScrutinee.toScrut, pattern, allowedBindings)(
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
        makeMatchSplit(scrutinee, first, allowedBindings)(
          (firstOutput, firstBindings) => makeMatchSplit(firstOutput, second, allowedBindings)(
            (secondOutput, secondBindings) => makeConsequent(secondOutput, firstBindings ++ secondBindings),
            alternative),
          alternative)
      case alias @ Alias(pattern, id) => alias.symbolOption match
        // Ignore those who don't have symbols. `Elaborator` should have
        // reported errors.
        case N =>
          log(s"pattern ${pattern.showDbg} doesn't have an alias symbol: ${id.name}")
          makeMatchSplit(scrutinee, pattern, allowedBindings)
        case S(symbol) => (makeConsequent, alternative) =>
          makeMatchSplit(scrutinee, pattern, allowedBindings)(
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
          tail = makeMatchSplit(scrutinee, pattern, symbols)(
            // Note that the output is not used. Semantically, the `transform`
            // term can only access the matched values by bindings.
            (_output, bindings) =>
              log(s"we are handling pattern ${pattern.showDbg}")
              log(s"produced bindings are ${bindings.keys.map(_.nme).mkString(", ")}")
              val arguments = symbols.iterator.map(bindings).map(_() |> fld).toSeq
              val resultTerm = app(lambdaSymbol.ref(), tup(arguments*), "the transform's result")
              val resultSymbol = TempSymbol(N, "transformResult")
              Split.Let(resultSymbol, resultTerm, makeConsequent(resultSymbol.toScrut, Map.empty)),
            alternative))
  
  /** Construct a UCS split to match the prefix of the given scrutinee.
   * 
   *  @return The return value is a function that builds the split. */
  private def makeStringPrefixMatchSplit(
      scrutinee: Scrut,
      pattern: Pattern,
  ): MakePrefixSplit = pattern match
    case Constructor(target, patternArguments, arguments) => (makeConsequent, alternative) =>
      // TODO: Handle `patternArguments` and `arguments` accordingly.
      // This case is very different from the `Constructor` case in
      // `makeMatchSplit` because `target` can only be a pattern. Currently,
      // I have not figured out how to handle `arguments`. So, let me just
      // ignore them for now.
      val outputSymbol = TempSymbol(N, "output") // Denotes the pattern's output.
      val remainingSymbol = TempSymbol(N, "remaining") // Denotes the remaining value.
      val consequent = makeConsequent(outputSymbol.toScrut, remainingSymbol.toScrut, Map.empty)
      val mode = MatchMode.StringPrefix(outputSymbol, remainingSymbol)
      // `Normalization.normalizeStringPrefixPattern` is responsible for
      // declaring the symbols we created here.
      val pattern = FlatPattern.ClassLike(target, N, mode, false)(Tree.Dummy, outputSymbol :: Nil)
      Branch(scrutinee(), pattern, consequent) ~: alternative
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
        (leftOutput, leftRemains, leftBindings) => makeMatchSplit(scrutinee, right, Nil /* TODO */)(
          (rightOutput, rightBindings) => 
            val productSymbol = TempSymbol(N, "product")
            val productTerm = tup(leftOutput() |> fld, rightOutput() |> fld)
            Split.Let(productSymbol, productTerm, makeConsequent(
              productSymbol.toScrut, leftRemains, leftBindings ++ rightBindings)),
          alternative),
        alternative)
    case Negation(pattern) => (makeConsequent, alternative) =>
      // This case is tricky. The question is how many of characters should be
      // left to the continuation? For example, to match string "match is over"
      // against pattern `~"game" ~ " is over"`. The first step is to match
      // pattern `"game"` as a prefix of the input. After we found it doesn't
      // not match, how many characters should we consume in this step? From a
      // global perspective, we know that we should consume the prefix
      // `"match is "``, but with backtracking, we have to try every
      // combinations before we can make a conclusion.
      ???
    case Wildcard() => (makeConsequent, alternative) => 
      // Because the wildcard pattern always matches, we can match the entire
      // string and returns an empty string as the remaining value.
      val emptyStringSymbol = TempSymbol(N, "emptyString")
      makeConsequent(scrutinee, emptyStringSymbol.toScrut, Map.empty)
      Branch(scrutinee(), FlatPattern.ClassLike(ctx.builtins.Str.ref(), N)(Nil),
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
        Branch(isLeadingSymbol.ref(),
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
      val nonEmptyTerm = app(this.lt.ref(), tup(fld(int(0)), fld(sel(scrutinee(), "length"))), "string is not empty")
      Split.Let(nonEmptySymbol, nonEmptyTerm, // `0 < string.length`
        Branch(nonEmptySymbol.ref(),
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
          makeMatchSplit(firstOutput, second, Nil /* TODO */)(
            (secondOutput, secondBindings) =>
              makeConsequent(secondOutput, firstRemains, firstBindings ++ secondBindings),
            alternative),
        alternative)
    case alias @ Alias(pattern, id) => (makeConsequent, alternative) =>
      // TODO: Duplicate code with the `Alias` case in `makeMatchSplit`.
      makeStringPrefixMatchSplit(scrutinee, pattern)(
        (output, remains, bindings) =>
          makeConsequent(output, remains, bindings + (alias.symbol -> output)),
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
            val resultTerm = app(lambdaSymbol.ref(), tup(arguments*), "the transform's result")
            val resultSymbol = TempSymbol(N, "transformResult")
            Split.Let(resultSymbol, resultTerm, makeConsequent(resultSymbol.toScrut, remains, Map.empty)),
          alternative))
  
  /** Generate a split that consumes the prefix of the scrutinee. */
  private def stringPrefix(scrut: Scrut, pat: Tree, inner: PrefixInner)(using Raise): Split = trace(
    pre = s"stringPrefix <<< $pat", 
    post = (split: Split) => s"stringPrefix >>> $split"
  ):
    pat.deparenthesized match
    case lhs or rhs => stringPrefix(scrut, lhs, inner) ~~: stringPrefix(scrut, rhs, inner)
    case (lo: StrLit) to (incl, hi: StrLit) => if isInvalidStringBounds(lo, hi) then failure else
      val emptyTest = app(eq.ref(), tup(fld(scrut()), fld(str(""))), "test empty")
      val headTerm = callStringGet(scrut(), 0, "head")
      val tailTerm = callStringDrop(scrut(), 1, "tail")
      plainTest(emptyTest, "emptyTest")(failure) ~~:
        tempLet("head", headTerm): headSym =>
          tempLet("tail", tailTerm): tailSym =>
            makeRange(() => headSym.ref(), lo, hi, incl, captures =>
              inner(Map.empty, () => tailSym.ref()))
    case (lo: IntLit) to (incl, hi: IntLit) => Split.End
    case (lo: DecLit) to (incl, hi: DecLit) => Split.End
    case (lo: syntax.Literal) to (_, hi: syntax.Literal) =>
      error(msg"Incompatible range types: ${lo.describe} to ${hi.describe}" -> pat.toLoc)
      errorSplit
    case lit @ StrLit(value) =>
      plainTest(callStringStartsWith(scrut(), Term.Lit(lit), "startsWith")):
        tempLet("sliced", callStringDrop(scrut(), value.length, "sliced")): slicedSym =>
          inner(Map.empty, () => slicedSym.ref())
    case prefix ~ postfix =>
      stringPrefix(scrut, prefix, (captures1, postfixScrut1) =>
        stringPrefix(postfixScrut1, postfix, (captures2, postfixScrut2) =>
          inner(captures2 ++ captures1, postfixScrut2)))
    case Under() => inner(Map.empty, scrut) // TODO: check if this is correct
    case ctor @ (_: Ident | _: Sel) =>
      val ctorTrm = term(ctor)
      val prefixSymbol = new TempSymbol(N, "prefix")
      val postfixSymbol = new TempSymbol(N, "postfix")
      val mode = MatchMode.StringPrefix(prefixSymbol, postfixSymbol)
      val pattern = FlatPattern.ClassLike(ctorTrm, N, mode, false)(ctor, Nil)
      Branch(scrut(), pattern, inner(Map.empty, () => postfixSymbol.ref())) ~: Split.End
    case pat =>
      error(msg"Unrecognized pattern (${pat.describe})" -> pat.toLoc)
      errorSplit
  
  /** Create a function that compiles the resulting term of each case. It checks
   *  the captured references and sort them in the order of parameters.
   */
  private def success(params: Ls[Param]): Inner =
    val paramIndexMap = params.zipWithIndex.toMap
    captures => trace(
      pre = s"success <<< ${params.iterator.map(_.sym).mkString(", ")}", 
      post = (split: Split) => s"success >>> ${display(split)}"
    ):
      require(captures.forall(_._1 |> paramIndexMap.contains))
      if captures.size != params.size then
        // TODO: report uncaptured parameters and add tests after captures/extraction is done
        error(msg"Unmatched number of captures and parameters." -> N)
        Split.Else(Term.Error)
      else
        val fields = captures.toList.sortBy(_._1 |> paramIndexMap).map:
          case (_, ref) => Fld(FldFlags.empty, ref, N)
        Split.Else(makeMatchResult(Term.Tup(fields)(Tup(Nil))))
  
  /* The successful matching result used in prefix matching functions. */
  private def prefixSuccess(params: Ls[Param]): PrefixInner =
    val paramIndexMap = params.zipWithIndex.toMap
    (captures, postfixScrut) => trace(
      pre = s"prefixSuccess <<< ${params.iterator.map(_.sym).mkString(", ")}", 
      post = (split: Split) => s"prefixSuccess >>> ${display(split)}"
    ):
      require(captures.forall(_._1 |> paramIndexMap.contains))
      if captures.size != params.size then
        // TODO: report uncaptured parameters
        error(msg"Unmatched number of captures and parameters." -> N)
        Split.Else(Term.Error)
      else
        val fields = captures.toList.sortBy(_._1 |> paramIndexMap).map:
          case (_, ref) => Fld(FldFlags.empty, ref, N)
        val head = Fld(FldFlags.empty, postfixScrut(), N)
        Split.Else(makeMatchResult(Term.Tup(head :: fields)(Tup(Nil))))
  
  /** Failed matctching result. */
  private def failure: Split = Split.Else(makeMatchFailure)
  
  private def errorSplit: Split = Split.Else(Term.Error)
  
  /** Create a function definition from the given UCS splits.
   *  The function has a parameter list that contains the pattern parameters and
   *  a parameter that represents the input value.
   */
  private def makeMatcher(name: Str, patternParameters: List[Param], scrut: VarSymbol, topmost: Split): TermDefinition =
    val sym = BlockMemberSymbol(name, Nil)
    // Pattern parameters are passed as objects.
    val patternInputs = patternParameters.map(_.copy(flags = FldFlags.empty))
    val scrutParam = Param(FldFlags.empty, scrut, N, Modulefulness.none)
    val ps = PlainParamList(patternInputs :+ scrutParam)
    val body = Term.IfLike(Keyword.`if`, topmost)
    val res = FlowSymbol(s"the return value of $name")
    TermDefinition(N, Fun, sym, ps :: Nil, N, N, S(body), res, TermDefFlags.empty, Modulefulness.none, Nil)
  
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
  def apply(patternParams: Ls[Param], params: Ls[Param], body: Tree, pattern: Pattern): Ls[TermDefinition] = trace(
    pre = s"Translator <<< ${params.mkString(", ")} $body", 
    post = (blk: Ls[TermDefinition]) => s"Translator >>> $blk"
  ):
    val unapply = scoped("ucs:translation"):
      val inputSymbol = VarSymbol(Ident("input"))
      val topmost = makeMatchSplit(
        scrutinee = () => inputSymbol.ref().withIArgs(Nil),
        pattern = pattern,
        allowedBindings = Nil // TODO: pass proper bindings
      )(
        (output, bindings) => Split.Else(makeMatchResult(output())),
        failure
      )
      log(s"Translated `unapply`: ${display(topmost)}")
      makeMatcher("unapply", patternParams, inputSymbol, topmost)
    val unapplyStringPrefix = scoped("ucs:cp"):
      // We don't report errors here because they are already reported in the
      // translation of `unapply` function.
      given Raise = Function.const(())
      val scrutSym = VarSymbol(Ident("topic"))
      stringPrefix(() => scrutSym.ref(), body, prefixSuccess(params)) match
      case Split.Else(Term.Error) =>
        makeMatcher("unapplyStringPrefix", patternParams, scrutSym, failure)
      case split =>
        val topmost = split ~~: failure
        log(s"Translated `unapplyStringPrefix`: ${display(topmost)}")
        makeMatcher("unapplyStringPrefix", patternParams, scrutSym, topmost)
    unapply :: unapplyStringPrefix :: Nil
  
  /** Translate an anonymous pattern. They are usually pattern arguments. */
  def translateAnonymousPattern(patternParams: Ls[Param], params: Ls[Param], pattern: Pattern): Term.Rcd = trace(
    pre = s"translateAnonymousPattern <<< $pattern", 
    post = (blk: Term.Rcd) => s"translateAnonymousPattern >>> $blk"
  ):
    // We should apply an optimization to avoid generating unnecessary objects.
    // If the pattern is a constructor pattern, we can just reference the
    // `target` term. Currently, we don't do this because it is until resolution
    // stage that we can know the `target` refers to a pattern or not.
    val unapplyStmts = scoped("ucs:translation"):
      val inputSymbol = VarSymbol(Ident("input"))
      val topmost = makeMatchSplit(
        scrutinee = () => inputSymbol.ref().withIArgs(Nil),
        pattern = pattern,
        allowedBindings = Nil // TODO: pass proper bindings
      )(
        (output, bindings) => Split.Else(makeMatchResult(output())),
        failure
      )
      log(s"Translated `unapply`: ${display(topmost)}")
      makeAnonymousPatternObject("unapply", patternParams, inputSymbol, topmost)
    // val stmts2 = scoped("ucs:cp"):
    //   // We don't report errors here because they are already reported in the
    //   // translation of `unapply` function.
    //   given Raise = Function.const(())
    //   val scrutSym = VarSymbol(Ident("input"))
    //   stringPrefix(() => scrutSym.ref(), body, prefixSuccess(params)) match
    //   case Split.Else(Term.Error) =>
    //     makeAnonymousPatternObject("unapplyStringPrefix", patternParams, scrutSym, failure)
    //   case split =>
    //     val topmost = split ~~: failure
    //     log(s"Translated `unapplyStringPrefix`: ${display(topmost)}")
    //     makeAnonymousPatternObject("unapplyStringPrefix", patternParams, scrutSym, topmost)
    Term.Rcd(unapplyStmts)
