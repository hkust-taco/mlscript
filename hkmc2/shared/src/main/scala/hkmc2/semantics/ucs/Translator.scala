package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import Split.display, ucs.Normalization
import syntax.{Fun, Keyword, Literal, ParamBind, Tree}, Tree.*, Keyword.{`as`, `=>`}
import scala.collection.mutable.{Buffer, Set as MutSet}
import Elaborator.{Ctx, State}
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

import Translator.*

/** This class translates a tree describing a pattern into functions that can
 *  perform pattern matching on terms described by the pattern.
 */
class Translator(val elaborator: Elaborator)(using State, Ctx, Raise) extends DesugaringBase:
  import elaborator.term, elaborator.tl.*, HelperExtractors.*, FlatPattern.MatchMode
  
  /** Each scrutinee is represented by a function that creates a reference to
   *  the scrutinee symbol. It is sufficient for current implementation.
   */
  private type Scrut = () => Term.Ref
  
  private type CaptureMap = Map[Param, Term.Ref]
  
  private type Inner = CaptureMap => Split
  
  private type PrefixInner = (CaptureMap, Scrut) => Split
  
  private lazy val lteq = State.builtinOpsMap("<=")
  private lazy val lt = State.builtinOpsMap("<")
  private lazy val eq = State.builtinOpsMap("==")
  
  private def makeRangeTest(scrut: Scrut, lo: Literal, hi: Literal, rightInclusive: Bool, innerSplit: Split) =
    def scrutFld = fld(scrut())
    val test1 = app(lteq.ref(), tup(fld(Term.Lit(lo)), scrutFld), "isGreaterThanLower")
    val upperOp = if rightInclusive then lteq else lt
    val test2 = app(upperOp.ref(), tup(scrutFld, fld(Term.Lit(hi))), "isLessThanUpper")
    plainTest(test1, "isGreaterThanLower")(plainTest(test2, "isLessThanUpper")(innerSplit))
  
  @deprecated("Remove after we finished the new pattern translation.")
  private def makeRange(scrut: Scrut, lo: Literal, hi: Literal, rightInclusive: Bool, inner: Inner) =
    def scrutFld = fld(scrut())
    val test1 = app(lteq.ref(), tup(fld(Term.Lit(lo)), scrutFld), "gtLo")
    val upperOp = if rightInclusive then lteq else lt
    val test2 = app(upperOp.ref(), tup(scrutFld, fld(Term.Lit(hi))), "ltHi")
    plainTest(test1, "gtLo")(plainTest(test2, "ltHi")(inner(Map.empty)))
  
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
      
  
  /** The continuation function returned by `makeStringPrefixMatchSplit`. */
  type MakePrefixSplit = (makeConsequent: (prefixOutput: Scrut, postfixScrutinee: Scrut) => Split, alternative: Split) => Split
  
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
      case Constructor(target, arguments) => (makeConsequent, alternative) =>
        // If we treat a constructor pattern as the intersection of constructor
        // instance pattern and argument patterns, the output value should be
        // a tuple made of the input value and values of each argument.
        val z = (Nil: Ls[TempSymbol], makeConsequent)
        val (subScrutinees, makeChainedConsequent) = arguments.iterator.zipWithIndex.foldRight(z):
          case ((argument, index), (subScrutinees, makeInnerSplit)) =>
            val subScrutinee = TempSymbol(N, s"argument$index")
            val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
              makeMatchSplit(() => subScrutinee.ref().withIArgs(Nil), argument, allowedBindings)(
                (argumentOutput, argumentBindings) => makeInnerSplit(
                  argumentOutput, // TODO: Combine `outerOutput` and `argumentOutput`
                  outerBindings ++ argumentBindings
                ),
                Split.End
              )
            (subScrutinee :: subScrutinees, makeThisSplit)
        val consequent = makeChainedConsequent(scrutinee, Map.empty)
        Branch(scrutinee(), FlatPattern.ClassLike(target, S(subScrutinees)), consequent) ~: alternative
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
        // Currently, the negation pattern produces an unit. In the future, we
        // would include diagnostic information about why the pattern failed.
        // Note that this feature requires the `alternative` parameter to be
        // a function that takes a diagnostic information generation function.
        val outputIdent = Ident("negationOutput")
        val outputSymbol = TempSymbol(N, "negationOutput")
        val outputTerm = Term.Lit(UnitLit(true))
        makeMatchSplit(scrutinee, pattern, allowedBindings)(
          (_output, _bindings) => alternative, // The output and bindings are discarded.
          Split.Let(outputSymbol, outputTerm, makeConsequent(() => outputSymbol.ref(), Map.empty) ~~: alternative)
        )
      // Because a wildcard pattern always matches, `alternative` is not used.
      case Wildcard() => (makeConsequent, _) => makeConsequent(scrutinee, Map.empty)
      case Literal(literal) => (makeConsequent, alternative) =>
        Branch(scrutinee(), FlatPattern.Lit(literal), makeConsequent(scrutinee, Map.empty)) ~: alternative
      case Range(lower, upper, rightInclusive) => (makeConsequent, alternative) =>
        makeRangeTest(scrutinee, lower, upper, rightInclusive, makeConsequent(scrutinee, Map.empty)) ~~: alternative
      case Concatenation(left, right) => (makeConsequent, alternative) =>
        makeStringPrefixMatchSplit(scrutinee, left, allowedBindings)(
          (prefixOutput, postfixScrutinee) =>
            makeMatchSplit(postfixScrutinee, right, allowedBindings)(
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
            val subScrutinee = TempSymbol(N, s"element$index")
            val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
              makeMatchSplit(() => subScrutinee.ref().withIArgs(Nil), element, allowedBindings)(
                (elementOutput, elementBindings) => makeInnerSplit(
                  elementOutput, // TODO: Combine `outerOutput` and `elementOutput`
                  outerBindings ++ elementBindings
                ),
                Split.End
              )
            (subScrutinee :: subScrutinees, makeThisSplit)
        // END TODO
        makeTupleBranch(scrutinee().withIArgs(Nil), subScrutinees, makeChainedConsequent(scrutinee, Map.empty), alternative)
      case Tuple(leading, spread, trailing) => ???
      case Record(fields) => (makeConsequent, alternative) =>
        // This case is similar to the `Constructor` case.
        val z = (Nil: Ls[(Ident, TempSymbol)], makeConsequent)
        // TODO: Deduplicate the code with the `Constructor` case.
        val (entries, makeChainedConsequent) = fields.iterator.zipWithIndex.foldRight(z):
          case (((key, pattern), index), (fields, makeInnerSplit)) =>
            val subScrutinee = TempSymbol(N, s"field_${key.name}$$")
            val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
              makeMatchSplit(() => subScrutinee.ref().withIArgs(Nil), pattern, allowedBindings)(
                (fieldOutput, fieldBindings) => makeInnerSplit(
                  fieldOutput, // TODO: Combine `outerOutput` and `fieldOutput`
                  outerBindings ++ fieldBindings
                ),
                Split.End
              )
            ((key, subScrutinee) :: fields, makeThisSplit)
        // END TODO
        Branch(scrutinee(), FlatPattern.Record(entries), makeChainedConsequent(scrutinee, Map.empty)) ~: alternative
      case Chain(first, second) => (makeConsequent, alternative) =>
        makeMatchSplit(scrutinee, first, allowedBindings)(
          (firstOutput, firstBindings) => makeMatchSplit(firstOutput, second, allowedBindings)(
            (secondOutput, secondBindings) => makeConsequent(secondOutput, firstBindings ++ secondBindings),
            alternative
          ),
          alternative
        )
      case alias @ Alias(pattern, id) => (makeConsequent, alternative) =>
        // Not sure how to handle this case. Should we just check if `id` is in
        // `bindings` and set the symbol to the corresponding parameter?
        makeMatchSplit(scrutinee, pattern, allowedBindings)(
          (output, bindings) =>
            log(s"bind pattern $pattern to ${output()}")
            makeConsequent(output, bindings + (alias.symbol -> output)),
          alternative
        )
      case Transform(pattern, transform) =>
        // We should first create a local function that transforms the captured
        // values. So far, `pattern`'s variables should be bound to symbols.
        // Thus, we can make a parameter list from the symbols. Then, we make
        // a lambda term from the parameter list and the transform term. Because
        // `pattern` might be translated to many branches, making a lambda term
        // in advance reduces code duplication.
        val symbols = pattern.variables.varMap.values.map(_.symbol).toList
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
              val arguments = symbols.iterator.map(bindings).map(_() |> fld).toSeq
              log(s"arguments: ${arguments.mkString(", ")}")
              val resultTerm = app(lambdaSymbol.ref(), tup(arguments*), "the transform's result")
              val resultSymbol = TempSymbol(N, "transformResult")
              Split.Let(resultSymbol, resultTerm, makeConsequent(() => resultSymbol.ref().withIArgs(Nil), Map.empty) ~~: Split.End),
            alternative
          )
        )
  
  private def makeStringPrefixMatchSplit(
      scrutinee: Scrut,
      pattern: Pattern,
      bindings: Ls[VarSymbol]
  ): MakePrefixSplit = ???
  
  /** Generate an `unapply` method that matches the given pattern. */
  private def makeUnapplyMethod(scrutinee: Scrut, pattern: Pattern): TermDefinition = ???
  
  /** Generate a split that consumes the entire scrutinee. */
  private def full(scrut: Scrut, pat: Tree, inner: Inner)(using patternParams: Ls[Param]): Split = trace(
    pre = s"full <<< $pat", 
    post = (split: Split) => s"full >>> $split"
  ):
    pat.deparenthesized match
      // TODO: Implement this after we're about to finish the pattern compilation.
      // BEGIN OF TEMPORARY ALLOWANCE
      // This temporarily allows the pattern `p => t`.
      case _ `=>` _ => errorSplit
      // This temporarily allows the pattern `~p`.
      case App(Ident("~"), Tup(p :: Nil)) => errorSplit
      // This temporarily allows the pattern `(a: p1, b: p2, ...pn)`.
      case Block(_) => errorSplit
      // This temporarily allows the pattern `[p1, p2, ...pn]`.
      case Tup(_) => errorSplit
      // This temporarily allows the pattern `p as id`.
      case _ as _ => errorSplit
      // END OF TEMPORARY ALLOWANCE
      case lhs or rhs => full(scrut, lhs, inner) ~~: full(scrut, rhs, inner)
      case (lo: StrLit) to (incl, hi: StrLit) => if isInvalidStringBounds(lo, hi) then failure else
        makeRange(scrut, lo, hi, incl, inner)
      case (lo: IntLit) to (incl, hi: IntLit) => makeRange(scrut, lo, hi, incl, inner) 
      case (lo: DecLit) to (incl, hi: DecLit) => makeRange(scrut, lo, hi, incl, inner)
      case (lo: Literal) to (_, hi: Literal) =>
        error(msg"Incompatible range types: ${lo.describe} to ${hi.describe}" -> pat.toLoc)
        failure
      case lit: Literal => Branch(scrut(), FlatPattern.Lit(lit), inner(Map.empty)) ~: Split.End
      case App(Ident("-"), Tup(IntLit(value) :: Nil)) =>
        Branch(scrut(), FlatPattern.Lit(IntLit(-value)), inner(Map.empty)) ~: Split.End
      case App(Ident("-"), Tup(DecLit(value) :: Nil)) =>
        Branch(scrut(), FlatPattern.Lit(DecLit(-value)), inner(Map.empty)) ~: Split.End
      case prefix ~ postfix => stringPrefix(scrut, prefix, (captures1, postfixScrut) =>
        full(postfixScrut, postfix, captures2 => inner(captures2 ++ captures1)))
      case Under() => inner(Map.empty)
      case ctor @ (_: Ident | _: Sel) =>
        val ctorTrm = term(ctor)
        val pattern = FlatPattern.ClassLike(ctorTrm, N, MatchMode.Default, false)(ctor)
        Branch(scrut(), pattern, inner(Map.empty)) ~: Split.End
      case App(ctor @ (_: Ident | _: Sel), Tup(params)) =>
        // TODO(rp/str): handle input params
        val ctorTrm = term(ctor)
        val pattern = FlatPattern.ClassLike(ctorTrm, N, MatchMode.Default, false)(ctor)
        Branch(scrut(), pattern, inner(Map.empty)) ~: Split.End
      case pat =>
        error(msg"Unrecognized pattern (${pat.describe})" -> pat.toLoc)
        errorSplit
  
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
    case (lo: Literal) to (_, hi: Literal) =>
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
      val pattern = FlatPattern.ClassLike(ctorTrm, N, mode, false)(ctor)
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
    if patternParams.nonEmpty then
      // Temporarily disable the translation of pattern with pattern parameters.
      // TODO(rp): pass pattern parameters as objects to the `unapply` function
      Nil
    else
      // val unapply = scoped("ucs:cp"):
      //   val scrutSym = VarSymbol(Ident("scrut"))
      //   val topmost = full(() => scrutSym.ref(), body, success(params))(using patternParams) ~~: failure
      //   log(s"Translated `unapply`: ${display(topmost)}")
      //   makeMatcher("unapply", scrutSym, topmost)
      val unapply = scoped("ucs:translation"):
        val inputSymbol = VarSymbol(Ident("input"))
        val topmost = makeMatchSplit(
          scrutinee = () => inputSymbol.ref(),
          pattern = pattern,
          allowedBindings = Nil // TODO: pass proper bindings
        )(
          (output, bindings) => Split.Else(makeMatchResult(tup(output() |> fld))),
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
