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
  /** A class that can generate `Ref` to the scrutinee. It also comes with a few
   *  mutable maps to reuse sub-scrutinees. Memoization of sub-scrutinees help
   *  the normalization to merge let bindings from different branches.
   */
  sealed abstract class Scrut:
    private val subScrutinees: Buffer[SymbolScrut[?]] = Buffer.empty
    private val fields: HashMap[Ident, SymbolScrut[?]] = HashMap.empty
    private val tupleLead: HashMap[Int, SymbolScrut[?]] = HashMap.empty
    private val tupleLast: HashMap[Int, SymbolScrut[?]] = HashMap.empty
    
    def apply(): Term.Ref
    def getSubScrutinee(index: Int)(using State): SymbolScrut[?] =
      while subScrutinees.size <= index do
        subScrutinees += TempSymbol(N, s"argument${subScrutinees.size}$$").toScrut
      subScrutinees(index)
    def getTupleLeadSubScrutinee(index: Int)(using State): SymbolScrut[?] =
      tupleLead.getOrElseUpdate(index, TempSymbol(N, s"element$index$$").toScrut)
    def getTupleLastSubScrutinee(index: Int)(using State): SymbolScrut[?] =
      tupleLast.getOrElseUpdate(index, TempSymbol(N, s"lastElement$index$$").toScrut)
    def getFieldScrutinee(fieldName: Ident)(using State): SymbolScrut[?] =
      fields.getOrElseUpdate(fieldName, TempSymbol(N, s"field_${fieldName.name}$$").toScrut)
  
  object Scrut:
    def from(ref: Term.Ref): RefScrut = RefScrut(() => ref)
  
  class RefScrut(make: () => Term.Ref) extends Scrut:
    def apply(): Ref = make()
  
  class SymbolScrut[SymbolType <: BlockLocalSymbol](val symbol: SymbolType) extends Scrut:
    def apply(): Ref = symbol.ref()
  
  extension [SymbolType <: BlockLocalSymbol](symbol: SymbolType)
    def toScrut: SymbolScrut[SymbolType] = SymbolScrut(symbol)
  
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
  
  object RejectSplit extends ((MakeConsequent, Split) => Split):
    def apply(makeConsequent: MakeConsequent, alternative: Split): Split = alternative
  
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
  
  object RejectPrefixSplit extends ((MakePrefixConsequent, Split) => Split):
    def apply(makeConsequent: MakePrefixConsequent, alternative: Split): Split = alternative
    
  extension (makePrefixSplit: MakePrefixSplit)
    /** Build another `MakePrefixSplit` if the function does not reject. */
    transparent inline def whenAccept(derivedFunction: => MakePrefixSplit): MakePrefixSplit =
      if makePrefixSplit is RejectPrefixSplit then RejectPrefixSplit else derivedFunction
  
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
  import tl.*, SP.*
  
  private lazy val lteq = State.builtinOpsMap("<=")
  private lazy val lt = State.builtinOpsMap("<")
  private lazy val add = State.builtinOpsMap("+")
  
  private def makeRangeTest(scrut: Scrut, lo: syntax.Literal, hi: syntax.Literal, rightInclusive: Bool, innerSplit: Split) =
    def scrutFld = fld(scrut())
    val test1 = app(lteq.safeRef, tup(fld(Term.Lit(lo)), scrutFld), "isGreaterThanLower")
    val upperOp = if rightInclusive then lteq else lt
    val test2 = app(upperOp.safeRef, tup(scrutFld, fld(Term.Lit(hi))), "isLessThanUpper")
    plainTest(test1, "isGreaterThanLower")(plainTest(test2, "isLessThanUpper")(innerSplit))
  
  extension (patterns: Ls[SP])
    /**
     * Folds over sub-patterns to create a consequent making function with
     * accumulated sub-scrutinees. This function processes a list of patterns by
     * creating a consequent making function that applies consequent making
     * function of each sub-pattern from right to left.
     * 
     * Mental model example: for patterns `[p1, p2, p3]` with sub-scrutinees
     * `[s1, s2, s3]`, this function creates:
      
     * ```
     * s1 is p1 and s2 is p2 and s3 is p3 and
     *   {| z(outerOutput + bindings1 + bindings2 + bindings3) |}
     * ```
     * 
     * @param z The initial consequent making function to start the fold with.
     * @param getSubScrutinee To get a scrutinee for a given pattern index.
     * @return A tuple containing:
     *         - A list of `(BlockLocalSymbol, Option[Loc])` pairs for each
     *           sub-scrutinee and its location.
     *         - A `MakeConsequent` function that creates the nested match split.
     */
    def folded(z: MakeConsequent)(getSubScrutinee: Int => SymbolScrut[?])
    : (Ls[(BlockLocalSymbol, Opt[Loc])], MakeConsequent) =
      patterns.iterator.zipWithIndex.foldRight((Nil, z)):
        case ((subPattern, index), (accSubScrutinees, makeInnerSplit)) =>
          val subScrutinee = getSubScrutinee(index)
          val makeThisSplit: MakeConsequent = (outerOutput, outerBindings) =>
            makeMatchSplit(subScrutinee, subPattern)(
              // Note that the individual pattern's output is ignored because
              // in real world it's hard to synthesized a valid object if the
              // pattern carries some transformation.
              (_elementOutput, elementBindings) => makeInnerSplit(
                outerOutput, // TODO: Combine `outerOutput` and `elementOutput`
                outerBindings ++ elementBindings),
              Split.End)
          ((subScrutinee.symbol -> subPattern.toLoc) :: accSubScrutinees, makeThisSplit)
    
    /** Same as the other overload, but for `MakePrefixConsequent`. */
    def folded(z: MakePrefixConsequent)(getSubScrutinee: Int => SymbolScrut[?])
    : (Ls[(BlockLocalSymbol, Opt[Loc])], MakePrefixConsequent) =
      patterns.iterator.zipWithIndex.foldRight((Nil, z)):
        case ((subPattern, index), (accSubScrutinees, makeInnerSplit)) =>
          val subScrutinee = getSubScrutinee(index)
          val makeThisSplit: MakePrefixConsequent = (outerOutput, outerRemaining, outerBindings) =>
            makeStringPrefixMatchSplit(subScrutinee, subPattern)(
              // Note that the individual pattern's output is ignored because
              // in real world it's hard to synthesized a valid object if the
              // pattern carries some transformation.
              (_elementOutput, _elementRemaining, elementBindings) => makeInnerSplit(
                outerOutput, // TODO: Combine `outerOutput` and `elementOutput`
                outerRemaining, // TODO: Combine `outerRemaining` and `elementRemaining`
                outerBindings ++ elementBindings),
              Split.End)
          ((subScrutinee.symbol -> subPattern.toLoc) :: accSubScrutinees, makeThisSplit)
  
    def makePatternBindings(using State): Ls[(TempSymbol, SP)] =
      patterns.iterator.zipWithIndex.map:
        case (pattern, index) => new TempSymbol(N, s"patternArgument${index}$$") -> pattern
      .toList
  
  /**
    * Check whether the number of parameters in class-like patterns matches the
    * number in their definition, and whether each parameter is accessible.
    *
    * @param scrutinee the scrutinee
    * @param classTerm the term that resolves to the class
    * @param classSymbol the symbol for the class to be matched
    * @param arguments sub-patterns 
    */
  private def makeMatchClassSplit(
      scrutinee: Scrut,
      classTerm: Term,
      classSymbol: ClassSymbol,
      arguments: Opt[Ls[SP]]
  ): MakeSplit =
    // Obtain the `classHead` used for error reporting and the parameter list
    // from the class definitions.
    val (classHead, paramsOpt) = classSymbol.defn match
      case N => lastWords(s"Class ${classSymbol.name} does not have a definition")
      // Use the constructor pattern's location for error reporting.
      case S(cd) => new Tree.Ident(classSymbol.name).withLoc(classTerm.toLoc) -> cd.paramsOpt
    // Check if the number of arguments matches the number of parameters.
    val successful = paramsOpt match
      case S(paramList) => arguments match
        case S(args) =>
          // Check the number of parameters is correct.
          if args.size != paramList.params.size then
            val loc = Loc(args) orElse classTerm.toLoc
            error:
              if paramList.params.isEmpty then
                msg"The constructor does not take any arguments but found ${
                  "argument" countBy args.size}." -> loc
              else
                msg"Expected ${"argument" countBy paramList.params.size
                }, but found ${if args.size < paramList.params.size then "only " else ""
                }${"argument" countBy args.size}." -> loc
          // Check the fields are accessible.
          paramList.params.iterator.zip(args).map:
            case (_, Wildcard()) => true
            case (Param(flags, sym, _, _), arg) if !flags.isVal =>
              error(msg"This pattern cannot be matched" -> arg.toLoc, // TODO: use correct location
                msg"because the corresponding parameter `${sym.name}` is not publicly accessible" -> sym.toLoc,
                msg"Suggestion: use a wildcard pattern `_` in this position" -> N,
                msg"Suggestion: mark this parameter with `val` so it becomes accessible" -> N)
              false
            case _ => true
          // If the number of arguments are more than the number of parameters,
          // or one of parameters is incessible, we cannot make the branch.
          .foldLeft(args.size <= paramList.params.size)(_ && _)
        case N => arguments match
          case S(args) =>
            error(msg"class ${classSymbol.name} does not have parameters" -> classHead.toLoc,
              msg"but the pattern has ${"sub-pattern" countBy args.size}" -> Loc(args))
            false
          case N => true // No parameters, no arguments. This is fine.
      case N => arguments match // No parameter lists. Check if scruts are empty.
        case S(Nil) =>
          error(msg"Class ${classSymbol.name} does not have a parameter list" -> classTerm.toLoc)
          true
        case S(args) =>
          error(msg"Class ${classSymbol.name} does not have a parameter list" -> classTerm.toLoc,
            msg"but the pattern has ${"sub-pattern" countBy args.size}" -> Loc(args))
          false
        case N => true
    if successful then (makeConsequent, alternative) =>
      // The pattern arguments for destructing the constructor's arguments.
      val (theArguments, makeConsequentForArguments) = arguments.fold((N, makeConsequent)):
        _.folded(makeConsequent)(scrutinee.getSubScrutinee).mapFirst(S(_))
      val outputSymbol = new LazyScrut()
      val consequent = makeConsequentForArguments(outputSymbol, SeqMap.empty)
      val pattern = FlatPattern.ClassLike(classTerm, classSymbol, theArguments, false)(Tree.Dummy)
      Branch(scrutinee(), pattern, outputSymbol.toLet(scrutinee(), consequent)) ~: alternative
    else RejectSplit
  
  /**
    * Make a split that matches the given object. Meanwhile, check whether the
    * object pattern has an argument list.
    *
    * @param scrutinee the scrutinee
    * @param objectSymbol the symbol for the object
    * @param arguments objects do not have parameters, thus the arguments are
    *                  only used for error checking
    */
  private def makeMatchObjectSplit(
      patternLoc: Opt[Loc],
      scrutinee: Scrut,
      objectTerm: Term,
      objectSymbol: ModuleOrObjectSymbol,
      arguments: Opt[Ls[SP]]
  ): MakeSplit =
    val shouldReject = arguments match
      case S(Nil) =>
        // The object pattern comes with an unnecessary parameter list, but it
        // can still be compiled.
        error(msg"`${objectSymbol.name}` is an object." -> objectSymbol.id.toLoc,
          msg"Its pattern cannot have an argument list." -> patternLoc)
        false
      case S(_ :: _) =>
        // One or more parameters are provided, thus we cannot compile the
        // following consequent split.
        error(msg"`${objectSymbol.name}` is an object." -> objectSymbol.id.toLoc,
          msg"Its pattern cannot have arguments." -> patternLoc)
        true
      case N => false
    if shouldReject then RejectSplit else (makeConsequent, alternative) =>
      val outputSymbol = new LazyScrut()
      val consequent = makeConsequent(outputSymbol, SeqMap.empty)
      val pattern = FlatPattern.ClassLike(objectTerm, objectSymbol, N, false)(Tree.Dummy)
      Branch(scrutinee(), pattern, outputSymbol.toLet(scrutinee(), consequent)) ~: alternative
  
  /**
    * When a scrutinee is matched with a defined pattern `P`, this method checks
    * whether the arguments provided by the user (both pattern arguments and
    * extraction parameters) match the parameters in the definition of `P`. This
    * part of the logic is used by both efficiently compiled patterns and
    * naively compiled patterns to ensure the consistency of diagnostics.
    *
    * @param scrutinee the scrutinee of the match
    * @param defn the pattern's definition
    * @param arguments all arguments provided by the user
    * @return Return a triple. The first element is the pattern arguments
    *         received when `P` is parameterized. The second element is the
    *         sub-patterns used to match the value returned after `P` is applied.
    *         The third element indicates whether expanding this branch should
    *         be abandoned due to invalid arguments.
    */
  private def matchParametersWithArguments(
      scrutinee: Scrut,
      defn: PatternDef,
      arguments: Opt[Ls[SP]]
  ): (Ls[SP], Opt[Ls[SP]], Bool) =
    val argumentCount = arguments.fold(0)(_.length)
    val patternParameterCount = defn.patternParams.length
    val loc = Loc(arguments.getOrElse(Nil))
    if argumentCount < patternParameterCount then
      // Since pattern parameters are required, if the total number of arguments
      // is less than this number, the pattern matching is definitely incorrect.
      error:
        msg"Expected ${"pattern argument" countBy patternParameterCount
        }, but found only ${"pattern argument" countBy argumentCount}." -> loc
      (Nil, N, true)
    else arguments match
      // Now that the number of pattern parameters can definitely be satisfied,
      // what we need is to properly pair the parameters with the arguments.
      case N => (Nil, N, false) // This implies `patternParameterCount` is 0.
      case S(arguments) if argumentCount === patternParameterCount =>
        // All the arguments satisfy the pattern arguments, with none left over.
        (arguments, N, false)
      case S(arguments) =>
        val extractionParameterCount = defn.extractionParams.size
        val extractionArgumentCount = argumentCount - patternParameterCount
        if extractionArgumentCount === extractionParameterCount then
          // Match arguments and parameters pairwisely.
          val (patternArguments, extractionSubPatterns) =
            arguments.iterator.zip(defn.parameters).toList.partitionMap:
              case (patternArgument, Param(FldFlags(pat = true), _, _, _)) =>
                L(patternArgument)
              case (subPattern, _) => R(subPattern)
          (patternArguments, S(extractionSubPatterns), false)
        else arguments match
          // When the pattern does not have any parameters, the user can provide
          // an argument as a shorthand of matching the output. For example,
          // `x is P(Q) === x is P as Q` when `P`` is not parameterized.
          case outputPattern :: Nil if defn.parameters.isEmpty =>
            (Nil, S(outputPattern :: Nil), false)
          case _ :: _ | Nil =>
            error:
              msg"Expected ${"extraction argument" countBy extractionParameterCount
              }, but found ${if extractionArgumentCount < extractionParameterCount then "only " else ""
              }${"argument" countBy extractionArgumentCount}." -> loc
            (Nil, N, true)
  
  /**
    * Create a split that naively compiles and then binds the pattern arguments.
    *
    * @param patternArguments the pattern arguments with their symbols
    * @param split the inner split to be enclosed
    */
  def buildPatternArguments(
      patternArguments: List[(BlockLocalSymbol, SP)],
      split: Split
  ): Split = patternArguments.foldRight(split):
    case ((symbol, pattern), innerSplit) =>
      Split.Let(symbol, compileAnonymousPattern(Nil, Nil, pattern), innerSplit)
  
  /**
    * Make a split that matches the given pattern in the naive way. Note that
    * the efficient pattern compilation without backtracking is handled in the
    * case of `Annotated(_, _)`.
    *
    * @param scrutinee the scrutinee
    * @param patternTerm the term that resolved to the pattern
    * @param patternSymbol the symbol for the pattern
    * @param arguments pattern arguments and extraction arguments
    */
  private def makeMatchPatternSplit(
      scrutinee: Scrut,
      patternTerm: Term,
      patternSymbol: PatternSymbol,
      arguments: Opt[Ls[SP]]
  ): MakeSplit =
    val defn = patternSymbol.defn.getOrElse:
      lastWords(s"Pattern `${patternSymbol.nme}` has not been elaborated.")
    val (patternArguments, extractionMatches, shouldReject) =
      matchParametersWithArguments(scrutinee, defn, arguments)
    if shouldReject then RejectSplit else (makeConsequent, alternative) =>
      val (extractionArguments, makeConsequentForSubPatterns) =
        val z = (N: Opt[Ls[(BlockLocalSymbol, Opt[Loc])]], makeConsequent)
        extractionMatches.fold(z):
          _.folded(makeConsequent)(scrutinee.getSubScrutinee).mapFirst(S(_))
      // First, we need to prepare the objects that performs the naive matching
      // of pattern arguments which will be passed to the pattern.
      val patternBindings = patternArguments.makePatternBindings
      val wrapPatternArgumentDefinitions = buildPatternArguments(patternBindings, _)
      // Then, we can call the `unapply` method.
      val unapplyArguments = patternBindings.map(_._1.safeRef |> fld) :+ fld(scrutinee())
      val unapplyCall = app(sel(patternTerm, "unapply").resolve, tup(unapplyArguments*), s"result of unapply")
      val unapplyResult = TempSymbol(N, "unapplyResult")
      val wrapUnapply = Split.Let(unapplyResult, unapplyCall, _)
      // Then, we need to destruct the produced `MatchSuccess`.
      val outputSymbol = TempSymbol(N, "output").toScrut // TODO: We can use `LazyScrut` for this, but the match result pattern's parameters requires a symbol.
      val bindingsSymbol = TempSymbol(N, "bindings") // TODO: This can be automatically removed when no transformation is used.
      val wrapDestruction = (consequent: Split) =>
        val pattern = matchSuccessPattern(S(outputSymbol.symbol :: bindingsSymbol :: Nil))
        Branch(unapplyResult.safeRef, pattern, consequent) ~: alternative
      // Check the number of extraction arguments.
      val wrapExtractionArguments = extractionArguments match
        case N | S(Nil) => identity[Split]
        case S((single, _) :: Nil) => Split.Let(single, outputSymbol(), _)
        case S(extractionArguments) => (split: Split) =>
          makeTupleBranch(scrutinee(), extractionArguments.map(_._1), split, Split.End)
      // Finally, the inner split that does the work.
      val consequent = makeConsequentForSubPatterns(outputSymbol, SeqMap.empty)
      // Here we go!
      wrapPatternArgumentDefinitions(wrapUnapply(wrapDestruction(wrapExtractionArguments(consequent))))
  
  /** Report errors when pattern parameters are used incorrectly. */
  private def validatePatternParameter[A](
      parameterTerm: Term,
      parameterSymbol: VarSymbol,
      arguments: Opt[Ls[SP]],
      patternLoc: Opt[Loc],
      default: A
  )(body: => A)(using Raise): A = parameterSymbol.decl match
    case S(param @ Param(flags = FldFlags(pat = true))) => arguments match
      case S(list) =>
        // The object pattern comes with an unnecessary parameter list, but it
        // can still be compiled.
        error(msg"`${parameterSymbol.name}` is a pattern parameter." -> param.toLoc,
          msg"It cannot be applied${if list.isEmpty then "" else " to any arguments"}." -> patternLoc)
        default
      case N => body
    case S(_) | N =>
      error(msg"Cannot use this ${parameterTerm.describe} as a pattern" -> parameterTerm.toLoc)
      default
  
  private def makeMatchPatternParameterSplit(
      scrutinee: Scrut,
      parameterTerm: Term,
      parameterSymbol: VarSymbol,
      arguments: Opt[Ls[SP]],
      patternLoc: Opt[Loc]
  ): MakeSplit =
    validatePatternParameter[MakeSplit](
      parameterTerm, parameterSymbol, arguments, patternLoc, RejectSplit
    ): (makeConsequent, alternative) =>
      val unapplyTerm = sel(parameterTerm, "unapply").resolve
      val unapplyCall = app(unapplyTerm, tup(fld(scrutinee())), s"result of unapply")
      tempLet(s"matchSuccess_${parameterSymbol.name}", unapplyCall): matchSuccessSymbol =>
        val outputSymbol = TempSymbol(N, "output").toScrut
        val bindingsSymbol = TempSymbol(N, "bindings").toScrut
        val pattern = matchSuccessPattern(S(Ls(outputSymbol.symbol, bindingsSymbol.symbol)))
        val consequent = makeConsequent(outputSymbol, SeqMap.empty)
        Branch(matchSuccessSymbol.safeRef, pattern, consequent) ~: alternative
  
  /** Make a UCS split that matches the entire scrutinee against the pattern.
   *  Since each pattern has an output, the split is responsible for creating
   *  a binding that holds the output value and pass it to the continuation
   *  function that makes the conseuqent split.
   */
  def makeMatchSplit(scrutinee: Scrut, pattern: SP): MakeSplit =
    pattern match
      case Constructor(target, arguments) => target.resolvedSym match
        case S(symbol: VarSymbol) =>
          makeMatchPatternParameterSplit(scrutinee, target, symbol, arguments, pattern.toLoc)
        case symbolOption => symbolOption.flatMap(_.asClsLike) match
          case S(classSymbol: ClassSymbol) =>
            makeMatchClassSplit(scrutinee, target, classSymbol, arguments)
          case S(objectSymbol: ModuleOrObjectSymbol) =>
            makeMatchObjectSplit(pattern.toLoc, scrutinee, target, objectSymbol, arguments)
          case S(patternSymbol: PatternSymbol) =>
            makeMatchPatternSplit(scrutinee, target, patternSymbol, arguments)
          case N =>
            error(msg"Cannot use this ${target.describe} as a pattern." -> target.toLoc)
            RejectSplit
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
        Branch(scrutinee(), FlatPattern.Lit(literal), makeConsequent(scrutinee, SeqMap.empty)) ~: alternative
      case Range(lower, upper, rightInclusive) => (makeConsequent, alternative) =>
        makeRangeTest(scrutinee, lower, upper, rightInclusive, makeConsequent(scrutinee, SeqMap.empty)) ~~: alternative
      case Concatenation(left, right) => (makeConsequent, alternative) =>
        makeStringPrefixMatchSplit(scrutinee, left)(
          (_consumedOutput, remainingOutput, bindingsFromConsumed) =>
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
        val (subScrutinees, makeChainedConsequent) =
          elements.folded(makeConsequent)(scrutinee.getTupleLeadSubScrutinee)
        val consequent = makeChainedConsequent(scrutinee, SeqMap.empty)
        makeTupleBranch(scrutinee(), subScrutinees.map(_._1), consequent, alternative)
      case Tuple(leading, S((_, spread, trailing))) => (makeConsequent, alternative) =>
        val (trailSubScrutinees, makeConsequent0) = trailing.folded(makeConsequent):
          index => scrutinee.getTupleLastSubScrutinee(index)
        val spreadSubScrutinee = TempSymbol(N, "middleElements")
        val makeConsequent1: MakeConsequent = (outerOutput, outerBindings) =>
          makeMatchSplit(spreadSubScrutinee.toScrut, spread)(
            (spreadOutput, spreadBindings) => makeConsequent0(
              spreadOutput, // TODO: Combine `outerOutput` and `spreadOutput`
              outerBindings ++ spreadBindings),
            Split.End)
        val (leadingSubScrutinees, makeConsequent2) = leading.folded(makeConsequent1):
          index => scrutinee.getTupleLeadSubScrutinee(index)
        makeTupleBranch(
          scrutinee(),
          leadingSubScrutinees.map(_._1),
          spreadSubScrutinee,
          trailSubScrutinees.map(_._1),
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
        Branch(scrutinee(), FlatPattern.Record(entries), consequent) ~: alternative
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
        val shouldCompile = annotations.foldLeft(true): (acc, termOrLoc) =>
          val res = termOrLoc match
            case R(term) => term.resolvedSym match
              case S(symbol) if symbol is ctx.builtins.annotations.compile => N
              case S(_) | N => S(term.toLoc)
            case L(loc) => S(loc)
          res match
            case S(loc) =>
              warn(msg"This annotation is not supported here." -> loc,
                msg"Note: Patterns only support the `@compile` annotation." -> pattern.toLoc)
              acc
            case N => true
        if shouldCompile then
          compilePattern(scrutinee, pattern)
        else
          makeMatchSplit(scrutinee, pattern)
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
  
  private def makeMatchPrefixPatternSplit(
      scrutinee: Scrut,
      patternTerm: Term,
      patternSymbol: PatternSymbol,
      arguments: Opt[Ls[SP]]
  )(using Raise): MakePrefixSplit =
    val defn = patternSymbol.defn.getOrElse(die)
    val (patternArguments, extractionMatches, shouldReject) =
      matchParametersWithArguments(scrutinee, defn, arguments)
    if shouldReject then RejectPrefixSplit else (makeConsequent, alternative) =>
      val outputSymbol = TempSymbol(N, "output").toScrut
      val remainingSymbol = TempSymbol(N, "remaining").toScrut
      val (extractionArguments, makeConsequentForArguments) =
        extractionMatches.fold((N, makeConsequent)):
          _.folded(makeConsequent)(scrutinee.getSubScrutinee).mapFirst(S(_))
      val consequent = makeConsequentForArguments(outputSymbol, remainingSymbol, SeqMap.empty)
      val patternBindings = patternArguments.makePatternBindings
      val unapplyCall =
        val method = "unapplyStringPrefix"
        val args = tup(patternBindings.map(_._1.safeRef) :+ scrutinee())
        app(sel(patternTerm, method), args, s"result of $method")
      val split = tempLet("unapplyResult", unapplyCall): matchSuccessSymbol =>
        val outputPairSymbol = TempSymbol(N, "outputPair")
        val bindingsSymbol = TempSymbol(N, "bindings")
        Branch(
          matchSuccessSymbol.safeRef,
          matchSuccessPattern(S(outputPairSymbol :: bindingsSymbol :: Nil)),
          // Bind the `remaining` variable to the second element of the output
          // of `matchSuccess`.
          Split.Let(outputSymbol.symbol, callTupleGet(outputPairSymbol.safeRef, 0, "prefix"),
            Split.Let(remainingSymbol.symbol, callTupleGet(outputPairSymbol.safeRef, 1, "postfix"), consequent))
        ) ~: alternative
      buildPatternArguments(patternBindings, split)
  
  private def makeMatchPrefixPatternParameterSplit(
      scrutinee: Scrut,
      parameterTerm: Term,
      parameterSymbol: VarSymbol,
      arguments: Opt[Ls[SP]],
      patternLoc: Opt[Loc]
  )(using Raise): MakePrefixSplit =
    validatePatternParameter[MakePrefixSplit](
      parameterTerm, parameterSymbol, arguments, patternLoc, RejectPrefixSplit
    ): (makeConsequent, alternative) =>
      val unapplyTerm = sel(parameterTerm, "unapplyStringPrefix").resolve
      val unapplyCall = app(unapplyTerm, tup(fld(scrutinee())), s"result of unapply")
      tempLet(s"matchSuccess_${parameterSymbol.name}", unapplyCall): matchSuccessSymbol =>
        // Destruct the `MatchSuccess` produced by the `unapply` method.
        val outputPairSymbol = TempSymbol(N, "outputPair").toScrut
        val bindingsSymbol = TempSymbol(N, "bindings").toScrut
        val pattern = matchSuccessPattern(S(Ls(outputPairSymbol.symbol, bindingsSymbol.symbol)))
        // Destruct the first field of the `MatchSuccess` as a pair.
        val outputSymbol = TempSymbol(N, "output").toScrut // Denotes the pattern's output.
        val remainingSymbol = TempSymbol(N, "remaining").toScrut // Denotes the remaining value.
        // Assemble the `Split`s in order from inside to outside.
        val consequent1 = makeConsequent(outputSymbol, remainingSymbol, SeqMap.empty)
        val consequent2 = makeTupleBranch(outputPairSymbol(),
          Ls(outputSymbol.symbol, remainingSymbol.symbol), consequent1, Split.End)
        Branch(matchSuccessSymbol.safeRef, pattern, consequent2) ~: alternative
  
  /** Construct a UCS split to match the prefix of the given scrutinee.
   * 
   *  @return The return value is a function that builds the split. */
  protected def makeStringPrefixMatchSplit(
      scrutinee: Scrut,
      pattern: SP,
  )(using Raise): MakePrefixSplit = pattern match
    case Constructor(target, arguments) => target.resolvedSym match
      // The case when the target refers to a pattern parameter.
      case S(symbol: VarSymbol) =>
        makeMatchPrefixPatternParameterSplit(scrutinee, target, symbol, arguments, pattern.toLoc)
      case symbolOption => symbolOption.flatMap(_.asPat) match
        // The case when the target refers to a pattern symbol.
        case S(symbol: PatternSymbol) =>
          makeMatchPrefixPatternSplit(scrutinee, target, symbol, arguments)
        // The other cases are not compatible with strings.
        case S(_) | N => RejectPrefixSplit
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
      RejectPrefixSplit
    case Wildcard() => (makeConsequent, alternative) => 
      // Because the wildcard pattern always matches, we can match the entire
      // string and returns an empty string as the remaining value.
      val emptyStringSymbol = TempSymbol(N, "emptyString")
      makeConsequent(scrutinee, emptyStringSymbol.toScrut, SeqMap.empty)
      Branch(scrutinee(), FlatPattern.ClassLike(ctx.builtins.Str.safeRef, ctx.builtins.Str, N, false)(Tree.Dummy),
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
    case Literal(_) => RejectPrefixSplit
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
    case Range(_, _, _) => RejectPrefixSplit
    case Concatenation(left, right) => (makeConsequent, alternative) =>
      makeStringPrefixMatchSplit(scrutinee, left)(
        (leftConsumedOutput, leftRemainingOutput, leftBindings) =>
          makeStringPrefixMatchSplit(leftRemainingOutput, right)(
            (rightConsumedOutput, rightRemainingOutput, rightBindings) =>
              val combinedOutputSymbol = LazyScrut(S("combinedOutput"))
              combinedOutputSymbol.toLet(
                app(add.ref(), tup(fld(leftConsumedOutput()), fld(rightConsumedOutput())), "combined output"),
                makeConsequent(combinedOutputSymbol, rightRemainingOutput, leftBindings ++ rightBindings)),
            alternative),
        alternative)
    // Tuples and records cannot be string prefixes.
    case Tuple(_, _) => RejectPrefixSplit
    case Record(_) => RejectPrefixSplit
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
    case Annotated(pattern, annotations) =>
      // Currently, we only support `@compile` annotation, so here we only
      // check whether this annotation exists, and report an error for all
      // other annotations.
      val shouldCompile = annotations.foldLeft(true): (acc, termOrLoc) =>
        val res = termOrLoc match
          case R(term) => term.resolvedSym match
            case S(symbol) if symbol is ctx.builtins.annotations.compile => N
            case S(_) | N => S(term.toLoc)
          case L(loc) => S(loc)
        res match
          case S(loc) =>
            warn(msg"This annotation is not supported here." -> loc,
              msg"Note: Patterns only support the `@compile` annotation." -> pattern.toLoc)
            acc
          case N => true
      if shouldCompile then error:
        msg"String patterns are not yet supported by efficient compilation." -> pattern.toLoc
      makeStringPrefixMatchSplit(scrutinee, pattern)
  
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
      val matchSuccessSymbol = TempSymbol(N, "matchSuccess")
      val matchSuccessTerm = sel(recordSymbol.safeRef, fieldName)
      val f2 = Split.Let(matchSuccessSymbol, matchSuccessTerm, _)
      // 3. Check if the field value is a `MatchSuccess` and bind the output.
      val outputSymbol = TempSymbol(N, "patternOutput")
      val bindingsSymbol = TempSymbol(N, "bindings") // TODO: This is useless.
      // val consequent = aliasOutputSymbols(outputSymbol.safeRef, outputSymbols, consequent)
      // TODO: How to forward the bindings from the pattern compilation to here?
      val consequent = makeConsequent(outputSymbol.toScrut, SeqMap.empty)
      val pattern = matchSuccessPattern(S(outputSymbol :: bindingsSymbol :: Nil))
      val branch = Branch(matchSuccessSymbol.safeRef, pattern, consequent)
      f1(f2(branch ~: alternative))
    implementations.iterator.foldRight(innermostSplit):
      case ((symbol, paramList, term), innerSplit) =>
        log(term.showDbg)
        Split.Let(symbol, Term.Lam(paramList, term), innerSplit)
  
  /** Make a term like `MatchFailure(null)`. We will synthesize detailed
   *  error messages and pass them to the function. */
  private def failure: Split = Split.Else(makeMatchFailure())
  
  /**
    * Create a method from the given UCS splits. The function has a parameter
    * list that contains the pattern parameters and a parameter that represents
    * the input value.
    *
    * @param name the method's name
    * @param patternParameters all pattern parameters
    * @param scrut the symbol of the input value
    * @param topmost the topmost split
    */
  private def makeMethod(
      name: Str,
      patternParameters: List[Param],
      scrut: VarSymbol,
      topmost: Split
  ): (BlockMemberSymbol, ParamList, Split) =
    val sym = BlockMemberSymbol(name, Nil)
    // Pattern parameters are passed as objects.
    val patternInputs = patternParameters.map(_.copy(flags = FldFlags.empty))
    // The last parameter is the scrutinee.
    val scrutParam = Param(FldFlags.empty, scrut, N, Modulefulness.none)
    val ps = PlainParamList(patternInputs :+ scrutParam)
    (sym, ps, topmost)
  
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
  def compilePattern(pd: PatternDef): Ls[(BlockMemberSymbol, ParamList, Split)] =
  trace(
    pre = s"compilePattern <<< ${pd.showDbg}", 
    post = (blk: Ls[(BlockMemberSymbol, ParamList, Split)]) =>
      s"compilePattern >>> $blk"
  ):
    // TODO: Use `pd.extractionParams`.
    val unapply = scoped("ucs:translation"):
      val inputSymbol = VarSymbol(Ident("input"))
      val topmost = makeMatchSplit(inputSymbol.toScrut, pd.pattern)
        ((output, bindings) => Split.Else(makeMatchSuccess(output())), failure)
      log(s"Translated `unapply`: ${topmost.prettyPrint}")
      makeMethod("unapply", pd.patternParams, inputSymbol, topmost)
    // TODO: Use `pd.extractionParams`.
    val unapplyStringPrefix = scoped("ucs:cp"):
      // We don't report errors here because they have been already reported in
      // the translation of `unapply` function.
      given Raise = Function.const(())
      val inputSymbol = VarSymbol(Ident("input"))
      val topmost = makeStringPrefixMatchSplit(inputSymbol.toScrut, pd.pattern)
        ((consumedOutput, remainingOutput, bindings) => Split.Else:
          makeMatchSuccess(tup(fld(consumedOutput()), fld(remainingOutput()))), failure)
      log(s"Translated `unapplyStringPrefix`: ${topmost.prettyPrint}")
      makeMethod("unapplyStringPrefix", pd.patternParams, inputSymbol, topmost)
    unapply :: unapplyStringPrefix :: Nil
  
  /** Generate the record statements of `unapply` methods that can be used in
   *  objects for anonymous patterns. */
  private def makeUnapplyRecordStatements(
      name: Str,
      patternParameters: List[Param],
      scrut: VarSymbol,
      topmost: Split
  ): Ls[Statement] =
    val fieldSymbol = TempSymbol(N, name)
    val decl = LetDecl(fieldSymbol, Nil)
    val param = Param(FldFlags.empty, scrut, N, Modulefulness.none)
    val paramList = PlainParamList(param :: Nil)
    val lambda = Term.Lam(paramList, Term.SynthIf(topmost))
    val defineVar = DefineVar(fieldSymbol, lambda)
    val field = RcdField(str(name), fieldSymbol.safeRef)
    decl :: defineVar :: field :: Nil
  
  /** Translate an anonymous pattern. They are usually pattern arguments. */
  private def compileAnonymousPattern(patternParams: Ls[Param], params: Ls[Param], pattern: SP): Term = trace(
    pre = s"compileAnonymousPattern <<< $pattern", 
    post = (blk: Term) => s"compileAnonymousPattern >>> $blk"
  ):
    // If the `target` refers to a pattern symbol, we can reference the pattern.
    val term = pattern match
      case Constructor(target, N) =>
        target.symbol.flatMap(_.asPat).flatMap(Compiler.reference(_, target.toLoc))
      case _ => N
    term.getOrElse:
      val unapply = scoped("ucs:translation"):
        val inputSymbol = VarSymbol(Ident("input"))
        val topmost = makeMatchSplit(inputSymbol.toScrut, pattern)
          ((output, bindings) => Split.Else(makeMatchSuccess(output())), failure)
        log(s"Translated `unapply`: ${topmost.prettyPrint}")
        makeUnapplyRecordStatements("unapply", patternParams, inputSymbol, topmost)
      val unapplyStringPrefix = scoped("ucs:cp"):
        // We don't report errors here because they have been already reported in
        // the translation of `unapply` function.
        given Raise = Function.const(())
        val inputSymbol = VarSymbol(Ident("input"))
        val topmost = makeStringPrefixMatchSplit(inputSymbol.toScrut, pattern)
          ((consumedOutput, remainingOutput, bindings) => Split.Else:
            makeMatchSuccess(tup(fld(consumedOutput()), fld(remainingOutput()))), failure)
        log(s"Translated `unapplyStringPrefix`: ${topmost.prettyPrint}")
        makeUnapplyRecordStatements("unapplyStringPrefix", patternParams, inputSymbol, topmost)
      Term.Rcd(false, unapply ::: unapplyStringPrefix)

