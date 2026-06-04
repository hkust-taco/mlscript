package hkmc2
package semantics
package ups


import mlscript.utils.*, shorthands.*

import syntax.{Keyword, LetBind, Tree}, Tree.{BoolLit, DecLit, Ident, IntLit, StrLit, UnitLit}
import Term.{Blk, Rcd, Ref, SynthIf, SynthSel}
import Pattern.{Instantiation, Head}
import Elaborator.{Ctx, State, ctx}, utils.TL
import ucs.{TermSynthesizer, FlatPattern, safeRef}
import Message.MessageContext, ucs.error

import collection.mutable.{Queue, Map as MutMap}, collection.immutable.{Set, Map}
import scala.annotation.tailrec

/** The compiler for pattern definitions. It compiles instantiated patterns into
  * a few matcher functions. Each matcher function matches a set of patterns
  * and returns a record that contains the results of each pattern.
  */
class Compiler(using Context)(using tl: TL)(using Ctx, State, Raise) extends TermSynthesizer:
  import Compiler.*, tl.*
  import Pattern.*

  /** A previously-computed matcher result for one field of the current
    * multi-matcher. The runtime representation is shape-dependent:
    * singleton-label matchers return the label's value directly, while
    * multi-label matchers return a record keyed by label field names.
    */
  private final case class MatcherResult(symbol: VarSymbol, labels: Set[Label]):
    private def result: Term = sel(symbol.safeRef, "result")
    def input: Term = sel(symbol.safeRef, "input")
    /** Read the result for one label from this matcher result, abstracting over
      * the singleton direct-return optimization.
      */
    def select(label: Label): Term =
      if labels.size is 1 then result
      else sel(result, label.asFieldName)
    /** Produce the default failure value for this matcher result with the same
      * shape that a successful submatcher call would have produced.
      */
    def default(using ResultMode): Term =
      val result = labels.toList match
        case label :: Nil => emptyMatchResult("empty")
        case labels =>
          Rcd(false, labels.map: label =>
            RcdField(str(label.asFieldName), emptyMatchResult("empty")))
      rcd(
        RcdField(str("input"), `null`),
        RcdField(str("result"), result)
      )

  private def bool(value: Bool): Term = Term.Lit(BoolLit(value))

  private def isMatchOnly(using mode: ResultMode): Bool = mode is ResultMode.MatchOnly

  private def emptyMatchResult(reason: Str)(using mode: ResultMode): Term =
    if isMatchOnly then bool(false) else makeMatchFailure(str(reason))

  private def nullifyEmptyBindings(bindings: Term): Term = bindings match
    case Rcd(false, Nil) => `null`
    case bindings => bindings
  
  extension (label: Label)
    /** This decides the the field name of each label in the match record. */
    def asFieldName: Str = s"p_$label"
  
  extension (pattern: Pat)
    /** Get or create a label for the pattern. */
    def label: Label = labelMap.getOrElseUpdate(pattern, labelMap.size)
  
  extension (field: Ident | Int)
    def showDbg: Str = field match
      case id: Ident => id.name
      case index: Int => s"p_$index"
    /** Convert the field name to an `Ident`. */
    def asIdent: Ident = field match
      case id: Ident => new Ident(id.name)
      case index: Int => Ident(index.toString)
  
  extension (head: Head)
    /** Create a flat pattern that can be used in the UCS expressions. */
    def toFlatPattern: FlatPattern = head match
      case lit: syntax.Literal => FlatPattern.Lit(lit)
      case sym: (ClassSymbol | ModuleOrObjectSymbol) =>
        val constructor = reference(sym, head.toLoc).getOrElse(Term.Error)
        FlatPattern.ClassLike(constructor, sym, N, false)(Tree.Dummy)
    def showDbg: Str = head match
      case lit: syntax.Literal => lit.idStr
      case sym: ClassLikeSymbol => sym.nme
  
  extension (patterns: Set[(Label, ExPat)])
    /** Specialize a set of patterns. Also display them in the debug log. */
    def specializeSet(head: Opt[Head]): Set[(Label, SpPat)] =
      log(s"Specialized patterns of ${head.fold("the case without tags")(_.showDbg)}:")
      patterns.map: (label, pattern) =>
        val spec = pattern.specialize(head)
        val simp = spec.simplify
        log(s"• Label $label")
        log(s"  ‣ Expanded: ${spec.showDbg}")
        log(s"  ‣ Simplified: ${simp.showDbg}")
        (label, simp)
  
  val labelMap: MutMap[Pat, Label] = MutMap()
  
  val multiMatchers: MutMap[Set[Label], LocalVarSymbol] = MutMap.empty
  
  /** The built multi-matcher functions. */
  val implementations: MutMap[LocalVarSymbol, (ParamList, Term)] = MutMap.empty
  
  val buildQueue: Queue[(LocalVarSymbol, Set[Pat])] = Queue.empty
  
  /** Build a matcher function that matches a single pattern. This function
   *  should be applied to the pattern that is considered as the entry point.*/
  def buildMatcher(pattern: Pat, resultMode: ResultMode): (LocalVarSymbol, Ls[Implementation]) = scoped("ucs:compiler"):
    given ResultMode = resultMode
    val entryPointSymbol = buildMultiMatcher(Set(pattern))
    while buildQueue.nonEmpty do
      val (symbol, patterns) = buildQueue.dequeue()
      implementations += (symbol -> buildMultiMatcherBody(patterns))
    entryPointSymbol -> implementations.iterator.map:
      case (symbol, (paramList, term)) => (symbol, paramList, term)
    .toList
  
  /** Build a multi-matcher function and returns the local symbol that we can
   *  use to call it. The built function definition is stored in the map
   *  `implementations`. */
  def buildMultiMatcher(patterns: Set[Pat])(using ResultMode): LocalVarSymbol =
    // Get or create the label for each pattern. Multi-matchers are identified
    // by the set of labels (orders are not important).
    val labels = patterns.map(_.label)
    multiMatchers.get(labels).getOrElse:
      val f = TempSymbol(N, makeMultiMatcherName(patterns))
      multiMatchers += (labels -> f)
      buildQueue enqueue (f -> patterns)
      f // Return the symbol of the built function.
  
  /** Build the body of a multi-matcher function. The memoization is done by
   *  `buildMultiMatcher`. */
  def buildMultiMatcherBody(patterns: Set[Pat])(using ResultMode): (ParamList, Term) = trace(
    pre = s"buildMultiMatcherBody: ${
      patterns.iterator.map: pattern =>
        s"${pattern.showDbg} => ${pattern.label}"
      .mkString("{", ", ", "}")}"
  ):
    val expandedPatterns = patterns.map(p => (p.label, p.expand(Set.empty)))
    val heads = expandedPatterns.flatMap((_, p) => p.heads).toList
    // This is the parameter of the current multi-matcher.
    val scrutinee = VarSymbol(Ident("input"))
    // Assemble branches for constructors and literals.
    val branches = heads.map: head =>
      // Weird. Removing type annotations caused type errors.
      val specialized = expandedPatterns.specializeSet(S(head))
      val consequent = Split.Else(multiMatcherBranch(specialized, scrutinee))
      Branch(scrutinee.safeRef, head.toFlatPattern, consequent)
    // Assemble the default branch.
    val default =
      // Weird. Removing type annotations caused type errors.
      val specialized = expandedPatterns.specializeSet(N)
      Split.Else(multiMatcherBranch(specialized, scrutinee))
    // Make a split that tries all branches in order.
    val topmostSplit = branches.foldRight(default)(_ ~: _)
    val bodyTerm = SynthIf(topmostSplit)
    log(s"Multi-matcher body:\n${topmostSplit.prettyPrint}")
    (paramList(param(scrutinee)), bodyTerm)
  
  def multiMatcherBranch(
      patterns: Set[(Label, SpPat)],
      scrutinee: LocalVarSymbol
  )(using ResultMode): Blk = trace(
    pre = s"multiMatcherBranch: scrutinee = ${scrutinee} | patterns = ${
      patterns.iterator.map: (label, pattern) =>
        s"${pattern.showDbg} => ${label}"
      .mkString("{", ", ", "}")}"
  ):
    val fields = patterns.flatMap((_, p) => p.fields)
    log(s"fields: ${fields.iterator.map(_.showDbg).mkString("{", ", ", "}")}")
    val subPatternsByField = Map.from(fields.map: field =>
      field -> patterns.flatMap((_, p) => p.collectSubPatterns(field)))
    val subScrutinees = Map.from(subPatternsByField.map: (field, subPatterns) =>
      field -> MatcherResult(VarSymbol(field.asIdent), subPatterns.map(_.label)))
    // Let bindings that bind the sub-scrutinee to the result of each matcher.
    val bindings = subPatternsByField.iterator.flatMap: (field, subPatterns) =>
      val subScrutinee = subScrutinees(field)
      log(s"subPattern for field ${field.showDbg}: ${
        subPatterns.iterator.map(_.showDbg).mkString("{", ", ", "}")}")
      val subMatcherSymbol = buildMultiMatcher(subPatterns)
      val conditional =
        // Check the presence of the field, and call the matcher if it exists.
        val fieldIdent: Ident = field.asIdent
        val fieldSymbol = TempSymbol(N, fieldIdent.name)
        val fieldTest = FlatPattern.Record((fieldIdent -> fieldSymbol) :: Nil)
        val consequent = Split.Else:
          val resultTerm = app(subMatcherSymbol.safeRef, tup(fld(fieldSymbol.safeRef)), "result")
          rcd(
            RcdField(str("input"), fieldSymbol.safeRef),
            RcdField(str("result"), resultTerm)
          )
        val branch = Branch(scrutinee.safeRef, fieldTest, consequent)
        SynthIf(branch ~: Split.Else(subScrutinee.default))
      LetDecl(subScrutinee.symbol, Nil) :: DefineVar(subScrutinee.symbol, conditional) :: Nil
    .toList
    // For each pattern, we compile a split and bind the result to a variable.
    // The variable will be a field of the output record.
    val z = (Nil: Ls[Statement], Nil: Ls[(Label, Term)])
    val (tests, resultTerms) = patterns.iterator.foldLeft(z):
      case ((stmts, results), (label, pattern)) =>
        val symbol = TempSymbol(N, label.asFieldName + "$")
        val makeSplit = completePattern(pattern, scrutinee, subScrutinees, Nil)
        val split = makeSplit(
          // There is no topmost transform here, so we emit the direct success
          // value: `MatchSuccess` in full mode, `true` in match-only mode.
          makeConsequent = (outputSymbol, bindings) => Split.Else:
            if isMatchOnly then bool(true)
            else makeMatchSuccess(outputSymbol.use, nullifyEmptyBindings(bindings.use)),
          alternative = Split.Else(emptyMatchResult("topmost")))
        val test = SynthIf(split)
        (DefineVar(symbol, test) :: LetDecl(symbol, Nil) :: stmts, (label, symbol.safeRef) :: results)
    // Materialize the matcher's final return value. Singleton matchers return
    // their only field directly; multi-label matchers still return a record.
    val resultTerm = resultTerms.reverse match
      case (_, term) :: Nil => term
      case terms => Rcd(false, terms.map: (label, term) =>
        RcdField(str(label.asFieldName), term))
    // Lastly, we return the matcher result, directly for singleton matchers
    // and as a record otherwise.
    Blk(bindings ::: tests.reverse, resultTerm)
  
  import Pattern.*
  
  /** Represent things that can be used as expressions in consequents. */
  type Usable = LocalVarSymbol | Term
  
  extension (usable: Usable)
    def use: Term = usable match
      case symbol: LocalVarSymbol => symbol.safeRef
      case term: Term => term
  
  /** The bindings can be a `Term` or a `TempSymbol`. */
  type MakeConsequent = (output: Usable, bindings: Usable) => Split
  
  /** A function that makes a split in matcher functions. The first argument
   *  is the function that makes the innermost split. The second argument is the
   *  alternative split. Note that the alternative is not a fallback.
   */
  type MakeSplit = (makeConsequent: MakeConsequent, alternative: Split) => Split
  
  /** Create the innermost `Else` split based on whether we have a transform
   *  term or not.
   *  @param output The default output of the pattern. It will not be evaluated
   *                if there is a transform term.
   */
  private def completeMatchSuccess(
    transformOpt: Opt[TempSymbol],
    output: => Term,
    bindings: => Term
  ): Split = transformOpt match
    // If no transform is provided, we just return the current scrutinee and
    // the bindings through `MatchSuccess`.
    case N => Split.Else:
      makeMatchSuccess(output, nullifyEmptyBindings(bindings))
    case S(transform) =>
      val resultSymbol = TempSymbol(N, "transformResult")
      val bindingsTerm = nullifyEmptyBindings(bindings)
      val transformTerm = app(transform.safeRef, tup(fld(bindingsTerm)), "the transform's result")
      Split.Let(resultSymbol, transformTerm, Split.Else(
        makeMatchSuccess(resultSymbol.safeRef)))
  
  private def completePattern(
      pattern: SpPat,
      scrutinee: LocalVarSymbol,
      subScrutinees: Map[Ident | Int, MatcherResult],
      aliases: Ls[VarSymbol]
  )(using ResultMode): MakeSplit = trace(pre = s"completePattern: ${pattern.showDbg}"):
    pattern match
    case MatchedClassLike(sym, fields) if isMatchOnly =>
      val acceptAll: MakeSplit = (makeConsequent, _) => makeConsequent(scrutinee, rcd())
      fields.iterator.foldRight(acceptAll):
        case ((field, pattern), makeInnerSplit) =>
          val label = pattern.label
          val target = subScrutinees(field).select(label)
          val resultSymbol = TempSymbol(N, s"result$label$$")
          (makeConsequent, alternative) =>
            Split.Let(resultSymbol, target,
              Branch(resultSymbol.safeRef,
                makeInnerSplit(makeConsequent, Split.End)) ~: alternative)
    case MatchedClassLike(sym, fields) =>
      val rebuildNeeded = fields.iterator.exists((_, pattern) => !pattern.preservesOriginalScrutinee)
      val constructor = sym match
        case symbol: (ClassSymbol | ModuleOrObjectSymbol) =>
          reference(symbol, symbol.toLoc).getOrElse(Term.Error)
      val makeMakeSplit = fields.iterator.foldRight(
        (fields: Ls[(Ident, Term)], bindingsSymbols: Ls[TempSymbol]) =>
          ((makeConsequent, alternative) =>
            log(s"current bindings: " + aliases.map(_.name).mkString("{", ", ", "}"))
            val currentBindings = aliases.map:
              alias => RcdField(str(alias.name), scrutinee.safeRef)
            val bindings = bindingsSymbols match
              case Nil => makeBindings(currentBindings)
              case bindingsSymbol :: Nil =>
                if currentBindings.isEmpty then bindingsSymbol.safeRef
                else makeBindings(RcdSpread(bindingsSymbol.safeRef) :: currentBindings)
              case _ =>
                val spreads = bindingsSymbols.reverseIterator.map:
                  _.safeRef |> RcdSpread.apply
                .toList
                makeBindings(spreads ::: currentBindings)
            val output =
              if rebuildNeeded then
                `new`(
                  constructor,
                  tup(fields.reverseIterator.map(_._2 |> fld).toSeq*) :: Nil,
                  s"rebuilt ${sym.nme}"
                )
              else
                scrutinee.safeRef
            makeConsequent(output, bindings)
          ): MakeSplit
      ):
        case ((field, pattern), makeInnerSplit) =>
          val label = pattern.label
          val target = subScrutinees(field).select(label)
          val resultSymbol = TempSymbol(N, s"result$label$$")
          val outputSymbol = TempSymbol(N, s"output$label$$")
          val fieldAliases = pattern.aliases
          val fieldBindingsSymbol = TempSymbol(N, "fieldBindings")
          val fieldBindingsTerm = makeBindings(fieldAliases.map:
            alias => RcdField(str(alias.name), outputSymbol.safeRef))
          val fieldOutput =
            if rebuildNeeded && !pattern.preservesOriginalScrutinee then outputSymbol.safeRef
            else subScrutinees(field).input
          (outputFields: Ls[(Ident, Term)], bindingsSymbols: Ls[TempSymbol]) =>
            ((makeConsequent, alternative) =>
              val bindingsSymbol = TempSymbol(N, "bindings")
              val accumulatedBindings =
                val withFieldAliases =
                  if fieldAliases.isEmpty then bindingsSymbols
                  else fieldBindingsSymbol :: bindingsSymbols
                if pattern.symbols.isEmpty then withFieldAliases
                else bindingsSymbol :: withFieldAliases
              val innerSplit =
                makeInnerSplit((field, fieldOutput) :: outputFields, accumulatedBindings)
                  (makeConsequent, Split.End)
              Split.Let(resultSymbol, target, Branch(
                scrutinee = resultSymbol.safeRef,
                pattern = matchSuccessPattern(S(outputSymbol :: bindingsSymbol :: Nil)),
                continuation =
                  if fieldAliases.isEmpty then innerSplit
                  else Split.Let(fieldBindingsSymbol, fieldBindingsTerm, innerSplit)
              ) ~: alternative)): MakeSplit
      makeMakeSplit(Nil, Nil)
    case Record(fields) if isMatchOnly =>
      val acceptAll: MakeSplit = (makeConsequent, _) => makeConsequent(scrutinee, rcd())
      fields.iterator.foldRight(acceptAll):
        case ((field, pattern), makeInnerSplit) =>
          val label = pattern.label
          val target = subScrutinees(field).select(label)
          val resultSymbol = TempSymbol(N, s"result$label$$")
          (makeConsequent, alternative) =>
            Split.Let(resultSymbol, target,
              Branch(resultSymbol.safeRef,
                makeInnerSplit(makeConsequent, Split.End)) ~: alternative)
    case Record(fields) =>
      // Input: a record pattern made of several fields.
      // Output: a record, each field of which is the output of the
      //   corresponding field's pattern.
      // Construct a conjunction of tests for each field.
      val makeMakeSplit = fields.iterator.foldRight(
        (fields: Ls[RcdField], bindingsSymbols: Ls[TempSymbol]) =>
          ((makeConsequent, alternative) =>
            log(s"current bindings: " + aliases.map(_.name).mkString("{", ", ", "}"))
            // The current pattern's bindings.
            val currentBindings = aliases.map:
              alias => RcdField(str(alias.name), scrutinee.safeRef)
            // Here, we need to merge the current bindings with previously
            // accumulated bindings. Some special cases here are to make the
            // generated code more concise and efficient.
            val bindings = bindingsSymbols match
              case Nil => makeBindings(currentBindings)
              case bindingsSymbol :: Nil =>
                if currentBindings.isEmpty then bindingsSymbol.safeRef
                else makeBindings(RcdSpread(bindingsSymbol.safeRef) :: currentBindings)
              case _ =>
                // Spread the previously accumulated bindings.
                val spreads = bindingsSymbols.reverseIterator.map:
                  _.safeRef |> RcdSpread.apply
                .toList
                // Append the current bindings to the spreads.
                makeBindings(spreads ::: currentBindings)
            makeConsequent(Rcd(false, fields.reverse), bindings)
          ): MakeSplit
      ):
        case ((field, pattern), makeInnerSplit) =>
          val label = pattern.label
          val target = subScrutinees(field).select(label)
          // This is the symbol for `MatchSuccess`.
          val resultSymbol = TempSymbol(N, s"result$label$$")
          // This is the symbol for the output of the pattern.
          val outputSymbol = TempSymbol(N, s"output$label$$")
          val outputField = RcdField(str(field.name), outputSymbol.safeRef)
          // This is the bindings of the current field.
          val fieldAliases = pattern.aliases
          val fieldBindingsSymbol = TempSymbol(N, "fieldBindings")
          val fieldBindingsTerm = makeBindings(fieldAliases.map:
            alias => RcdField(str(alias.name), outputSymbol.safeRef))
          (outputFields: Ls[RcdField], bindingsSymbols: Ls[TempSymbol]) =>
            ((makeConsequent, alternative) =>
              val bindingsSymbol = TempSymbol(N, "bindings")
              val accumulatedBindings =
                val withFieldAliases =
                  if fieldAliases.isEmpty then bindingsSymbols
                  else fieldBindingsSymbol :: bindingsSymbols
                if pattern.symbols.isEmpty then withFieldAliases
                else bindingsSymbol :: withFieldAliases
              val innerSplit =
                makeInnerSplit(outputField :: outputFields, accumulatedBindings)
                  (makeConsequent, Split.End)
              Split.Let(resultSymbol, target, Branch(
                scrutinee = resultSymbol.safeRef,
                pattern = matchSuccessPattern(S(outputSymbol :: bindingsSymbol :: Nil)),
                continuation =
                  if fieldAliases.isEmpty then innerSplit
                  else Split.Let(fieldBindingsSymbol, fieldBindingsTerm, innerSplit)
              ) ~: alternative)): MakeSplit
      makeMakeSplit(Nil, Nil)
    case Tuple(leading, spread) => (_, _) => 
      // TODO: Think about how to handle the spread pattern.
      error(msg"Tuple patterns are not supported yet." -> pattern.toLoc)
      Split.Else(emptyMatchResult("unsupported tuple pattern"))
    // The wildcard case always succeeds. Thus, the `alternative` is not used.
    case Or(Nil) => (makeConsequent, _) =>
      if isMatchOnly then makeConsequent(scrutinee, rcd()) else
        val bindings = aliases.map:
          alias => RcdField(str(alias.name), scrutinee.safeRef)
        makeConsequent(scrutinee, makeBindings(bindings))
    // The never case should always fail.
    case And(Nil) => (_, _) => Split.Else(emptyMatchResult("never"))
    // The disjunction case should check the result from each pattern in order.
    case Or(patterns) =>
      // Make those functions first so that symbols are allocated top-down.
      val functions = patterns.map:
        completePattern(_, scrutinee, subScrutinees, aliases)
      (makeConsequent, alternative) => functions.foldRight(alternative):
        case (makeSplit, innerSplit) => makeSplit(makeConsequent, innerSplit)
    // The conjunction case should check all results from patterns and only
    // return `MatchSuccess` if all patterns succeed.
    case And(patterns) if isMatchOnly =>
      val functions = patterns.map:
        completePattern(_, scrutinee, subScrutinees, Nil)
      val acceptAll: MakeSplit = (makeConsequent, _) => makeConsequent(scrutinee, rcd())
      functions.foldRight(acceptAll):
        case (makeSplit, makeInnerSplit) =>
        (makeConsequent, alternative) => makeSplit(
          makeConsequent = (_output, _bindings) =>
            makeInnerSplit(makeConsequent, Split.End),
          alternative = alternative)
    case And(patterns) =>
      val functions = patterns.map: pattern =>
        pattern -> completePattern(pattern, scrutinee, subScrutinees, aliases)
      val makeMakeSplit = functions.foldRight(
        (allOutputs: Ls[Usable], allBindings: Ls[Usable]) => (
          (makeConsequent, alternative) =>
            // Here, we need to make a tuple of all output values of patterns.
            // Then we merge the bindings of all patterns.
            val outputSymbol = TempSymbol(N, "combinedOutput")
            val outputTerm = tup(allOutputs.reverseIterator.map(_.use |> fld).toSeq*)
            val bindingsSymbol = TempSymbol(N, "combinedBindings")
            // I think the bindings do not need to be reversed.
            val bindingsTerm = makeBindings(allBindings.map:
              binding => RcdSpread(binding.use))
            splitLet(outputSymbol, outputTerm) <|:
              splitLet(bindingsSymbol, bindingsTerm) <|:
                makeConsequent(outputSymbol, bindingsSymbol)
        ): MakeSplit
      ):
        case ((pattern, makeSplit), makeInnerMakeSplit) =>
          (accOutputs: Ls[Usable], accBindings: Ls[Usable]) => (
            (makeConsequent, alternative) => makeSplit(
              // Get the output and bindings of the current pattern.
              makeConsequent = (output, bindings) =>
                val nextBindings =
                  if aliases.nonEmpty || pattern.symbols.nonEmpty then
                    bindings :: accBindings
                  else
                    accBindings
                makeInnerMakeSplit(output :: accOutputs, nextBindings)
                  (makeConsequent, Split.End),
              alternative = alternative)
          ): MakeSplit
      makeMakeSplit(Nil, Nil)
    case Not(pattern) => (_, _) =>
      // TODO: Think about how to handle negation patterns.
      error(msg"Negation patterns are not supported yet." -> pattern.toLoc)
      Split.Else(emptyMatchResult("unsupported negation pattern"))
    case Rename(pattern, name) =>
      completePattern(pattern, scrutinee, subScrutinees,
        if isMatchOnly then Nil else name :: aliases)
    case Extract(pattern, correspondence, term) =>
      if isMatchOnly then
        completePattern(pattern, scrutinee, subScrutinees, Nil)
      else
      // The symbol representing the transform function, which should be
      // declared at the outermost level.
        val transformSymbol = TempSymbol(N, "transform")
        // The transform function takes a single record as the argument.
        val bindingsSymbol = VarSymbol(Ident("args"))
        val params = paramList(param(bindingsSymbol))
        // Because we pass the extracted values using recoreds. We need to bind
        // each property to its corresponding variable which is accessible from
        // then `term`.
        val letBindings = pattern.symbols.flatMap: symbol =>
          val termSymbol = correspondence(symbol)
          LetDecl(termSymbol, Nil) ::
          DefineVar(termSymbol, sel(bindingsSymbol.safeRef, termSymbol.name)) :: Nil
        val makeSplit = completePattern(pattern, scrutinee, subScrutinees, Nil)
        (makeConsequent, alternative) => Split.Let(
          sym = transformSymbol,
          term = Term.Lam(params, Blk(letBindings, term.mkClone)),
          tail = makeSplit(
            // The `outputSymbol` is the output of `pattern`.
            //                vvvvvvvvvvvv
            makeConsequent = (outputSymbol, bindings) =>
              // Apply the transform to the bindings.
              val transformTerm = app(transformSymbol.safeRef,
                tup(fld(bindings.use)), "the transform's result")
              // Bind the transformation result to a new output symbol.
              val resultSymbol = TempSymbol(N, "transformResult")
              // Don't forget that current pattern may also have aliases which are
              // available in some outer transform patterns.
              val currentBindingsSymbol = TempSymbol(N, "bindings")
              val currentBindings = makeBindings(aliases.map:
                alias => RcdField(str(alias.name), resultSymbol.safeRef))
              Split.Let(resultSymbol, transformTerm,
                Split.Let(currentBindingsSymbol, currentBindings,
                  makeConsequent(resultSymbol, currentBindingsSymbol))),
            alternative = alternative))
  
  /** Make a human-readable name for patterns that only have class patterns. If
   *  the patterns are too complicated, we just use the counter. */
  def makeMultiMatcherName(patterns: Set[Pat]): Str =
    "matcher" +
    patterns.iterator.mapOption(_.shortName()).fold(multiMatchers.size.toString):
      _.reverse.mkString("__", "_", "")
    + "$"

object Compiler:
  type Label = Int

  enum ResultMode:
    case Full, MatchOnly
  
  /** A multi-matcher implementation. */
  type Implementation = (LocalVarSymbol, ParamList, Term)
  
  /** Perform a reverse lookup for a term that references a symbol in the
    *  current context. */
  def reference(symbol: ClassSymbol | ModuleOrObjectSymbol | PatternSymbol, loc: Opt[Loc])(using tl: TL)(using Ctx, State): Opt[Term] =
    /** To make `Lowering` happy about the terms. */
    def fillImplicitArgs(term: Term): Term = term match
      case ref: Ref => ref.resolve
      case sel: SynthSel =>
        fillImplicitArgs(sel.prefix)
        sel.resolve
      case _: Term => term
    type ClassLikeDefnSymbol = ClassSymbol | ModuleOrObjectSymbol | PatternSymbol
    def classLikeCandidates(symbol: Symbol): Iterator[ClassLikeDefnSymbol] = symbol match
      case symbol: ClassLikeDefnSymbol =>
        Iterator.single(symbol)
      case member: BlockMemberSymbol =>
        (member.clsTree.iterator.map(_.symbol.asClsLike) ++
          member.modOrObjTree.iterator.map(_.symbol.asClsLike) ++
          member.patTree.iterator.map(_.symbol.asClsLike))
        .flatten
      case _ => Iterator.empty
    def memberReference(
        ownerRef: Term,
        key: Str,
        member: Symbol
    ): Opt[Term] =
      classLikeCandidates(member).collectFirst:
        case candidate if candidate is symbol =>
          val memberSymbol = candidate.defn.get.bsym
          SynthSel(ownerRef, new Ident(key).withLoc(loc))(S(memberSymbol), FlowSymbol.synthSel(key), N, S(summon))
            .resolved(candidate)
    def ownerMemberReference(owner: ClassSymbol | ModuleOrObjectSymbol): Opt[Term] =
      val ownerRef = owner.defn.get.bsym.ref()
      owner.tree.definedSymbols.iterator.map:
        case (key, member) => memberReference(ownerRef, key, member)
      .firstSome
    def findSymbol(elem: Ctx.Elem): Opt[Term] =
      val direct = elem.symbol.iterator.flatMap(classLikeCandidates).collectFirst:
        case candidate if candidate is symbol =>
          elem.ref(new Ident(candidate.nme)).withLoc(loc).resolved(candidate)
      direct.orElse:
        elem.symbol.iterator.collectFirst:
          case owner: (ClassSymbol | ModuleOrObjectSymbol) =>
            ownerMemberReference(owner)
        .flatten
    def ownerChainReference(symbol: ClassLikeDefnSymbol): Opt[Term] =
      def mkSelect(prefix: Term, member: BlockMemberSymbol, target: ClassLikeDefnSymbol): Term =
        SynthSel(prefix, new Ident(member.nme).withLoc(loc))(S(member), FlowSymbol.synthSel(member.nme), N, S(summon))
          .resolved(target)
      def go(symbol: ClassLikeDefnSymbol): Term =
        val defn = symbol.defn.getOrElse(lastWords(s"Missing definition for symbol `${symbol.nme}`."))
        defn.owner match
          case S(owner: ClassLikeDefnSymbol) =>
            mkSelect(go(owner), defn.bsym, symbol)
          case S(owner) =>
            mkSelect(owner.ref().resolve, defn.bsym, symbol)
          case N =>
            defn.bsym.ref(new Ident(defn.bsym.nme).withLoc(loc)).resolved(symbol)
      symbol.defn.map(_ => go(symbol))
    @tailrec def go(ctx: Ctx): Opt[Term] =
      val fromEnv = ctx.env.values.iterator.map(findSymbol).firstSome
      val fromOuter = ctx.outer.inner.collectFirst:
          case owner: (ClassSymbol | ModuleOrObjectSymbol) =>
            ownerMemberReference(owner)
        .flatten
      (fromEnv orElse fromOuter) match
        case S(term) => S(fillImplicitArgs(term))
        case N => ctx.parent match
          case N => N
          case S(parent) => go(parent)
    go(ctx).orElse(ownerChainReference(symbol))
  
  import Pattern.*
  
  extension [X](xs: Iterator[X])
    /** Apply a function to each element of the iterator. If any of the calls
     *  returns `None`, then the whole function returns `None`. */
    def mapOption[Y](f: X => Opt[Y]): Opt[Ls[Y]] =
      xs.foldLeft(S(Nil): Opt[Ls[Y]]):
        case (S(acc), x) => f(x) match
          case S(y) => S(y :: acc)
          case N => N
        case (N, _) => N
  
  /** Canadian Syllabics Pa */
  val FAKE_LEFT_ANGLE = "ᐸ"
  /** Canadian Syllabics Na */
  val FAKE_RIGHT_ANGLE = "ᐳ"
  
  // I learned the characters above from Go's trick:
  // https://news.ycombinator.com/item?id=14276891
  // and I introduced more symbols by following the trick.
  
  /** Katakana-Hiragana Prolonged Sound Mark */
  val FAKE_MINUS = "ー"
  /** Lisu Letter Ta */
  val FAKE_TOP = "ꓔ"
  /** Lisu Letter Tha */
  val FAKE_BOTTOM = "ꓕ"
  /** Lisu Letter Tone Na Po */
  val FAKE_COMMA = "ꓹ"
  /** Modifier Letter Left Half Ring */
  val FAKE_LEFT_PAREN = "ʿ"
  /** Modifier Letter Right Half Ring */
  val FAKE_RIGHT_PAREN = "ʾ"
  /** Latin Letter Lateral Click */
  val FAKE_BAR = "ǁ"
  
  extension (pattern: Pat)
    /** Make a human-readable short name using Unicode letters, which are
     *  allowed in in identifiers in the generated code, for patterns. */
    def shortName(prec: Int = 0): Opt[Str] = pattern match
      case Literal(IntLit(n)) => S((if n < 0 then FAKE_MINUS else "") + n.toString)
      case Literal(StrLit(s)) => S(s"str${s.length}")
      case Literal(UnitLit(true)) => S("null")
      case Literal(UnitLit(false)) => S("undefined")
      case ClassLike(sym, arguments) => arguments.fold(S(sym.nme)): arguments =>
        arguments.iterator.mapOption:
          case (_, pat) => pat.shortName(0)
        .map(_.reverse.mkString(sym.nme + FAKE_LEFT_PAREN, FAKE_COMMA, FAKE_RIGHT_PAREN))
      case MatchedClassLike(sym, entries) =>
        entries.iterator.mapOption:
          case (_, pat) => pat.shortName(0)
        .map(_.reverse.mkString(sym.nme + FAKE_LEFT_PAREN, FAKE_COMMA, FAKE_RIGHT_PAREN))
      case Synonym(Instantiation(symbol, patterns)) =>
        if patterns.isEmpty then S(symbol.nme) else
          patterns.iterator.mapOption(_.shortName(0)).map:
            _.reverse.mkString(symbol.nme + FAKE_LEFT_ANGLE, FAKE_COMMA, FAKE_RIGHT_ANGLE)
      case Or(Nil) => S(FAKE_BOTTOM)
      case Or(patterns) => patterns.iterator.mapOption(_.shortName(1)).map:
        _.reverse.mkString(
          if prec > 0 then FAKE_LEFT_PAREN else "",
          FAKE_BAR,
          if prec > 0 then FAKE_RIGHT_PAREN else "")
      case And(Nil) => S(FAKE_TOP)
      case _ => N
