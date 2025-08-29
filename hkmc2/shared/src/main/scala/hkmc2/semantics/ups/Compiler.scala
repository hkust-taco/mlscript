package hkmc2
package semantics
package ups


import mlscript.utils.*, shorthands.*

import syntax.{Keyword, LetBind, Tree}, Tree.{DecLit, Ident, IntLit, StrLit, UnitLit}
import Term.{Blk, IfLike, Rcd, Ref, SynthSel}
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
      case lit: syntax.Literal => FlatPattern.Lit(lit)(Nil)
      case sym: (ClassSymbol | ModuleOrObjectSymbol) =>
        FlatPattern.ClassLike(reference(sym, head.toLoc).getOrElse(Term.Error), N, Nil)
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
  
  val multiMatchers: MutMap[Set[Label], BlockLocalSymbol] = MutMap.empty
  
  /** The built multi-matcher functions. */
  val implementations: MutMap[BlockLocalSymbol, (ParamList, Term)] = MutMap.empty
  
  val buildQueue: Queue[(BlockLocalSymbol, Set[Pat])] = Queue.empty
  
  /** Build a matcher function that matches a single pattern. This function
   *  should be applied to the pattern that is considered as the entry point.*/
  def buildMatcher(pattern: Pat): ((BlockLocalSymbol, Str), Ls[Implementation]) = scoped("ucs:compiler"):
    val entryPointSymbol = buildMultiMatcher(Set(pattern))
    while buildQueue.nonEmpty do
      val (symbol, patterns) = buildQueue.dequeue()
      implementations += (symbol -> buildMultiMatcherBody(patterns))
    (entryPointSymbol, pattern.label.asFieldName) -> implementations.iterator.map:
      case (symbol, (paramList, term)) => (symbol, paramList, term)
    .toList
  
  /** Build a multi-matcher function and returns the local symbol that we can
   *  use to call it. The built function definition is stored in the map
   *  `implementations`. */
  def buildMultiMatcher(patterns: Set[Pat]): BlockLocalSymbol =
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
  def buildMultiMatcherBody(patterns: Set[Pat]): (ParamList, Term) = trace(
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
    val bodyTerm = IfLike(Keyword.`if`, topmostSplit)
    log(s"Multi-matcher body:\n${topmostSplit.prettyPrint}")
    (paramList(param(scrutinee)), bodyTerm)
  
  def multiMatcherBranch(
      patterns: Set[(Label, SpPat)],
      scrutinee: BlockLocalSymbol
  ): Blk = trace(
    pre = s"multiMatcherBranch: scrutinee = ${scrutinee} | patterns = ${
      patterns.iterator.map: (label, pattern) =>
        s"${pattern.showDbg} => ${label}"
      .mkString("{", ", ", "}")}"
  ):
    val labels = patterns.map((l, _) => l)
    val fields = patterns.flatMap((_, p) => p.fields)
    log(s"fields: ${fields.iterator.map(_.showDbg).mkString("{", ", ", "}")}")
    val subScrutinees = Map.from(fields.map(id => id -> VarSymbol(id.asIdent)))
    // The default record value for each sub-scrutinee. It is only used in the
    // bindings of fields.
    val emptyRecordSymbol = TempSymbol(N, s"emptyRecord$$")
    val recordItems = patterns.map: (label, _) =>
      RcdField(str(label.asFieldName), makeMatchFailure(str("empty")))
    .toList
    val emptyRecord = Rcd(false, recordItems)
    // Let bindings that bind the sub-scrutinee to the result of each matcher.
    val bindings = subScrutinees.iterator.flatMap: (field, subScrutineeVar) =>
      val subPatterns = patterns.flatMap((_, p) => p.collectSubPatterns(field))
      log(s"subPattern for field ${field.showDbg}: ${
        subPatterns.iterator.map(_.showDbg).mkString("{", ", ", "}")}")
      val subMatcherSymbol = buildMultiMatcher(subPatterns)
      val conditional =
        // Check the presence of the field, and call the matcher if it exists.
        val fieldIdent: Ident = field.asIdent
        val fieldSymbol = TempSymbol(N, fieldIdent.name)
        val fieldTest = FlatPattern.Record((fieldIdent -> fieldSymbol) :: Nil)(Nil)
        val consequent = Split.Else:
          app(subMatcherSymbol.safeRef, tup(fld(fieldSymbol.safeRef)), "result")
        val branch = Branch(scrutinee.safeRef, fieldTest, consequent)
        IfLike(Keyword.`if`, branch ~: Split.Else(emptyRecordSymbol.safeRef))
      LetDecl(subScrutineeVar, Nil) :: DefineVar(subScrutineeVar, conditional) :: Nil
    .toList
    // If there are no bindings, we do not need to create the empty record.
    val bindings2 = if bindings.isEmpty then Nil else
      LetDecl(emptyRecordSymbol, Nil) ::
        DefineVar(emptyRecordSymbol, emptyRecord) :: bindings
    // For each pattern, we compile a split and bind the result to a variable.
    // The variable will be a field of the output record.
    val z = (Nil: Ls[Statement], Nil: Ls[RcdField])
    val (tests, recordFields) = patterns.iterator.foldLeft(z):
      case ((stmts, fields), (label, pattern)) =>
        val symbol = TempSymbol(N, label.asFieldName + "$")
        val makeSplit = completePattern(pattern, scrutinee, subScrutinees, Nil)
        val split = makeSplit(
          // There's no transform in the topmost pattern. So, we just make and
          // return a `MatchResult` instance.
          makeConsequent = (outputSymbol, bindings) => Split.Else:
            makeMatchResult(outputSymbol.use, bindings.use),
          // Here the string "topmost" is just to indicate the failure is
          // passed from the topmost split for the purpose of debugging.
          alternative = Split.Else(makeMatchFailure(str("topmost"))))
        val test = IfLike(Keyword.`if`, split)
        // The corresponding record field should just take the result of the split.
        val field = RcdField(str(label.asFieldName), symbol.safeRef)
        (DefineVar(symbol, test) :: LetDecl(symbol, Nil) :: stmts, field :: fields)
    // Lastly, we return the output record.
    Blk(bindings2 ::: tests.reverse, Rcd(false, recordFields.reverse))
  
  import Pattern.*
  
  /** Represent things that can be used as expressions in consequents. */
  type Usable = BlockLocalSymbol | Term
  
  extension (usable: Usable)
    def use: Term = usable match
      case symbol: BlockLocalSymbol => symbol.safeRef
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
  private def completeMatchResult(
    transformOpt: Opt[TempSymbol],
    output: => Term,
    bindings: => Term
  ): Split = transformOpt match
    // If no transform is provided, we just return the current scrutinee and
    // the bindings through `MatchResult`.
    case N => Split.Else:
      makeMatchResult(output, bindings)
    case S(transform) =>
      val resultSymbol = TempSymbol(N, "transformResult")
      val transformTerm = app(transform.safeRef, tup(fld(bindings)), "the transform's result")
      Split.Let(resultSymbol, transformTerm, Split.Else(
        makeMatchResult(resultSymbol.safeRef)))
  
  def completePattern(
      pattern: SpPat,
      scrutinee: BlockLocalSymbol,
      subScrutinees: Map[Ident | Int, BlockLocalSymbol],
      aliases: Ls[VarSymbol]
  ): MakeSplit = trace(pre = s"completePattern: ${pattern.showDbg}"):
    pattern match
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
              case Nil => if currentBindings.isEmpty then rcd() else Rcd(false, currentBindings)
              case bindingsSymbol :: Nil =>
                if currentBindings.isEmpty then bindingsSymbol.safeRef
                else Rcd(false, RcdSpread(bindingsSymbol.safeRef) :: currentBindings)
              case _ =>
                // Spread the previously accumulated bindings.
                val spreads = bindingsSymbols.reverseIterator.map:
                  _.safeRef |> RcdSpread.apply
                .toList
                // Append the current bindings to the spreads.
                Rcd(false, spreads ::: currentBindings)
            makeConsequent(Rcd(false, fields.reverse), bindings)
          ): MakeSplit
      ):
        case ((field, pattern), makeInnerSplit) =>
          val label = pattern.label
          val target = sel(subScrutinees(field).safeRef, label.asFieldName)
          // This is the symbol for `MatchResult`.
          val resultSymbol = TempSymbol(N, s"result$label$$")
          // This is the symbol for the output of the pattern.
          val outputSymbol = TempSymbol(N, s"output$label$$")
          val outputField = RcdField(str(field.name), outputSymbol.safeRef)
          // This is the bindings of the current field.
          val fieldAliases = pattern.aliases
          val fieldBindingsSymbol = TempSymbol(N, "fieldBindings")
          val fieldBindingsTerm = Rcd(false, fieldAliases.map:
            alias => RcdField(str(alias.name), outputSymbol.safeRef))
          (outputFields: Ls[RcdField], bindingsSymbols: Ls[TempSymbol]) =>
            ((makeConsequent, alternative) =>
              val bindingsSymbol = TempSymbol(N, "bindings")
              Split.Let(resultSymbol, target, Branch(
                scrutinee = resultSymbol.safeRef,
                pattern = matchResultPattern(S(outputSymbol :: bindingsSymbol :: Nil)),
                continuation = Split.Let(
                  fieldBindingsSymbol,
                  fieldBindingsTerm,
                  makeInnerSplit(
                    outputField :: outputFields,
                    fieldBindingsSymbol :: bindingsSymbol :: bindingsSymbols
                  )(makeConsequent, Split.End)
                )
              ) ~: alternative)): MakeSplit
      makeMakeSplit(Nil, Nil)
    case Tuple(leading, spread, trailing) => (_, _) => 
      // TODO: Think about how to handle the spread pattern.
      error(msg"Tuple patterns are not supported yet." -> pattern.toLoc)
      Split.Else(makeMatchFailure(str("unsupported tuple pattern")))
    // The wildcard case always succeeds. Thus, the `alternative` is not used.
    case Or(Nil) => (makeConsequent, _) =>
      // Do forget to add the aliases of the current pattern to bindings.
      val bindings = aliases.map:
        alias => RcdField(str(alias.name), scrutinee.safeRef)
      makeConsequent(scrutinee, Rcd(false, bindings))
    // The never case should always fail.
    case And(Nil) => (_, _) => Split.Else(makeMatchFailure(str("never")))
    // The disjunction case should check the result from each pattern in order.
    case Or(patterns) =>
      // Make those functions first so that symbols are allocated top-down.
      val functions = patterns.map:
        completePattern(_, scrutinee, subScrutinees, aliases)
      (makeConsequent, alternative) => functions.foldRight(alternative):
        case (makeSplit, innerSplit) => makeSplit(makeConsequent, innerSplit)
    // The conjunction case should check all results from patterns and only
    // return `MatchResult` if all patterns succeed.
    case And(patterns) =>
      val functions = patterns.map:
        completePattern(_, scrutinee, subScrutinees, aliases)
      val makeMakeSplit = functions.foldRight(
        (allOutputs: Ls[Usable], allBindings: Ls[Usable]) => (
          (makeConsequent, alternative) =>
            // Here, we need to make a tuple of all output values of patterns.
            // Then we merge the bindings of all patterns.
            val outputSymbol = TempSymbol(N, "combinedOutput")
            val outputTerm = tup(allOutputs.reverseIterator.map(_.use |> fld).toSeq*)
            val bindingsSymbol = TempSymbol(N, "combinedBindings")
            // I think the bindings do not need to be reversed.
            val bindingsTerm = Rcd(false, allBindings.map:
              binding => RcdSpread(binding.use))
            splitLet(outputSymbol, outputTerm) <|:
              splitLet(bindingsSymbol, bindingsTerm) <|:
                makeConsequent(outputSymbol, bindingsSymbol)
        ): MakeSplit
      ): (makeSplit, makeInnerMakeSplit) =>
        (accOutputs: Ls[Usable], accBindings: Ls[Usable]) => (
          (makeConsequent, alternative) => makeSplit(
            // Get the output and bindings of the current pattern.
            makeConsequent = (output, bindings) =>
              makeInnerMakeSplit(output :: accOutputs, bindings :: accBindings)
                (makeConsequent, Split.End),
            alternative = alternative)
        ): MakeSplit
      makeMakeSplit(Nil, Nil)
    case Not(pattern) => (_, _) =>
      // TODO: Think about how to handle negation patterns.
      error(msg"Negation patterns are not supported yet." -> pattern.toLoc)
      Split.Else(makeMatchFailure(str("unsupported negation pattern")))
    case Rename(pattern, name) =>
      // We should add those fields to a context.
      completePattern(pattern, scrutinee, subScrutinees, name :: aliases)
    case Extract(pattern, term) =>
      // The symbol representing the transform function, which should be
      // declared at the outermost level.
      val transformSymbol = TempSymbol(N, "transform")
      // The transform function takes a single record as the argument.
      val bindingsSymbol = VarSymbol(Ident("args"))
      val params = paramList(param(bindingsSymbol))
      // We then bind the variables to fields of the record.
      val letBindings = pattern.symbols.flatMap: symbol =>
        LetDecl(symbol, Nil) ::
        DefineVar(symbol, sel(bindingsSymbol.safeRef, symbol.name)) :: Nil
      val makeSplit = completePattern(pattern, scrutinee, subScrutinees, Nil)
      (makeConsequent, alternative) => Split.Let(
        sym = transformSymbol,
        term = Term.Lam(params, Blk(letBindings, term.clone)),
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
            val currentBindings = Rcd(false, aliases.map:
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
  
  /** A multi-matcher implementation. */
  type Implementation = (BlockLocalSymbol, ParamList, Term)
  
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
    def findSymbol(elem: Ctx.Elem): Opt[Term] =
      elem.symbol.flatMap(_.asClsLike).collectFirst:
        // Check the element's symbol.
        case `symbol` => S(elem.ref(new Ident(symbol.nme)).withLoc(loc))
        // Look up the symbol in module members.
        case module: ModuleOrObjectSymbol =>
          val moduleRef = module.defn.get.bsym.ref()
          module.tree.definedSymbols.iterator.map(_.mapSecond(_.asClsLike)).collectFirst:
            case (key, S(`symbol`)) =>
              val memberSymbol = symbol.defn.get.bsym
              SynthSel(moduleRef, Ident(key))(S(memberSymbol))
      .flatten
    @tailrec def go(ctx: Ctx): Opt[Term] =
      ctx.env.values.iterator.map(findSymbol).firstSome match
        case S(term) => S(fillImplicitArgs(term))
        case N => ctx.parent match
          case N => N
          case S(parent) => go(parent)
    go(ctx).map: term =>
      // If the `symbol` is a virtual class, then do not select `class`.
      symbol match
        case s: ClassSymbol if !(ctx.builtins.virtualClasses contains s) =>
          SynthSel(term, Ident("class"))(S(s)).resolve
        case _: (ClassSymbol | ModuleOrObjectSymbol | PatternSymbol) => term
  
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
