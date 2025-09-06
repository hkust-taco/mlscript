package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.{Literal, Tree}, utils.TraceLogger
import Message.MessageContext
import Elaborator.{Ctx, State, ctx}
import utils.*
import FlatPattern.Argument
import ups.Instantiator
import hkmc2.semantics.ups.NaiveCompiler

class Normalization(using tl: TL)(using Raise, Ctx, State) extends TermSynthesizer:
  import Normalization.*, Mode.*, FlatPattern.MatchMode
  import tl.*

  def reportUnreachableCase[T <: Located](unreachable: Located, subsumedBy: T, when: Bool = true): T =
    if when then warn(
      msg"this case is unreachable" -> unreachable.toLoc,
      msg"because it is subsumed by the branch" -> subsumedBy.toLoc)
    subsumedBy

  extension (these: Split)
    def markAsFallback: Split =
      these.isFallback = true
      these

    def clearFallback: Split =
      these.isFallback = false
      these

    def ++(those: Split): Split =
      if these.isFull then
        log("tail is discarded")
        these
      else (these match
        case Split.Cons(head, tail) => Split.Cons(head, tail ++ those)
        case Split.Let(name, term, tail) => Split.Let(name, term, tail ++ those)
        case Split.Else(_) /* impossible */ | Split.End => those)

  extension (lhs: FlatPattern.ClassLike)
    /** Generate a term that really resolves to the class at runtime. */
    def selectClass: FlatPattern.ClassLike =
      val constructor = lhs.constructor.symbol match
        case S(cls: ClassSymbol) => lhs.constructor
        case S(mem: BlockMemberSymbol) =>
          // If the class is declaration-only, we do not need to select the
          // class.
          if !mem.hasLiftedClass || mem.defn.exists(_.hasDeclareModifier.isDefined) then
            lhs.constructor
          else
            Term.SynthSel(lhs.constructor, Tree.Ident("class"))(mem.clsTree.orElse(mem.modOrObjTree).map(_.symbol), N).resolve
        case _ => lhs.constructor
      lhs.copy(constructor)(lhs.tree, lhs.output)
  
  extension (lhs: FlatPattern)
    /** Checks if two patterns are the same. */
    def =:=(rhs: FlatPattern): Bool = (lhs, rhs) match
      case (lhs: FlatPattern.ClassLike, rhs: FlatPattern.ClassLike) =>
        lhs.constructor.symbol === rhs.constructor.symbol
      case (FlatPattern.Lit(l1), FlatPattern.Lit(l2)) => l1 === l2
      case (FlatPattern.Tuple(n1, b1), FlatPattern.Tuple(n2, b2)) => n1 === n2 && b1 === b2
      case (FlatPattern.Record(ls1), FlatPattern.Record(ls2)) =>
        ls1.lazyZip(ls2).forall:
          case ((fieldName1, p1), (fieldName2, p2)) =>
            fieldName1 === fieldName2 && p1 === p2
      case (_: FlatPattern.ClassLike, _) | (_: FlatPattern.Lit, _) |
        (_: FlatPattern.Tuple, _) | (_: FlatPattern.Record, _) => false
    /** Checks if `lhs` can be subsumed under `rhs`. */
    def <:<(rhs: FlatPattern): Bool = compareCasePattern(lhs, rhs)
    /**
      * If two class-like patterns has different `refined` flag. Report the
      * inconsistency as a warning.
      */
    infix def reportInconsistentRefinedWith(rhs: FlatPattern): Unit = (lhs, rhs) match
      // case (Pattern.Class(n1, _, r1), Pattern.Class(n2, _, r2)) if r1 =/= r2 =>
      case (FlatPattern.ClassLike(c1, _, _, rfd1), FlatPattern.ClassLike(c2, _, _, rfd2)) if rfd1 =/= rfd2 =>
        def be(value: Bool): Str = if value then "is" else "is not"
        warn(
          msg"Found two inconsistently refined patterns:" -> rhs.toLoc,
          msg"one ${be(rfd1)} refined," -> c1.toLoc,
          msg"but the other ${be(rfd2)} refined." -> c2.toLoc)
      case (_, _) => ()
    /** If the pattern is a class-like pattern, override its `refined` flag. */
    def markAsRefined: Unit = lhs match
      case lhs: FlatPattern.ClassLike => lhs.refined = true
      case _ => ()
  
  extension (lhs: FlatPattern.Record)
    /** reduces the record pattern `lhs` assuming we have matched `rhs`.
      * It removes field matches that may now be unnecessary
      */
    infix def assuming(rhs: FlatPattern): FlatPattern.Record = rhs match
      case FlatPattern.Record(rhsEntries) =>
        val filteredEntries = lhs.entries.filter:
          (fieldName1, _) => rhsEntries.forall { (fieldName2, _) => !(fieldName1 === fieldName2)}
        FlatPattern.Record(filteredEntries)(lhs.output)
      case rhs: FlatPattern.ClassLike => rhs.constructor.symbol.flatMap(_.asCls) match
        case S(cls: ClassSymbol) => cls.defn match
          case S(ClassDef.Parameterized(params = paramList)) =>
            val filteredEntries = lhs.entries.filter:
              (fieldName1, _) => paramList.params.forall { (param:Param) => !(fieldName1 === param.sym.id)}
            FlatPattern.Record(filteredEntries)(lhs.output)
          case S(_) | N => lhs
        case S(_) | N => lhs
      case _ => lhs

  inline def apply(split: Split): Split = normalize(split)(using VarSet())
  
  /**
    * Normalize core abstract syntax to MLscript syntax.
    *
    * @param split the split to normalize
    * @return the normalized term
    */ 
  private def normalize(split: Split)(using vs: VarSet): Split = trace(
    pre = s"normalize <<< ${split.prettyPrint}",
    post = (res: Split) => "normalize >>> " + res.prettyPrint,
  ):
    normalizeImpl(split)
  
  /** Bind the current scrutinee to a flat pattern's output symbols. */
  def aliasOutputSymbols(scrutinee: => Term.Ref, outputSymbols: Ls[BlockLocalSymbol], split: Split): Split =
    outputSymbols.foldRight(split):
      // Can we use `Subst` to transform the inner split?
      case (symbol, innerSplit) => Split.Let(symbol, scrutinee, innerSplit)
  
  def normalizeImpl(split: Split)(using vs: VarSet): Split = split match
    case Split.Cons(Branch(scrutinee, pattern, consequent), alternative) => pattern match
      case pattern: (FlatPattern.Lit | FlatPattern.Tuple | FlatPattern.Record) =>
        log(s"MATCH: ${scrutinee.showDbg} is ${pattern.showDbg}")
        // TODO(ucs): deduplicate [1]
        val whenTrue = aliasOutputSymbols(scrutinee, pattern.output,
          normalize(specialize(consequent ++ alternative, +, scrutinee, pattern)))
        val whenFalse = normalizeImpl(specialize(alternative, -, scrutinee, pattern).clearFallback)
        Branch(scrutinee, pattern, whenTrue) ~: whenFalse
      case pattern @ FlatPattern.ClassLike(ctor, argsOpt, mode, _) =>
        log(s"MATCH: ${scrutinee.showDbg} is ${pattern.showDbg}")
        // Make sure that the pattern has correct arity and fields are accessible.
        ctor.symbol.map(_.asClsLike) match
          case N => // The constructor is not resolved. The error should have been reported.
            normalizeImpl(alternative)
          case S(N) =>
            // The constructor is not a class-like symbol. But it might be a
            // `VarSymbol` referencing to a pattern parameter.
            ctor.symbol match
              case S(symbol: VarSymbol) => symbol.decl match
                case S(param @ Param(flags = FldFlags(pat = true))) =>
                  if argsOpt.fold(false)(_.nonEmpty) then
                    error(msg"Pattern parameters cannot be applied." -> ctor.toLoc)
                  mode match
                    case MatchMode.Default =>
                      normalizeExtractorPatternParameter(scrutinee, ctor, pattern.output, consequent, alternative)
                    case sp: MatchMode.StringPrefix =>
                      log(s"symbol name is ${symbol.nme}")
                      normalizeStringPrefixPattern(scrutinee, ctor, N, sp, pattern.output, consequent, alternative)
                    case MatchMode.Annotated(annotation) =>
                      error(msg"Annotated pattern parameters are not supported here." -> annotation.toLoc)
                      normalizeImpl(alternative)
                case S(_) | N =>
                  error(msg"Cannot use this ${ctor.describe} as a pattern" -> ctor.toLoc)
                  normalizeImpl(alternative)
              case S(_) | N =>
                error(msg"Cannot use this ${ctor.describe} as a pattern" -> ctor.toLoc)
                normalizeImpl(alternative)
          case S(S(cls: (ClassSymbol | ModuleOrObjectSymbol))) if mode.isInstanceOf[MatchMode.StringPrefix] =>
            // Match classes and modules are disallowed in the string mode.
            normalizeImpl(alternative)
          case S(S(cls: ClassSymbol)) =>
            validateMatchMode(ctor, cls, mode)
            if validateClassPattern(ctor, cls, ensureArguments(argsOpt)) then // TODO(ucs): deduplicate [1]
              val whenTrue = aliasOutputSymbols(scrutinee, pattern.output,
                normalize(specialize(consequent ++ alternative, +, scrutinee, pattern)))
              val whenFalse = normalizeImpl(specialize(alternative, -, scrutinee, pattern).clearFallback)
              Branch(scrutinee, pattern.selectClass, whenTrue) ~: whenFalse
            else // If any errors were raised, we skip the branch.
              log("BROKEN"); normalizeImpl(alternative)
          case S(S(mod: ModuleOrObjectSymbol)) =>
            validateMatchMode(ctor, mod, mode)
            if validateObjectPattern(pattern, mod, argsOpt) then // TODO(ucs): deduplicate [1]
              val whenTrue = aliasOutputSymbols(scrutinee, pattern.output,
                normalize(specialize(consequent ++ alternative, +, scrutinee, pattern)))
              val whenFalse = normalizeImpl(specialize(alternative, -, scrutinee, pattern).clearFallback)
              Branch(scrutinee, pattern.selectClass, whenTrue) ~: whenFalse
            else // If any errors were raised, we skip the branch.
              log("BROKEN"); normalizeImpl(alternative)
          case S(S(pat: PatternSymbol)) => mode match
            // Note: `argsOpt` is supposed to be used in following cases, but
            // the current implementation does not use it. The future version
            // should properly handle the pattern arguments.
            case MatchMode.Default =>
              normalizeExtractorPattern(scrutinee, pat, ctor, argsOpt, pattern.output, consequent, normalizeImpl(alternative))
            case sp: MatchMode.StringPrefix =>
              normalizeStringPrefixPattern(scrutinee, ctor, argsOpt, sp, pattern.output, consequent, normalizeImpl(alternative))
            case MatchMode.Annotated(annotation) => annotation.symbol match
              case S(symbol) if symbol === ctx.builtins.annotations.compile =>
                normalizeCompiledPattern(scrutinee, pat, ctor, argsOpt, pattern.output, consequent, normalizeImpl(alternative))
              case S(_) =>
                warn(msg"This annotation is not supported here." -> annotation.toLoc,
                  msg"Note: Patterns (like `${pat.nme}`) only support the `@compile` annotation." -> N)
                normalizeExtractorPattern(scrutinee, pat, ctor, argsOpt, pattern.output,consequent, normalizeImpl(alternative))
              case N =>
                // Name resolution should have already reported an error. We
                // treat this as an extractor pattern.
                normalizeExtractorPattern(scrutinee, pat, ctor, argsOpt, pattern.output, consequent, normalizeImpl(alternative))
    case Split.Let(v, _, tail) if vs has v =>
      log(s"LET: SKIP already declared scrutinee $v")
      normalizeImpl(tail)
    case Split.Let(v, rhs, tail) =>
      log(s"LET: $v")
      Split.Let(v, rhs, normalizeImpl(tail)(using vs + v))
    case Split.Else(default) =>
      log(s"DFLT: ${default.showDbg}")
      Split.Else(default)
    case Split.End => Split.End
  
  /** Check whether the number of parameters in class-like patterns matches the
   *  number in their definition, and whether each parameter is accessible.
   */
  private def validateClassPattern(
      ctorTerm: Term,
      ctorSymbol: ClassSymbol,
      argsOpt: Opt[Ls[FlatPattern.Argument.Term]]
  ): Bool =
    // Obtain the `classHead` used for error reporting and the parameter list
    // from the class definitions.
    val (classHead, paramsOpt) = ctorSymbol.defn match
      case N => lastWords(s"Class ${ctorSymbol.name} does not have a definition")
      // Use the constructor pattern's location for error reporting.
      case S(cd) => new Tree.Ident(ctorSymbol.name).withLoc(ctorTerm.toLoc) -> cd.paramsOpt
    paramsOpt match
      case S(paramList) => argsOpt match
        case S(args) =>
          // Check the number of parameters is correct.
          if args.size != paramList.params.size then
            val loc = Loc(args) orElse ctorTerm.toLoc
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
            case (_, Argument.Term(_, Tree.Under())) => true
            case (Param(flags, sym, _, _), arg) if !flags.isVal =>
              error(msg"This pattern cannot be matched" -> arg.toLoc, // TODO: use correct location
                msg"because the corresponding parameter `${sym.name}` is not publicly accessible" -> sym.toLoc,
                msg"Suggestion: use a wildcard pattern `_` in this position" -> N,
                msg"Suggestion: mark this parameter with `val` so it becomes accessible" -> N)
              false
            case _ => true
          // If patterns are more than parameters, or one of parameters is
          // incessible, we cannot make the branch.
          .foldLeft(args.size <= paramList.params.size)(_ && _)
        case N => argsOpt match
          case S(args) =>
            error(msg"class ${ctorSymbol.name} does not have parameters" -> classHead.toLoc,
              msg"but the pattern has ${"sub-pattern" countBy args.size}" -> Loc(args))
            false
          case N => true // No parameters, no arguments. This is fine.
      case N =>
        // The class doesn't have parameters. Check if scruts are empty.
        argsOpt match
          case S(Nil) =>
            error(msg"Class ${ctorSymbol.name} does not have a parameter list" -> ctorTerm.toLoc)
            true
          case S(args) =>
            error(msg"Class ${ctorSymbol.name} does not have a parameter list" -> ctorTerm.toLoc,
              msg"but the pattern has ${"sub-pattern" countBy args.size}" -> Loc(args))
            false
          case N => true
  
  /** Check whether the object pattern has an argument list. */
  private def validateObjectPattern(pattern: FlatPattern.ClassLike, mod: ModuleOrObjectSymbol, argsOpt: Opt[Ls[FlatPattern.Argument]]): Bool = argsOpt match
    case S(Nil) =>
      // This means the pattern has an unnecessary parameter list.
      error(msg"`${mod.name}` is an object." -> mod.id.toLoc,
        msg"Its pattern cannot have an argument list." -> pattern.tree.toLoc)
      true
    case S(_ :: _) =>
      // This means the pattern is an object with parameters.
      error(msg"`${mod.name}` is an object." -> mod.id.toLoc,
        msg"Its pattern cannot have arguments." -> pattern.tree.toLoc)
      false
    case N => true
  
  /** Ensure that there are no pattern arguments. */
  private def ensureArguments(
      arguments: Opt[Ls[FlatPattern.Argument]]
  ): Opt[Ls[FlatPattern.Argument.Term]] = arguments.map:
    _.flatMap:
      case arg: FlatPattern.Argument.Term => S(arg)
      case FlatPattern.Argument.Pattern(_, pattern) =>
        error(msg"This ${pattern.describe} pattern cannot be used as an argument here." -> pattern.toLoc); N
  
  /** Warn about inappropriate annotations used on class or object patterns. */
  private def validateMatchMode(
      ctorTerm: Term,
      ctorSymbol: ClassSymbol | ModuleOrObjectSymbol,
      mode: MatchMode
  ): Unit = mode match
    case MatchMode.Default | _: MatchMode.StringPrefix => ()
    case MatchMode.Annotated(annotation) => annotation.symbol match
      case S(symbol) if symbol === ctx.builtins.annotations.compile =>
        warn(msg"`@compile` cannot be used on ${ctorSymbol.tree.k.desc} instance patterns." -> annotation.toLoc,
          msg"Note: The `@compile` annotation is for compiling pattern definitions." -> N)
      case S(_) =>
        warn(msg"This annotation is not supported on ${ctorSymbol.tree.k.desc} instance patterns." -> annotation.toLoc)
      case N => () // `Resolver` should have already reported an error.
  
  /** This function normalizes a pattern that resolves to a pattern parameter.
   *  We might be able to merge this function with `normalizeExtractorPattern`.
   *  The difference is that we don't have a way to check the arity of the 
   *  referenced pattern argument. */
  private def normalizeExtractorPatternParameter(
      scrutinee: Term.Ref,
      ctorTerm: Term,
      outputSymbols: Ls[BlockLocalSymbol],
      consequent: Split,
      alternative: Split,
  )(using VarSet): Split =
    val call = app(sel(ctorTerm, "unapply").resolve, tup(fld(scrutinee)), s"result of unapply")
    val split = tempLet("patternParamMatchResult", call): resultSymbol =>
      if outputSymbols.isEmpty then
        // No need to destruct the result.
        Branch(resultSymbol.safeRef, matchResultPattern(N), consequent) ~: alternative
      else
        val outputSymbol = TempSymbol(N, "output")
        val bindingsSymbol = TempSymbol(N, "bindings") // TODO: This is useless.
        Branch(resultSymbol.safeRef, matchResultPattern(S(outputSymbol :: bindingsSymbol :: Nil)),
          aliasOutputSymbols(outputSymbol.safeRef, outputSymbols, consequent)
        ) ~: alternative
    normalize(split)
  
  /** Create a split that binds the pattern arguments. */
  def buildPatternArguments(
      patternArguments: List[(BlockLocalSymbol, Pattern)],
      split: Split
  ): Split =
    val compiler = new NaiveCompiler
    patternArguments.foldRight(split):
      case ((symbol, pattern), innerSplit) =>
        scoped("ucs:translation"):
          log(s"build anonymous pattern: ${pattern.showDbg} for symbol ${symbol.nme}")
        val record = compiler.compileAnonymousPattern(Nil, Nil, pattern)
        Split.Let(symbol, record, innerSplit)
  
  /** Normalize splits whose leading branch matches a pattern and does not have
   *  a `@compile` annotation. */
  private def normalizeExtractorPattern(
      scrutinee: Term.Ref,
      patternSymbol: PatternSymbol,
      ctorTerm: Term,
      allArgsOpt: Opt[Ls[FlatPattern.Argument]],
      outputSymbols: Ls[BlockLocalSymbol],
      consequent: Split,
      alternative: Split,
  )(using VarSet): Split =
    scoped("ucs:np"):
      log:
        allArgsOpt.fold(Iterator.empty[Str]):
          _.iterator.map:
            case Argument.Term(scrutinee, _) => s"extraction: ${scrutinee.nme}"
            case Argument.Pattern(scrutinee, pattern) => s"pattern: ${scrutinee.nme} = ${pattern.showDbg}"
        .mkString("extractor pattern arguments:\n", "\n", "")
    val defn = patternSymbol.defn.getOrElse:
      lastWords(s"Pattern `${patternSymbol.nme}` has not been elaborated.")
    // Partition the arguments into pattern arguments and bindings.
    val (extractionArgsOpt, patternArguments) = allArgsOpt.fold((N: Opt[Ls[BlockLocalSymbol]], Nil)): args =>
      val (extractionArgs, patternArgs) = args.partitionMap:
        case Argument.Term(scrutinee, _) => Left(scrutinee)
        case Argument.Pattern(scrutinee, pattern) => Right((scrutinee, pattern))
      (if extractionArgs.isEmpty then N else S(extractionArgs), patternArgs)
    // Place pattern arguments first, then the scrutinee.
    val unapplyArgs = patternArguments.map(_._1.safeRef |> fld) :+ fld(scrutinee)
    val unapplyCall = app(sel(ctorTerm, "unapply").resolve, tup(unapplyArgs*), s"result of unapply")
    val split = buildPatternArguments(patternArguments, tempLet("matchResult", unapplyCall): resultSymbol =>
      extractionArgsOpt match
        case N =>
          if outputSymbols.isEmpty then
            // No need to destruct the result.
            Branch(resultSymbol.safeRef, matchResultPattern(N), consequent) ~: alternative
          else
            val extractionSymbol = TempSymbol(N, "output")
            val bindingsSymbol = TempSymbol(N, "bindings") // TODO: This is useless.
            Branch(resultSymbol.safeRef, matchResultPattern(S(extractionSymbol :: bindingsSymbol :: Nil)),
              aliasOutputSymbols(extractionSymbol.safeRef, outputSymbols, consequent)
            ) ~: alternative
        case S(extractionArgs) =>
          val extractionParams = defn.extractionParams
          // TODO: Check if the number of arguments is correct.
          // Note that if the pattern definition doesn't have any extraction
          // parameters, we still allow there to be a single argument, which
          // represents the entire output.
          val extractionSymbol = TempSymbol(N, "tuple")
          val bindingsSymbol = TempSymbol(N, "bindings") // TODO: This is useless.
          if extractionArgs.size === extractionParams.size then
            log(s"number of arguments is correct")
            // If the number of arguments is the same as the number of extraction
            // parameters, we destruct the `MatchResult`'s argument as a tuple
            // with length equal to the number of extraction parameters.
            // 
            // For example, with pattern `pattern Foo(x, y, z) = ...`, we are
            // allowed to do `if input is Foo(x, y, z) then ...`.
            Branch(resultSymbol.safeRef, matchResultPattern(S(extractionSymbol :: bindingsSymbol :: Nil)),
              aliasOutputSymbols(extractionSymbol.safeRef, outputSymbols,
                makeTupleBranch(extractionSymbol.safeRef, extractionArgs, consequent, Split.End))
            ) ~: alternative
          else extractionArgs match
            case arg :: Nil if extractionParams.isEmpty =>
              log(s"only one argument and no extraction params")
              // If the pattern definition doesn't have any extraction parameters,
              // we allow there to be a single argument, which represents the
              // entire output of the pattern.
              // 
              // For example, with pattern `pattern Foo = ...`, we are allowed to
              // do `if input is Foo(output) then ...`, which is equivalent to
              // `if input is Foo as output then ...`.
              Branch(resultSymbol.safeRef, matchResultPattern(S(extractionSymbol :: bindingsSymbol :: Nil)),
                aliasOutputSymbols(extractionSymbol.safeRef, outputSymbols,
                  Split.Let(arg, extractionSymbol.safeRef, consequent))
              ) ~: alternative
            case _ =>
              log(s"number of arguments is incorrect")
              // Otherwise, the number of arguments is incorrect.
              error(msg"Expected ${"argument" countBy extractionParams.size
              }, but found ${if extractionArgs.size < extractionParams.size then "only " else ""
              }${"argument" countBy extractionArgs.size}." -> Loc(extractionArgs))
              // TODO: Improve the error message by checking the pattern definition
              // and demonstrating how to correctly write the pattern.
              normalizeImpl(alternative))
    normalize(split)
  
  private def normalizeStringPrefixPattern(
      scrutinee: Term.Ref,
      ctorTerm: Term,
      allArgsOpt: Opt[Ls[FlatPattern.Argument]],
      stringPrefix: MatchMode.StringPrefix,
      outputSymbols: Ls[BlockLocalSymbol],
      consequent: Split,
      alternative: Split,
  )(using VarSet): Split = trace(
    pre = s"normalizeStringPrefixPattern <<< ${ctorTerm.showDbg}",
    post = (r: Split) => s"normalizeStringPrefixPattern >>> ${r.prettyPrint}"
  ):
    val patternArguments = allArgsOpt.fold(Nil)(_.collect:
      case Argument.Pattern(symbol, pattern) => symbol -> pattern)
    val call =
      val method = "unapplyStringPrefix"
      val args = tup(patternArguments.map(_._1.safeRef) :+ scrutinee)
      app(sel(ctorTerm, method), args, s"result of $method")
    val split = tempLet("matchResult", call): resultSymbol =>
      // let `matchResult` be the return value
      val outputSymbol = TempSymbol(N, "arg")
      val bindingsSymbol = TempSymbol(N, "bindings")
      Branch(
        resultSymbol.safeRef,
        matchResultPattern(S(outputSymbol :: bindingsSymbol :: Nil)),
        aliasOutputSymbols(resultSymbol.safeRef, outputSymbols,
          // Bind the `remaining` variable to the second element of the output
          // of `matchResult`.
          Split.Let(stringPrefix.prefix, callTupleGet(outputSymbol.safeRef, 0, "prefix"),
            Split.Let(stringPrefix.postfix, callTupleGet(outputSymbol.safeRef, 1, "postfix"), consequent)))
      ) ~: alternative
    normalize(buildPatternArguments(patternArguments, split))
  
  // Note: This function will be overhauled in the new pattern compilation scheme.
  private def normalizeCompiledPattern(
      scrutinee: Term.Ref,
      symbol: PatternSymbol,
      ctorTerm: Term,
      argsOpt: Opt[Ls[FlatPattern.Argument]],
      outputSymbols: Ls[BlockLocalSymbol],
      consequent: Split,
      alternative: Split,
  )(using VarSet): Split = scoped("ucs:rp"):
    import ups.*
    
    // Instantiate the pattern and all patterns used in it.
    val instantiator = new Instantiator
    val patternArguments = argsOpt.fold(Nil)(_.collect:
      case Argument.Pattern(_, pattern) => pattern)
    val (synonym, context) = instantiator(symbol, patternArguments, Loc(ctorTerm :: patternArguments))
    // Initate the compilation.
    val compiler = new Compiler(using context)
    val ((matcherSymbol, fieldName), implementations) = compiler.buildMatcher(synonym)
    val innermostSplit =
      // 1. Bind the call result to a variable.
      val recordSymbol = TempSymbol(N, "matchRecord")
      val recordTerm = app(matcherSymbol.safeRef, tup(fld(scrutinee)), "result of matcher function")
      val f1 = Split.Let(recordSymbol, recordTerm, _)
      // 2. Select the selection field to the result.
      val matchResultSymbol = TempSymbol(N, "matchResult")
      val matchResultTerm = sel(recordSymbol.safeRef, fieldName)
      val f2 = Split.Let(matchResultSymbol, matchResultTerm, _)
      // 3. Check if the field value is a `MatchResult` and bind the output.
      val outputSymbol = TempSymbol(N, "patternOutput")
      val bindingsSymbol = TempSymbol(N, "bindings") // TODO: This is useless.
      val branch = Branch(matchResultSymbol.safeRef, matchResultPattern(S(outputSymbol :: bindingsSymbol :: Nil)),
        aliasOutputSymbols(outputSymbol.safeRef, outputSymbols, consequent))
      f1(f2(branch ~: alternative))
    implementations.iterator.foldRight(innermostSplit):
      case ((symbol, paramList, term), innerSplit) =>
        Split.Let(symbol, Term.Lam(paramList, term), innerSplit)

  /**
    * Specialize `split` with the assumption that `scrutinee` matches `pattern`.
    * If `mode` is `+`, the function _keeps_ branches that agree on
    * `scrutinee` matching `pattern` and simplifies the record patterns it sees if the fields were already matched.
    * Otherwise (if `mode` is `-`), the function _removes_ branches
    * that agree on `scrutinee` matches `pattern`.
    */
  private def specialize(
      split: Split,
      mode: Mode,
      scrutinee: Term.Ref,
      pattern: FlatPattern
  )(using VarSet): Split = trace(
    pre = s"S$mode <<< ${scrutinee.showDbg} is ${pattern.showDbg} : ${split.prettyPrint}",
    post = (r: Split) => s"S$mode >>> ${r.prettyPrint}"
  ):
    def rec(split: Split)(using mode: Mode, vs: VarSet): Split = split match
      case Split.End => log("CASE Nil"); split
      case Split.Else(_) => log("CASE Else"); split
      case split @ Split.Let(sym, _, tail) =>
        log(s"CASE Let ${sym}")
        split.copy(tail = rec(tail))
      case split @ Split.Cons(head @ Branch(thatScrutinee, thatPattern, continuation), tail) =>
        log(s"CASE Cons ${head.showDbg}")
        if scrutinee === thatScrutinee then mode match
          case + =>
            log(s"Case 1.1: $scrutinee === $thatScrutinee")
            if thatPattern =:= pattern then
              log(s"Case 1.1.1: $pattern =:= $thatPattern")
              thatPattern reportInconsistentRefinedWith pattern
              aliasBindings(pattern, thatPattern)(rec(continuation) ++ rec(tail))
            else if thatPattern <:< pattern then
              log(s"Case 1.1.2: $pattern <:< $thatPattern")
              pattern.markAsRefined; split
            else if split.isFallback then
              log(s"Case 1.1.3: $pattern is unrelated with $thatPattern")
              rec(tail)
            else thatPattern match
            case thatPattern: FlatPattern.Record =>
              log(s"Case 1.1.4: $thatPattern is a record")
              // we can use information if pattern is itself a record, or if it is a constructor with arguments
              val simplifiedRecord = thatPattern assuming pattern
              if simplifiedRecord.entries.isEmpty then
                tail
              else
                Split.Cons(Branch(thatScrutinee, simplifiedRecord, continuation), tail)
            case _ =>
              if pattern <:< thatPattern then
                // TODO: the warning will be useful when we have inheritance information
                // raiseDesugaringWarning(
                //   msg"the pattern always matches" -> thatPattern.toLoc,
                //   msg"the scrutinee was matched against ${pattern.toString}" -> pattern.toLoc,
                //   msg"which is a subtype of ${thatPattern.toString}" -> (pattern match {
                //     case Pattern.Class(cls, _, _) => cls.toLoc
                //     case _ => thatPattern.toLoc
                //   }))
                log(s"case 1.1.5: $pattern <:< $thatPattern")
                split
              else
                // TODO: the warning will be useful when we have inheritance information
                // raiseDesugaringWarning(
                //   msg"possibly conflicting patterns for this scrutinee" -> scrutinee.toLoc,
                //   msg"the scrutinee was matched against ${pattern.toString}" -> pattern.toLoc,
                //   msg"which is unrelated with ${thatPattern.toString}" -> thatPattern.toLoc)
                log(s"Case 1.1._ else : ${tail}")
                rec(tail)
          case - =>
            log(s"Case 1.2: $scrutinee === $thatScrutinee")
            thatPattern reportInconsistentRefinedWith pattern
            if thatPattern =:= pattern || thatPattern <:< pattern then
              log(s"Case 1.2.1: $pattern =:= (or <:<) $thatPattern")
              rec(tail)
            else
              log(s"Case 1.2.2: $pattern are unrelated to $thatPattern")
              split.copy(tail = rec(tail))
        else
          log(s"Case 2: $scrutinee =/= $thatScrutinee")
          head.copy(continuation = rec(continuation)) ~: rec(tail)
    end rec
    rec(split)(using mode, summon)
  
  private def aliasBindings(p: FlatPattern, q: FlatPattern): Split => Split = (p, q) match
    case (FlatPattern.ClassLike(_, S(ss1), _, _), FlatPattern.ClassLike(_, S(ss2), _, _)) =>
      ss1.iterator.zip(ss2.iterator).foldLeft(identity[Split]):
        case (acc, (l, r)) if l.scrutinee === r.scrutinee => acc
        case (acc, (l, r)) => innermost => Split.Let(r.scrutinee, l.scrutinee.safeRef, acc(innermost))
    case (_, _) => identity
end Normalization

object Normalization:
  /**
    * Hard-coded subtyping relations used in normalization and coverage checking.
    * TODO use base classes and also handle modules
    */
  def compareCasePattern(lhs: FlatPattern, rhs: FlatPattern)(using ctx: Elaborator.Ctx): Bool =
    import FlatPattern.*, ctx.builtins as blt
    (lhs, rhs) match
    // `Object` is the supertype of all (non-virtual) classes and modules.
    case (Class(cs: ClassSymbol), Class(blt.`Object`))
        if !ctx.builtins.virtualClasses.contains(cs) => true
    // Class and module are subtypes of `Object`.
    case (Module(_), Class(blt.`Object`)) => true
    case (Tuple(n1, false), Tuple(n2, false)) if n1 === n2 => true
    case (Tuple(n1, _), Tuple(n2, true)) if n2 <= n1 => true
    case (Class(blt.`Int`), Class(blt.`Num`)) => true
    // case (s1: ClassSymbol, s2: ClassSymbol) => s1 <:< s2 // TODO: find a way to check inheritance
    case (Lit(Tree.IntLit(_)), Class(blt.`Int` | blt.`Num`)) => true
    case (Lit(Tree.StrLit(_)), Class(blt.`Str`)) => true
    case (Lit(Tree.DecLit(_)), Class(blt.`Num`)) => true
    case (Lit(Tree.BoolLit(_)), Class(blt.`Bool`)) => true
    case (Record(entries1), Record(entries2)) =>
      entries1.forall { (fieldName1, _) => entries2.exists { (fieldName2, _) => fieldName1 === fieldName2 } }
    case (Record(entries), rhs: ClassLike) =>
      val clsParams = rhs.constructor.symbol.flatMap(_.asCls) match
        case S(symbol) => symbol.defn match
          case S(ClassDef.Parameterized(params = paramList)) => paramList.params
          case S(_) | N => Nil
        case (S(_) | N) => Nil
      entries.forall { (fieldName, _) => clsParams.exists {
        case Param(flags = FldFlags(isVal = isVal), sym = sym) => isVal && fieldName === sym.id
      }}
    case (_: FlatPattern, _: FlatPattern)  => false

  final case class VarSet(declared: Set[BlockLocalSymbol]):
    def +(nme: BlockLocalSymbol): VarSet = copy(declared + nme)
    infix def has(nme: BlockLocalSymbol): Bool = declared.contains(nme)
    def showDbg: Str = declared.iterator.mkString("{", ", ", "}")

  object VarSet:
    def apply(): VarSet = VarSet(Set())

  /** Specialization mode */
  enum Mode:
    case +
    case -
