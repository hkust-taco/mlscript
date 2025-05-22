package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.{Literal, Tree}, utils.TraceLogger
import Message.MessageContext
import Elaborator.{Ctx, State, ctx}
import utils.*

class Normalization(using tl: TL)(using Raise, Ctx, State) extends DesugaringBase:
  import Normalization.*, Mode.*, Pattern.MatchMode
  import tl.*

  def raiseDesugaringError(msgs: (Message -> Opt[Loc])*): Unit =
    raise(ErrorReport(msgs.toList, source = Diagnostic.Source.Typing))

  def raiseDesugaringWarning(msgs: (Message -> Opt[Loc])*): Unit =
    raise(WarningReport(msgs.toList, source = Diagnostic.Source.Typing))

  def reportUnreachableCase[T <: Located](unreachable: Located, subsumedBy: T, when: Bool = true): T =
    if when then raiseDesugaringWarning(
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

  extension (lhs: Pattern)
    /** Generate a term that really resolves to the class at runtime. */
    def selectClass: Pattern = lhs match
      case lhs: Pattern.ClassLike =>
        val constructor = lhs.constructor.symbol match
          case S(cls: ClassSymbol) => lhs.constructor
          case S(mem: BlockMemberSymbol) =>
            // If the class is declaration-only, we do not need to select the
            // class.
            if !mem.hasLiftedClass || mem.defn.exists(_.isDeclare.isDefined) then
              lhs.constructor
            else
              Term.SynthSel(lhs.constructor, Tree.Ident("class"))(mem.clsTree.orElse(mem.modOrObjTree).map(_.symbol)).withIArgs(Nil)
          case _ => lhs.constructor
        lhs.copy(constructor)(lhs.tree)
      case _: (Pattern.Lit | Pattern.Tuple | Pattern.Record) => lhs
     
    /** Checks if two patterns are the same. */
    def =:=(rhs: Pattern): Bool = (lhs, rhs) match
      case (lhs: Pattern.ClassLike, rhs: Pattern.ClassLike) =>
        lhs.constructor.symbol === rhs.constructor.symbol
      case (Pattern.Lit(l1), Pattern.Lit(l2)) => l1 === l2
      case (Pattern.Tuple(n1, b1), Pattern.Tuple(n2, b2)) => n1 === n2 && b1 === b2
      case (_, _) => false
    /** Checks if `lhs` can be subsumed under `rhs`. */
    def <:<(rhs: Pattern): Bool = compareCasePattern(lhs, rhs)
    /**
      * If two class-like patterns has different `refined` flag. Report the
      * inconsistency as a warning.
      */
    infix def reportInconsistentRefinedWith(rhs: Pattern): Unit = (lhs, rhs) match
      // case (Pattern.Class(n1, _, r1), Pattern.Class(n2, _, r2)) if r1 =/= r2 =>
      case (Pattern.ClassLike(c1, _, _, rfd1), Pattern.ClassLike(c2, _, _, rfd2)) if rfd1 =/= rfd2 =>
        def be(value: Bool): Str = if value then "is" else "is not"
        val sym1 = c1.symbol.get // TODO(ucs)
        val sym2 = c2.symbol.get // TODO(ucs)
        raiseDesugaringWarning(
          msg"inconsistent refined pattern" -> rhs.toLoc,
          msg"pattern `${sym1.nme}` ${be(rfd1)} refined" -> sym1.toLoc,
          msg"but pattern `${sym2.nme}` ${be(rfd2)} refined" -> sym2.toLoc)
      case (_, _) => ()
    /** If the pattern is a class-like pattern, override its `refined` flag. */
    def markAsRefined: Unit = lhs match
      case lhs: Pattern.ClassLike => lhs.refined = true
      case _ => ()
  
  inline def apply(split: Split): Split = normalize(split)(using VarSet())
  
  /**
    * Normalize core abstract syntax to MLscript syntax.
    *
    * @param split the split to normalize
    * @return the normalized term
    */ 
  private def normalize(split: Split)(using vs: VarSet): Split = trace(
    pre = s"normalize <<< ${Split.display(split)}",
    post = (res: Split) => "normalize >>> " + Split.display(res),
  ):
    normalizeImpl(split)
  
  def normalizeImpl(split: Split)(using vs: VarSet): Split = split match
    case Split.Cons(Branch(scrutinee, pattern, consequent), alternative) => pattern match
      case pattern: (Pattern.Lit | Pattern.Tuple) =>
        log(s"MATCH: ${scrutinee.showDbg} is ${pattern.showDbg}")
        // TODO(ucs): deduplicate [1]
        val whenTrue = normalize(specialize(consequent ++ alternative, +, scrutinee, pattern))
        val whenFalse = normalizeImpl(specialize(alternative, -, scrutinee, pattern).clearFallback)
        Branch(scrutinee, pattern.selectClass, whenTrue) ~: whenFalse
      case Pattern.ClassLike(ctor, argsOpt, mode, _) =>
        log(s"MATCH: ${scrutinee.showDbg} is ${pattern.showDbg}")
        // Make sure that the pattern has correct arity and fields are accessible.
        ctor.symbol.flatMap(_.asClsLike) match
          case N =>
            // The constructor is not resolved. Report the error and skip the branch.
            error(msg"Cannot use this ${ctor.describe} as a pattern" -> ctor.toLoc)
            log("BROKEN"); normalizeImpl(alternative)
          case S(cls: (ClassSymbol | ModuleSymbol)) if mode.isInstanceOf[MatchMode.StringPrefix] =>
            // Match classes and modules are disallowed in the string mode.
            log("incompatible"); normalizeImpl(alternative)
          case S(cls: ClassSymbol) =>
            // Error messages should use the location from `classHead`.
            val (classHead, paramsOpt) =
              // Unfortunately, class symbols of `MatchResult` and `MatchFailure`
              // are coined in the elaborator state, so it does not have `defn`.
              // TODO(ucs): do not make special case for them
              if cls == State.matchResultClsSymbol then
                (cls.id: Located) -> matchResultClassParamOpt
              else if cls == State.matchFailureClsSymbol then
                (cls.id: Located) -> matchFailureClassParamOpt
              else
                cls.defn match
                  case N => lastWords(s"Class ${cls.name} does not have a definition")
                  case S(cd) => cls.id -> cd.paramsOpt
            validateMatchMode(ctor, cls, mode)
            val broken: Bool = paramsOpt match
              case S(paramList) => argsOpt match
                case S(args) =>
                  // Check the number of parameters is correct.
                  val n = args.size.toString
                  val m = paramList.params.size.toString
                  if n != m then
                    val argsLoc = Loc(args.iterator.map(_.pattern))
                    error:
                      if paramList.params.isEmpty then
                        msg"the constructor does not take any arguments but found $n" -> argsLoc
                      else
                        msg"mismatched arity: expect $m, found $n" -> argsLoc
                  // Check the fields are accessible.
                  paramList.params.iterator.zip(args).map:
                    case (_, (_, Tree.Under(), _)) => false
                    case (Param(flags, sym, _, _), arg) if !flags.value =>
                      error(msg"This pattern cannot be matched" -> arg.pattern.toLoc, // TODO: use correct location
                        msg"because the corresponding parameter `${sym.name}` is not publicly accessible" -> sym.toLoc,
                        msg"Suggestion: use a wildcard pattern `_` in this position" -> N,
                        msg"Suggestion: mark this parameter with `val` so it becomes accessible" -> N)
                      true
                    case _ => false
                  // If patterns are more than parameters, or one of parameters
                  // is incessible we cannot make the branch.
                  .foldLeft(n > m)(_ || _)
                case N => argsOpt match
                  case S(args) =>
                    error(msg"class ${cls.name} does not have parameters" -> classHead.toLoc,
                      msg"but the pattern has ${"sub-pattern".pluralize(args.size, true, false)}" -> Loc(args.iterator.map(_.pattern)))
                    true
                  case N => false // No parameters, no arguments. This is fine.
              case N =>
                // The class doesn't have parameters. Check if scruts are empty.
                argsOpt match
                  case S(Nil) =>
                    error(msg"Class ${cls.name} does not have a parameter list" -> ctor.toLoc)
                    false
                  case S(args) =>
                    error(msg"Class ${cls.name} does not have a parameter list" -> ctor.toLoc,
                      msg"but the pattern has ${"sub-pattern".pluralize(args.size, true, false)}" -> Loc(args.iterator.map(_.pattern)))
                    true
                  case N => false
            // end match
            if broken then
              // If `broken` is true, we skip the branch and continue to the next.
              log("BROKEN")
              normalizeImpl(alternative)
            else
              // TODO(ucs): deduplicate [1]
              val whenTrue = normalize(specialize(consequent ++ alternative, +, scrutinee, pattern))
              val whenFalse = normalizeImpl(specialize(alternative, -, scrutinee, pattern).clearFallback)
              Branch(scrutinee, pattern.selectClass, whenTrue) ~: whenFalse
          case S(mod: ModuleSymbol) =>
            validateMatchMode(ctor, mod, mode)
            val broken = argsOpt match
              case S(args) =>
                // This means the pattern is an application of a module.
                error(msg"the constructor ${ctor.showDbg} is a module" -> ctor.toLoc,
                  msg"but the pattern has scrutinees" -> pattern.toLoc)
                false
              case N => false
            if broken then
              // If `broken` is true, we skip the branch and continue to the next.
              log("BROKEN")
              normalizeImpl(alternative)
            else
              // TODO(ucs): deduplicate [1]
              val whenTrue = normalize(specialize(consequent ++ alternative, +, scrutinee, pattern))
              val whenFalse = normalizeImpl(specialize(alternative, -, scrutinee, pattern).clearFallback)
              Branch(scrutinee, pattern.selectClass, whenTrue) ~: whenFalse
          case S(pat: PatternSymbol) => mode match
            // Note: `argsOpt` is supposed to be used in following cases, but
            // the current implementation does not use it. The future version
            // should properly handle the pattern arguments.
            case MatchMode.Default =>
              normalizeExtractorPattern(scrutinee, pat, ctor, consequent, alternative)
            case MatchMode.StringPrefix(prefix, postfix) =>
              normalizeStringPrefixPattern(scrutinee, pat, ctor, postfix, consequent, alternative)
            case MatchMode.Annotated(annotation) => annotation.symbol.flatMap(_.asObj) match
              case S(symbol) if symbol === ctx.builtins.compile =>
                normalizeCompiledPattern(scrutinee, pat, ctor, argsOpt, mode, consequent, alternative)
              case S(_) =>
                warn(msg"Unknown annotation on pattern" -> annotation.toLoc,
                  msg"Note: only `@compile` is supported." -> N)
                normalizeExtractorPattern(scrutinee, pat, ctor, consequent, alternative)
              case N =>
                // Name resolution should have already reported an error. We
                // treat this as an extractor pattern.
                normalizeExtractorPattern(scrutinee, pat, ctor, consequent, alternative)
      case _ =>
          raiseDesugaringError(msg"unsupported pattern matching: ${scrutinee.toString} is ${pattern.toString}" -> pattern.toLoc)
          Split.default(Term.Error)
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
  
  private def validateMatchMode(ctorTerm: Term, ctorSymbol: ClassSymbol | ModuleSymbol, mode: MatchMode): Unit = mode match
    case MatchMode.Default | _: MatchMode.StringPrefix => ()
    case MatchMode.Annotated(annotation) => annotation.symbol.flatMap(_.asObj) match
      case S(symbol) if symbol === ctx.builtins.compile =>
        warn(msg"Cannot compile `${ctorSymbol.name}`," -> Loc(annotation :: ctorTerm :: Nil),
          msg"because it is a ${ctorSymbol.tree.k.desc}." -> ctorSymbol.toLoc,
          msg"Note: only patterns can be compiled." -> N)
      case S(_) =>
        warn(msg"Unknown annotation on pattern" -> annotation.toLoc,
        msg"Note: only `@compile` is supported on patterns." -> N)
      // Name resolution should have already reported an error.
      case N => ()
  
  private def normalizeExtractorPattern(
      scrutinee: Term.Ref,
      patternSymbol: PatternSymbol,
      ctorTerm: Term,
      consequent: Split,
      alternative: Split,
  )(using VarSet): Split =
    normalize(makeUnapplyBranch(scrutinee, ctorTerm, consequent)(alternative))
  
  private def normalizeStringPrefixPattern(
      scrutinee: Term.Ref,
      patternSymbol: PatternSymbol,
      ctorTerm: Term,
      postfixSymbol: TempSymbol,
      consequent: Split,
      alternative: Split,
  )(using VarSet): Split =
    normalize(makeUnapplyStringPrefixBranch_NEW(scrutinee, ctorTerm, postfixSymbol, consequent)(alternative))
  
  private def normalizeCompiledPattern(
      scrutinee: Term.Ref,
      symbol: PatternSymbol,
      ctorTerm: Term,
      argsOpt: Opt[Ls[(scrutinee : BlockLocalSymbol, pattern : Tree, split : Opt[DeBrujinSplit])]],
      mode: MatchMode,
      consequent: Split,
      alternative: Split,
  )(using VarSet): Split = scoped("ucs:rp"):
    log(s"SYNONYM: ${scrutinee.showDbg} is $symbol")
    import DeBrujinSplit.*, PatternStub.*
    // The reason why we comment the pattern arguments number check is that
    // it has been checked during elaboration, as the old pattern compilation
    // scheme still resolves symbols. The new pattern compilation scheme, which
    // will be implemented in the near future, should not do this.
    val arguments = argsOpt match
      case S(args) =>
        val patternArgs = args.collect:
          case (_, pattern, S(split)) => (split, pattern)
        // if symbol.patternParams.size != patternArgs.size then error(
        //   msg"Pattern `${symbol.nme}` expects ${"pattern argument".pluralize(symbol.patternParams.size, true)}" ->
        //     Loc(symbol.patternParams.iterator.map(_.sym)),
        //   msg"But ${"pattern argument".pluralize(patternArgs.size, true)} were given" -> Loc(args.iterator.map(_.pattern)))
        patternArgs
      case N =>
        // if symbol.patternParams.size > 0 then error(
        //   msg"Pattern `${symbol.nme}` expects ${"pattern argument".pluralize(symbol.patternParams.size, true)}" ->
        //     Loc(symbol.patternParams.iterator.map(_.sym)),
        //   msg"But no arguments were given" -> ctorTerm.toLoc)
        Nil
    val mainSplit = Binder:
      Branch(
        scrutinee = Outermost,
        // Here we run into a problem: during elaboration, we don't know whether
        // a constructor will be resolved to a pattern symbol. So we don't know
        // whether we should elaborate its arguments into terms or de Bruijn
        // splits. What's worse, `Desugarer` treats pattern arguments as
        // sub-patterns and expands them... For example:
        // ```
        // pattern Nullable(pattern A) = null | A
        // 0 is @compile Nullable(Int)
        // ```
        // My solution is to add `pattern` before each pattern argument.
        // ```
        // 0 is @compile Nullable(pattern Int)
        // ```
        pattern = ClassLike(ConstructorLike.Instantiation(symbol, arguments)),
        consequent = Accept(42),
        alternative = Reject
      )
    log(s"the initial split:\n${mainSplit.display}")
    val (normalizedMainSplit, indexSplitMap) = scoped("ucs:rpn"):
      mainSplit.normalize
    log(s"the normalized main split:\n${normalizedMainSplit.display}")
    // The entry in the local pattern map.
    val desugaring = new DesugaringBase {}
    val indexSplitSymbolMap = indexSplitMap.map:
      case (index, split) => (index, (split, TempSymbol(N, s"match$index")))
    val idSymbolMap = indexSplitSymbolMap.map(_ -> _._2)
    val compiledMainSplit = normalizedMainSplit.toSplit(
      scrutinees = Vector(() => scrutinee),
      localPatterns = idSymbolMap,
      outcomes = Map(S(42) -> consequent),
    )
    log(s"the compiled main split:\n${Split.display(compiledMainSplit)}")
    // Insert local pattern bindings before the split.
    val compiled = indexSplitSymbolMap.foldRight(normalizeImpl(compiledMainSplit ++ alternative)):
      case ((index, (split, symbol)), inner) =>
        val definition =
          log(s"making definition for ${split.display}")
          import syntax.{Fun, Keyword, ParamBind, Tree}, Tree.Ident
          // The memorized splits may have free variables. We will count
          // the number of free variables, bind them, and substitute them
          // with the new indices.
          val paramSymbols = (1 to split.arity).map: i =>
            VarSymbol(Ident(s"param$i"))
          .toVector
          val paramList = PlainParamList:
            paramSymbols.iterator.map(Param(FldFlags.empty, _, N, Modulefulness.none)).toList
          val success = Split.Else(desugaring.makeMatchResult(Term.Tup(Nil)(Tree.Tup(Nil))))
          val failure = Split.Else(desugaring.makeMatchFailure)
          val bodySplit = scoped("ucs:rp:split"):
            val bodySplit = split.toSplit(
              scrutinees = paramSymbols.map(symbol => () => symbol.ref().withIArgs(Nil)),
              localPatterns = idSymbolMap,
              outcomes = Map(S(0) -> success, N -> failure)
            ) ++ Split.Else(desugaring.makeMatchFailure)
            log(s"the compiled local pattern $index:\n${Split.display(bodySplit)}")
            bodySplit
          val funcBody: Term = Term.IfLike(Keyword.`if`, bodySplit)
          Term.Lam(paramList, funcBody)
        Split.Let(symbol, definition, inner)
    scoped("ucs:compiled"):
      log(s"the compiled split:\n${compiledMainSplit.toString()}")
    compiled

  /**
    * Specialize `split` with the assumption that `scrutinee` matches `pattern`.
    * If `matchOrNot` is `true`, the function _keeps_ branches that agree on
    * `scrutinee` matches `pattern`. Otherwise, the function _removes_ branches
    * that agree on `scrutinee` matches `pattern`.
    */
  private def specialize(
      split: Split,
      mode: Mode,
      scrutinee: Term.Ref,
      pattern: Pattern
  )(using VarSet): Split = trace(
    pre = s"S$mode <<< ${scrutinee.showDbg} is ${pattern.showDbg} : ${Split.display(split)}",
    post = (r: Split) => s"S$mode >>> ${Split.display(r)}"
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
            else if pattern <:< thatPattern then
              // TODO: the warning will be useful when we have inheritance information
              // raiseDesugaringWarning(
              //   msg"the pattern always matches" -> thatPattern.toLoc,
              //   msg"the scrutinee was matched against ${pattern.toString}" -> pattern.toLoc,
              //   msg"which is a subtype of ${thatPattern.toString}" -> (pattern match {
              //     case Pattern.Class(cls, _, _) => cls.toLoc
              //     case _ => thatPattern.toLoc
              //   }))
              rec(continuation) ++ rec(tail)
            else
              // TODO: the warning will be useful when we have inheritance information
              // raiseDesugaringWarning(
              //   msg"possibly conflicting patterns for this scrutinee" -> scrutinee.toLoc,
              //   msg"the scrutinee was matched against ${pattern.toString}" -> pattern.toLoc,
              //   msg"which is unrelated with ${thatPattern.toString}" -> thatPattern.toLoc)
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
  
  private def aliasBindings(p: Pattern, q: Pattern): Split => Split = (p, q) match
    case (Pattern.ClassLike(_, S(ss1), _, _), Pattern.ClassLike(_, S(ss2), _, _)) =>
      ss1.iterator.zip(ss2.iterator).foldLeft(identity[Split]):
        case (acc, (l, r)) if l.scrutinee === r.scrutinee => acc
        case (acc, (l, r)) => innermost => Split.Let(r.scrutinee, l.scrutinee.ref(), acc(innermost))
    case (_, _) => identity
end Normalization

object Normalization:
  /**
    * Hard-coded subtyping relations used in normalization and coverage checking.
    * TODO use base classes and also handle modules
    */
  def compareCasePattern(lhs: Pattern, rhs: Pattern)(using ctx: Elaborator.Ctx): Bool =
    import Pattern.*, ctx.builtins as blt
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
    case (_, _) => false

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
