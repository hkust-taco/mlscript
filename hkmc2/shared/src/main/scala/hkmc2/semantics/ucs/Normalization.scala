package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.{Literal, Tree}, utils.TraceLogger
import Message.MessageContext
import Elaborator.Ctx

class Normalization(elaborator: Elaborator)(using raise: Raise, ctx: Ctx):
  import Normalization.*, Mode.*
  import elaborator.tl.*

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
    /** Checks if two patterns are the same. */
    def =:=(rhs: Pattern): Bool = (lhs, rhs) match
      case (c1: Pattern.ClassLike, c2: Pattern.ClassLike) => c1.sym === c2.sym
      case (Pattern.Lit(l1), Pattern.Lit(l2)) => l1 === l2
      case (Pattern.Tuple(n1, b1), Pattern.Tuple(n2, b2)) => n1 == n2 && b1 == b2
      case (_, _) => false
    /** Checks if `lhs` can be subsumed under `rhs`. */
    def <:<(rhs: Pattern): Bool = compareCasePattern(lhs, rhs)
    /**
      * If two class-like patterns has different `refined` flag. Report the
      * inconsistency as a warning.
      */
    infix def reportInconsistentRefinedWith(rhs: Pattern): Unit = (lhs, rhs) match
      // case (Pattern.Class(n1, _, r1), Pattern.Class(n2, _, r2)) if r1 =/= r2 =>
      case (c1: Pattern.ClassLike, c2: Pattern.ClassLike) if c1.refined =/= c2.refined =>
        def be(value: Bool): Str = if value then "is" else "is not"
        raiseDesugaringWarning(
          msg"inconsistent refined pattern" -> rhs.toLoc,
          msg"pattern `${c1.sym.nme}` ${be(c1.refined)} refined" -> c1.sym.toLoc,
          msg"but pattern `${c2.sym.nme}` ${be(c2.refined)} refined" -> c2.sym.toLoc)
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
    def rec(split: Split)(using vs: VarSet): Split = split match
      case Split.Cons(Branch(scrutinee, pattern, consequent), alternative) => pattern match
        case pattern: (Pattern.Lit | Pattern.ClassLike | Pattern.Tuple) =>
          log(s"MATCH: ${scrutinee.showDbg} is ${pattern.showDbg}")
          val whenTrue = normalize(specialize(consequent ++ alternative, +, scrutinee, pattern))
          val whenFalse = rec(specialize(alternative, -, scrutinee, pattern).clearFallback)
          Branch(scrutinee, pattern, whenTrue) ~: whenFalse
        case Pattern.Synonym(symbol, arguments) => scoped("ucs:rp"):
          log(s"SYNONYM: ${scrutinee.showDbg} is $symbol")
          import DeBrujinSplit.*, PatternStub.*
          val pattern2 = ClassLike(ConstructorLike.Instantiation(symbol, arguments))
          val mainSplit = Binder(Branch(Outermost, pattern2, Accept(42), Reject))
          log(s"the initial split:\n${mainSplit.display}")
          val (normalizedMainSplit, idSplitMap) = scoped("ucs:rpn"):
            mainSplit.normalize(using elaborator.tl)
          log(s"the normalized main split:\n${normalizedMainSplit.display}")
          given Elaborator.State = elaborator.state
          // The entry in the local pattern map.
          val desugaring = new DesugaringBase:
            val elaborator: Elaborator = Normalization.this.elaborator
          val idSplitSymbolMap = idSplitMap.map:
            case (id, split) => (id, (split, TempSymbol(N, s"match$id")))
          val idSymbolMap = idSplitSymbolMap.map(_ -> _._2)
          val compiledMainSplit = normalizedMainSplit.toSplit(
            scrutinees = Vector(() => scrutinee),
            localPatterns = idSymbolMap,
            outcomes = Map(S(42) -> consequent),
            elab = elaborator
          )
          log(s"the compiled main split:\n${Split.display(compiledMainSplit)}")
          // Insert local pattern bindings before the split.
          idSplitSymbolMap.foldRight(rec(compiledMainSplit ++ alternative)):
            case ((id, (split, symbol)), inner) =>
              val definition =
                log(s"making definition for ${split.display}")
                import syntax.{Fun, Keyword, ParamBind, Tree}, Tree.Ident
                // The memorized splits may have free variables. We will count
                // the number of free variables, bind them, and substitute them
                // with the new indices.
                val paramSymbols = (1 to split.arity).map: i =>
                  TermSymbol(ParamBind, N, Ident(s"param$i"))
                .toVector
                val paramList = PlainParamList:
                  paramSymbols.iterator.map(Param(FldFlags.empty, _, N)).toList
                val success = Split.Else(desugaring.makeMatchResult(Term.Tup(Nil)(Tree.Tup(Nil))))
                val failure = Split.Else(desugaring.makeMatchFailure)
                val bodySplit = scoped("ucs:rp:split"):
                  val bodySplit = split.toSplit(
                    scrutinees = paramSymbols.map(symbol => () => symbol.ref()),
                    localPatterns = idSymbolMap,
                    outcomes = Map(S(0) -> success, N -> failure),
                    elab = elaborator) ++ Split.Else(desugaring.makeMatchFailure)
                  log(s"the compiled local pattern ${id}:\n${Split.display(bodySplit)}")
                  bodySplit
                val funcBody: Term = Term.IfLike(Keyword.`if`, bodySplit)(bodySplit)
                Term.Lam(paramList, funcBody)
              Split.Let(symbol, definition, inner)
        case _ =>
          raiseDesugaringError(msg"unsupported pattern matching: ${scrutinee.toString} is ${pattern.toString}" -> pattern.toLoc)
          Split.default(Term.Error)
      case Split.Let(v, _, tail) if vs has v =>
        log(s"LET: SKIP already declared scrutinee $v")
        rec(tail)
      case Split.Let(v, rhs, tail) =>
        log(s"LET: $v")
        Split.Let(v, rhs, rec(tail)(using vs + v))
      case Split.Else(default) =>
        log(s"DFLT: ${default.showDbg}")
        Split.Else(default)
      case Split.End => Split.End
    rec(split)
  
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
    case (Pattern.ClassLike(_, _, S(ps1), _), Pattern.ClassLike(_, _, S(ps2), _)) =>
      ps1.iterator.zip(ps2.iterator).foldLeft(identity[Split]):
        case (acc, (p1, p2)) if p1 == p2 => acc
        case (acc, (p1, p2)) => innermost => Split.Let(p2, p1.ref(), acc(innermost))
    case (_, _) => identity
end Normalization

object Normalization:
  /**
    * Hard-coded subtyping relations used in normalization and coverage checking.
    * TODO use base classes and also handle modules
    */
  def compareCasePattern(lhs: Pattern, rhs: Pattern)(using ctx: Elaborator.Ctx): Bool =
    import Pattern.*, ctx.Builtins.*
    (lhs, rhs) match
    // `Object` is the supertype of all (non-virtual) classes and modules.
    case (ClassLike(cs: ClassSymbol, _, _, _), ClassLike(`Object`, _, _, _))
        if !ctx.Builtins.virtualClasses.contains(cs) => true
    case (ClassLike(cs: ModuleSymbol, _, _, _), ClassLike(`Object`, _, _, _)) => true
    case (Tuple(n1, false), Tuple(n2, false)) if n1 == n2 => true
    case (Tuple(n1, _), Tuple(n2, true)) if n2 <= n1 => true
    case (ClassLike(`Int`, _, _, _), ClassLike(`Num`, _, _, _)) => true
    // case (s1: ClassSymbol, s2: ClassSymbol) => s1 <:< s2 // TODO: find a way to check inheritance
    case (Lit(Tree.IntLit(_)), ClassLike(`Int` | `Num`, _, _, _)) => true
    case (Lit(Tree.StrLit(_)), ClassLike(`Str`, _, _, _)) => true
    case (Lit(Tree.DecLit(_)), ClassLike(`Num`, _, _, _)) => true
    case (Lit(Tree.BoolLit(_)), ClassLike(`Bool`, _, _, _)) => true
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
