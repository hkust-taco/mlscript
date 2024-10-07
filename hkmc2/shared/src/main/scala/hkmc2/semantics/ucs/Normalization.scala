package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.{Literal, Tree}, utils.TraceLogger
import Message.MessageContext

class Normalization(tl: TraceLogger)(using raise: Raise):
  import Normalization.*, Mode.*
  import Elaborator.Ctx
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
        case Split.Else(_) /* impossible */ | Split.Nil => those)

  /** We don't care about `Pattern.Name` because they won't appear in `specialize`. */
  extension (lhs: Pattern)
    /** Checks if two patterns are the same. */
    def =:=(rhs: Pattern): Bool = (lhs, rhs) match
      case (Pattern.Class(s1, _, _), Pattern.Class(s2, _, _)) => s1 === s2
      case (Pattern.LitPat(l1), Pattern.LitPat(l2)) => l1 === l2
      case (_, _) => false
    /** Checks if `self` can be subsumed under `rhs`. */
    def <:<(rhs: Pattern): Bool =
      def mk(pattern: Pattern): Option[Literal | ClassSymbol] = lhs match
        case Pattern.Class(s, _, _) => S(s)
        case Pattern.LitPat(l) => S(l)
        case _ => N
      compareCasePattern(mk(lhs), mk(rhs))
    /**
      * If two class-like patterns has different `refined` flag. Report the
      * inconsistency as a warning.
      */
    infix def reportInconsistentRefinedWith(rhs: Pattern): Unit = (lhs, rhs) match
      case (Pattern.Class(n1, _, r1), Pattern.Class(n2, _, r2)) if r1 =/= r2 =>
        def be(value: Bool): Str = if value then "is" else "is not"
        raiseDesugaringWarning(
          msg"inconsistent refined pattern" -> rhs.toLoc,
          msg"pattern `${n1.nme}` ${be(r1)} refined" -> n1.toLoc,
          msg"but pattern `${n2.nme}` ${be(r2)} refined" -> n2.toLoc)
      case (_, _) => ()
    /** If the pattern is a class-like pattern, override its `refined` flag. */
    def markAsRefined: Unit = lhs match
      case lhs: Pattern.Class => lhs.refined = true
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
        case Pattern.Var(vs) =>
          log(s"ALIAS: $scrutinee is $vs")
          Split.Let(vs, scrutinee, rec(consequent ++ alternative))
        case pattern @ (Pattern.LitPat(_) | Pattern.Class(_, _, _)) =>
          log(s"MATCH: $scrutinee is $pattern")
          val whenTrue = normalize(specialize(consequent ++ alternative, +, scrutinee, pattern))
          val whenFalse = rec(specialize(alternative, -, scrutinee, pattern).clearFallback)
          Branch(scrutinee, pattern, whenTrue) :: whenFalse
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
      case Split.Nil => Split.Nil
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
    pre = s"S$mode <<< $scrutinee is $pattern : ${Split.display(split)}",
    post = (r: Split) => s"S$mode >>> ${Split.display(r)}"
  ):
    def rec(split: Split)(using mode: Mode, vs: VarSet): Split = split match
      case Split.Nil => log("CASE Nil"); split
      case Split.Else(_) => log("CASE Else"); split
      case split @ Split.Let(nme, _, tail) =>
        log(s"CASE Let ${nme.name}")
        split.copy(tail = rec(tail))
      case split @ Split.Cons(head, tail) =>
        log(s"CASE Cons ${head.showDbg}")
        head match
          case Branch(thatScrutineeVar, Pattern.Var(alias), continuation) =>
            Split.Let(alias, thatScrutineeVar, rec(continuation))
          case Branch(test, Pattern.LitPat(Tree.BoolLit(true)), continuation) =>
            head.copy(continuation = rec(continuation)) :: rec(tail)
          case Branch(thatScrutinee, thatPattern, continuation) =>
            if scrutinee === thatScrutinee then mode match
              case + =>
                log(s"Case 1.1: $scrutinee === $thatScrutinee")
                if thatPattern =:= pattern then
                  log(s"Case 1.1.1: $pattern =:= $thatPattern")
                  thatPattern reportInconsistentRefinedWith pattern
                  aliasBindings(pattern, thatPattern)(rec(continuation) ++ rec(tail))
                else if (thatPattern <:< pattern) then
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
              head.copy(continuation = rec(continuation)) :: rec(tail)
        end match
    end rec
    rec(split)(using mode, summon)
  
  private def aliasBindings(p: Pattern, q: Pattern): Split => Split = (p, q) match
    case (Pattern.Class(_, S(ps1), _), Pattern.Class(_, S(ps2), _)) =>
      ps1.iterator.zip(ps2.iterator).foldLeft(identity[Split]):
        case (acc, (p1, p2)) => innermost => Split.Let(p2, p1.ref(p1.id), acc(innermost))
    case (_, _) => identity
end Normalization

object Normalization:
  /**
    * Hard-coded subtyping relations used in normalization and coverage checking.
    */
  def compareCasePattern(
      lhs: Opt[Literal | ClassSymbol],
      rhs: Opt[Literal | ClassSymbol]
  ): Bool = (lhs, rhs) match
    case (S(lhs), S(rhs)) => compareCasePattern(lhs, rhs)
    case (_, _) => false
  /**
    * Hard-coded subtyping relations used in normalization and coverage checking.
    */
  def compareCasePattern(
      lhs: Literal | ClassSymbol,
      rhs: Literal | ClassSymbol
  ): Bool = (lhs, rhs) match
    case (_, s: ClassSymbol) if s.nme === "Object" => true
    case (s1: ClassSymbol, s2: ClassSymbol) if s1.nme === "Int" && s2.nme === "Num" => true
    // case (s1: ClassSymbol, s2: ClassSymbol) => s1 <:< s2 // TODO: find a way to check inheritance
    case (Tree.IntLit(_), s: ClassSymbol) if s.nme === "Int" || s.nme === "Num" => true
    case (Tree.StrLit(_), s: ClassSymbol) if s.nme === "Str" => true
    case (Tree.DecLit(_), s: ClassSymbol) if s.nme === "Num" => true
    case (Tree.BoolLit(_), s: ClassSymbol) if s.nme === "Bool" => true
    case (Tree.UnitLit(true), s: ClassSymbol) if s.nme === "Unit" => true // TODO: how about undefined?
    case (_, _) => false

  final case class VarSet(declared: Set[VarSymbol]):
    def +(nme: VarSymbol): VarSet = copy(declared + nme)
    infix def has(nme: VarSymbol): Bool = declared.contains(nme)
    def showDbg: Str = declared.iterator.map(_.name).mkString("{", ", ", "}")

  object VarSet:
    def apply(): VarSet = VarSet(Set())

  /** Specialization mode */
  enum Mode:
    case +
    case -
