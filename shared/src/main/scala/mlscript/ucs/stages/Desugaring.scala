package mlscript.ucs.stages

import mlscript.{Term, Var}
import mlscript.ucs.{syntax => s, core => c, PartialTerm}
import mlscript.utils._, shorthands._
import mlscript.pretyper.{ScrutineeSymbol, SubValueSymbol, ValueSymbol}
import mlscript.ucs.DesugaringException
import mlscript.Message, Message.MessageContext

trait Desugaring { self: mlscript.pretyper.Traceable =>
  @inline def desugar(term: s.TermSplit): c.Split = desugarTermSplit(term)(PartialTerm.Empty)

  private var nextScrutineeIndex: Int = 0

  private def freshName(): Str = {
    val thisIndex = nextScrutineeIndex
    nextScrutineeIndex += 1
    s"scrut$thisIndex" // FIXME: use `freeVars` to avoid name collision.
  }

  private def freshScrutinee(): Var = Var(freshName())

  private def freshScrutinee(parentScrutinee: Var, parentClassName: Var, index: Int): Var =
    Var(s"${parentScrutinee}$$${parentClassName}_${index.toString}")

  private val truePattern = c.Pattern.Class(Var("true"), N)

  private def flattenClassParameters(parentScrutinee: Var, parentClassName: Var, parameters: Opt[Ls[Opt[s.Pattern]]]): Opt[Ls[Opt[Var]]] -> Ls[Opt[Var -> s.ClassPattern]] =
    parameters match {
      case S(parameters) =>
        val (a, b) = parameters.zipWithIndex.unzip {
          case (N, index) => N -> N
          case (S(s.NamePattern(name)), index) => (S(name), N)
          case (S(parameterPattern: s.ClassPattern), index) =>
            val scrutinee = freshScrutinee(parentScrutinee, parentClassName, index)
            (S(scrutinee), Some((scrutinee, parameterPattern)))
          case _ => ??? // Other patterns are not implemented yet.
        }
        (S(a), b)
      case N => (N, Nil)
    }

  private def flattenNestedSplitLet(pattern: s.ClassPattern, term: Var, tail: c.Split): c.Split = {
    val (parameterBindings, childrenBindings) = flattenClassParameters(term, pattern.nme, pattern.parameters)
    c.Branch(term, c.Pattern.Class(pattern.nme, parameterBindings), childrenBindings.foldRight(tail){ 
      case (N, tail) => tail
      case (S((nme, parameterPattern)), tail) =>
        flattenNestedSplitLet(parameterPattern, nme, tail)
    }) :: c.Split.Nil
  }

  private def desugarTermSplit(split: s.TermSplit)(implicit termPart: PartialTerm): c.Split =
    split match {
      case s.Split.Cons(head, tail) => desugarTermBranch(head) ++ desugarTermSplit(tail)
      case s.Split.Let(rec, nme, rhs, tail) => c.Split.Let(rec, nme, rhs, desugarTermSplit(tail))
      case s.Split.Else(default) => c.Split.Else(default); 
      case s.Split.Nil => c.Split.Nil
    }

  private def desugarTermBranch(branch: s.TermBranch)(implicit termPart: PartialTerm): c.Split =
    // Note: `Branch` is `(Term, Pattern, Either[Split, Term])`.
    branch match {
      case s.TermBranch.Boolean(condition, continuation) =>
        val `var` = freshScrutinee()
        c.Split.Let(
          rec = false,
          name = `var`,
          term = condition,
          tail = c.Branch(`var`, truePattern, desugarTermSplit(continuation)) :: c.Split.Nil
        )
      case s.TermBranch.Match(scrutinee, split) =>
        desugarPatternSplit(split)(termPart.addTerm(scrutinee, true).get)
      case s.TermBranch.Left(left, continuation) =>
        desugarOperatorSplit(continuation)(termPart.addTerm(left, true))
    }

  private def desugarOperatorSplit(split: s.OperatorSplit)(implicit termPart: PartialTerm): c.Split =
    split match {
      case s.Split.Cons(head, tail) => desugarOperatorBranch(head) ++ desugarOperatorSplit(tail)
      case s.Split.Let(rec, nme, rhs, tail) => c.Split.Let(rec, nme, rhs, desugarOperatorSplit(tail))
      case s.Split.Else(default) => c.Split.Else(default)
      case s.Split.Nil => c.Split.Nil
    }

  private def desugarOperatorBranch(branch: s.OperatorBranch)(implicit termPart: PartialTerm): c.Split =
    branch match {
      case s.OperatorBranch.Binary(op, split) => desugarTermSplit(split)(termPart.addOp(op))
      case s.OperatorBranch.Match(_, split) => desugarPatternSplit(split)(termPart.get)
    }

  private def flattenNestedPattern(pattern: s.ClassPattern, scrutinee: Var, next: c.Split): c.Branch = {
    val (parameterBindings, subPatterns) = flattenClassParameters(scrutinee, pattern.nme, pattern.parameters)
    c.Branch(scrutinee, c.Pattern.Class(pattern.nme, parameterBindings), subPatterns.foldRight(next) {
      case (None, next) => next
      case (Some((nme, pattern)), next) =>
        flattenNestedPattern(pattern, nme, next) :: c.Split.Nil
    })
  }

  private def desugarPatternBranch(scrutinee: Var, branch: s.PatternBranch): c.Branch = {
    lazy val continuation = desugarTermSplit(branch.continuation)(PartialTerm.Empty)
    branch.pattern match {
      case s.AliasPattern(nme, pattern) => ???
      case s.LiteralPattern(literal) => ???
      case s.NamePattern(nme) => c.Branch(scrutinee, c.Pattern.Name(nme), continuation)
      case pattern @ s.ClassPattern(nme, fields) => flattenNestedPattern(pattern, scrutinee, continuation)
      case s.TuplePattern(fields) => ???
      case s.RecordPattern(entries) => ???
    }
  }

  private def desugarPatternSplit(split: s.PatternSplit)(implicit scrutinee: Term): c.Split = {
    def rec(scrutinee: Var, split: s.PatternSplit): c.Split = split match {
      case s.Split.Cons(head, tail) => desugarPatternBranch(scrutinee, head) :: rec(scrutinee, tail)
      case s.Split.Let(isRec, nme, rhs, tail) => c.Split.Let(isRec, nme, rhs, rec(scrutinee, tail))
      case s.Split.Else(default) => c.Split.Else(default)
      case s.Split.Nil => c.Split.Nil
    }
    scrutinee match {
      case nme: Var => rec(nme, split)
      case other =>
        val alias = freshScrutinee()
        c.Split.Let(false, alias, scrutinee, rec(alias, split))
    }
  }
}
