package mlscript.ucs.stages

import mlscript.{App, Asc, Fld, Term, Var, TypeName}
import mlscript.ucs.{syntax => s, core => c, PartialTerm}
import mlscript.ucs.helpers.mkBinOp
import mlscript.utils._, shorthands._
import mlscript.pretyper.symbol._
import mlscript.ucs.DesugaringException
import mlscript.Message, Message.MessageContext

trait Desugaring { self: mlscript.pretyper.Traceable =>
  @inline def desugar(term: s.TermSplit): c.Split = desugarTermSplit(term)(PartialTerm.Empty)

  import Desugaring._

  private val freshCache = new VariableGenerator(cachePrefix)
  private val freshScrutinee = new VariableGenerator(scrutineePrefix)
  private val freshTest = new VariableGenerator(testPrefix)

  private def freshScrutinee(parentScrutinee: Var, parentClassName: Var, index: Int): Var =
    Var(s"${parentScrutinee}$$${parentClassName}_${index.toString}")

  private def truePattern = c.Pattern.Class(Var("true"), N)

  private def flattenClassParameters(parentScrutinee: Var, parentClassName: Var, parameters: Opt[Ls[Opt[s.Pattern]]]): Opt[Ls[Opt[Var]]] -> Ls[Opt[Var -> s.Pattern]] =
    parameters match {
      case S(parameters) =>
        val (a, b) = parameters.zipWithIndex.unzip {
          case (N, index) => N -> N
          case (S(s.NamePattern(name)), index) => (S(name), N)
          case (S(parameterPattern: s.ClassPattern), index) =>
            val scrutinee = freshScrutinee(parentScrutinee, parentClassName, index)
            (S(scrutinee), Some((scrutinee, parameterPattern)))
          case (S(parameterPattern: s.LiteralPattern), index) =>
            val scrutinee = freshScrutinee(parentScrutinee, parentClassName, index)
            (S(scrutinee), Some((scrutinee, parameterPattern)))
          case _ => ??? // Other patterns are not implemented yet.
        }
        (S(a), b)
      case N => (N, Nil)
    }

  private def desugarTermSplit(split: s.TermSplit)(implicit termPart: PartialTerm): c.Split =
    split match {
      case s.Split.Cons(head, tail) => desugarTermBranch(head) ++ desugarTermSplit(tail)
      case s.Split.Let(rec, nme, rhs, tail) => c.Split.Let(rec, nme, rhs, desugarTermSplit(tail))
      case s.Split.Else(default) => c.Split.Else(default); 
      case s.Split.Nil => c.Split.Nil
    }

  // This function does not need to can `withCachedTermPart` because all branches assume that
  // `termPart` is either empty or waiting for an RHS.
  private def desugarTermBranch(branch: s.TermBranch)(implicit termPart: PartialTerm): c.Split =
    trace(s"desugarTermBranch <== $termPart") {
      branch match {
        case s.TermBranch.Boolean(testPart, continuation) =>
          val test = freshTest()
          c.Split.Let(
            rec = false,
            name = test,
            term = Asc(termPart.addTerm(testPart, true).get, TypeName("Bool")),
            tail = c.Branch(test, truePattern, desugarTermSplit(continuation)(PartialTerm.Empty)) :: c.Split.Nil
          )
        case s.TermBranch.Match(scrutinee, split) =>
          desugarPatternSplit(split)(termPart.addTerm(scrutinee, true).get)
        case s.TermBranch.Left(left, continuation) =>
          desugarOperatorSplit(continuation)(termPart.addTerm(left, true))
      }
    }()

  private def withCachedTermPart[B <: s.Branch](desugar: (PartialTerm) => c.Split)(implicit termPart: PartialTerm): c.Split =
    termPart.get match {
      case v: Var => desugar(termPart) // No need to cache variables.
      case rhs =>
        val cache = freshCache()
        c.Split.Let(false, cache, rhs, desugar(PartialTerm.Total(cache, Nil)))
    }

  private def desugarOperatorSplit(split: s.OperatorSplit)(implicit termPart: PartialTerm): c.Split =
    withCachedTermPart { termPart => split match {
      case s.Split.Cons(head, tail) => desugarOperatorBranch(head)(termPart) ++ desugarOperatorSplit(tail)(termPart)
      case s.Split.Let(rec, nme, rhs, tail) => c.Split.Let(rec, nme, rhs, desugarOperatorSplit(tail)(termPart))
      case s.Split.Else(default) => c.Split.Else(default)
      case s.Split.Nil => c.Split.Nil
    }}

  private def desugarOperatorBranch(branch: s.OperatorBranch)(implicit termPart: PartialTerm): c.Split =
    trace(s"desugarOperatorBranch <== $termPart") {
      branch match {
        case s.OperatorBranch.Binary(op, split) => desugarTermSplit(split)(termPart.addOp(op))
        case s.OperatorBranch.Match(_, split) => desugarPatternSplit(split)(termPart.get)
      }
    }()

  private def flattenNestedPattern(pattern: s.ClassPattern, scrutinee: Var, next: c.Split): c.Branch = {
    val (parameterBindings, subPatterns) = flattenClassParameters(scrutinee, pattern.nme, pattern.parameters)
    c.Branch(scrutinee, c.Pattern.Class(pattern.nme, parameterBindings), subPatterns.foldRight(next) {
      case (None, next) => next
      case (Some((nme, pattern: s.ClassPattern)), next) =>
        flattenNestedPattern(pattern, nme, next) :: c.Split.Nil
      case (Some((nme, pattern: s.LiteralPattern)), next) =>
        val scrutinee = freshScrutinee()
        c.Split.Let(
          rec = false,
          scrutinee,
          mkBinOp(nme, Var("=="), pattern.literal, true),
          c.Branch(scrutinee, truePattern, next) :: c.Split.Nil
        )
      case (Some((nme, pattern)), next) => ??? // Other patterns are not implemented yet.
    })
  }

  private def desugarPatternSplit(split: s.PatternSplit)(implicit scrutinee: Term): c.Split = {
    def rec(scrutinee: Var, split: s.PatternSplit): c.Split = split match {
      case s.Split.Cons(head, tail) => 
        lazy val continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty)
        head.pattern match {
          case s.AliasPattern(nme, pattern) => ???
          case s.LiteralPattern(literal) => ???
          case s.ConcretePattern(nme) => 
            val condition = freshScrutinee()
            c.Split.Let(
              rec = false,
              name = condition,
              term = mkBinOp(scrutinee, Var("==="), nme, true),
              tail = c.Branch(condition, truePattern, continuation) :: rec(scrutinee, tail)
            )
          case s.NamePattern(nme) => c.Branch(scrutinee, c.Pattern.Name(nme), continuation) :: rec(scrutinee, tail)
          case pattern @ s.ClassPattern(nme, fields) => flattenNestedPattern(pattern, scrutinee, continuation) :: rec(scrutinee, tail)
          case s.TuplePattern(fields) => ???
          case s.RecordPattern(entries) => ???
        }
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

object Desugaring {
  class VariableGenerator(prefix: Str) {
    private var nextIndex = 0

    def apply(): Var = {
      val thisIndex = nextIndex
      nextIndex += 1
      Var(s"$prefix$thisIndex")
    }
  }

  val cachePrefix = "cache$"
  val scrutineePrefix = "scrut$"
  val testPrefix = "test$"

  def isCacheVar(nme: Var): Bool = nme.name.startsWith(cachePrefix)
  def isScrutineeVar(nme: Var): Bool = nme.name.startsWith(scrutineePrefix)
  def isTestVar(nme: Var): Bool = nme.name.startsWith(testPrefix)
}