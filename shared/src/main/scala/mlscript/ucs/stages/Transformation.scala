package mlscript.ucs.stages

import mlscript.ucs.helpers
import mlscript.{If, IfBody, IfBlock, IfElse, IfLet, IfOpApp, IfOpsApp, IfThen}
import mlscript.{Term, Var, App, Tup, Lit, Fld, Loc}
import mlscript.ucs.syntax._
import mlscript.Message, Message._
import mlscript.utils._, shorthands._
import mlscript.NuFunDef
import mlscript.PlainTup
import scala.collection.immutable

/**
  * Transform the parsed AST into an AST similar to the one in the paper.
  * The parsed AST represents pattern with terms and does not distingiush
  * `is` and `and` operators.
  * The AST in the paper is more flexible. For example, it allows interleaved
  * `let` bindings in operator splits.
  */
trait Transformation { self: mlscript.pretyper.Traceable =>
  import Transformation._

  def transform(`if`: If, useNewDefs: Bool = true): TermSplit =
    transformIfBody(`if`.body)(useNewDefs) ++ `if`.els.fold(Split.empty)(Split.default)

  import helpers.splitAnd

  private def transformIfBody(body: IfBody)(implicit useNewDefs: Bool): TermSplit = {
    body match {
      case IfThen(expr, rhs) =>
        splitAnd(expr).foldRight(Split.then(rhs)) {
          case (OperatorIs(scrutinee, pattern), acc) =>
            TermBranch.Match(scrutinee, PatternBranch(transformPattern(pattern), acc) |> Split.single) |> Split.single
          case (test, acc) => TermBranch.Boolean(test, acc) |> Split.single
        }
      case IfLet(isRec, name, rhs, body) => rare
      case IfElse(expr) => Split.then(expr)
      case IfOpApp(lhs, Var("is"), rhs) =>
        splitAnd(lhs) match {
          case init :+ last =>
            init.foldRight[TermSplit](TermBranch.Match(last, transformPatternMatching(rhs)) |> Split.single) {
              case (OperatorIs(scrutinee, pattern), acc) =>
                TermBranch.Match(scrutinee, PatternBranch(transformPattern(pattern), acc) |> Split.single) |> Split.single
              case (test, acc) => TermBranch.Boolean(test, acc) |> Split.single
            }
          case _ => rare
        }
      case IfOpApp(lhs, op, rhs) => 
        splitAnd(lhs) match {
          case init :+ last =>
            val first = TermBranch.Left(last, OperatorBranch.Binary(op, transformIfBody(rhs)) |> Split.single) |> Split.single
            init.foldRight[TermSplit](first) {
              case (OperatorIs(scrutinee, pattern), acc) =>
                TermBranch.Match(scrutinee, PatternBranch(transformPattern(pattern), acc) |> Split.single) |> Split.single
              case (test, acc) => TermBranch.Boolean(test, acc) |> Split.single
            }
          case _ => rare
        }
      case IfBlock(lines) =>
        lines.foldLeft(Split.empty[TermBranch]) {
          case (acc, L(body)) => acc ++ transformIfBody(body)
          case (acc, R(NuFunDef(S(rec), nme, _, _, L(rhs)))) =>
            acc ++ Split.Let(rec, nme, rhs, Split.Nil)
          case (acc, R(statement)) =>
            throw new TransformException(msg"Unexpected statement in an if block", statement.toLoc)
        }
      case IfOpsApp(lhs, opsRhss) =>
        TermBranch.Left(lhs, Split.from(opsRhss.map(transformOperatorBranch))) |> Split.single
    }
  }
  
  private def transformOperatorBranch(opsRhs: Var -> IfBody)(implicit useNewDefs: Bool): OperatorBranch =
    opsRhs match {
      case (op @ Var("is"), rhs) => OperatorBranch.Match(op, transformPatternMatching(rhs))
      case (op, rhs) => OperatorBranch.Binary(op, transformIfBody(rhs))
    }

  private def transformPatternMatching(body: IfBody)(implicit useNewDefs: Bool): PatternSplit = {
    body match {
      case IfThen(expr, rhs) => 
        separatePattern(expr) match {
          case (pattern, S(extraTest)) =>
            PatternBranch(pattern, transformIfBody(IfThen(extraTest, rhs))) |> Split.single
          case (pattern, N) =>
            PatternBranch(pattern, Split.default(rhs)) |> Split.single
        }
      case IfOpApp(lhs, Var("and"), rhs) =>
        separatePattern(lhs) match {
          case (pattern, S(extraTest)) =>
            PatternBranch(transformPattern(lhs), ???) |> Split.single
          case (pattern, N) =>
            PatternBranch(transformPattern(lhs), transformIfBody(rhs)) |> Split.single
        }
      case IfOpApp(lhs, op, rhs) => ???
      case IfOpsApp(lhs, opsRhss) => ???
      case IfLet(rec, nme, rhs, body) => rare
      case IfBlock(lines) => lines.foldLeft(Split.empty[PatternBranch]) {
        case (acc, L(body)) => acc ++ transformPatternMatching(body)
        case (acc, R(NuFunDef(S(rec), nme, _, _, L(rhs)))) =>
          acc ++ Split.Let(rec, nme, rhs, Split.Nil)
        case (acc, R(statement)) =>
          throw new TransformException(msg"Unexpected statement in an if block", statement.toLoc)
      }
      case IfElse(expr) => Split.default(expr)
    }
  }

  private def transformPattern(term: Term)(implicit useNewDefs: Bool): Pattern = term match {
    case nme @ Var("true" | "false") => ConcretePattern(nme)
    case nme @ Var(name) if name.headOption.exists(_.isUpper) => ClassPattern(nme, N)
    case nme: Var => NamePattern(nme)
    case literal: Lit => LiteralPattern(literal)
    case App(classNme @ Var(_), Tup(parameters)) =>
      ClassPattern(classNme, S(parameters.map {
        case (_, Fld(_, Var("_"))) => N // Consider "_" as wildcard.
        case (_, Fld(_, t)) => S(transformPattern(t))
      }))
    case Tup(fields) => TuplePattern(fields.map {
      case _ -> Fld(_, Var("_")) => N // Consider "_" as wildcard.
      case _ -> Fld(_, t       ) => S(transformPattern(t))
    })
    // TODO: Support more patterns.
    case _ => throw new TransformException(msg"Unknown pattern", term.toLoc)
  }

  private def separatePattern(term: Term)(implicit useNewDefs: Bool): (Pattern, Opt[Term]) = {
    val (rawPattern, extraTest) = helpers.separatePattern(term, useNewDefs)
    (transformPattern(rawPattern), extraTest)
  }

  private def rare: Nothing = throw new TransformException(msg"Wow, a rare case.", N)
}

object Transformation {
  private object OperatorIs {
    def unapply(term: Term)(implicit useNewDefs: Bool): Opt[(Term, Term)] = term match {
      case App(App(Var("is"), Tup(_ -> Fld(_, scrutinee) :: Nil)), Tup(_ -> Fld(_, pattern) :: Nil)) if !useNewDefs => S(scrutinee -> pattern)
      case App(Var("is"), PlainTup(scrutinee, pattern)) => S(scrutinee -> pattern)
      case _ => N
    }
  }

  class TransformException(val messages: Ls[Message -> Opt[Loc]]) extends Throwable {
    def this(message: Message, location: Opt[Loc]) = this(message -> location :: Nil)
  }
}