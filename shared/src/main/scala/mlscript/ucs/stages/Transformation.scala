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

  private def transformIfBody(body: IfBody)(implicit useNewDefs: Bool): TermSplit = trace(s"transformIfBody <== ${inspect.shallow(body)}") {
    body match {
      case IfThen(expr, rhs) =>
        splitAnd(expr).foldRight(Split.then(rhs)) {
          case (OperatorIs(scrutinee, pattern), acc) =>
            TermBranch.Match(scrutinee, PatternBranch(transformPattern(pattern), acc) |> Split.single) |> Split.single
          case (Var("_"), acc) => acc
          case (test, acc) => TermBranch.Boolean(test, acc) |> Split.single
        }
      case IfLet(isRec, name, rhs, body) => rare
      case IfElse(expr) => Split.then(expr)
      case IfOpApp(lhs, Var("is"), rhs) =>
        splitAnd(lhs) match {
          case tests :+ scrutinee =>
            tests.foldRight[TermSplit](TermBranch.Match(scrutinee, transformPatternMatching(rhs)) |> Split.single) {
              case (OperatorIs(scrutinee, pattern), acc) =>
                TermBranch.Match(scrutinee, PatternBranch(transformPattern(pattern), acc) |> Split.single) |> Split.single
              case (test, acc) => TermBranch.Boolean(test, acc) |> Split.single
            }
          case _ => rare
        }
      case IfOpApp(lhs, Var("and"), rhs) =>
        splitAnd(lhs).foldRight(transformIfBody(rhs)) {
          case (OperatorIs(scrutinee, pattern), acc) =>
            TermBranch.Match(scrutinee, PatternBranch(transformPattern(pattern), acc) |> Split.single) |> Split.single
          case (Var("_"), acc) => acc
          case (test, acc) => TermBranch.Boolean(test, acc) |> Split.single
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
        splitAnd(lhs) match {
          case init :+ last =>
            val first = TermBranch.Left(last, Split.from(opsRhss.map(transformOperatorBranch))) |> Split.single
            init.foldRight[TermSplit](first) {
              case (OperatorIs(scrutinee, pattern), acc) =>
                TermBranch.Match(scrutinee, PatternBranch(transformPattern(pattern), acc) |> Split.single) |> Split.single
              case (test, acc) => TermBranch.Boolean(test, acc) |> Split.single
            }
          case _ => rare
        }
    }
  }(_ => "transformIfBody ==> ")
  
  private def transformOperatorBranch(opsRhs: Var -> IfBody)(implicit useNewDefs: Bool): OperatorBranch =
    opsRhs match {
      case (op @ Var("is"), rhs) => OperatorBranch.Match(op, transformPatternMatching(rhs))
      case (op, rhs) => OperatorBranch.Binary(op, transformIfBody(rhs))
    }

  /**
    * Transform an `IfBody` into a `PatternSplit`.
    */
  private def transformPatternMatching(body: IfBody)(implicit useNewDefs: Bool): PatternSplit =
    trace(s"transformPatternMatching <== ${inspect.shallow(body)}") {
      body match {
        case IfThen(expr, rhs) => 
          separatePattern(expr) match {
            case (pattern, S(extraTest)) =>
              PatternBranch(pattern, transformIfBody(IfThen(extraTest, rhs))) |> Split.single
            case (pattern, N) =>
              PatternBranch(pattern, Split.default(rhs)) |> Split.single
          }
        case IfOpApp(lhs, Var("and"), rhs) =>
          println(s"lhs: ${inspect.deep(lhs)}")
          separatePattern(lhs) match {
            case (pattern, S(extraTest)) =>
              PatternBranch(pattern, TermBranch.Boolean(extraTest, transformIfBody(rhs)) |> Split.single) |> Split.single
            case (pattern, N) =>
              PatternBranch(pattern, transformIfBody(rhs)) |> Split.single
          }
        case IfOpApp(lhs, op, rhs) => ??? // <-- Syntactic split of patterns are not supported.
        case IfOpsApp(lhs, opsRhss) => ??? // <-- Syntactic split of patterns are not supported.
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
    }(_ => "transformPatternMatching ==>")

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
    case _ =>
      println(s"unknown pattern: $term")
      throw new TransformException(msg"Unknown pattern", term.toLoc)
  }

  private def separatePattern(term: Term)(implicit useNewDefs: Bool): (Pattern, Opt[Term]) = {
    val (rawPattern, extraTest) = helpers.separatePattern(term, useNewDefs)
    println("rawPattern: " + inspect.deep(rawPattern))
    println("extraTest: " + inspect.deep(extraTest))
    (transformPattern(rawPattern), extraTest)
  }

  private def rare: Nothing = throw new TransformException(msg"Wow, a rare case.", N)

  private def splitAnd(t: Term): Ls[Term] = trace(s"splitAnd <== ${inspect.deep(t)}") {
    t match {
      case App(
        App(Var("and"),
            Tup((_ -> Fld(_, lhs)) :: Nil)),
        Tup((_ -> Fld(_, rhs)) :: Nil)
      ) => // * Old-style operators
        splitAnd(lhs) :+ rhs
      case App(Var("and"), PlainTup(lhs, rhs)) =>
        splitAnd(lhs) :+ rhs
      case _ => t :: Nil
    }
  }(r => "splitAnd ==> " + r.iterator.map(_.toString).mkString(" ∧ "))
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