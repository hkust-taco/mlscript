package mlscript.ucs.stages

import mlscript.ucs.helpers
import mlscript.{If, IfBody, IfBlock, IfElse, IfLet, IfOpApp, IfOpsApp, IfThen}
import mlscript.{Term, Var, App, Tup, Lit, Fld, Loc}
import mlscript.Diagnostic.PreTyping
import mlscript.pretyper.{Diagnosable, Traceable}
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
trait Transformation { self: Traceable with Diagnosable =>
  import Transformation._

  /** The entry point of transformation. */
  def transform(`if`: If): TermSplit =
    transformIfBody(`if`.body) ++ `if`.els.fold(Split.empty)(Split.default)

  /**
    * Transform a conjunction of terms into a nested split. The conjunction is
    * of the following form.
    * ```bnf
    * conjunction ::= term "is" term conjunction-tail
    *               | "_" conjunction-tail
    *               | term conjunction-tail
    * conjunction-tail ::= "and" conjunction
    *                    | ε
    * ```
    * @param init a list of term representing the conjunction
    * @param last the innermost split we should take if all terms of the
    *             conjunction work
    * @return
    */
  private def transformConjunction[B <: Branch](init: Ls[Term], last: TermSplit, skipWildcard: Bool): TermSplit =
    init.foldRight(last) {
      case (scrutinee is pattern, following) =>
        val branch = PatternBranch(transformPattern(pattern), following).toSplit
        TermBranch.Match(scrutinee, branch).toSplit
      // Maybe we don't need `skipWildcard` flag and we should take care of
      // wildcards at _this_ level in all cases.
      case (Var("_"), following) if skipWildcard => following
      case (test, following) => TermBranch.Boolean(test, following).toSplit
    }

  private def transformIfBody(body: IfBody): TermSplit = trace(s"transformIfBody <== ${inspect.shallow(body)}") {
    body match {
      case IfThen(expr, rhs) => transformConjunction(splitAnd(expr), Split.then(rhs), true)
      case IfLet(isRec, name, rhs, body) => rare
      case IfElse(expr) => Split.then(expr)
      case IfOpApp(lhs, Var("is"), rhs) =>
        val (tests, scrutinee) = extractLast(splitAnd(lhs))
        transformConjunction(tests, TermBranch.Match(scrutinee, transformPatternMatching(rhs)).toSplit, false)
      case IfOpApp(lhs, Var("and"), rhs) => transformConjunction(splitAnd(lhs), transformIfBody(rhs), true)
      case IfOpApp(lhs, op, rhs) => 
        val (init, last) = extractLast(splitAnd(lhs))
        transformConjunction(init, TermBranch.Left(last, OperatorBranch.Binary(op, transformIfBody(rhs)).toSplit).toSplit, false)
      case IfBlock(lines) =>
        lines.foldLeft(Split.empty[TermBranch]) {
          case (acc, L(body)) => acc ++ transformIfBody(body)
          case (acc, R(NuFunDef(S(rec), nme, _, _, L(rhs)))) =>
            acc ++ Split.Let(rec, nme, rhs, Split.Nil)
          case (acc, R(statement)) =>
            raiseError(PreTyping, msg"Unexpected statement in an if block" -> statement.toLoc)
            acc
        }
      case IfOpsApp(lhs, opsRhss) =>
        splitAnd(lhs) match {
          case init :+ (scrutinee is pattern) =>
            // If `last` is in the form of `scrutinee is pattern`, the `op` in
            // `opsRhss` must be `and`. Otherwise, it's a syntax error.
            val innermost = transformBrokenIfOpsApp(opsRhss)
            val inner = TermBranch.Match(scrutinee, PatternBranch(transformPattern(pattern), innermost).toSplit).toSplit
            transformConjunction(init, inner, false)
          case init :+ last =>
            transformConjunction(init, TermBranch.Left(last, Split.from(opsRhss.map(transformOperatorBranch))).toSplit, false)
          case _ => rare
        }
    }
  }(_ => "transformIfBody ==> ")

  /**
    * Transform the case where `lhs` of `IfOpsApp` concludes pattern matching
    * and we need to handle its `opsRhss`. This is special, because the first
    * field of elements of `opsRhss` must be `and`.
    */
  private def transformBrokenIfOpsApp(opsRhss: Ls[Var -> IfBody]): TermSplit = {
    opsRhss.iterator.flatMap {
      case Var("and") -> rhs => S(transformIfBody(rhs))
      case op -> rhs =>
        raiseError(PreTyping,
          msg"cannot transform due to an illegal split operator ${op.name}" -> op.toLoc,
          msg"the following branch will be discarded" -> rhs.toLoc)
        N
    }.foldLeft(Split.Nil: TermSplit)(_ ++ _)
  }
  
  private def transformOperatorBranch(opsRhs: Var -> IfBody): OperatorBranch =
    opsRhs match {
      case (op @ Var("is"), rhs) => OperatorBranch.Match(op, transformPatternMatching(rhs))
      case (op, rhs) => OperatorBranch.Binary(op, transformIfBody(rhs))
    }

  /**
    * Transform an `IfBody` into a `PatternSplit`.
    */
  private def transformPatternMatching(body: IfBody): PatternSplit =
    trace(s"transformPatternMatching <== ${inspect.shallow(body)}") {
      body match {
        case IfThen(expr, rhs) => 
          separatePattern(expr) match {
            case (pattern, S(extraTest)) =>
              PatternBranch(pattern, transformIfBody(IfThen(extraTest, rhs))).toSplit
            case (pattern, N) =>
              PatternBranch(pattern, Split.default(rhs)).toSplit
          }
        case IfOpApp(lhs, Var("and"), rhs) =>
          println(s"lhs: ${inspect.deep(lhs)}")
          separatePattern(lhs) match {
            case (pattern, S(extraTest)) =>
              PatternBranch(pattern, TermBranch.Boolean(extraTest, transformIfBody(rhs)).toSplit).toSplit
            case (pattern, N) =>
              PatternBranch(pattern, transformIfBody(rhs)).toSplit
          }
        case IfOpApp(lhs, op, rhs) => ??? // <-- Syntactic split of patterns are not supported.
        case IfOpsApp(lhs, opsRhss) =>
          // BEGIN TEMPORARY PATCH
          // Generally, syntactic split of patterns are not supported. Examples
          // like the following code is impossible.
          // ```
          // fun pairwise(xs) =
          //   if xs is Cons of
          //     x, Nil then [x, x]
          //     x, Cons of x', tail then [x, x'] :: pairwise of tail
          //     else Nil
          // ```
          // We could support this in future but it's disallowed for now. But I
          // found some mis-parsed examples. For example, as in `zipWith.mls:76`.
          // ```
          // fun zipWith_wrong(f, xs, ys) =
          //   if  xs is Cons(x, xs)
          //     and ys is Cons(y, ys)
          //     and zipWith_wrong(f, xs, ys) is Some(tail) then Some(Cons(f(x, y), tail))
          //   else None
          // ```
          // This is parsed as `{ and ( Cons x xs ) [ is ys ( Cons y ys ) ] }`.
          // I think it's not very well-formed. But I still implement it for not
          // breaking existing tests.
          splitAnd(lhs) match {
            case Nil => rare // It's impossible to be empty.
            case pattern :: tail =>
              // Here, `pattern` will be `( Cons x xs )` and `tail` will be
              // `[ is ys (Cons y ys) ]`. We can make a new `IfOpsApp`.
              println(s"lol, pattern is $pattern")
              println(s"lol, tail is $tail")
              tail match {
                case init :+ last =>
                  println(s"lol, init is $init")
                  println(s"lol, last is $last")
                  val remake = IfOpsApp(last, opsRhss)
                  val following = transformConjunction(init, transformIfBody(remake), true)
                  PatternBranch(transformPattern(pattern), following).toSplit
                case _ => // This can only be `Nil`.
                  PatternBranch(transformPattern(pattern), transformBrokenIfOpsApp(opsRhss)).toSplit
              }
          }
          // END TEMPORARY PATCH
        case IfLet(rec, nme, rhs, body) => rare
        case IfBlock(lines) => lines.foldLeft(Split.empty[PatternBranch]) {
          case (acc, L(body)) => acc ++ transformPatternMatching(body)
          case (acc, R(NuFunDef(S(rec), nme, _, _, L(rhs)))) =>
            acc ++ Split.Let(rec, nme, rhs, Split.Nil)
          case (acc, R(statement)) =>
            raiseError(PreTyping, msg"Unexpected statement in an if block" -> statement.toLoc)
            acc
        }
        case IfElse(expr) => Split.default(expr)
      }
    }(_ => "transformPatternMatching ==>")

  private def transformTupleTerm(tuple: Tup): Ls[Pattern] =
    tuple.fields.map(_._2.value |> transformPattern)

  /**
    * If we know the `term` represents a pattern, we can transform it to a
    * pattern with this function.
    *
    * @param term the term representing a pattern
    * @return 
    */
  private def transformPattern(term: Term): Pattern = term match {
    case wildcard @ Var("_") => EmptyPattern(wildcard) // The case for wildcard.
    case nme @ Var("true" | "false") => ConcretePattern(nme)
    case nme @ Var(name) if name.headOption.exists(_.isUpper) => ClassPattern(nme, N)
    case nme: Var => NamePattern(nme)
    case literal: Lit => LiteralPattern(literal)
    case App(classNme @ Var(_), parameters: Tup) =>
      ClassPattern(classNme, S(transformTupleTerm(parameters)))
    case tuple: Tup => TuplePattern(transformTupleTerm(tuple))
    case other =>
      println(s"other $other")
      raiseError(PreTyping, msg"Unknown pattern ${other.toString}" -> other.toLoc)
      EmptyPattern(other)
  }

  private def separatePattern(term: Term): (Pattern, Opt[Term]) = {
    val (rawPattern, extraTest) = helpers.separatePattern(term, true)
    println("rawPattern: " + inspect.deep(rawPattern))
    println("extraTest: " + inspect.deep(extraTest))
    (transformPattern(rawPattern), extraTest)
  }

  // TODO: Maybe we can change the return type to `::[Term]` so that it will not
  // empty.
  private def splitAnd(t: Term): List[Term] = trace(s"splitAnd <== ${inspect.deep(t)}") {
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
  private def rare: Nothing = lastWords("found a very rare case during desugaring UCS terms")

  private def extractLast[T](xs: List[T]): (List[T], T) = xs match {
    case init :+ last => init -> last
    case _ => rare
  }

  private object is {
    def unapply(term: Term): Opt[(Term, Term)] = term match {
      case App(Var("is"), PlainTup(scrutinee, pattern)) => S(scrutinee -> pattern)
      case _ => N
    }
  }
}
