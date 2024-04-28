package mlscript
package ucs
package stages

import collection.immutable, annotation.tailrec, util.chaining._
import utils._, shorthands._, Message._
import syntax.source._, pretyper.Traceable

/**
  * Transform the parsed AST into an AST similar to the one in the paper.
  * The parsed AST represents pattern with terms and does not distingiush
  * `is` and `and` operators.
  * The AST in the paper is more flexible. For example, it allows interleaved
  * `let` bindings in operator splits.
  */
trait Transformation { self: Desugarer with Traceable =>
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

  private def transformIfBody(body: IfBody): TermSplit = trace(s"transformIfBody <== ${body.showDbg}") {
    body match {
      case IfThen(expr, rhs) => transformConjunction(splitAnd(expr), Split.then(rhs), true)
      case IfLet(isRec, name, rhs, body) => die
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
            raiseDesugaringError(msg"Unexpected statement in an if block" -> statement.toLoc)
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
          case _ => die
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
        raiseDesugaringError(
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
    trace(s"transformPatternMatching <== ${body.showDbg}") {
      body match {
        case IfThen(expr, rhs) => 
          val ::(head, tail) = splitAnd(expr)
          PatternBranch(transformPattern(head), transformConjunction(tail, Split.then(rhs), false)).toSplit
        case IfOpApp(lhs, Var("and"), rhs) =>
          val ::(head, tail) = splitAnd(lhs)
          PatternBranch(transformPattern(head), transformConjunction(tail, transformIfBody(rhs), false)).toSplit
        case IfOpApp(lhs, op, rhs) =>
          raiseDesugaringError(msg"Syntactic split of patterns are not supported" -> op.toLoc)
          Split.Nil
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
          val ::(pattern, tail) = splitAnd(lhs)
          // Here, `pattern` will be `( Cons x xs )` and `tail` will be
          // `[ is ys (Cons y ys) ]`. We can make a new `IfOpsApp`.
          tail match {
            case init :+ last =>
              val remake = IfOpsApp(last, opsRhss)
              val following = transformConjunction(init, transformIfBody(remake), true)
              PatternBranch(transformPattern(pattern), following).toSplit
            case _ => // This can only be `Nil`.
              PatternBranch(transformPattern(pattern), transformBrokenIfOpsApp(opsRhss)).toSplit
          }
          // END TEMPORARY PATCH
        case IfLet(rec, nme, rhs, body) => die
        case IfBlock(lines) => lines.foldLeft(Split.empty[PatternBranch]) {
          case (acc, L(body)) => acc ++ transformPatternMatching(body)
          case (acc, R(NuFunDef(S(rec), nme, _, _, L(rhs)))) =>
            acc ++ Split.Let(rec, nme, rhs, Split.Nil)
          case (acc, R(statement)) =>
            raiseDesugaringError(msg"Unexpected statement in an if block" -> statement.toLoc)
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
    case nme @ Var(name) if name.isCapitalized => ClassPattern(nme, N, refined = false)
    case nme: Var => NamePattern(nme)
    case literal: Lit => LiteralPattern(literal)
    case App(Var("refined"), PlainTup(p)) =>
      transformPattern(p) match {
        case cp: ClassPattern => cp.copy(refined = true).withLocOf(cp)
        case p =>
          raiseDesugaringError(msg"only class patterns can be refined" -> p.toLoc)
          p
      }
    case App(Var("as"), PlainTup(pattern, alias)) =>
      alias match {
        case nme @ Var(_) => AliasPattern(nme, transformPattern(pattern))
        case other =>
          raiseDesugaringError(msg"the pattern alias must be a variable" -> other.toLoc)
          transformPattern(pattern)
      }
    case App(TyApp(classNme @ Var(_), targs), parameters: Tup) =>
      raiseDesugaringWarning(msg"type parameters in patterns are currently ignored" -> Loc(targs))
      ClassPattern(classNme, S(transformTupleTerm(parameters)), refined = false)
    case App(classNme @ Var(_), parameters: Tup) =>
      ClassPattern(classNme, S(transformTupleTerm(parameters)), refined = false)
    case tuple: Tup => TuplePattern(transformTupleTerm(tuple))
    case Blk((term: Term) :: Nil) => transformPattern(term) // A speical case for FunnyIndet.mls
    case Bra(false, term) => transformPattern(term)
    case other =>
      println(s"other $other")
      raiseDesugaringError(msg"unknown pattern ${other.showDbg}" -> other.toLoc)
      EmptyPattern(other)
  }

  /**
    * Split a term into a list of terms. Note that the return type is `::[Term]`
    * because there should be at least one term even we don't split. It used to
    * split right-associate `and` terms, but it turned out that `and` may
    * nested in a left-associate manner. Therefore, the function now traverse
    * the entire term and split all `and` terms.
    */
  private def splitAnd(t: Term): ::[Term] = {
    @tailrec def rec(acc: Ls[Term], rest: ::[Term]): ::[Term] = rest.head match {
      case lhs and rhs => rec(acc, ::(rhs, lhs :: rest.tail))
      case sole => rest.tail match {
        case Nil => ::(sole, acc)
        case more @ ::(_, _) => rec(sole :: acc, more)
      }
    }
    rec(Nil, ::(t, Nil)).tap { rs =>
      println(s"splitAnd ${t.showDbg} ==> ${rs.iterator.map(_.showDbg).mkString(" ∧ ")}")
    }
  }
}

object Transformation {
  private def extractLast[T](xs: List[T]): (List[T], T) = xs match {
    case init :+ last => init -> last
    case _ => die
  }

  /** Matches terms like `x is y`. */
  private object is {
    def unapply(term: Term): Opt[Term -> Term] = term match {
      case App(Var("is"), PlainTup(scrutinee, pattern)) => S(scrutinee -> pattern)
      case _ => N
    }
  }

  /** Matches terms like `x and y` */
  private object and {
    def unapply(term: Term): Opt[(Term, Term)] = term match {
      case App(Var("and"), PlainTup(lhs, rhs)) => S((lhs, rhs))
      case _ => N
    }
  }
}
