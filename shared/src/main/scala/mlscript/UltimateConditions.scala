package mlscript

import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet, Buffer}
import scala.collection.mutable.Buffer
import mlscript.utils._, shorthands._

class UltimateConditions extends TypeDefs { self: Typer =>
  import UltimateConditions._

  private def desugarPositionals
    (scrutinee: Term, params: IterableOnce[Term], positionals: Ls[Str])
    (implicit aliasMap: MutMap[Term, MutMap[Str, Var]]): (Buffer[Var -> Term], Ls[Str -> Var]) = {
    val subPatterns = Buffer.empty[(Var, Term)]
    val bindings = params.iterator.zip(positionals).flatMap {
      // `x is A(_)`: ignore this binding
      case (Var("_"), _) => N
      // `x is A(value)`: generate bindings directly
      case (name: Var, fieldName) => S(fieldName -> name)
      // `x is B(A(x))`: generate a temporary name
      // use the name in the binding, and destruct sub-patterns
      case (pattern: Term, fieldName) =>
        // We should always use the same temporary for the same `fieldName`.
        // This uniqueness is decided by (scrutinee, fieldName).
        val alias = aliasMap
          .getOrElseUpdate(scrutinee, MutMap.empty)
          .getOrElseUpdate(fieldName, Var(freshName))
        subPatterns += ((alias, pattern))
        S(fieldName -> alias)
    }.toList
    subPatterns -> bindings
  }

  private def destructSubPatterns
    (subPatterns: Iterable[Var -> Term], ctx: Typer#Ctx)
    (implicit aliasMap: MutMap[Term, MutMap[Str, Var]]): Ls[Condition] = {
      subPatterns.iterator.flatMap[Condition] {
        case (scrutinee, subPattern) => destructPattern(scrutinee, subPattern, ctx)
      }.toList
    }

  /**
    * Destruct nested patterns to a list of simple condition with bindings.

    *
    * @param scrutinee the scrutinee of the pattern matching
    * @param pattern the pattern we will destruct
    * @param tyDefs `TypeDef`s in the context
    * @return a list of simple condition with bindings
    */
  private def destructPattern
      (scrutinee: Term, pattern: Term, ctx: Typer#Ctx)
      (implicit aliasMap: MutMap[Term, MutMap[Str, Var]]): Ls[Condition] = 
    pattern match {
      // This case handles top-level wildcard `Var`.
      // We don't make any conditions in this level.
      case Var("_") => Nil
      // This case handles literals.
      // x is true | x is false | x is 0 | x is "text" | ...
      case literal @ (Var("true") | Var("false") | _: Lit) =>
        val test = mkBinOp(scrutinee, Var("=="), literal)
        Condition.BooleanTest(test) :: Nil
      // This case handles simple class tests.
      // x is A
      case className @ Var(name) =>
        ctx.tyDefs.get(name) match {
          case N => throw IfDesugaringException(s"constructor $name not found")
          case S(_) => Condition.MatchClass(scrutinee, className, Nil) :: Nil
        }
      // This case handles classes with destruction.
      // x is A(r, s, t)
      case App(className @ Var(name), Tup(args)) =>
        ctx.tyDefs.get(name) match {
          case N => throw IfDesugaringException(s"class $name not found")
          case S(td) =>
            if (args.length === td.positionals.length) {
              val (subPatterns, bindings) = desugarPositionals(
                scrutinee,
                args.iterator.map(_._2.value),
                td.positionals
              )
              Condition.MatchClass(scrutinee, className, bindings) ::
                destructSubPatterns(subPatterns, ctx)
            } else {
              throw new Exception(s"$name expects ${td.positionals.length} but meet ${args.length}")
            }
        }
      // This case handles operator-like constructors.
      // x is head :: Nil
      case App(
        App(
          opVar @ Var(op),
          Tup((_ -> Fld(_, _, lhs)) :: Nil)
        ),
        Tup((_ -> Fld(_, _, rhs)) :: Nil)
      ) =>
        ctx.tyDefs.get(op) match {
          case N => throw IfDesugaringException(s"operator $op not found")
          case S(td) if td.positionals.length === 2 =>
            val (subPatterns, bindings) = desugarPositionals(
              scrutinee,
              lhs :: rhs :: Nil,
              td.positionals
            )
            Condition.MatchClass(scrutinee, opVar, bindings) ::
              destructSubPatterns(subPatterns, ctx)
          case S(td) =>
            val num = td.positionals.length
            throw new IfDesugaringException(s"$op has $num parameters but found two")
        }
      // This case handles tuple destructions.
      // x is (a, b, c)
      case Bra(_, Tup(elems)) =>
        val (subPatterns, bindings) = desugarPositionals(
          scrutinee,
          elems.iterator.map(_._2.value),
          1.to(elems.length).map("_" + _).toList
        )
        Condition.MatchTuple(scrutinee, elems.length, bindings) ::
          destructSubPatterns(subPatterns, ctx)
      // What else?
      case _ => throw new Exception(s"illegal pattern: ${mlscript.codegen.Helpers.inspect(pattern)}")
    }


  def desugarIf(body: IfBody, fallback: Opt[Term])(implicit ctx: Ctx): Ls[Ls[Condition] -> Term] = {
    // We allocate temporary variable names for nested patterns.
    // This prevents aliasing problems.
    implicit val scrutineeFieldAliases: MutMap[Term, MutMap[Str, Var]] = MutMap.empty
    // A list of flattened if-branches.
    val branches = Buffer.empty[Ls[Condition] -> Term]

    /**
      * Translate a list of atomic UCS conditions.
      * What is atomic? No "and".
      *
      * @param ts a list of atomic UCS conditions
      * @return a list of `Condition`
      */
    def desugarConditions(ts: Ls[Term]): Ls[Condition] =
      ts.flatMap {
        case App(
          App(Var("is"),
              Tup((_ -> Fld(_, _, scrutinee)) :: Nil)),
          Tup((_ -> Fld(_, _, pattern)) :: Nil)
        ) => destructPattern(scrutinee, pattern, ctx)
        case test => Iterable.single(Condition.BooleanTest(test))
      }

    /**
      * Recursively desugar a pattern matching branch.
      *
      * @param scrutinee the scrutinee of this pattern matching
      * @param body one element of `lines` of the `IfBlock`
      * @param pat the accumulated pattern, since patterns can be split
      * @param acc the accumulated conditions so far
      * @param ctx the typing context
      */
    def desugarMatchBranch
        (scrutinee: Term, body: IfBody \/ Statement, pat: PartialTerm, acc: Ls[Condition])
        (implicit ctx: Typer#Ctx): Unit =
      body match {
        // if x is
        //   A(...) then ...
        //   _      then ...
        case L(IfThen(Var("_"), consequent)) =>
          branches += (acc -> consequent)
        // if x is
        //   A(...) then ...         // Case 1: no conjunctions
        //   B(...) and ... then ... // Case 2: more conjunctions
        case L(IfThen(patTest, consequent)) =>
          val (patternPart, extraTestOpt) = separatePattern(patTest)
          // TODO: Find a way to extract this boilerplate.
          addTerm(pat, patternPart) match {
            case N => ??? // Error: it cannot be empty
            case S(R(_)) => ??? // Error: it cannot be R since we added a term.
            case S(L(pattern)) =>
              val patternConditions = destructPattern(scrutinee, pattern, ctx)
              extraTestOpt match {
                // Case 1. Just a pattern. Easy!
                case N => 
                  branches += ((acc ::: patternConditions) -> consequent)
                // Case 2. A pattern and an extra test
                case S(extraTest) =>
                  desugarIfBody(IfThen(extraTest, consequent))(N, acc :::patternConditions)
              }
          }
        // if x is
        //   A(...) and t <> // => IfOpApp(A(...), "and", IfOpApp(...))
        //     a then ...
        //     b then ...
        //   A(...) and y is // => IfOpApp(A(...), "and", IfOpApp(...))
        //     B(...) then ...
        //     B(...) then ...
        case L(IfOpApp(patLhs, Var("and"), consequent)) =>
          val (pattern, optTests) = separatePattern(patLhs)
          val patternConditions = destructPattern(scrutinee, pattern, ctx)
          val tailTestConditions = optTests.fold(Nil: Ls[Condition])(x => desugarConditions(splitAnd(x)))
          desugarIfBody(consequent)(N, acc ::: patternConditions ::: tailTestConditions)
        case L(IfOpApp(patLhs, op, consequent)) =>
          separatePattern(patLhs) match {
            // Case 1.
            // The pattern is completed. There is also a conjunction.
            // So, we need to separate the pattern from remaining parts.
            case (pattern, S(extraTests)) =>
              val patternConditions = destructPattern(scrutinee, pattern, ctx)
              val extraConditions = desugarConditions(splitAnd(extraTests))
              desugarIfBody(consequent)(N, acc ::: patternConditions ::: extraConditions)
            // Case 2.
            // The pattern is incomplete. Remaining parts are at next lines.
            // if x is
            //   head ::
            //     Nil then ...  // do something with head
            //     tail then ... // do something with head and tail
            case (patternPart, N) =>
              val partialPattern = addTermOp(pat, patternPart, op)
              desugarMatchBranch(scrutinee, L(consequent), partialPattern, acc)
          }
        case L(IfOpsApp(patLhs, opsRhss)) =>
          separatePattern(patLhs) match {
            case (patternPart, N) =>
              val partialPattern = addTerm(pat, patternPart)
              opsRhss.foreach { case op -> consequent =>
                desugarMatchBranch(scrutinee, L(consequent), addOp(partialPattern, op), acc)
              }
            case (patternPart, S(extraTests)) =>
              addTerm(pat, patternPart) match {
                case N => ??? // Error: cannot be empty
                case S(R(_)) => ??? // Error: cannot be incomplete
                case S(L(pattern)) =>
                  val patternConditions = destructPattern(scrutinee, pattern, ctx)
                  val testTerms = splitAnd(extraTests)
                  val middleConditions = desugarConditions(testTerms.init)
                  val accumulatedConditions = acc ::: patternConditions ::: middleConditions
                  opsRhss.foreach { case op -> consequent =>
                    // TODO: Use lastOption
                    desugarIfBody(consequent)(S(L(testTerms.last)), accumulatedConditions)
                  }
              }
          }
        case L(IfElse(consequent)) =>
          // Because this pattern matching is incomplete, it's not included in
          // `acc`. This means that we discard this incomplete pattern matching.
          branches += (acc -> consequent)
        // This case usually happens with pattern split by linefeed.
        case L(IfBlock(lines)) =>
          lines.foreach { desugarMatchBranch(scrutinee, _, pat, acc) }
        // Other cases are considered to be ill-formed.
        case L(_) =>
          println(s"Unexpected pattern match case: $body")
          ???
        // This case handles interleaved lets.
        case R(NuFunDef(S(isRec), letVar @ Var(name), _, L(rhs))) =>
          ???
        // Other cases are considered to be ill-formed.
        case R(_) => throw new Exception(s"illegal thing: $body")
      }
    def desugarIfBody(body: IfBody)(expr: PartialTerm, acc: List[Condition]): Unit = {
      body match {
        case IfOpsApp(exprPart, opsRhss) =>
          addTerm(expr, exprPart) match {
            case N => ??? // Error: The expression cannot be empty.
            case exprStart =>
              opsRhss.foreach { case opVar -> contBody =>
                desugarIfBody(contBody)(addOp(exprStart, opVar), acc)
              }
          }
        case IfThen(Var("_"), consequent) =>
          branches += (acc -> consequent)
        // The termination case.
        case IfThen(term, consequent) =>
          println(s"desugarIfBody > case IfThen > term = $term")
          addTerm(expr, term) match {
            case N => ??? // Error: Empty expression.
            case S(R(_)) => ??? // Error: Incomplete expression.
            case S(L(test)) =>
              println(s"desugarIfBody > case IfThen > test = $test")
              branches += ((acc ::: desugarConditions(splitAnd(test))) -> consequent)
          }
        // This is the entrance of the Simple UCS.
        case IfOpApp(scrutinee, Var("is"), IfBlock(lines)) =>
          lines.foreach(desugarMatchBranch(scrutinee, _, N, acc))
        // For example: "if x == 0 and y is \n ..."
        case IfOpApp(testPart, Var("and"), consequent) =>
          addTerm(expr, testPart) match {
            case N => ??? // Error: Empty expression.
            case S(R(_)) => ??? // Error: Incomplete expression.
            case S(L(test)) =>
              desugarIfBody(consequent)(N, acc ::: desugarConditions(test :: Nil))
          }
        // Otherwise, this is not a pattern matching.
        // We create a partial term from `lhs` and `op` and dive deeper.
        case IfOpApp(lhs, op, body) =>
          desugarIfBody(body)(addTermOp(expr, lhs, op), acc)
        // This case is rare. Let's put it aside.
        case IfLet(isRec, name, rhs, body) => ???
        // In this case, the accumulated partial term is discarded.
        // We create a branch directly from accumulated conditions.
        case IfElse(term) => branches += (acc -> term)
        case IfBlock(lines) =>
          lines.foreach {
            case L(subBody) => desugarIfBody(subBody)(expr, acc)
            case R(NuFunDef(S(isRec), letVar @ Var(name), _, L(rhs))) => ???
            case R(_) =>
              throw new Error("unexpected statements at desugarIfBody")
          }
      }
    }
    desugarIfBody(body)(N, Nil)
    // Add the fallback case to conjunctions if there is any.
    fallback.foreach { branches += Nil -> _ }
    branches.toList
  }
}

object UltimateConditions {
  final case class IfDesugaringException(message: Str) extends Exception(message)

  abstract class Condition

  object Condition {
    final case class MatchClass(
      scrutinee: Term,
      className: Var,
      fields: List[Str -> Var]
    ) extends Condition
    final case class MatchTuple(
      scrutinee: Term,
      arity: Int,
      fields: List[Str -> Var]
    ) extends Condition
    final case class BooleanTest(test: Term) extends Condition
  }

  def mkMonuple(t: Term): Tup = Tup(N -> Fld(false, false, t) :: Nil)

  def mkBinOp(lhs: Term, op: Var, rhs: Term): Term =
    App(App(op, mkMonuple(lhs)), mkMonuple(rhs))

  type PartialTerm = Opt[Term \/ (Term -> Var)]

  // Add a term to a partial term.
  def addTerm(sum: PartialTerm, rhs: Term): PartialTerm = 
    sum match {
      case N => S(L(rhs))
      case S(L(_)) => ???
      case S(R(scrutinee -> (isVar @ Var("is")))) =>
        // Special treatment for pattern matching.
        val (pattern, extraTestOpt) = separatePattern(rhs)
        val assertion = mkBinOp(scrutinee, isVar, pattern)
        extraTestOpt match {
          case N => S(L(assertion))
          case S(extraTest) =>
            S(L(mkBinOp(assertion, Var("and"), extraTest)))
        }
      case S(R(lhs -> op)) =>
        val (realRhs, extraExprOpt) = separatePattern(rhs)
        val leftmost = mkBinOp(lhs, op, realRhs)
        S(L(extraExprOpt.fold(leftmost){ mkBinOp(leftmost, Var("and"), _) }))
    }

  // Add an operator to a partial term.
  def addOp(sum: PartialTerm, op: Var): PartialTerm =
    sum match {
      case N => ???
      case S(L(lhs)) => S(R(lhs -> op))
      case S(R(_)) => ???
    }

  def addTermOp(sum: PartialTerm, t: Term, op: Var): PartialTerm
    = addOp(addTerm(sum, t), op)

  // Split a term joined by `and` into a list of terms.
  // E.g. x and y and z => x, y, z
  def splitAnd(t: Term): Ls[Term] =
    t match {
      case App(
        App(Var("and"),
            Tup((_ -> Fld(_, _, lhs)) :: Nil)),
        Tup((_ -> Fld(_, _, rhs)) :: Nil)
      ) =>
        splitAnd(lhs) :+ rhs
      case _ => t :: Nil
    }

  private var idLength: Int = 0
  def freshName: String = {
    val res = s"tmp$idLength"
    idLength += 1
    res
  }

  def separatePattern(term: Term): (Term, Opt[Term]) =
    term match {
      case App(
        App(and @ Var("and"),
            Tup((_ -> Fld(_, _, lhs)) :: Nil)),
        Tup((_ -> Fld(_, _, rhs)) :: Nil)
      ) =>
        separatePattern(lhs) match {
          case (pattern, N) => (pattern, S(rhs))
          case (pattern, S(lshRhs)) => (pattern, S(mkBinOp(lshRhs, and, rhs)))
        }
      case _ => (term, N)
    }

  def mkLetFromFields(scrutinee: Term, fields: Ls[Str -> Var], body: Term): Term = {
    val generatedFields = MutSet.empty[(Str, Str)]
    def rec(fields: Ls[Str -> Var]): Term =
      fields match {
        case Nil => body
        case (field -> (aliasVar @ Var(alias))) :: tail
            if !generatedFields.contains((field, alias)) =>
          generatedFields += ((field, alias))
          Let(false, aliasVar, Sel(scrutinee, Var(field)), rec(tail))
        case _ :: tail => rec(tail)
      }
    rec(fields)
  }

  def showConjunctions(println: (=> Any) => Unit, cnf: Ls[Ls[Condition] -> Term]): Unit = {
    println("Flattened conjunctions")
    cnf.foreach { case (conditions, term) =>
      println("+ " + conditions.iterator.map {
        case Condition.BooleanTest(test) => s"<$test>"
        case Condition.MatchClass(scrutinee, Var(className), fields) =>
          s"$scrutinee is $className"
        case Condition.MatchTuple(scrutinee, arity, fields) =>
          s"$scrutinee is Tuple#$arity"
      }.mkString("«", "» and «", s"» => $term"))
    }
  }
}

abstract class MutCaseOf {
  import UltimateConditions._

  def merge
    (branch: Ls[Condition] -> Term)
    (implicit raise: Diagnostic => Unit): Unit
  def mergeDefault
    (default: Term)
    (implicit raise: Diagnostic => Unit): Unit
  def toTerm: Term
}

object MutCaseOf {
  import UltimateConditions._

  def checkExhaustive(t: MutCaseOf)(implicit scrutineePatternMap: MutMap[Term, MutSet[Str]]): Unit =
    t match {
      case Consequent(term) => ()
      case MissingCase => ()
      case IfThenElse(condition, whenTrue, whenFalse) =>
        checkExhaustive(whenTrue)
        checkExhaustive(whenFalse)
      case Match(scrutinee, branches) =>
        scrutineePatternMap.get(scrutinee) match {
          case N => ???
          case S(patterns) =>
            if (!patterns.forall { expectedClassName =>
              branches.exists {
                case Branch(S(Var(className) -> _), _) =>
                  className === expectedClassName
                case Branch(_, _) => false
              }
            }) throw IfDesugaringException("not exhaustive")
        }
        branches.foreach(_.consequent |> checkExhaustive)
    }

  def summarizePatterns(t: MutCaseOf): MutMap[Term, MutSet[Str]] = {
    val scrutineePatternMap = MutMap.empty[Term, MutSet[Str]]
    def rec(t: MutCaseOf): Unit =
      t match {
        case Consequent(term) => ()
        case MissingCase => ()
        case IfThenElse(_, whenTrue, whenFalse) =>
          rec(whenTrue)
          rec(whenFalse)
        case Match(scrutinee, branches) =>
          branches.foreach {
            case Branch(N, consequent) => rec(consequent)
            case Branch(S(Var(className) -> _), consequent) =>
              scrutineePatternMap.getOrElseUpdate(scrutinee, MutSet.empty) += className
              rec(consequent)
          }
      }
    rec(t)
    scrutineePatternMap
  }

  def show(t: MutCaseOf): Ls[Str] = {
    val lines = Buffer.empty[String]
    def rec(t: MutCaseOf, indent: Int, leading: String): Unit = {
      val baseIndent = "  " * indent
      t match {
        case IfThenElse(condition, whenTrue, whenFalse) =>
          // Output the `whenTrue` with the prefix "if".
          lines += baseIndent + leading + s"if «$condition"
          rec(whenTrue, indent + 1, "")
          // Output the `whenFalse` case with the prefix "else".
          lines += s"$baseIndent${leading}else"
          rec(whenFalse, indent + 1, "")
        case Match(scrutinee, branches) =>
          lines += baseIndent + leading + s"«$scrutinee» match"
          branches.foreach {
            case Branch(N, consequent) =>
              lines += s"$baseIndent  default"
              rec(consequent, indent + 2, "")
            case Branch(S(Var(className) -> fields), consequent) =>
              lines += s"$baseIndent  case $className =>"
              fields.foreach { case (field, Var(alias)) =>
                lines += s"$baseIndent    let $alias = .$field"
              }
              rec(consequent, indent + 2, "")
          }
        case Consequent(term) =>
          lines += s"$baseIndent$leading«$term»"
        case MissingCase =>
          lines += s"$baseIndent$leading<missing case>"
      }
    }
    rec(t, 0, "")
    lines.toList
  }

  final case class Branch(
    val patternFields: Opt[Var -> Buffer[Str -> Var]],
    var consequent: MutCaseOf
  ) {
    def matches(expected: Var): Bool = matches(expected.name)
    def matches(expected: Str): Bool = patternFields match {
      case N => false
      case S(Var(className) -> _) => expected === className
    }
    def addFields(fields: Iterable[Str -> Var]): Unit =
      patternFields match {
        case N => ??? // Error: the branch has no pattern, it is a wildcard.
        case S(_ -> fieldBuffer) => fieldBuffer ++= fields
      }
    def isWildcard: Bool = patternFields.isEmpty
  }

  // A short-hand for pattern matchings with only true and false branches.
  final case class IfThenElse(condition: Term, var whenTrue: MutCaseOf, var whenFalse: MutCaseOf) extends MutCaseOf {
    override def merge(branch: Ls[Condition] -> Term)(implicit raise: Diagnostic => Unit): Unit =
      branch match {
        case Nil -> term => this.mergeDefault(term)
        case (Condition.BooleanTest(test) :: tail) -> term =>
          if (test === condition) {
            whenTrue.merge(tail -> term)
          } else {
            whenFalse match {
              case Consequent(_) => ??? // duplicated branch
              case MissingCase => whenFalse =  buildBranch(branch._1, branch._2)
              case _ => whenFalse.merge(branch)
            }
          }
        case _ =>
          whenFalse match {
            case Consequent(_) => ??? // duplicated branch
            case MissingCase => whenFalse = buildBranch(branch._1, branch._2)
            case _ => whenFalse.merge(branch)
          }
      }

    override def mergeDefault(default: Term)(implicit raise: Diagnostic => Unit): Unit = {
      whenTrue.mergeDefault(default)
      whenFalse match {
        case Consequent(_) =>
          raise(WarningReport(Message.fromStr("duplicated else branch") -> N :: Nil))
        case MissingCase => whenFalse = Consequent(default)
        case _: IfThenElse | _: Match => whenFalse.mergeDefault(default)
      }
    }

    override def toTerm: Term = {
      val falseBranch = Wildcard(whenFalse.toTerm)
      val trueBranch = Case(Var("true"), whenTrue.toTerm, falseBranch)
      CaseOf(condition, trueBranch)
    }
  }
  final case class Match(scrutinee: Term, val branches: Buffer[Branch]) extends MutCaseOf {
    override def merge(branch: Ls[Condition] -> Term)(implicit raise: Diagnostic => Unit): Unit = {
      branch match {
        case (Condition.MatchClass(scrutinee2, className, fields) :: tail) -> term if scrutinee2 === scrutinee =>
          branches.find(_.matches(className)) match {
            // No such pattern. We should create a new one.
            case N =>
              branches += Branch(S(className -> Buffer.from(fields)), buildBranch(tail, term))
            case S(branch) =>
              branch.addFields(fields)
              branch.consequent.merge(tail -> term)
          }
        case (Condition.MatchTuple(scrutinee2, arity, fields) :: tail) -> term if scrutinee2 === scrutinee =>
          val tupleClassName = Var(s"Tuple#$arity") // TODO: Find a name known by Typer.
          branches.find(_.matches(tupleClassName)) match {
            case N =>
              branches += Branch(S(tupleClassName -> Buffer.from(fields)), buildBranch(tail, term))
            case S(branch) =>
              branch.addFields(fields)
              branch.consequent.merge(tail -> term)
          }
        // A wild card case. We should propagate wildcard to every default positions.
        case Nil -> term => mergeDefault(term)
        case conditions -> term =>
          // Locate the wildcard case.
          branches.find(_.isWildcard) match {
            // No wildcard. We will create a new one.
            case N => branches += Branch(N, buildBranch(conditions, term))
            case S(Branch(N, consequent)) => consequent.merge(conditions -> term)
            case S(_) => ??? // Impossible case. What we find should be N.
          }
      }
    }

    override def mergeDefault(default: Term)(implicit raise: Diagnostic => Unit): Unit = {
      var hasWildcard = false
      branches.foreach {
        case Branch(_, _: Consequent | MissingCase) => ()
        case Branch(patternFields, consequent) =>
          consequent.mergeDefault(default)
          hasWildcard &&= patternFields.isEmpty
      }
      // If this match doesn't have a default case, we make one.
      if (!hasWildcard) branches += Branch(N, Consequent(default))
    }

    override def toTerm: Term = {
      def rec(xs: Ls[Branch]): CaseBranches =
        xs match {
          case Nil => NoCases
          case Branch(S(className -> fields), cases) :: next =>
            // TODO: expand bindings here
            Case(className, mkLetFromFields(scrutinee, fields.toList, cases.toTerm), rec(next))
          case Branch(N, cases) :: next =>
            // TODO: Warns if next is not Nil
            Wildcard(cases.toTerm)
        }
      CaseOf(scrutinee, rec(branches.toList))
    }
  }
  final case class Consequent(term: Term) extends MutCaseOf {
    override def merge(branch: Ls[Condition] -> Term)(implicit raise: Diagnostic => Unit): Unit =
      raise(WarningReport(Message.fromStr("duplicated branch") -> N :: Nil))

    override def mergeDefault(default: Term)(implicit raise: Diagnostic => Unit): Unit = ()

    override def toTerm: Term = term
  }
  final case object MissingCase extends MutCaseOf {
    override def merge(branch: Ls[Condition] -> Term)(implicit raise: Diagnostic => Unit): Unit = ???

    override def mergeDefault(default: Term)(implicit raise: Diagnostic => Unit): Unit = ()

    override def toTerm: Term =
      throw new IfDesugaringException("missing a default branch")
  }

  private def buildBranch(conditions: Ls[Condition], term: Term): MutCaseOf = {
    def rec(conditions: Ls[Condition]): MutCaseOf = conditions match {
      case head :: next =>
        head match {
          case Condition.BooleanTest(test) => IfThenElse(test, rec(next), MissingCase)
          case Condition.MatchClass(scrutinee, className, fields) =>
            val branches = Buffer.empty[Branch]
            branches += Branch(S(className -> Buffer.from(fields)), rec(next))
            Match(scrutinee, branches)
          case Condition.MatchTuple(scrutinee, arity, fields) =>
            val branches = Buffer.empty[Branch]
            val tupleClassName = Var(s"Tuple#$arity")
            branches += Branch(S(tupleClassName -> Buffer.from(fields)), rec(next))
            Match(scrutinee, branches)
        }
      case Nil => Consequent(term)
    }
    rec(conditions)
  }

  def build(cnf: Ls[Ls[Condition] -> Term])(implicit raise: Diagnostic => Unit): MutCaseOf = {
    cnf match {
      case Nil => ???
      case (conditions -> term) :: next =>
        val root = MutCaseOf.buildBranch(conditions, term)
        next.foreach(root.merge(_))
        root
    }
  }
}
