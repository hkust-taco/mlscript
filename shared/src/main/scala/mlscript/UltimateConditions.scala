package mlscript

import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet, Buffer}
import scala.collection.mutable.Buffer
import mlscript.utils._, shorthands._

class UltimateConditions extends TypeDefs { self: Typer =>
  import UltimateConditions._

  type FieldAliasMap = MutMap[Term, MutMap[Str, Var]]

  private def desugarPositionals
    (scrutinee: Term, params: IterableOnce[Term], positionals: Ls[Str])
    (implicit aliasMap: FieldAliasMap): (Buffer[Var -> Term], Ls[Str -> Var]) = {
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

  /**
    * Desugar sub-patterns from fields to conditions.
    *
    * @param subPatterns a list of field name -> pattern term
    * @param ctx the typing context
    * @param aliasMap the field alias map
    * @return desugared conditions representing the sub-patterns
    */
  private def destructSubPatterns(subPatterns: Iterable[Var -> Term])
      (implicit ctx: Ctx, raise: Raise, aliasMap: FieldAliasMap): Ls[ConditionClause] = {
    subPatterns.iterator.flatMap[ConditionClause] {
      case (scrutinee, subPattern) => destructPattern(scrutinee, subPattern)
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
      (scrutinee: Term, pattern: Term)
      (implicit ctx: Ctx, raise: Raise, aliasMap: FieldAliasMap): Ls[ConditionClause] = 
    pattern match {
      // This case handles top-level wildcard `Var`.
      // We don't make any conditions in this level.
      case Var("_") => Nil
      // This case handles literals.
      // x is true | x is false | x is 0 | x is "text" | ...
      case literal @ (Var("true") | Var("false") | _: Lit) =>
        val test = mkBinOp(scrutinee, Var("=="), literal)
        ConditionClause.BooleanTest(test) :: Nil
      // This case handles simple class tests.
      // x is A
      case className @ Var(name) =>
        ctx.tyDefs.get(name) match {
          case N => throw IfDesugaringException(s"constructor $name not found")
          case S(_) => ConditionClause.MatchClass(scrutinee, className, Nil) :: Nil
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
              ConditionClause.MatchClass(scrutinee, className, bindings) ::
                destructSubPatterns(subPatterns)
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
            ConditionClause.MatchClass(scrutinee, opVar, bindings) ::
              destructSubPatterns(subPatterns)
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
        ConditionClause.MatchTuple(scrutinee, elems.length, bindings) ::
          destructSubPatterns(subPatterns)
      // What else?
      case _ => throw new Exception(s"illegal pattern: ${mlscript.codegen.Helpers.inspect(pattern)}")
    }


  def desugarIf
      (body: IfBody, fallback: Opt[Term])
      (implicit ctx: Ctx, raise: Raise)
  : Ls[Ls[ConditionClause] -> Term] = {
    // We allocate temporary variable names for nested patterns.
    // This prevents aliasing problems.
    implicit val scrutineeFieldAliasMap: FieldAliasMap = MutMap.empty
    // A list of flattened if-branches.
    val branches = Buffer.empty[Ls[ConditionClause] -> Term]

    /**
      * Translate a list of atomic UCS conditions.
      * What is atomic? No "and".
      *
      * @param ts a list of atomic UCS conditions
      * @return a list of `Condition`
      */
    def desugarConditions(ts: Ls[Term]): Ls[ConditionClause] =
      ts.flatMap {
        case App(
          App(Var("is"),
              Tup((_ -> Fld(_, _, scrutinee)) :: Nil)),
          Tup((_ -> Fld(_, _, pattern)) :: Nil)
        ) => destructPattern(scrutinee, pattern)
        case test => Iterable.single(ConditionClause.BooleanTest(test))
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
    def desugarMatchBranch(scrutinee: Term, body: IfBody \/ Statement, pat: PartialTerm, acc: Ls[ConditionClause]): Unit =
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
          val patternConditions = destructPattern(scrutinee, pat.addTerm(patternPart).term)
          extraTestOpt match {
            // Case 1. Just a pattern. Easy!
            case N => 
              branches += ((acc ::: patternConditions) -> consequent)
            // Case 2. A pattern and an extra test
            case S(extraTest) =>
              desugarIfBody(IfThen(extraTest, consequent))(PartialTerm.Empty, acc :::patternConditions)
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
          val patternConditions = destructPattern(scrutinee, pattern)
          val tailTestConditions = optTests.fold(Nil: Ls[ConditionClause])(x => desugarConditions(splitAnd(x)))
          desugarIfBody(consequent)(PartialTerm.Empty, acc ::: patternConditions ::: tailTestConditions)
        case L(IfOpApp(patLhs, op, consequent)) =>
          separatePattern(patLhs) match {
            // Case 1.
            // The pattern is completed. There is also a conjunction.
            // So, we need to separate the pattern from remaining parts.
            case (pattern, S(extraTests)) =>
              val patternConditions = destructPattern(scrutinee, pattern)
              val extraConditions = desugarConditions(splitAnd(extraTests))
              desugarIfBody(consequent)(PartialTerm.Empty, acc ::: patternConditions ::: extraConditions)
            // Case 2.
            // The pattern is incomplete. Remaining parts are at next lines.
            // if x is
            //   head ::
            //     Nil then ...  // do something with head
            //     tail then ... // do something with head and tail
            case (patternPart, N) =>
              val partialPattern = pat.addTermOp(patternPart, op)
              desugarMatchBranch(scrutinee, L(consequent), partialPattern, acc)
          }
        case L(IfOpsApp(patLhs, opsRhss)) =>
          separatePattern(patLhs) match {
            case (patternPart, N) =>
              val partialPattern = pat.addTerm(patternPart)
              opsRhss.foreach { case op -> consequent =>
                desugarMatchBranch(scrutinee, L(consequent), partialPattern.addOp(op), acc)
              }
            case (patternPart, S(extraTests)) =>
              val patternConditions = destructPattern(scrutinee, pat.addTerm(patternPart).term)
              val testTerms = splitAnd(extraTests)
              val middleConditions = desugarConditions(testTerms.init)
              val accumulatedConditions = acc ::: patternConditions ::: middleConditions
              opsRhss.foreach { case op -> consequent =>
                // TODO: Use lastOption
                desugarIfBody(consequent)(PartialTerm.Total(testTerms.last), accumulatedConditions)
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
    def desugarIfBody(body: IfBody)(expr: PartialTerm, acc: List[ConditionClause]): Unit = {
      body match {
        case IfOpsApp(exprPart, opsRhss) =>
          val exprStart = expr.addTerm(exprPart)
          opsRhss.foreach { case opVar -> contBody =>
            desugarIfBody(contBody)(exprStart.addOp(opVar), acc)
          }
        case IfThen(Var("_"), consequent) =>
          branches += (acc -> consequent)
        // The termination case.
        case IfThen(term, consequent) =>
          branches += ((acc ::: desugarConditions(splitAnd(expr.addTerm(term).term))) -> consequent)
        // This is the entrance of the Simple UCS.
        case IfOpApp(scrutinee, Var("is"), IfBlock(lines)) =>
          lines.foreach(desugarMatchBranch(scrutinee, _, PartialTerm.Empty, acc))
        // For example: "if x == 0 and y is \n ..."
        case IfOpApp(testPart, Var("and"), consequent) =>
          desugarIfBody(consequent)(PartialTerm.Empty, acc ::: desugarConditions(expr.addTerm(testPart).term :: Nil))
        // Otherwise, this is not a pattern matching.
        // We create a partial term from `lhs` and `op` and dive deeper.
        case IfOpApp(lhs, op, body) =>
          desugarIfBody(body)(expr.addTermOp(lhs, op), acc)
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
    desugarIfBody(body)(PartialTerm.Empty, Nil)
    // Add the fallback case to conjunctions if there is any.
    fallback.foreach { branches += Nil -> _ }
    branches.toList
  }
}

abstract class ConditionClause

object ConditionClause {
  final case class MatchClass(
    scrutinee: Term,
    className: Var,
    fields: List[Str -> Var]
  ) extends ConditionClause

  final case class MatchTuple(
    scrutinee: Term,
    arity: Int,
    fields: List[Str -> Var]
  ) extends ConditionClause

  final case class BooleanTest(test: Term) extends ConditionClause

  def print(println: (=> Any) => Unit, cnf: Ls[Ls[ConditionClause] -> Term]): Unit = {
    println("Flattened conjunctions")
    cnf.foreach { case (conditions, term) =>
      println("+ " + conditions.iterator.map {
        case ConditionClause.BooleanTest(test) => s"<$test>"
        case ConditionClause.MatchClass(scrutinee, Var(className), fields) =>
          s"$scrutinee is $className"
        case ConditionClause.MatchTuple(scrutinee, arity, fields) =>
          s"$scrutinee is Tuple#$arity"
      }.mkString("«", "» and «", s"» => $term"))
    }
  }
}

abstract class PartialTerm {
  def addTerm(term: Term): PartialTerm.Total
  def addOp(op: Var): PartialTerm.Half
  def addTermOp(term: Term, op: Var): PartialTerm.Half =
    this.addTerm(term).addOp(op)
}

object PartialTerm {
  import UltimateConditions._

  final case object Empty extends PartialTerm {
    override def addTerm(term: Term): Total = Total(term)
    override def addOp(op: Var): Half =
      throw IfDesugaringException("expect a term")
  }

  final case class Total(val term: Term) extends PartialTerm {
    override def addTerm(term: Term): Total =
      throw IfDesugaringException("expect an operator")
    override def addOp(op: Var): Half = Half(term, op)
  }

  final case class Half(lhs: Term, op: Var) extends PartialTerm {
    override def addTerm(rhs: Term): Total = op match {
      case isVar @ Var("is") =>
        // Special treatment for pattern matching.
        val (pattern, extraTestOpt) = separatePattern(rhs)
        val assertion = mkBinOp(lhs, isVar, pattern)
        extraTestOpt match {
          case N => Total(assertion)
          case S(extraTest) =>
            Total(mkBinOp(assertion, Var("and"), extraTest))
        }
      case _ =>
        val (realRhs, extraExprOpt) = separatePattern(rhs)
        val leftmost = mkBinOp(lhs, op, realRhs)
        Total(extraExprOpt.fold(leftmost){ mkBinOp(leftmost, Var("and"), _) })
    }
    override def addOp(op: Var): Half =
      throw IfDesugaringException("expect a term")
  }
}

object UltimateConditions {
  final case class IfDesugaringException(message: Str) extends Exception(message)

  def mkMonuple(t: Term): Tup = Tup(N -> Fld(false, false, t) :: Nil)

  def mkBinOp(lhs: Term, op: Var, rhs: Term): Term =
    App(App(op, mkMonuple(lhs)), mkMonuple(rhs))

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
}

abstract class MutCaseOf {
  import UltimateConditions._

  def merge
    (branch: Ls[ConditionClause] -> Term)
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
    override def merge(branch: Ls[ConditionClause] -> Term)(implicit raise: Diagnostic => Unit): Unit =
      branch match {
        case Nil -> term => this.mergeDefault(term)
        case (ConditionClause.BooleanTest(test) :: tail) -> term =>
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
    override def merge(branch: Ls[ConditionClause] -> Term)(implicit raise: Diagnostic => Unit): Unit = {
      branch match {
        case (ConditionClause.MatchClass(scrutinee2, className, fields) :: tail) -> term if scrutinee2 === scrutinee =>
          branches.find(_.matches(className)) match {
            // No such pattern. We should create a new one.
            case N =>
              branches += Branch(S(className -> Buffer.from(fields)), buildBranch(tail, term))
            case S(branch) =>
              branch.addFields(fields)
              branch.consequent.merge(tail -> term)
          }
        case (ConditionClause.MatchTuple(scrutinee2, arity, fields) :: tail) -> term if scrutinee2 === scrutinee =>
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
    override def merge(branch: Ls[ConditionClause] -> Term)(implicit raise: Diagnostic => Unit): Unit =
      raise(WarningReport(Message.fromStr("duplicated branch") -> N :: Nil))

    override def mergeDefault(default: Term)(implicit raise: Diagnostic => Unit): Unit = ()

    override def toTerm: Term = term
  }
  final case object MissingCase extends MutCaseOf {
    override def merge(branch: Ls[ConditionClause] -> Term)(implicit raise: Diagnostic => Unit): Unit = ???

    override def mergeDefault(default: Term)(implicit raise: Diagnostic => Unit): Unit = ()

    override def toTerm: Term =
      throw new IfDesugaringException("missing a default branch")
  }

  private def buildBranch(conditions: Ls[ConditionClause], term: Term): MutCaseOf = {
    def rec(conditions: Ls[ConditionClause]): MutCaseOf = conditions match {
      case head :: next =>
        head match {
          case ConditionClause.BooleanTest(test) => IfThenElse(test, rec(next), MissingCase)
          case ConditionClause.MatchClass(scrutinee, className, fields) =>
            val branches = Buffer.empty[Branch]
            branches += Branch(S(className -> Buffer.from(fields)), rec(next))
            Match(scrutinee, branches)
          case ConditionClause.MatchTuple(scrutinee, arity, fields) =>
            val branches = Buffer.empty[Branch]
            val tupleClassName = Var(s"Tuple#$arity")
            branches += Branch(S(tupleClassName -> Buffer.from(fields)), rec(next))
            Match(scrutinee, branches)
        }
      case Nil => Consequent(term)
    }
    rec(conditions)
  }

  def build(cnf: Ls[Ls[ConditionClause] -> Term])(implicit raise: Diagnostic => Unit): MutCaseOf = {
    cnf match {
      case Nil => ???
      case (conditions -> term) :: next =>
        val root = MutCaseOf.buildBranch(conditions, term)
        next.foreach(root.merge(_))
        root
    }
  }
}
