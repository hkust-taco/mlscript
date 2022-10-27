package mlscript

import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet, Buffer}
import scala.collection.mutable.Buffer
import mlscript.utils._, shorthands._
import scala.collection.immutable

class UltimateConditions extends TypeDefs { self: Typer =>
  import UltimateConditions._
  import ConditionClause.{ConjunctedConditions, MatchClass, MatchTuple, BooleanTest}

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

  private val localizedScrutineeMap = MutMap.empty[Term, Var]

  def localizeScrutinee(scrutinee: Term): Opt[Var] -> Term =
    scrutinee match {
      case _: Var => N -> scrutinee
      case _ => S(localizedScrutineeMap.getOrElseUpdate(scrutinee, Var(freshName))) -> scrutinee
    }

  /**
    * Destruct nested patterns to a list of simple condition with bindings.

    *
    * @param scrutinee the scrutinee of the pattern matching
    * @param pattern the pattern we will destruct
    * @param tyDefs `TypeDef`s in the context
    * @return a list of simple condition with bindings. This method does not
    * return `ConjunctedCondition` because conditions built from nested patterns
    * do not contain interleaved let bindings.
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
          case S(_) => ConditionClause.MatchClass(localizeScrutinee(scrutinee), className, Nil) :: Nil
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
              ConditionClause.MatchClass(localizeScrutinee(scrutinee), className, bindings) ::
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
            ConditionClause.MatchClass(localizeScrutinee(scrutinee), opVar, bindings) ::
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
        ConditionClause.MatchTuple(localizeScrutinee(scrutinee), elems.length, bindings) ::
          destructSubPatterns(subPatterns)
      // What else?
      case _ => throw new Exception(s"illegal pattern: ${mlscript.codegen.Helpers.inspect(pattern)}")
    }


  def desugarIf
      (body: IfBody, fallback: Opt[Term])
      (implicit ctx: Ctx, raise: Raise)
  : Ls[ConjunctedConditions -> Term] = {
    // We allocate temporary variable names for nested patterns.
    // This prevents aliasing problems.
    implicit val scrutineeFieldAliasMap: FieldAliasMap = MutMap.empty
    // A list of flattened if-branches.
    val branches = Buffer.empty[ConjunctedConditions -> Term]

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

    import ConditionClause.withBindings

    /**
      * Recursively desugar a pattern matching branch.
      *
      * @param scrutinee the scrutinee of this pattern matching
      * @param body one element of `lines` of the `IfBlock`
      * @param pat the accumulated pattern, since patterns can be split
      * @param acc the accumulated conditions so far
      * @param ctx the typing context
      * @param interleavedLets interleaved let bindings before this branch
      */
    def desugarMatchBranch(
      scrutinee: Term,
      body: IfBody \/ Statement,
      partialPattern: PartialTerm,
      collectedConditions: ConjunctedConditions,
    )(implicit interleavedLets: Buffer[(Bool, Var, Term)]): Unit =
      body match {
        // This case handles default branches. For example,
        // if x is
        //   A(...) then ...
        //   else ...
        case L(IfElse(consequent)) =>
          // Because this pattern matching is incomplete, it's not included in
          // `acc`. This means that we discard this incomplete pattern matching.
          branches += (collectedConditions -> consequent)
        // This case handles default branches indicated by wildcards.
        // if x is
        //   A(...) then ...
        //   _      then ...
        case L(IfThen(Var("_"), consequent)) =>
          branches += (collectedConditions -> consequent)
        // if x is
        //   A(...) then ...         // Case 1: no conjunctions
        //   B(...) and ... then ... // Case 2: more conjunctions
        case L(IfThen(patTest, consequent)) =>
          val (patternPart, extraTestOpt) = separatePattern(patTest)
          val patternConditions = destructPattern(scrutinee, partialPattern.addTerm(patternPart).term)
          val conditions = ConditionClause.concat(
            collectedConditions,
            withBindings((patternConditions, Nil))
          )
          extraTestOpt match {
            // Case 1. Just a pattern. Easy!
            case N => 
              branches += (conditions -> consequent)
            // Case 2. A pattern and an extra test
            case S(extraTest) =>
              desugarIfBody(IfThen(extraTest, consequent), PartialTerm.Empty, conditions)
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
          val conditions = ConditionClause.concat(
            collectedConditions,
            withBindings((patternConditions ::: tailTestConditions, Nil))
          )
          desugarIfBody(consequent, PartialTerm.Empty, conditions)
        case L(IfOpApp(patLhs, op, consequent)) =>
          separatePattern(patLhs) match {
            // Case 1.
            // The pattern is completed. There is also a conjunction.
            // So, we need to separate the pattern from remaining parts.
            case (pattern, S(extraTests)) =>
              val patternConditions = destructPattern(scrutinee, pattern)
              val extraConditions = desugarConditions(splitAnd(extraTests))
              val conditions = ConditionClause.concat(
                collectedConditions,
                withBindings((patternConditions ::: extraConditions, Nil))
              )
              desugarIfBody(consequent, PartialTerm.Empty, conditions)
            // Case 2.
            // The pattern is incomplete. Remaining parts are at next lines.
            // if x is
            //   head ::
            //     Nil then ...  // do something with head
            //     tail then ... // do something with head and tail
            case (patternPart, N) =>
              desugarMatchBranch(scrutinee, L(consequent), partialPattern.addTermOp(patternPart, op), collectedConditions)
          }
        case L(IfOpsApp(patLhs, opsRhss)) =>
          separatePattern(patLhs) match {
            case (patternPart, N) =>
              val partialPattern2 = partialPattern.addTerm(patternPart)
              opsRhss.foreach { case op -> consequent =>
                desugarMatchBranch(scrutinee, L(consequent), partialPattern2.addOp(op), collectedConditions)
              }
            case (patternPart, S(extraTests)) =>
              val patternConditions = destructPattern(scrutinee, partialPattern.addTerm(patternPart).term)
              val testTerms = splitAnd(extraTests)
              val middleConditions = desugarConditions(testTerms.init)
              val conditions = ConditionClause.concat(
                collectedConditions,
                withBindings((patternConditions ::: middleConditions, Nil))
              )
              opsRhss.foreach { case op -> consequent =>
                // TODO: Use lastOption
                desugarIfBody(consequent, PartialTerm.Total(testTerms.last), conditions)
              }
          }
        // This case usually happens with pattern split by linefeed.
        case L(IfBlock(lines)) =>
          lines.foreach { desugarMatchBranch(scrutinee, _, partialPattern, collectedConditions) }
        // This case is rare. Let's put it aside.
        case L(IfLet(_, _, _, _)) => ???
        // This case handles interleaved lets.
        case R(NuFunDef(S(isRec), nameVar, _, L(term))) =>
          interleavedLets += ((isRec, nameVar, term))
        // Other statements are considered to be ill-formed.
        case R(statement) => throw new IfDesugaringException(s"illegal statement: $statement")
      }
    def desugarIfBody
      (body: IfBody, expr: PartialTerm, acc: ConjunctedConditions)
      (implicit interleavedLets: Buffer[(Bool, Var, Term)])
    : Unit = {
      body match {
        case IfOpsApp(exprPart, opsRhss) =>
          val exprStart = expr.addTerm(exprPart)
          opsRhss.foreach { case opVar -> contBody =>
            desugarIfBody(contBody, exprStart.addOp(opVar), acc)
          }
        case IfThen(Var("_"), consequent) =>
          branches += (acc -> consequent)
        // The termination case.
        case IfThen(term, consequent) =>
          val conditions = ConditionClause.concat(
            acc,
            (desugarConditions(splitAnd(expr.addTerm(term).term)), Nil)
          )
          branches += (withBindings(conditions) -> consequent)
        // This is the entrance of the Simple UCS.
        case IfOpApp(scrutinee, Var("is"), IfBlock(lines)) =>
          val interleavedLets = Buffer.empty[(Bool, Var, Term)]
          lines.foreach(desugarMatchBranch(scrutinee, _, PartialTerm.Empty, acc)(interleavedLets))
        // For example: "if x == 0 and y is \n ..."
        case IfOpApp(testPart, Var("and"), consequent) =>
          val conditions = ConditionClause.concat(
            acc,
            (desugarConditions(expr.addTerm(testPart).term :: Nil), Nil)
          )
          desugarIfBody(consequent, PartialTerm.Empty, conditions)
        // Otherwise, this is not a pattern matching.
        // We create a partial term from `lhs` and `op` and dive deeper.
        case IfOpApp(lhs, op, body) =>
          desugarIfBody(body, expr.addTermOp(lhs, op), acc)
        // This case is rare. Let's put it aside.
        case IfLet(isRec, name, rhs, body) => ???
        // In this case, the accumulated partial term is discarded.
        // We create a branch directly from accumulated conditions.
        case IfElse(term) => branches += (withBindings(acc) -> term)
        case IfBlock(lines) =>
          lines.foreach {
            case L(subBody) => desugarIfBody(subBody, expr, acc)
            case R(NuFunDef(S(isRec), nameVar, _, L(term))) =>
              interleavedLets += ((isRec, nameVar, term))
            case R(_) =>
              throw new Error("unexpected statements at desugarIfBody")
          }
      }
    }
    // Top-level interleaved let bindings.
    val interleavedLets = Buffer.empty[(Bool, Var, Term)]
    desugarIfBody(body, PartialTerm.Empty, (Nil, Nil))(interleavedLets)
    // Add the fallback case to conjunctions if there is any.
    fallback.foreach { branches += (Nil, Nil) -> _ }
    branches.toList
  }
}

abstract class ConditionClause {
  // Local interleaved let bindings declared before this condition.
  var bindings: List[(Bool, Var, Term)] = Nil
}

object ConditionClause {
  // Make it a class, and then include the following two methods?
  type ConjunctedConditions = (Ls[ConditionClause], Ls[(Bool, Var, Term)])

  def concat(lhs: ConjunctedConditions, rhs: ConjunctedConditions): ConjunctedConditions = {
    val (lhsConditions, lhsTailBindings) = lhs
    val (rhsConditions, rhsTailBindings) = rhs
    rhsConditions match {
      case Nil => (lhsConditions, lhsTailBindings ::: rhsTailBindings)
      case head :: _ =>
        head.bindings = lhsTailBindings ::: head.bindings
        (lhsConditions ::: rhsConditions, rhsTailBindings)
    }
  }

  def separate(conditions: ConjunctedConditions, expectedScrutinee: Opt[Var] -> Term): Opt[(MatchClass, ConjunctedConditions)] = {
    def rec(past: Ls[ConditionClause], upcoming: Ls[ConditionClause])
        : Opt[(Ls[ConditionClause], MatchClass, Ls[ConditionClause])] = {
      upcoming match {
        case Nil => N
        case (head @ MatchClass(scrutinee, _, _)) :: tail =>
          if (scrutinee === expectedScrutinee) {
            S((past, head, tail))
          } else {
            rec(past :+ head, tail)
          }
        // TODO: Support tuples after merging `MatchClass` and `MatchTuple`.
        case head :: tail =>
          rec(past :+ head, tail)
      }
    }

    println(s"Searching $expectedScrutinee in $conditions")
    rec(Nil, conditions._1).map { case (past, wanted, remaining) =>
      println("Found!")
      (wanted, (past ::: remaining, conditions._2))
    }
  }

  final case class MatchClass(
    scrutinee: Opt[Var] -> Term,
    className: Var,
    fields: List[Str -> Var]
  ) extends ConditionClause

  final case class MatchTuple(
    scrutinee: Opt[Var] -> Term,
    arity: Int,
    fields: List[Str -> Var]
  ) extends ConditionClause

  final case class BooleanTest(test: Term) extends ConditionClause

  def print(println: (=> Any) => Unit, cnf: Ls[ConjunctedConditions -> Term]): Unit = {
    def showScrutinee(scrutinee: Opt[Var] -> Term): Str =
      (scrutinee._1 match {
        case N => ""
        case S(Var(alias)) => s"$alias @ "
      }) + s"${scrutinee._2}"

    def showBindings(bindings: Ls[(Bool, Var, Term)]): Str =
      bindings match {
        case Nil => ""
        case bindings => bindings.map {
          case (_, Var(name), _) => name
        }.mkString("(", ", ", ")")
      }

    println("Flattened conjunctions")
    cnf.foreach { case ((conditions, tailBindings), term) =>
      println("+ " + conditions.iterator.map { condition =>
        (condition match {
          case ConditionClause.BooleanTest(test) => s"«$test»"
          case ConditionClause.MatchClass(scrutinee, Var(className), fields) =>
            s"«${showScrutinee(scrutinee)} is $className»"
          case ConditionClause.MatchTuple(scrutinee, arity, fields) =>
            s"«${showScrutinee(scrutinee)} is Tuple#$arity»"
        }) + (if (condition.bindings.isEmpty) "" else " with " + showBindings(condition.bindings))
      }.mkString("", " and ", {
        (if (tailBindings.isEmpty) "" else " ") +
          showBindings(tailBindings) +
          s" => $term"
      }))
    }
  }

  /**
    * Attach bindings to the first condition of a CNF.
    *
    * @param conditions the conditions
    * @param interleavedLets the interleaved let buffer
    * @return idential to `conditions`
    */
  def withBindings
    (conditions: ConjunctedConditions)
    (implicit interleavedLets: Buffer[(Bool, Var, Term)])
  : ConjunctedConditions = {
    conditions._1 match {
      case Nil => (Nil, interleavedLets.toList ::: conditions._2)
      case head :: _ =>
        head.bindings = interleavedLets.toList
        conditions
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

  def showScrutinee(scrutinee: Opt[Var] -> Term): Str =
    s"«${scrutinee._2}»" + (scrutinee._1 match {
      case N => ""
      case S(Var(alias)) => s" as $alias"
    })

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

  def mkBindings(bindings: Ls[(Bool, Var, Term)], body: Term): Term = {
    val generated = MutSet.empty[(Bool, Var, Term)]
    def rec(bindings: Ls[(Bool, Var, Term)]): Term =
      bindings match {
        case Nil => body
        case (head @ (isRec, nameVar, value)) :: tail =>
          if (generated.contains(head)) {
            rec(tail)
          } else {
            generated += head
            Let(isRec, nameVar, value, rec(tail))
          }
      }
    rec(bindings)
  }

  def mkLetFromFields(scrutinee: Term, fields: Ls[Str -> Var], body: Term): Term = {
    def rec(fields: Ls[Str -> Var]): Term =
      fields match {
        case Nil => body
        case (field -> (aliasVar @ Var(alias))) :: tail =>
          Let(false, aliasVar, Sel(scrutinee, Var(field)), rec(tail))
      }
    rec(fields)
  }
}

trait WithBindings { this: MutCaseOf =>
  private val bindingsSet: MutSet[(Bool, Var, Term)] = MutSet.empty
  private val bindings: Buffer[(Bool, Var, Term)] = Buffer.empty

  def addBindings(newBindings: IterableOnce[(Bool, Var, Term)]): Unit = {
    newBindings.iterator.foreach {
      case binding if bindingsSet.contains(binding) => ()
      case binding =>
        bindingsSet += binding
        bindings += binding
    }
  }

  def getBindings: Iterable[(Bool, Var, Term)] = bindings

  def withBindings(newBindings: IterableOnce[(Bool, Var, Term)]): MutCaseOf = {
    addBindings(newBindings)
    this
  }
}

abstract class MutCaseOf extends WithBindings {
  import UltimateConditions._
  import ConditionClause.ConjunctedConditions

  def merge
    (branch: ConjunctedConditions -> Term)
    (implicit raise: Diagnostic => Unit): Unit
  def mergeDefault
    (bindings: Ls[(Bool, Var, Term)], default: Term)
    (implicit raise: Diagnostic => Unit): Unit
  def toTerm: Term
}

object MutCaseOf {
  import UltimateConditions._

  def toTerm(t: MutCaseOf): Term = {
    val term = t.toTerm
    mkBindings(t.getBindings.toList, term)
  }

  def checkExhaustive(t: MutCaseOf)(implicit scrutineePatternMap: MutMap[Term, MutSet[Str]]): Unit =
    t match {
      case Consequent(term) => ()
      case MissingCase => ()
      case IfThenElse(condition, whenTrue, whenFalse) =>
        checkExhaustive(whenTrue)
        checkExhaustive(whenFalse)
      case Match(scrutinee, branches, default) =>
        scrutineePatternMap.get(scrutinee._2) match {
          case N => ???
          case S(patterns) =>
            if (!patterns.forall { expectedClassName =>
              branches.exists {
                case Branch(Var(className) -> _, _) =>
                  className === expectedClassName
              }
            }) throw IfDesugaringException("not exhaustive")
        }
        default.foreach(checkExhaustive(_))
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
        case Match(scrutinee, branches, _) =>
          branches.foreach {
            case Branch(Var(className) -> _, consequent) =>
              scrutineePatternMap.getOrElseUpdate(scrutinee._2, MutSet.empty) += className
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
      val bindingNames = t.getBindings match {
        case Nil => ""
        case bindings => bindings.iterator.map(_._2.name).mkString("[", ", ", "] ")
      }
      t match {
        case IfThenElse(condition, whenTrue, whenFalse) =>
          // Output the `whenTrue` with the prefix "if".
          lines += baseIndent + leading + bindingNames + s"if «$condition»"
          rec(whenTrue, indent + 1, "")
          // Output the `whenFalse` case with the prefix "else".
          lines += s"$baseIndent${leading}else"
          rec(whenFalse, indent + 1, "")
        case Match(scrutinee, branches, default) =>
          lines += baseIndent + leading + bindingNames + showScrutinee(scrutinee) + " match"
          branches.foreach { case Branch(Var(className) -> fields, consequent) =>
            lines += s"$baseIndent  case $className =>"
            fields.foreach { case (field, Var(alias)) =>
              lines += s"$baseIndent    let $alias = .$field"
            }
            rec(consequent, indent + 2, "")
          }
          default.foreach { consequent =>
            lines += s"$baseIndent  default"
            rec(consequent, indent + 2, "")
          }
        case Consequent(term) =>
          lines += s"$baseIndent$leading$bindingNames«$term»"
        case MissingCase =>
          lines += s"$baseIndent$leading$bindingNames<missing case>"
      }
    }
    rec(t, 0, "")
    lines.toList
  }

  final case class Branch(
    val patternFields: Var -> Buffer[Str -> Var],
    var consequent: MutCaseOf
  ) {
    def matches(expected: Var): Bool = matches(expected.name)
    def matches(expected: Str): Bool = patternFields._1.name === expected
    def addFields(fields: Iterable[Str -> Var]): Unit =
      patternFields._2 ++= fields.iterator.filter(!patternFields._2.contains(_))
  }

  import ConditionClause.{ConjunctedConditions, MatchClass, MatchTuple, BooleanTest}

  // A short-hand for pattern matchings with only true and false branches.
  final case class IfThenElse(condition: Term, var whenTrue: MutCaseOf, var whenFalse: MutCaseOf) extends MutCaseOf {
    override def merge(branch: ConjunctedConditions -> Term)(implicit raise: Diagnostic => Unit): Unit =
      branch match {
        // The CC is a wildcard. So, we call `mergeDefault`.
        case (Nil, trailingBindings) -> term =>
          this.mergeDefault(trailingBindings, term)
        // The CC is an if-then-else. We create a pattern match of true/false.
        case ((head @ BooleanTest(test)) :: tail, trailingBindings) -> term =>
          // If the test is the same. So, we merge.
          if (test === condition) {
            whenTrue.addBindings(head.bindings)
            whenTrue.merge((tail, trailingBindings) -> term)
          } else {
            whenFalse match {
              case Consequent(_) =>
                raise(WarningReport(Message.fromStr("duplicated else in the if-then-else") -> N :: Nil))
              case MissingCase =>
                whenFalse = buildFirst(branch._1, branch._2)
                whenFalse.addBindings(head.bindings)
              case _ => whenFalse.merge(branch)
            }
          }
        case (head :: _, _) -> _ =>
          whenFalse match {
            case Consequent(_) =>
              raise(WarningReport(Message.fromStr("duplicated else in the if-then-else") -> N :: Nil))
            case MissingCase =>
              whenFalse = buildFirst(branch._1, branch._2)
              whenFalse.addBindings(head.bindings)
            case _ => whenFalse.merge(branch)
          }
      }

    override def mergeDefault(bindings: Ls[(Bool, Var, Term)], default: Term)(implicit raise: Diagnostic => Unit): Unit = {
      whenTrue.mergeDefault(bindings, default)
      whenFalse match {
        case Consequent(_) =>
          raise(WarningReport(Message.fromStr("duplicated else branch") -> N :: Nil))
        case MissingCase =>
          whenFalse = Consequent(default).withBindings(bindings)
        case _: IfThenElse | _: Match => whenFalse.mergeDefault(bindings, default)
      }
    }

    override def toTerm: Term = {
      val falseBody = mkBindings(whenFalse.getBindings.toList, whenFalse.toTerm)
      val trueBody = mkBindings(whenTrue.getBindings.toList, whenTrue.toTerm)
      val falseBranch = Wildcard(falseBody)
      val trueBranch = Case(Var("true"), trueBody, falseBranch)
      CaseOf(condition, trueBranch)
    }
  }
  final case class Match(
    scrutinee: Opt[Var] -> Term,
    val branches: Buffer[Branch],
    var wildcard: Opt[MutCaseOf]
  ) extends MutCaseOf {
    override def merge(branch: ConjunctedConditions -> Term)(implicit raise: Diagnostic => Unit): Unit = {
      ConditionClause.separate(branch._1, scrutinee) match {
        // No conditions against the same scrutinee.
        case N =>
          branch match {
            case ((head @ MatchTuple(scrutinee2, arity, fields)) :: tail, trailingBindings) -> term
                if scrutinee2 === scrutinee => // Same scrutinee!
              val tupleClassName = Var(s"Tuple#$arity") // TODO: Find a name known by Typer.
              branches.find(_.matches(tupleClassName)) match {
                // No such pattern. We should create a new one.
                case N =>
                  val newBranch = buildFirst((tail, trailingBindings), term)
                  newBranch.addBindings(head.bindings)
                  branches += Branch(tupleClassName -> Buffer.from(fields), newBranch)
                // Found existing pattern.
                case S(branch) =>
                  branch.consequent.addBindings(head.bindings)
                  branch.addFields(fields)
                  branch.consequent.merge((tail, trailingBindings) -> term)
              }
            // A wild card case. We should propagate wildcard to every default positions.
            case (Nil, trailingBindings) -> term => mergeDefault(trailingBindings, term)
            // The conditions to be inserted does not overlap with me.
            case conditions -> term =>
              wildcard match {
                // No wildcard. We will create a new one.
                case N => wildcard = S(buildFirst(conditions, term))
                // There is a wildcard case. Just merge!
                case S(consequent) => consequent.merge(conditions -> term)
              }
          }
        // Found a match condition against the same scrutinee
        case S((head @ MatchClass(_, className, fields), remainingConditions)) =>
          branches.find(_.matches(className)) match {
            // No such pattern. We should create a new one.
            case N =>
              val newBranch = buildFirst(remainingConditions, branch._2)
              // println(s"The original CNF is $branch")
              // println(s"It has bindings: ${head.bindings}")
              // println(s"Just build branch: $newBranch")
              // println(s"It has bindings: ${newBranch.getBindings}")
              newBranch.addBindings(head.bindings)
              branches += Branch(className -> Buffer.from(fields), newBranch)
            // Found existing pattern.
            case S(matchCase) =>
              // Merge interleaved bindings.
              matchCase.consequent.addBindings(head.bindings)
              matchCase.addFields(fields)
              matchCase.consequent.merge(remainingConditions -> branch._2)
          }
      }
    }

    override def mergeDefault(bindings: Ls[(Bool, Var, Term)], default: Term)(implicit raise: Diagnostic => Unit): Unit = {
      branches.foreach {
        case Branch(_, consequent) => consequent.mergeDefault(bindings, default)
      }
      wildcard match {
        case N => wildcard = S(Consequent(default).withBindings(bindings))
        case S(consequent) => consequent.mergeDefault(bindings, default)
      }
    }

    override def toTerm: Term = {
      def rec(xs: Ls[Branch]): CaseBranches =
        xs match {
          case Branch(className -> fields, cases) :: next =>
            // TODO: expand bindings here
            Case(className, mkLetFromFields(scrutinee._1.getOrElse(scrutinee._2), fields.toList, cases.toTerm), rec(next))
          case Nil =>
            wildcard match {
              case N => NoCases
              case S(mutCaseOf) => Wildcard(mutCaseOf.toTerm)
            }
        }
      val cases = rec(branches.toList)
      val resultTerm = scrutinee._1 match {
        case N => CaseOf(scrutinee._2, cases)
        case S(aliasVar) => Let(false, aliasVar, scrutinee._2, CaseOf(aliasVar, cases))
      }
      // Collect let bindings from case branches.
      val bindings = branches.iterator.flatMap(_.consequent.getBindings).toList
      mkBindings(bindings, resultTerm)
    }
  }
  final case class Consequent(term: Term) extends MutCaseOf {
    override def merge(branch: ConjunctedConditions -> Term)(implicit raise: Diagnostic => Unit): Unit =
      raise(WarningReport(Message.fromStr("duplicated branch") -> N :: Nil))

    override def mergeDefault(bindings: Ls[(Bool, Var, Term)], default: Term)(implicit raise: Diagnostic => Unit): Unit = ()

    override def toTerm: Term = term
  }
  final case object MissingCase extends MutCaseOf {
    override def merge(branch: ConjunctedConditions -> Term)(implicit raise: Diagnostic => Unit): Unit = ???

    override def mergeDefault(bindings: Ls[(Bool, Var, Term)], default: Term)(implicit raise: Diagnostic => Unit): Unit = ()

    override def toTerm: Term =
      throw new IfDesugaringException("missing a default branch")
  }

  private def buildFirst(conditions: ConjunctedConditions, term: Term): MutCaseOf = {
    def rec(conditions: ConjunctedConditions): MutCaseOf = conditions match {
      case (head :: tail, trailingBindings) =>
        val realTail = (tail, trailingBindings)
        val res = head match {
          case BooleanTest(test) => IfThenElse(test, rec(realTail), MissingCase)
          case MatchClass(scrutinee, className, fields) =>
            val branches = Buffer(Branch(className -> Buffer.from(fields), rec(realTail)))
            Match(scrutinee, branches, N)
          case MatchTuple(scrutinee, arity, fields) =>
            val branches = Buffer.empty[Branch]
            val tupleClassName = Var(s"Tuple#$arity")
            branches += Branch(tupleClassName -> Buffer.from(fields), rec(realTail))
            Match(scrutinee, branches, N)
        }
        res.addBindings(head.bindings)
        res
      case (Nil, trailingBindings) =>
        val res = Consequent(term)
        res.addBindings(trailingBindings)
        res
    }

    rec(conditions)
  }

  def build
    (cnf: Ls[ConjunctedConditions -> Term])
    (implicit raise: Diagnostic => Unit)
  : MutCaseOf = {
    cnf match {
      case Nil => ???
      case (conditions -> term) :: next =>
        val root = MutCaseOf.buildFirst(conditions, term)
        next.foreach(root.merge(_))
        root
    }
  }
}
