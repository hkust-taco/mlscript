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
    (implicit aliasMap: FieldAliasMap, matchRootLoc: Opt[Loc]): (Buffer[Var -> Term], Ls[Str -> Var]) = {
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
          .getOrElseUpdate(fieldName, Var(freshName).withLoc(pattern.toLoc))
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
      (implicit ctx: Ctx, raise: Raise, aliasMap: FieldAliasMap, matchRootLoc: Opt[Loc]): Ls[ConditionClause] = {
    subPatterns.iterator.flatMap[ConditionClause] {
      case (scrutinee, subPattern) => destructPattern(scrutinee, subPattern)
    }.toList
  }

  private val localizedScrutineeMap = MutMap.empty[Term, Var]

  /**
    * Create a `Scrutinee`. If the `term` is a simple expression (e.g. `Var` or
    * `Lit`), we do not create a local alias. Otherwise, we create a local alias
    * to avoid unnecessary computations.
    *
    * @param term the term in the local scrutinee position
    * @param matchRootLoc the caller is expect to be in a match environment,
    * this parameter indicates the location of the match root
    */
  def makeScrutinee(term: Term)(implicit matchRootLoc: Opt[Loc]): Scrutinee = {
    val res = term match {
      case _: Var => Scrutinee(N, term)
      case _ =>
        Scrutinee(S(localizedScrutineeMap.getOrElseUpdate(term, {
          Var(freshName).withLoc(term.toLoc)
        })), term)
    }
    res.matchRootLoc = matchRootLoc
    res
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
      (implicit ctx: Ctx, raise: Raise, aliasMap: FieldAliasMap, matchRootLoc: Opt[Loc]): Ls[ConditionClause] = 
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
      case classNameVar @ Var(className) =>
        ctx.tyDefs.get(className) match {
          case N => throw IfDesugaringException.Single({
            import Message.MessageContext
            msg"Cannot find the constructor `$className` in the context"
          }, classNameVar.toLoc)
          case S(_) => ConditionClause.MatchClass(makeScrutinee(scrutinee), classNameVar, Nil) :: Nil
        }
      // This case handles classes with destruction.
      // x is A(r, s, t)
      case app @ App(classNameVar @ Var(className), Tup(args)) =>
        ctx.tyDefs.get(className) match {
          case N =>
            throw IfDesugaringException.Single({
              import Message.MessageContext
              msg"Cannot find the class `$className` in the context"
            }, classNameVar.toLoc)
          case S(td) =>
            if (args.length === td.positionals.length) {
              val (subPatterns, bindings) = desugarPositionals(
                scrutinee,
                args.iterator.map(_._2.value),
                td.positionals
              )
              ConditionClause.MatchClass(makeScrutinee(scrutinee), classNameVar, bindings) ::
                destructSubPatterns(subPatterns)
            } else {
              throw IfDesugaringException.Single({
                import Message.MessageContext
                val expected = td.positionals.length
                val actual = args.length
                msg"${td.kind.str} $className expects ${expected.toString} ${
                  "parameter".pluralize(expected)
                } but found ${args.length.toString} ${
                  "parameter".pluralize(expected)
                }"
              }, app.toLoc)
            }
        }
      // This case handles operator-like constructors.
      // x is head :: Nil
      case app @ App(
        App(
          opVar @ Var(op),
          Tup((_ -> Fld(_, _, lhs)) :: Nil)
        ),
        Tup((_ -> Fld(_, _, rhs)) :: Nil)
      ) =>
        ctx.tyDefs.get(op) match {
          case N =>
            throw IfDesugaringException.Single({
              import Message.MessageContext
              msg"Cannot find operator `$op` in the context"
            }, opVar.toLoc)
          case S(td) if td.positionals.length === 2 =>
            val (subPatterns, bindings) = desugarPositionals(
              scrutinee,
              lhs :: rhs :: Nil,
              td.positionals
            )
            ConditionClause.MatchClass(makeScrutinee(scrutinee), opVar, bindings) ::
              destructSubPatterns(subPatterns)
          case S(td) =>
            val num = td.positionals.length
            throw IfDesugaringException.Single({
              import Message.MessageContext
              val expected = td.positionals.length
              msg"${td.kind.str} `$op` expects ${expected.toString} ${
                "parameter".pluralize(expected)
              } but found two parameters"
            }, app.toLoc)
        }
      // This case handles tuple destructions.
      // x is (a, b, c)
      case Bra(_, Tup(elems)) =>
        val (subPatterns, bindings) = desugarPositionals(
          scrutinee,
          elems.iterator.map(_._2.value),
          1.to(elems.length).map("_" + _).toList
        )
        ConditionClause.MatchTuple(makeScrutinee(scrutinee), elems.length, bindings) ::
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
        case isApp @ App(
          App(Var("is"),
              Tup((_ -> Fld(_, _, scrutinee)) :: Nil)),
          Tup((_ -> Fld(_, _, pattern)) :: Nil)
        ) => destructPattern(scrutinee, pattern)(ctx, raise, implicitly, isApp.toLoc)
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
      * @param rootLoc the location of the `IfOpApp`
      */
    def desugarMatchBranch(
      scrutinee: Term,
      body: IfBody \/ Statement,
      partialPattern: PartialTerm,
      collectedConditions: ConjunctedConditions,
    )(implicit interleavedLets: Buffer[(Bool, Var, Term)], rootLoc: Opt[Loc]): Unit =
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
                val partialTerm = PartialTerm.Total(testTerms.last, testTerms.last.toLoc.toList)
                desugarIfBody(consequent, partialTerm, conditions)
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
        case R(statement) => throw IfDesugaringException.Single({
          import Message.MessageContext
          msg"Illegal interleaved statement ${statement.toString}"
        }, statement.toLoc)
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
        case IfOpApp(scrutinee, isVar @ Var("is"), IfBlock(lines)) =>
          val interleavedLets = Buffer.empty[(Bool, Var, Term)]
          // We don't need to include the entire `IfOpApp` because it might be
          // very long... Indicating the beginning of the match is enough.
          val matchRootLoc = (scrutinee.toLoc, isVar.toLoc) match {
            case (S(first), S(second)) => S(Loc(first.spanStart, second.spanEnd, first.origin))
            case (_, _) => N
          }
          lines.foreach(desugarMatchBranch(scrutinee, _, PartialTerm.Empty, acc)(interleavedLets, matchRootLoc))
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

/**
  * Why we need a dedicated class for this?
  * Because the scrutinee might comes from different structures.
  * 1. Terms. E.g. `if x is A and y is B then ...`
  * 2. `IfOpApp`. In this case, the scrutinee is indicate by the `IfOpApp`.
  *    ```
  *    if x is
  *      A then ...
  *      B then ...
  *    ```
  * 3. `IfOpsApp`. In this case, the scrutinee may span multiple lines.
  *    ```
  *    if x
  *      is A then ...
  *    ```
  * 4. Nested pattern.
  *    ```
  *    if x is
  *      Left(Some(y)) then ...
  *    ```
  */
abstract class ScrutineeSource {
  protected def computeLoc: Opt[Loc]
  
  lazy val toLoc: Opt[Loc] = computeLoc
}

object ScrutineeSource {
  /**
    * The scrutinee is from a term.
    *
    * @param app the double applications
    */
  final case class Term(app: App) extends ScrutineeSource {
    override protected def computeLoc: Opt[Loc] = app.toLoc // TODO
  }

  final case class OpApp(body: IfOpApp) extends ScrutineeSource {
    override protected def computeLoc: Opt[Loc] =
      (body.lhs.toLoc, body.op.toLoc) match {
        case (S(lhs), S(rhs)) => S(lhs ++ rhs)
        case (_, _)           => N
      }
  }

  final case class OpsApp(body: IfOpsApp, line: Var -> IfBody) extends ScrutineeSource {
    override protected def computeLoc: Opt[Loc] = ???
  }

  final case class Nested(app: App) extends ScrutineeSource {
    override protected def computeLoc: Opt[Loc] = ???
  }
}

// The point is to remember where does the scrutinee come from.
// Is it from nested patterns? Or is it from a `IfBody`?
final case class Scrutinee(local: Opt[Var], term: Term) {
  var matchRootLoc: Opt[Loc] = N
  var localPatternLoc: Opt[Loc] = N

  override def toString: String =
    (local match {
      case N => ""
      case S(Var(alias)) => s"$alias @ "
    }) + s"$term"
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

  def separate(conditions: ConjunctedConditions, expectedScrutinee: Scrutinee): Opt[(MatchClass, ConjunctedConditions)] = {
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

    // println(s"Searching $expectedScrutinee in $conditions")
    rec(Nil, conditions._1).map { case (past, wanted, remaining) =>
      // println("Found!")
      (wanted, (past ::: remaining, conditions._2))
    }
  }

  final case class MatchClass(
    scrutinee: Scrutinee,
    className: Var,
    fields: List[Str -> Var]
  ) extends ConditionClause

  final case class MatchTuple(
    scrutinee: Scrutinee,
    arity: Int,
    fields: List[Str -> Var]
  ) extends ConditionClause

  final case class BooleanTest(test: Term) extends ConditionClause

  def print(println: (=> Any) => Unit, cnf: Ls[ConjunctedConditions -> Term]): Unit = {
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
            s"«$scrutinee is $className»"
          case ConditionClause.MatchTuple(scrutinee, arity, fields) =>
            s"«$scrutinee is Tuple#$arity»"
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

// FIXME: It seems the `locations` here does not really work.
// It's not used right now.
// Becuase we will split the term by `and`.
// We'd better precisely track detailed locations of each parts.
sealed abstract class PartialTerm(val locations: Ls[Loc]) {
  def addTerm(term: Term): PartialTerm.Total
  def addOp(op: Var): PartialTerm.Half
  def addTermOp(term: Term, op: Var): PartialTerm.Half =
    this.addTerm(term).addOp(op)

  protected final def prependLocation(loc: Opt[Loc]): Ls[Loc] =
    loc.fold(locations)(_ :: locations)
  protected final def prependLocations(locs: Opt[Loc]*): Ls[Loc] =
    locs.iterator.flatten.toList ::: locations
}

class PartialTermError(term: PartialTerm, message: Str) extends Error(message)

object PartialTerm {
  import UltimateConditions._

  final case object Empty extends PartialTerm(Nil) {
    override def addTerm(term: Term): Total = Total(term, prependLocation(term.toLoc))
    override def addOp(op: Var): Half =
      throw new PartialTermError(this, s"expect a term but operator $op was given")
  }

  final case class Total(val term: Term, override val locations: Ls[Loc]) extends PartialTerm(locations) {
    override def addTerm(term: Term): Total =
      throw new PartialTermError(this, s"expect an operator but term $term was given")
    override def addOp(op: Var): Half = Half(term, op, prependLocation(op.toLoc))
  }

  final case class Half(lhs: Term, op: Var, override val locations: Ls[Loc]) extends PartialTerm(locations) {
    override def addTerm(rhs: Term): Total = op match {
      case isVar @ Var("is") =>
        // Special treatment for pattern matching.
        val (pattern, extraTestOpt) = separatePattern(rhs)
        val assertion = mkBinOp(lhs, isVar, pattern)
        extraTestOpt match {
          case N => Total(assertion, prependLocation(pattern.toLoc))
          case S(extraTest) => Total(
            mkBinOp(assertion, Var("and"), extraTest),
            prependLocation(extraTest.toLoc)
          )
        }
      case _ =>
        val (realRhs, extraExprOpt) = separatePattern(rhs)
        val leftmost = mkBinOp(lhs, op, realRhs)
        Total(
          extraExprOpt.fold(leftmost){ mkBinOp(leftmost, Var("and"), _) },
          prependLocations(realRhs.toLoc, extraExprOpt.flatMap(_.toLoc))
        )
    }
    override def addOp(op: Var): Half =
      throw new PartialTermError(this, s"expect a term but operator $op was given")
  }
}

abstract class IfDesugaringException extends Throwable {
  def report(typer: Typer)(implicit raise: Diagnostic => Unit): typer.SimpleType
}

object IfDesugaringException {
  final case class Single(message: Message, location: Opt[Loc]) extends IfDesugaringException {
    override def report(typer: Typer)(implicit raise: Diagnostic => Unit): typer.SimpleType = {
      typer.err(message, location)
    }
  }
  final case class Multiple(messages: Ls[Message -> Opt[Loc]]) extends IfDesugaringException {
    override def report(typer: Typer)(implicit raise: Diagnostic => Unit): typer.SimpleType = {
      typer.err(messages)
    }
  }
}

object UltimateConditions {
  def showScrutinee(scrutinee: Scrutinee): Str =
    s"«${scrutinee.term}»" + (scrutinee.local match {
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

sealed abstract class MutCaseOf extends WithBindings {
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

  def checkExhaustive(t: MutCaseOf, parentOpt: Opt[MutCaseOf])(implicit scrutineePatternMap: MutMap[Term, MutSet[Var]]): Unit = {
    t match {
      case _: Consequent => ()
      case MissingCase =>
        import Message.MessageContext
        parentOpt match {
          case S(IfThenElse(test, whenTrue, whenFalse)) =>
            if (whenFalse === t) {
              throw IfDesugaringException.Single(msg"Missing the otherwise case of test ${test.toString}", test.toLoc)
            } else {
              ???
            }
          case S(Match(_, _, _)) => ???
          case S(Consequent(_)) | S(MissingCase) | N => die
        }
      case IfThenElse(condition, whenTrue, whenFalse) =>
        checkExhaustive(whenTrue, S(t))
        checkExhaustive(whenFalse, S(t))
      case Match(scrutinee, branches, default) =>
        scrutineePatternMap.get(scrutinee.term) match {
          case N => throw new Error(s"unreachable case: unknown scrutinee ${scrutinee.term}")
          case S(patterns) =>
            val missingCases = patterns.subtractAll(branches.iterator.map {
              case Branch(classNameVar -> _, _) => classNameVar
            })
            if (!missingCases.isEmpty) {
              throw IfDesugaringException.Multiple({
                import Message.MessageContext
                val numMissingCases = missingCases.size
                (msg"The match is not exhaustive." -> scrutinee.matchRootLoc) ::
                  (msg"The pattern at this position misses ${numMissingCases.toString} ${"case".pluralize(numMissingCases)}." -> scrutinee.term.toLoc) ::
                  missingCases.iterator.zipWithIndex.map { case (classNameVar, index) =>
                    val progress = s"[Missing Case ${index + 1}/$numMissingCases]"
                    msg"$progress The case `${classNameVar.name}` is missing, which first appears here." -> classNameVar.toLoc  
                  }.toList
              })
            }
        }
        default.foreach(checkExhaustive(_, S(t)))
        branches.foreach { case Branch(_, consequent) =>
          checkExhaustive(consequent, S(t))
        }
    }
  }

  def summarizePatterns(t: MutCaseOf): MutMap[Term, MutSet[Var]] = {
    val scrutineePatternMap = MutMap.empty[Term, MutSet[Var]]
    def rec(t: MutCaseOf): Unit =
      t match {
        case Consequent(term) => ()
        case MissingCase => ()
        case IfThenElse(_, whenTrue, whenFalse) =>
          rec(whenTrue)
          rec(whenFalse)
        case Match(scrutinee, branches, _) =>
          branches.foreach {
            case Branch((classNameVar: Var) -> _, consequent) =>
              scrutineePatternMap.getOrElseUpdate(scrutinee.term, MutSet.empty) += classNameVar
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
    scrutinee: Scrutinee,
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
            Case(className, mkLetFromFields(scrutinee.local.getOrElse(scrutinee.term), fields.toList, cases.toTerm), rec(next))
          case Nil =>
            wildcard match {
              case N => NoCases
              case S(mutCaseOf) => Wildcard(mutCaseOf.toTerm)
            }
        }
      val cases = rec(branches.toList)
      val resultTerm = scrutinee.local match {
        case N => CaseOf(scrutinee.term, cases)
        case S(aliasVar) => Let(false, aliasVar, scrutinee.term, CaseOf(aliasVar, cases))
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

    override def toTerm: Term = {
      import Message.MessageContext
      throw IfDesugaringException.Single(msg"missing a default branch", N)
    }
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
