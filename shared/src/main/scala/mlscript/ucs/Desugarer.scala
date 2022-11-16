package mlscript.ucs

import scala.collection.mutable.{Map => MutMap}
import scala.collection.mutable.Buffer

import mlscript._, utils._, shorthands._
import helpers._

/**
  * This class contains main desugaring methods.
  */
class Desugarer extends TypeDefs { self: Typer =>
  import Clause.{Conjunction, MatchClass, MatchTuple, BooleanTest}

  type FieldAliasMap = MutMap[Term, MutMap[Str, Var]]

  private var idLength: Int = 0

  def freshName: String = {
    val res = s"tmp$idLength"
    idLength += 1
    res
  }

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
      (implicit ctx: Ctx, raise: Raise, aliasMap: FieldAliasMap, matchRootLoc: Opt[Loc]): Ls[Clause] = {
    subPatterns.iterator.flatMap[Clause] {
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
  def makeScrutinee(term: Term, isMultiLineMatch: Bool)(implicit matchRootLoc: Opt[Loc]): Scrutinee =
    trace(s"Making a scrutinee for $term") {
      val res = term match {
        case _: Var => Scrutinee(N, term)
        case _ =>
          Scrutinee(
            S(localizedScrutineeMap.getOrElseUpdate(term, {
              Var(freshName).withLoc(term.toLoc)
            })),
            term,
          )
      }
      res.isMultiLineMatch = isMultiLineMatch
      res.matchRootLoc = matchRootLoc
      res
    }()

  /**
    * Destruct nested patterns to a list of simple condition with bindings.
    *
    * @param scrutinee the scrutinee of the pattern matching
    * @param pattern the pattern we will destruct
    * @param raise the `Raise` function
    * @param aliasMap the field alias map
    * @param matchRootLoc the location of the root of the pattern matching
    * @param fragments fragment term that used to construct the given pattern.
    *   It is used to tracking locations.
    * @param isMultiLineMatch whether the scrutinee is in multi-line pattern match.
    *   For example,
    *   ```
    *   if x is
    *     A then "x is A!"
    *     B then "x is B"
    *   ```
    *   is multi-line pattern match. Whereas `if x is Foo then 1 else 0` is not.
    * @return a list of simple condition with bindings. This method does not
    * return `ConjunctedCondition` because conditions built from nested patterns
    * do not contain interleaved let bindings.
    */
  private def destructPattern
      (scrutinee: Term, pattern: Term, isMultiLineMatch: Bool = false)
      (implicit ctx: Ctx,
                raise: Raise,
                aliasMap: FieldAliasMap,
                matchRootLoc: Opt[Loc],
                fragments: Ls[Term] = Nil): Ls[Clause] = {
    // This piece of code is use in two match cases.
    def desugarTuplePattern(tuple: Tup): Ls[Clause] = {
      val (subPatterns, bindings) = desugarPositionals(
        scrutinee,
        tuple.fields.iterator.map(_._2.value),
        1.to(tuple.fields.length).map("_" + _).toList
      )
      val clause = Clause.MatchTuple(
        makeScrutinee(scrutinee, isMultiLineMatch),
        tuple.fields.length,
        bindings
      )
      clause.locations = collectLocations(scrutinee)
      clause :: destructSubPatterns(subPatterns)
    }
    pattern match {
      // This case handles top-level wildcard `Var`.
      // We don't make any conditions in this level.
      case Var("_") => Nil
      // This case handles literals.
      // x is true | x is false | x is 0 | x is "text" | ...
      case literal @ (Var("true") | Var("false") | _: Lit) =>
        val test = mkBinOp(scrutinee, Var("=="), literal)
        Clause.BooleanTest(test) :: Nil
      // This case handles simple class tests.
      // x is A
      case classNameVar @ Var(className) =>
        ctx.tyDefs.get(className) match {
          case N => throw DesugaringException.Single({
            import Message.MessageContext
            msg"Cannot find the constructor `$className` in the context"
          }, classNameVar.toLoc)
          case S(_) => 
            val clause = Clause.MatchClass(makeScrutinee(scrutinee, isMultiLineMatch), classNameVar, Nil)
            println(s"Build a Clause.MatchClass from $scrutinee where pattern is $classNameVar")
            clause.locations = collectLocations(scrutinee)
            clause :: Nil
        }
      // This case handles classes with destruction.
      // x is A(r, s, t)
      case app @ App(classNameVar @ Var(className), Tup(args)) =>
        ctx.tyDefs.get(className) match {
          case N =>
            throw DesugaringException.Single({
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
              val clause = Clause.MatchClass(makeScrutinee(scrutinee, isMultiLineMatch), classNameVar, bindings)
              println(s"Build a Clause.MatchClass from $scrutinee where pattern is $pattern")
              println(s"Fragments: $fragments")
              clause.locations = pattern.toLoc.toList ::: collectLocations(scrutinee)
              println(s"The locations of the clause: ${clause.locations}")
              clause :: destructSubPatterns(subPatterns)
            } else {
              throw DesugaringException.Single({
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
            throw DesugaringException.Single({
              import Message.MessageContext
              msg"Cannot find operator `$op` in the context"
            }, opVar.toLoc)
          case S(td) if td.positionals.length === 2 =>
            val (subPatterns, bindings) = desugarPositionals(
              scrutinee,
              lhs :: rhs :: Nil,
              td.positionals
            )
            val clause = Clause.MatchClass(makeScrutinee(scrutinee, isMultiLineMatch), opVar, bindings)
            println(s"Build a Clause.MatchClass from $scrutinee where operator is $opVar")
            clause.locations = collectLocations(scrutinee)
            clause :: destructSubPatterns(subPatterns)
          case S(td) =>
            val num = td.positionals.length
            throw DesugaringException.Single({
              import Message.MessageContext
              val expected = td.positionals.length
              msg"${td.kind.str} `$op` expects ${expected.toString} ${
                "parameter".pluralize(expected)
              } but found two parameters"
            }, app.toLoc)
        }
      // This case handles **direct** tuple destructions.
      // x is (a, b, c)
      case Bra(_, tuple: Tup) => desugarTuplePattern(tuple)
      // This case handles **nested** tuple destructions.
      // x is Cons((x, y), Nil)
      case tuple: Tup => desugarTuplePattern(tuple)
      // What else?
      case _ => throw new Exception(s"illegal pattern: ${mlscript.codegen.Helpers.inspect(pattern)}")
    }
  }

  /**
    * Collect `Loc`s from a synthetic term.
    *
    * @param term the root of the synthetic term
    * @param fragments the fragment terms
    * @return all original locations
    */
  def collectLocations(term: Term)(implicit fragments: Ls[Term]): Ls[Loc] = {
    val locations = Buffer.empty[Loc]
    def rec(term: Term): Unit = term.children.foreach { located =>
      if (fragments.contains(located)) locations ++= located.toLoc
    }
    locations.toList
  }


  def desugarIf
      (body: IfBody, fallback: Opt[Term])
      (implicit ctx: Ctx, raise: Raise)
  : Ls[Conjunction -> Term] = {
    // We allocate temporary variable names for nested patterns.
    // This prevents aliasing problems.
    implicit val scrutineeFieldAliasMap: FieldAliasMap = MutMap.empty
    // A list of flattened if-branches.
    val branches = Buffer.empty[Conjunction -> Term]

    /**
      * Translate a list of atomic UCS conditions.
      * What is atomic? No "and".
      *
      * @param ts a list of atomic UCS conditions
      * @return a list of `Condition`
      */
    def desugarConditions(ts: Ls[Term])(implicit fragments: Ls[Term] = Nil): Ls[Clause] =
      ts.flatMap {
        case isApp @ App(
          App(Var("is"),
              Tup((_ -> Fld(_, _, scrutinee)) :: Nil)),
          Tup((_ -> Fld(_, _, pattern)) :: Nil)
        ) => destructPattern(scrutinee, pattern)(ctx, raise, implicitly, isApp.toLoc)
        case test =>
          val clause = Clause.BooleanTest(test)
          clause.locations = collectLocations(test)
          Iterable.single(clause)
      }

    import Clause.withBindings

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
      collectedConditions: Conjunction,
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
          val patternConditions = destructPattern(scrutinee, partialPattern.addTerm(patternPart).term, true)
          val conditions = Conjunction.concat(
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
          val tailTestConditions = optTests.fold(Nil: Ls[Clause])(x => desugarConditions(splitAnd(x)))
          val conditions = Conjunction.concat(
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
              val conditions = Conjunction.concat(
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
              val conditions = Conjunction.concat(
                collectedConditions,
                withBindings((patternConditions ::: middleConditions, Nil))
              )
              opsRhss.foreach { case op -> consequent =>
                // TODO: Use lastOption
                val last = testTerms.last
                val partialTerm = PartialTerm.Total(last, last :: Nil)
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
        case R(statement) => throw DesugaringException.Single({
          import Message.MessageContext
          msg"Illegal interleaved statement ${statement.toString}"
        }, statement.toLoc)
      }
    def desugarIfBody
      (body: IfBody, expr: PartialTerm, acc: Conjunction)
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
          val totalTerm = expr.addTerm(term)
          // “Atomic” means terms that do not contain `and`.
          val atomicTerms = splitAnd(totalTerm.term)
          val fragments = atomicTerms ::: totalTerm.fragments
          val newClauses = desugarConditions(atomicTerms)(fragments)
          val conjunction = Conjunction.concat(acc, (newClauses, Nil))
          branches += (withBindings(conjunction) -> consequent)
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
          val conditions = Conjunction.concat(
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

  import MutCaseOf.{MutCase, IfThenElse, Match, MissingCase, Consequent}

  /**
  * A map from each scrutinee term to all its cases and the first `MutCase`.
  */
  type ExhaustivenessMap = Map[Str \/ Int, Map[Var, MutCase]]

  type MutExhaustivenessMap = MutMap[Str \/ Int, MutMap[Var, MutCase]]

  def getScurtineeKey(scrutinee: Scrutinee)(implicit ctx: Ctx, raise: Raise): Str \/ Int = {
    scrutinee.term match {
      // The original scrutinee is an reference.
      case v @ Var(name) => 
        ctx.env.get(name) match {
          case S(VarSymbol(_, defVar)) => defVar.uid.fold[Str \/ Int](L(v.name))(R(_))
          case S(_) | N                => L(v.name)
        }
      // Otherwise, the scrutinee has a temporary name.
      case _ =>
        scrutinee.local match {
          case N => throw new Error("check your `makeScrutinee`")
          case S(localNameVar) => L(localNameVar.name)
        }
    }
  }

  /**
    * Check the exhaustiveness of the given `MutCaseOf`.
    *
    * @param t the mutable `CaseOf` of 
    * @param parentOpt
    * @param scrutineePatternMap
    */
  def checkExhaustive
    (t: MutCaseOf, parentOpt: Opt[MutCaseOf])
    (implicit scrutineePatternMap: ExhaustivenessMap, ctx: Ctx, raise: Raise)
  : Unit = {
    println(s"Check exhaustiveness of ${t.describe}")
    indent += 1
    try t match {
      case _: Consequent => ()
      case MissingCase =>
        import Message.MessageContext
        parentOpt match {
          case S(IfThenElse(test, whenTrue, whenFalse)) =>
            if (whenFalse === t) {
              throw DesugaringException.Single(msg"Missing the otherwise case of test ${test.toString}", test.toLoc)
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
        scrutineePatternMap.get(getScurtineeKey(scrutinee)) match {
          // Should I call `die` here?
          case N => throw new Error(s"unreachable case: unknown scrutinee ${scrutinee.term}")
          case S(patternMap) =>
            println(s"The exhaustiveness map is ${scrutineePatternMap}")
            println(s"The scrutinee key is ${getScurtineeKey(scrutinee)}")
            println("Pattern map of the scrutinee:")
            if (patternMap.isEmpty)
              println("<Empty>")
            else
              patternMap.foreach { case (key, mutCase) => println(s"- $key => $mutCase")}
            // Filter out missing cases in `branches`.
            val missingCases = patternMap.removedAll(branches.iterator.map {
              case MutCase(classNameVar -> _, _) => classNameVar
            })
            println(s"Number of missing cases: ${missingCases.size}")
            if (!missingCases.isEmpty) {
              throw DesugaringException.Multiple({
                import Message.MessageContext
                val numMissingCases = missingCases.size
                (msg"The match is not exhaustive." -> scrutinee.matchRootLoc) ::
                  (msg"The scrutinee at this position misses ${numMissingCases.toString} ${
                    "case".pluralize(numMissingCases)
                  }." -> scrutinee.term.toLoc) ::
                  missingCases.iterator.zipWithIndex.flatMap { case ((classNameVar, firstMutCase), index) =>
                    val progress = s"[Missing Case ${index + 1}/$numMissingCases]"
                    (msg"$progress `${classNameVar.name}`" -> N) ::
                      firstMutCase.locations.iterator.zipWithIndex.map { case (loc, index) =>
                        (if (index === 0) msg"It first appears here." else msg"continued at") -> S(loc)
                      }.toList
                  }.toList
              })
            }
        }
        // if (branches.length === 1 && scrutinee.isMultiLineMatch && default.isEmpty) {
        //   import Message.MessageContext
        //   raise(WarningReport({
        //     msg"This scrutinee has only one case." -> scrutinee.matchRootLoc
        //   } :: Nil))
        // }
        default.foreach(checkExhaustive(_, S(t)))
        branches.foreach { case MutCase(_, consequent) =>
          checkExhaustive(consequent, S(t))
        }
    } finally indent -= 1
  }

  def summarizePatterns(t: MutCaseOf)(implicit ctx: Ctx, raise: Raise): ExhaustivenessMap = {
    val m = MutMap.empty[Str \/ Int, MutMap[Var, MutCase]]
    def rec(t: MutCaseOf): Unit = {
      println(s"Summarize pattern of ${t.describe}")
      indent += 1
      try t match {
        case Consequent(term) => ()
        case MissingCase => ()
        case IfThenElse(_, whenTrue, whenFalse) =>
          rec(whenTrue)
          rec(whenFalse)
        case Match(scrutinee, branches, _) =>
          val key = getScurtineeKey(scrutinee)
          branches.foreach { mutCase =>
            val patternMap = m.getOrElseUpdate( key, MutMap.empty)
            if (!patternMap.contains(mutCase.patternFields._1)) {
              patternMap += ((mutCase.patternFields._1, mutCase))
            }
            rec(mutCase.consequent)
          }
      } finally indent -= 1
    }
    rec(t)
    Map.from(m.iterator.map { case (key, patternMap) => key -> Map.from(patternMap) })
  }
}
