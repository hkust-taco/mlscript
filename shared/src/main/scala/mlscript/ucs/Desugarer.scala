package mlscript.ucs

import scala.collection.mutable.{Map => MutMap}
import scala.collection.mutable.Buffer

import mlscript._, utils._, shorthands._
import helpers._
import Message.MessageContext
import mlscript.ucs.MutCaseOf.MutCase.Constructor

/**
  * This class contains main desugaring methods.
  */
class Desugarer extends TypeDefs { self: Typer =>
  var dbgUCS: Bool = false
  private def printlnUCS(msg: => Any): Unit = if (dbgUCS) println(msg)
  private def traceUCS[T](pre: => String)(thunk: => T)(post: T => String = noPostTrace) =
    if (dbgUCS) trace(pre)(thunk)(post) else thunk

  import Desugarer.{ExhaustivenessMap, SubClassMap, SuperClassMap}
  import Clause.{MatchClass, MatchTuple, BooleanTest}

  type FieldAliasMap = MutMap[SimpleTerm, MutMap[Str, Var]]

  private var idLength: Int = 0

  private def makeName: String = {
    val name = s"tmp$idLength"
    idLength += 1
    name
  }

  private def freshName(implicit ctx: Ctx): String = {
    var res = makeName
    while (ctx.env.contains(res)) {
      res = makeName
    }
    res
  }

  private type MutExhaustivenessMap = MutMap[Str \/ Int, MutMap[Either[Int, SimpleTerm], Buffer[Loc]]]

  private def addToExhaustivenessMap(scrutinee: Scrutinee, loc: Iterable[Loc])
      (implicit ctx: Ctx, raise: Raise, map: MutExhaustivenessMap) = {
    map.getOrElseUpdate(getScurtineeKey(scrutinee), MutMap.empty)
  }

  private def addToExhaustivenessMap(scrutinee: Scrutinee, tupleArity: Int, loc: Iterable[Loc])
      (implicit ctx: Ctx, raise: Raise, map: MutExhaustivenessMap) = {
    map.getOrElseUpdate(getScurtineeKey(scrutinee), MutMap.empty)
      .getOrElseUpdate(L(tupleArity), Buffer.empty) ++= loc
  }
  private def addToExhaustivenessMap(scrutinee: Scrutinee, litOrCls: SimpleTerm, loc: Iterable[Loc])
      (implicit ctx: Ctx, raise: Raise, map: MutExhaustivenessMap) = {
    map.getOrElseUpdate(getScurtineeKey(scrutinee), MutMap.empty)
      .getOrElseUpdate(R(litOrCls), Buffer.empty) ++= loc
  }

  /**
    * 
    *
    * @param scrutinee the scrutinee of the pattern matching
    * @param params parameters provided by the 
    * @param positionals the corresponding field names of each parameter
    * @param aliasMap a map used to cache each the alias of each field
    * @param matchRootLoc the location to the root of the match
    * @return two mappings: one is (variable -> sub-pattern), the other is (positional name -> variable)
    */
  private def desugarPositionals
    (scrutinee: Scrutinee, params: IterableOnce[Term], positionals: Ls[Str])
    (implicit ctx: Ctx, aliasMap: FieldAliasMap): (Ls[Var -> Term], Ls[Str -> Var]) = {
    val subPatterns = Buffer.empty[(Var, Term)]
    val bindings = params.iterator.zip(positionals).flatMap {
      // `x is A(_)`: ignore this binding
      case (Var("_"), _) => N
      // `x is A(value)`: generate bindings directly
      case (nameVar @ Var(n), fieldName) if (n.headOption.exists(_.isLower)) =>
        S(fieldName -> nameVar)
      // `x is B(A(x))`: generate a temporary name
      // use the name in the binding, and destruct sub-patterns
      case (pattern: Term, fieldName) =>
        // We should always use the same temporary for the same `fieldName`.
        // This uniqueness is decided by (scrutinee, fieldName).
        val alias = aliasMap
          .getOrElseUpdate(scrutinee.reference, MutMap.empty)
          .getOrElseUpdate(fieldName, Var(freshName).desugaredFrom(pattern))
        subPatterns += ((alias, pattern))
        S(fieldName -> alias)
    }.toList
    (subPatterns.toList, bindings)
  }

  /**
    * Desugar sub-patterns from fields to conditions.
    *
    * @param subPatterns a list of field name -> pattern term
    * @param ctx the typing context
    * @param aliasMap the field alias map
    * @return desugared conditions representing the sub-patterns
    */
  private def destructSubPatterns(scrutinee: Scrutinee, subPatterns: Iterable[Var -> Term])
      (implicit ctx: Ctx, raise: Raise, exhaustivenessMap: MutExhaustivenessMap, aliasMap: FieldAliasMap): Ls[Clause] = {
    subPatterns.iterator.flatMap[Clause] { case (subScrutinee, subPattern) =>
      destructPattern(makeScrutinee(subScrutinee, scrutinee.matchRootLoc), subPattern, false)
    }.toList
  }

  // `IdentityHashMap` is a workaround.
  private val localizedScrutineeMap = new java.util.IdentityHashMap[Term, Var]

  /**
    * Create a `Scrutinee`. If the `term` is a simple expression (e.g. `Var` or
    * `Lit`), we do not create a local alias. Otherwise, we create a local alias
    * to avoid unnecessary computations.
    *
    * @param term the term in the local scrutinee position
    * @param matchRootLoc the caller is expect to be in a match environment,
    * this parameter indicates the location of the match root
    */
  private def makeScrutinee(term: Term, matchRootLoc: Opt[Loc])(implicit ctx: Ctx): Scrutinee =
    traceUCS(s"Making a scrutinee for `$term`") {
      term match {
        case _: Var =>
          printlnUCS(s"The scrutinee does not need an alias.")
          Scrutinee(N, term)(matchRootLoc)
        case _ =>
          val localizedName = makeLocalizedName(term)
          printlnUCS(s"The scrutinee needs an alias: $localizedName")
          Scrutinee(S(localizedName), term)(matchRootLoc)
      }
    }()

  /**
    * Create a fresh name for scrutinee to be localized.
    *
    * @param scrutinee the term of the scrutinee
    * @param ctx the context
    * @return the fresh name, as `Var`
    */
  private def makeLocalizedName(scrutinee: Term)(implicit ctx: Ctx): Var = 
    if (localizedScrutineeMap.containsKey(scrutinee)) {
      localizedScrutineeMap.get(scrutinee)
    } else {
      val v = Var(freshName).desugaredFrom(scrutinee)
      localizedScrutineeMap.put(scrutinee, v)
      v
    }

  /**
    * Destruct nested patterns to a list of simple condition with bindings.
    *
    * @param scrutinee the scrutinee of the pattern matching
    * @param pattern the pattern we will destruct
    * @param isTopLevel whether this pattern just follows the `is` operator
    * @param raise the `Raise` function
    * @param aliasMap the field alias map
    * @param matchRootLoc the location of the root of the pattern matching
    * @param fragments fragment term that used to construct the given pattern.
    *   It is used to tracking locations.
    * @return a list of simple condition with bindings. This method does not
    * return `ConjunctedCondition` because conditions built from nested patterns
    * do not contain interleaved let bindings.
    */
  private def destructPattern
      (scrutinee: Scrutinee, pattern: Term, isTopLevel: Bool)
      (implicit ctx: Ctx,
                raise: Raise,
                exhaustivenessMap: MutExhaustivenessMap,
                aliasMap: FieldAliasMap,
                fragments: Ls[Term] = Nil): Ls[Clause] =
  trace(s"[Desugarer.destructPattern] scrutinee = ${scrutinee.term}; pattern = $pattern") {
    // This piece of code is use in two match cases.
    def desugarTuplePattern(tuple: Tup): Ls[Clause] = {
      val (subPatterns, bindings) = desugarPositionals(
        scrutinee,
        tuple.fields.iterator.map(_._2.value),
        1.to(tuple.fields.length).map("_" + _).toList
      )
      addToExhaustivenessMap(scrutinee, tuple.fields.length, tuple.toLoc)
      Clause.MatchTuple(
        scrutinee,
        tuple.fields.length,
        bindings
      )(collectLocations(scrutinee.term)) :: destructSubPatterns(scrutinee, subPatterns)
    }
    pattern match {
      // This case handles top-level wildcard `Var`.
      // We don't make any conditions in this level.
      case wildcard @ Var("_") if isTopLevel =>
        addToExhaustivenessMap(scrutinee, wildcard.toLoc)
        Clause.MatchAny(scrutinee)(wildcard.toLoc.toList) :: Nil
      // If it's not top-level, wildcard means we don't care.
      case Var("_") => Nil
      // This case handles literals.
      // x is true | x is false | x is 0 | x is "text" | ...
      case literal: Var if literal.name === "true" || literal.name === "false" =>
        addToExhaustivenessMap(scrutinee, literal, literal.toLoc)
        val clause = Clause.MatchLiteral(scrutinee, literal)(scrutinee.term.toLoc.toList ::: literal.toLoc.toList)
        clause.bindings = scrutinee.asBinding.toList
        printlnUCS(s"Add bindings to the clause: ${scrutinee.asBinding}")
        clause :: Nil
      case literal: Lit =>
        addToExhaustivenessMap(scrutinee, literal, literal.toLoc)
        val clause = Clause.MatchLiteral(scrutinee, literal)(scrutinee.term.toLoc.toList ::: literal.toLoc.toList)
        clause.bindings = scrutinee.asBinding.toList
        printlnUCS(s"Add bindings to the clause: ${scrutinee.asBinding}")
        clause :: Nil
      // This case handles name binding.
      // x is a
      case bindingVar @ Var(bindingName) if bindingName.headOption.exists(_.isLower) =>
        val locations = scrutinee.term.toLoc.toList ::: bindingVar.toLoc.toList
        if (isTopLevel) {
          // If the binding name is at the top-level. We create decision path like
          // ... /\ x is any /\ a = x /\ ...
          addToExhaustivenessMap(scrutinee, bindingVar.toLoc)
          Clause.MatchAny(scrutinee)(locations) ::
            Clause.Binding(bindingVar, scrutinee.reference, !isTopLevel)(locations) ::
            Nil
        } else {
          // Otherwise, we just create the binding.
          Clause.Binding(bindingVar, scrutinee.term, !isTopLevel)(locations) :: Nil
        }
      // This case handles simple class tests.
      // x is A
      case classNameVar @ Var(className) =>
        ctx.tyDefs.get(className).orElse(ctx.get(className)) match {
          case S(ti: LazyTypeInfo) if (ti.kind is Cls) || (ti.kind is Mod) =>
          case S(ti: LazyTypeInfo) if (ti.kind is Trt) => throw new DesugaringException({
            msg"Cannot match on trait `$className`"
          }, classNameVar.toLoc)
          case S(_: TypeDef) =>
          case _ => throw new DesugaringException({
            msg"Cannot find constructor `$className` in scope"
          }, classNameVar.toLoc)
        }
        printlnUCS(s"Build a Clause.MatchClass from $scrutinee where pattern is $classNameVar")
        addToExhaustivenessMap(scrutinee, classNameVar, classNameVar.toLoc)
        Clause.MatchClass(scrutinee, classNameVar, Nil)(collectLocations(scrutinee.term)) :: Nil
      // This case handles classes with destruction.
      // x is A(r, s, t)
      case app @ App(classNameVar @ Var(className), Tup(args)) =>
        ctx.tyDefs.get(className).map(td => (td.kind, td.positionals))
            .orElse(ctx.get(className) match {
              case S(ti: DelayedTypeInfo) if ti.decl.kind is Cls =>
                S((ti.decl.kind, ti.typedParams.map(_._1.name)))
              case S(CompletedTypeInfo(td: TypedNuCls)) =>
                S((td.decl.kind, td.params.map(_._1.name)))
              case _ => throw new DesugaringException(msg"Illegal pattern `$className`", classNameVar.toLoc)
            }) match {
          case N =>
            throw new DesugaringException({
              msg"Cannot find class `$className` in scope"
            }, classNameVar.toLoc)
          case S((kind, positionals)) =>
            if (args.length === positionals.length) {
              val (subPatterns, bindings) = desugarPositionals(
                scrutinee,
                args.iterator.map(_._2.value),
                positionals
              )
              addToExhaustivenessMap(scrutinee, classNameVar, app.toLoc)
              val clause = Clause.MatchClass(scrutinee, classNameVar, bindings)(pattern.toLoc.toList ::: collectLocations(scrutinee.term))
              printlnUCS(s"Build a Clause.MatchClass from $scrutinee where pattern is $pattern")
              printlnUCS(s"Fragments: $fragments")
              printlnUCS(s"The locations of the clause: ${clause.locations}")
              clause :: destructSubPatterns(scrutinee, subPatterns)
            } else {
              throw new DesugaringException({
                val expected = positionals.length
                val actual = args.length
                msg"${kind.str} $className expects ${expected.toString} ${
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
            throw new DesugaringException({
              msg"Cannot find operator `$op` in the context"
            }, opVar.toLoc)
          case S(td) if td.positionals.length === 2 =>
            val (subPatterns, fields) = desugarPositionals(
              scrutinee,
              lhs :: rhs :: Nil,
              td.positionals
            )
            addToExhaustivenessMap(scrutinee, opVar, app.toLoc)
            val clause = Clause.MatchClass(scrutinee, opVar, fields)(collectLocations(scrutinee.term))
            printlnUCS(s"Build a Clause.MatchClass from $scrutinee where operator is $opVar")
            clause :: destructSubPatterns(scrutinee, subPatterns)
          case S(td) =>
            val num = td.positionals.length
            throw new DesugaringException({
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
      case _ => throw new DesugaringException(msg"illegal pattern", pattern.toLoc)
    }
  }("[Desugarer.destructPattern] Result: " + _.mkString(", "))

  /**
    * Collect `Loc`s from a synthetic term.
    *
    * @param term the root of the synthetic term
    * @param fragments the fragment terms
    * @return all original locations
    */
  private def collectLocations(term: Term)(implicit fragments: Ls[Term]): Ls[Loc] = {
    val locations = Buffer.empty[Loc]
    def rec(term: Term): Unit = term.children.foreach { located =>
      if (fragments.contains(located)) locations ++= located.toLoc
    }
    locations.toList
  }

  private def unfoldNestedIf(elf: If, acc: Ls[IfBody] = Nil): (IfBody, Opt[Term]) =
    traceUCS("[unfoldNestedIf]") {
      elf.els match {
        case S(innerElf: If) => unfoldNestedIf(innerElf, elf.body :: acc)
        case default if acc.isEmpty => (elf.body, default)
        case default =>
          val lines = (elf.body :: acc).reverseIterator.flatMap {
            case IfBlock(subLines) => subLines
            case other => Iterable.single(L(other))
          }.toList
          (IfBlock(lines), default)
      }
    }(r => s"[unfoldNestedIf] (${r._1.getClass().getSimpleName()}, ${r._2})")

  /**
    * The entry point of UCS desugarer.
    *
    * @param elf the root `If` term
    * @param ctx the typing context
    * @param raise the function to raise errors
    * @return the desugared term
    */
  def desugarIf(elf: If)(implicit ctx: Ctx, raise: Raise): Term = traceUCS("[desugarIf]") {
    val superClassMap = getClassHierarchy()
    Desugarer.printGraph(superClassMap, printlnUCS, "Super-class map", "<:")
    val subClassMap = Desugarer.reverseGraph(superClassMap)
    Desugarer.printGraph(subClassMap, printlnUCS, "Sub-class map", ":>")
    val (body, els) = unfoldNestedIf(elf)
    val exhaustivenessMap: MutExhaustivenessMap = MutMap.empty
    printlnUCS("### Desugar the UCS to decision paths ###")
    val paths = desugarIf(body, els)(ctx, raise, exhaustivenessMap)
    printlnUCS("Exhaustiveness map")
    if (exhaustivenessMap.isEmpty)
      printlnUCS("  * <No entries>")
    else
      exhaustivenessMap.foreach { case (symbol, patternMap) =>
        printlnUCS(s"  * Patterns of $symbol")
        if (patternMap.isEmpty)
          printlnUCS(s"    + <No patterns>")
        else
          patternMap.foreach { case (pattern, locations) =>
            val first = pattern match {
              case Left(tupleArity) => s"()^$tupleArity"
              case Right(litOrCls) => litOrCls.toString()
            }
            val second = locations.mkString("[", ", ", "]")
            printlnUCS(s"    + $first -> $second")
          }
      }
    printlnUCS("### Build a case tree from decision paths ###")
    val imExhaustivenessMap = Map.from(exhaustivenessMap.iterator.map { case (k, m) => k -> Map.from(m) })
    val caseTree = buildCaseTree(paths)(raise, getScurtineeKey, imExhaustivenessMap, superClassMap)
    printlnUCS("### Checking exhaustiveness of the case tree ###")
    checkExhaustive(caseTree, N)(ctx, raise, imExhaustivenessMap, subClassMap)
    printlnUCS("### Construct a term from the case tree ###")
    val desugared = constructTerm(caseTree)
    println(s"Desugared term: ${desugared.print(false)}")
    elf.desugaredTerm = S(desugared)
    desugared
  }()


  private def desugarIf
      (body: IfBody, fallback: Opt[Term])
      (implicit ctx: Ctx, raise: Raise, exhaustivenessMap: MutExhaustivenessMap)
  : Ls[Conjunction -> Term] = traceUCS(s"[desugarIf] with fallback $fallback") {
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
              Tup(_ -> Fld(_, _, scrutinee) :: Nil)),
          Tup(_ -> Fld(_, _, pattern) :: Nil)
        ) =>
          // This is an inline `x is Class` match test.
          val inlineMatchLoc = isApp.toLoc
          val inlineScrutinee = makeScrutinee(scrutinee, inlineMatchLoc)
          destructPattern(inlineScrutinee, pattern, true)(ctx, raise, exhaustivenessMap, scrutineeFieldAliasMap)
        case test =>
          val clause = Clause.BooleanTest(test)(collectLocations(test))
          Iterable.single(clause)
      }

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
      scrutinee: Scrutinee,
      body: IfBody \/ Statement,
      partialPattern: PartialTerm,
      collectedConditions: Conjunction,
    )(implicit interleavedLets: Buffer[LetBinding]): Unit = traceUCS[Unit]("[desugarMatchBranch]") {
      body match {
        // This case handles default branches. For example,
        // if x is
        //   A(...) then ...
        //   else ...
        case L(els @ IfElse(consequent)) =>
          // Because this pattern matching is incomplete, it's not included in
          // `acc`. This means that we discard this incomplete pattern matching.
          // branches += (collectedConditions + Clause.MatchNot(scrutinee)(els.toLoc.toList) -> consequent)
          branches += (collectedConditions -> consequent)
        // This case handles default branches indicated by wildcards.
        // if x is
        //   A(...) then ...
        //   _      then ...
        case L(IfThen(wildcard @ Var("_"), consequent)) =>
          // branches += (collectedConditions + Clause.MatchNot(scrutinee)(wildcard.toLoc.toList) -> consequent)
          branches += (collectedConditions -> consequent)
        // if x is
        //   A(...) then ...         // Case 1: no conjunctions
        //   B(...) and ... then ... // Case 2: more conjunctions
        case L(IfThen(patTest, consequent)) =>
          val (patternPart, extraTestOpt) = separatePattern(patTest)
          val clauses = destructPattern(scrutinee, partialPattern.addTerm(patternPart).term, true)
          val conditions = collectedConditions + Conjunction(clauses, Nil).withBindings
          printlnUCS(s"Result: " + conditions.clauses.mkString(", "))
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
          val patternConditions = destructPattern(scrutinee, pattern, true)
          val tailTestConditions = optTests.fold(Nil: Ls[Clause])(x => desugarConditions(splitAnd(x)))
          val conditions =
            collectedConditions + Conjunction(patternConditions ::: tailTestConditions, Nil).withBindings
          desugarIfBody(consequent, PartialTerm.Empty, conditions)
        case L(IfOpApp(patLhs, op, consequent)) =>
          separatePattern(patLhs) match {
            // Case 1.
            // The pattern is completed. There is also a conjunction.
            // So, we need to separate the pattern from remaining parts.
            case (pattern, S(extraTests)) =>
              val patternConditions = destructPattern(scrutinee, pattern, true)
              val extraConditions = desugarConditions(splitAnd(extraTests))
              val conditions = 
                collectedConditions + Conjunction(patternConditions ::: extraConditions, Nil).withBindings
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
              val patternConditions = destructPattern(scrutinee, partialPattern.addTerm(patternPart).term, true)
              val testTerms = splitAnd(extraTests)
              val middleConditions = desugarConditions(testTerms.init)
              val conditions =
                collectedConditions + Conjunction(patternConditions ::: middleConditions, Nil).withBindings
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
        case L(IfLet(_, _, _, _)) =>
          TODO("please add this rare case to test files")
        // This case handles interleaved lets.
        case R(NuFunDef(S(isRec), nameVar, _, L(term))) =>
          interleavedLets += (LetBinding(LetBinding.Kind.InterleavedLet, isRec, nameVar, term))
        // Other statements are considered to be ill-formed.
        case R(statement) => throw new DesugaringException({
          msg"Illegal interleaved statement ${statement.toString}"
        }, statement.toLoc)
      }
    }(_ => "[desugarMatchBranch]")

    def desugarIfBody
      (body: IfBody, expr: PartialTerm, acc: Conjunction)
      (implicit interleavedLets: Buffer[LetBinding])
    : Unit = traceUCS[Unit]("[desugarIfBody]") {
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
          branches += ((acc + newClauses).withBindings -> consequent)
        // This is the entrance of the Simple UCS.
        case IfOpApp(scrutineePart, isVar @ Var("is"), IfBlock(lines)) =>
          // Create a synthetic scrutinee term by combining accumulated partial
          // term with the new part.
          val scrutineeTerm = expr.addTerm(scrutineePart).term
          // We don't need to include the entire `IfOpApp` because it might be
          // very long... Indicating the beginning of the match is enough.
          val matchRootLoc = (scrutineeTerm.toLoc, isVar.toLoc) match {
            case (S(first), S(second)) => S(first ++ second)
            case (_, _)                => N
          }
          val scrutinee = makeScrutinee(scrutineeTerm, matchRootLoc)
          // If there is an alias, we should add the let bindings to clauses.
          val conjunction = scrutinee.local match {
            case S(alias) => acc
            case N        => acc
          }
          // We need to make a snapshot because the sub-branches mutate the buffer.
          // But these changes should not affect sibling branches.
          val interleavedLetsSnapshot = interleavedLets.clone()
          // Iterate each match case.
          lines.foreach {
            desugarMatchBranch(scrutinee, _, PartialTerm.Empty, conjunction)(interleavedLetsSnapshot)
          }
        // For example: "if x == 0 and y is \n ..."
        case IfOpApp(testPart, Var("and"), consequent) =>
          val conditions = acc + (desugarConditions(expr.addTerm(testPart).term :: Nil))
          desugarIfBody(consequent, PartialTerm.Empty, conditions)
        // Otherwise, this is not a pattern matching.
        // We create a partial term from `lhs` and `op` and dive deeper.
        case IfOpApp(lhs, op, body) =>
          desugarIfBody(body, expr.addTermOp(lhs, op), acc)
        // This case is rare. Let's put it aside.
        case IfLet(isRec, name, rhs, body) =>
          TODO("please add this rare case to test files")
        // In this case, the accumulated partial term is discarded.
        // We create a branch directly from accumulated conditions.
        case IfElse(term) => branches += (acc.withBindings -> term)
        case IfBlock(lines) =>
          lines.foreach {
            case L(subBody) => desugarIfBody(subBody, expr, acc)
            case R(NuFunDef(S(isRec), nameVar, _, L(term))) =>
              printlnUCS(s"Found interleaved binding ${nameVar.name}")
              interleavedLets += LetBinding(LetBinding.Kind.InterleavedLet, isRec, nameVar, term)
            case R(_) =>
              throw new Error("unexpected statements at desugarIfBody")
          }
      }
    }(_ => "[desugarIfBody]")

    // Top-level interleaved let bindings.
    val interleavedLets = Buffer.empty[LetBinding]
    desugarIfBody(body, PartialTerm.Empty, Conjunction.empty)(interleavedLets)
    // Add the fallback case to conjunctions if there is any.
    fallback.foreach { branches += Conjunction.empty -> _ }
    printlnUCS("Decision paths:")
    branches.foreach { case conjunction -> term =>
      printlnUCS(s"+ $conjunction => $term")
    }
    branches.toList
  }(r => s"[desugarIf] produces ${r.size} ${"path".pluralize(r.size)}")

  import MutCaseOf.{MutCase, IfThenElse, Match, MissingCase, Consequent}

  /**
    * This method obtains a proper key of the given scrutinee
    * for memorizing patterns belongs to the scrutinee.
    *
    * @param scrutinee the scrutinee
    * @param ctx the context
    * @param raise we need this to raise errors.
    * @return the variable name or the variable ID
    */
  private def getScurtineeKey(scrutinee: Scrutinee)(implicit ctx: Ctx, raise: Raise): Str \/ Int =
    traceUCS(s"[getScrutineeKey] $scrutinee") {
      scrutinee.term match {
        // The original scrutinee is an reference.
        case v @ Var(name) => 
          printlnUCS("The original scrutinee is an reference.")
          ctx.env.get(name) match {
            case S(VarSymbol(_, defVar)) => defVar.uid.fold[Str \/ Int](L(v.name))(R(_))
            case S(_) | N                => L(v.name)
          }
        // Otherwise, the scrutinee was localized because it might be effectful.
        case _ =>
          printlnUCS("The scrutinee was localized because it might be effectful.")
          scrutinee.local match {
            case N => throw new Error("check your `makeScrutinee`")
            case S(localNameVar) => L(localNameVar.name)
          }
      }
    }()

  /**
    * Check the exhaustiveness of the given `MutCaseOf`.
    *
    * @param t the mutable `CaseOf` of 
    * @param parentOpt the parent `MutCaseOf`
    * @param scrutineePatternMap the exhaustiveness map
    */
  private def checkExhaustive
    (t: MutCaseOf, parentOpt: Opt[MutCaseOf])
    (implicit ctx: Ctx,
              raise: Raise,
              exhaustivenessMap: ExhaustivenessMap,
              subClassMap: SubClassMap)
  : Unit = traceUCS(s"[checkExhaustive] ${t.describe}") {
    t match {
      case _: Consequent => ()
      case MissingCase =>
        parentOpt match {
          case S(IfThenElse(test, whenTrue, whenFalse)) =>
            if (whenFalse === t)
              throw new DesugaringException(msg"The case when this is false is not handled: ${test.toString}", test.toLoc)
            else
              lastWords("`MissingCase` are not supposed to be the true branch of `IfThenElse`")
          case S(Match(_, _, _)) =>
            lastWords("`MissingCase` are not supposed to be a case of `Match`")
          case S(Consequent(_)) | S(MissingCase) | N => die // unreachable
        }
      case IfThenElse(condition, whenTrue, whenFalse) =>
        checkExhaustive(whenFalse, S(t))
        checkExhaustive(whenTrue, S(t))
      case Match(scrutinee, branches, default) =>
        exhaustivenessMap.get(getScurtineeKey(scrutinee)) match {
          case N => lastWords(s"unreachable case: unknown scrutinee ${scrutinee.term}")
          case S(_) if default.isDefined =>
            printlnUCS("The match has a default branch. So, it is always safe.")
          case S(patternMap) =>
            printlnUCS(s"The exhaustiveness map is")
            exhaustivenessMap.foreach { case (key, matches) =>
              printlnUCS(s"- $key -> ${matches.keysIterator.mkString(", ")}")
            }
            printlnUCS(s"The scrutinee key is ${getScurtineeKey(scrutinee)}")
            printlnUCS("Pattern map of the scrutinee:")
            if (patternMap.isEmpty)
              printlnUCS("<Empty>")
            else
              patternMap.foreach { case (key, mutCase) => printlnUCS(s"- $key => $mutCase")}
            // Compute all classes that can be covered by this match.
            val coveredClassNames = Set.from[String](branches.iterator.flatMap {
              case MutCase.Literal(_, _) => Nil
              case Constructor(Var(className) -> _, _) =>
                subClassMap.get(className).fold[List[String]](Nil)(identity)
            })
            printlnUCS("The match can cover following classes")
            printlnUCS(coveredClassNames.mkString("{", ", ", "}"))
            // Filter out missing cases in `branches`.
            val missingCases = patternMap.removedAll(branches.iterator.map {
              case MutCase.Literal(lit, _) => R(lit)
              case MutCase.Constructor(classNameVar -> _, _) =>
                classNameVar.name.split('#').toList match {
                  case "Tuple" :: ns :: Nil =>
                    ns.toIntOption match {
                      case N => R(classNameVar)
                      case S(arity) => L(arity)
                    }
                  case _ => R(classNameVar)
                }
            }).filter { // Remove classes subsumed by super classes.
              case R(Var(className)) -> _ =>
                !coveredClassNames.contains(className)
              case L(_) -> _ => true // Tuple. Don't remove.
              case R(_) -> _ => true // Literals. Don't remove.
            }
            printlnUCS("Missing cases")
            missingCases.foreach { case (key, m) =>
              printlnUCS(s"- $key -> ${m}")
            }
            if (!missingCases.isEmpty) {
              throw new DesugaringException({
                val numMissingCases = missingCases.size
                (msg"The match is not exhaustive." -> scrutinee.matchRootLoc) ::
                  (msg"The scrutinee at this position misses ${numMissingCases.toString} ${
                    "case".pluralize(numMissingCases)
                  }." -> scrutinee.term.toLoc) ::
                  missingCases.iterator.zipWithIndex.flatMap { case ((pattern, locations), index) =>
                    val patternName = pattern match {
                      case L(tupleArity) => s"$tupleArity-ary tuple"
                      case R(litOrCls) => litOrCls.toString()
                    }
                    val progress = s"[Missing Case ${index + 1}/$numMissingCases]"
                    (msg"$progress `$patternName`" -> N) ::
                      locations.iterator.zipWithIndex.map { case (loc, index) =>
                        (if (index === 0) msg"It first appears here." else msg"And here.") -> S(loc)
                      }.toList
                  }.toList
              })
            }
        }
        default.foreach(checkExhaustive(_, S(t)))
        branches.foreach { branch =>
          checkExhaustive(branch.consequent, S(t))
        }
    }
  }(_ => s"[checkExhaustive] ${t.describe}")

  /**
    * Make a term from a mutable case tree.
    * This should be called after exhaustiveness checking.
    *
    * @param m the mutable case tree
    * @param ctx the context
    * @return the case expression
    */
  private def constructTerm(m: MutCaseOf)(implicit ctx: Ctx): Term = traceUCS("[constructTerm]") {
    /**
     * Reconstruct case branches.
     */
    def rec2(xs: Ls[MutCase])(
      implicit defs: Set[Var], scrutinee: Scrutinee, wildcard: Option[MutCaseOf]
    ): CaseBranches = {
      xs match {
        case MutCase.Constructor(className -> fields, cases) :: next =>
          printlnUCS(s"• Constructor pattern: $className(${fields.iterator.map(x => s"${x._1} -> ${x._2}").mkString(", ")})")
          // TODO: expand bindings here
          val consequent = rec(cases)(defs ++ fields.iterator.map(_._2))
          Case(className, mkLetFromFields(scrutinee, fields.toList, consequent match {
            case _: Let => Blk(consequent :: Nil)
            case _ => consequent
          }), rec2(next))
        case MutCase.Literal(literal, cases) :: next =>
          printlnUCS(s"• Literal pattern: $literal")
          Case(literal, rec(cases), rec2(next))
        case Nil =>
          wildcard match {
            case None => 
              printlnUCS("• No wildcard branch")
              NoCases
            case Some(value) =>
              printlnUCS("• Wildcard branch")
              Wildcard(rec(value))
          }
      }
    }
    /**
     * Reconstruct the entire match.
     */
    def rec(m: MutCaseOf)(implicit defs: Set[Var]): Term = traceUCS(s"[rec] ${m.describe} -| {${defs.mkString(", ")}}") {
      m match {
        case Consequent(term) =>
          mkBindings(m.getBindings.toList, term, defs)
        case Match(scrutinee, branches, wildcard) =>
          printlnUCS("• Owned let bindings")
          val ownedBindings = m.getBindings.iterator.filterNot {
            _.kind === LetBinding.Kind.InterleavedLet
          }.toList
          if (ownedBindings.isEmpty)
            printlnUCS("  * <No bindings>")
          else
            ownedBindings.foreach { case LetBinding(kind, _, name, value) =>
              printlnUCS(s"  * ($kind) $name = $value")
            }
          // Collect interleaved let bindings from case branches.
          // Because they should be declared before 
          val interleavedBindings = branches.iterator.map(_.consequent).concat(wildcard).flatMap(_.getBindings).filter {
            _.kind === LetBinding.Kind.InterleavedLet
          }.toList
          printlnUCS("• Collect interleaved let bindings from case branches")
          if (interleavedBindings.isEmpty)
            printlnUCS("  * <No interleaved bindings>")
          else
            interleavedBindings.foreach { case LetBinding(_, _, name, value) =>
              printlnUCS(s"  * $name = $value")
            }
          val resultTerm = if (branches.isEmpty) {
            // If the match does not have any branches.
            wildcard match {
              case None =>
                // Internal error!
                printlnUCS("• The match has neither branches nor default case")
                throw new DesugaringException({
                  import Message.MessageContext
                  msg"found an empty match"
                }, scrutinee.term.toLoc)
              case Some(default) =>
                printlnUCS("• Degenerated case: the match only has a wildcard")
                val subTerm = rec(default)
                scrutinee.local match {
                  case N => subTerm
                  case S(aliasVar) => Let(false, aliasVar, scrutinee.term, subTerm)
                }
            }
          } else {
            // If the match has some branches.
            printlnUCS("• The match has some case branches")
            val cases = traceUCS("• For each case branch"){
              rec2(branches.toList)(defs, scrutinee, wildcard)
            }(_ => "• End for each")
            scrutinee.local match {
              case N => CaseOf(scrutinee.term, cases)
              case S(aliasVar) => Let(false, aliasVar, scrutinee.term, CaseOf(aliasVar, cases))
            }
          }
          mkBindings(ownedBindings, mkBindings(interleavedBindings, resultTerm, defs), defs)
        case MissingCase =>
          import Message.MessageContext
          throw new DesugaringException(msg"missing a default branch", N)
        case IfThenElse(condition, whenTrue, whenFalse) =>
          val falseBody = mkBindings(whenFalse.getBindings.toList, rec(whenFalse)(defs ++ whenFalse.getBindings.iterator.map(_.name)), defs)
          val trueBody = mkBindings(whenTrue.getBindings.toList, rec(whenTrue)(defs ++ whenTrue.getBindings.iterator.map(_.name)), defs)
          val falseBranch = Wildcard(falseBody)
          val trueBranch = Case(Var("true"), trueBody, falseBranch)
          CaseOf(condition, trueBranch)
      }
    }()
    val term = rec(m)(Set.from(m.getBindings.iterator.map(_.name)))
    // Create immutable map from the mutable map.
    mkBindings(m.getBindings.toList, term, Set.empty)
  }(_ => "[constructTerm]")

  /**
    * Generate a chain of field selection to the given scrutinee.
    *
    * @param scrutinee the pattern matching scrutinee
    * @param fields a list of pairs from field names to binding names
    * @param body the final body
    */
  private def mkLetFromFields(scrutinee: Scrutinee, fields: Ls[Str -> Var], body: Term)(implicit ctx: Ctx): Term = {
    def rec(scrutineeReference: SimpleTerm, fields: Ls[Str -> Var]): Term =
      fields match {
        case Nil => body
        case (field -> (aliasVar @ Var(alias))) :: tail =>
          scrutinee.term match {
            // Check if the scrutinee is a `Var` and its name conflicts with
            // one of the positionals. If so, we create an alias and extract
            // fields by selecting the alias.
            case Var(scrutineeName) if alias === scrutineeName =>
              val scrutineeAlias = Var(freshName)
              Let(
                false,
                scrutineeAlias,
                scrutinee.reference,
                Let(
                  false,
                  aliasVar,
                  Sel(scrutineeAlias, Var(field)).desugaredFrom(scrutinee.term),
                  rec(scrutineeAlias, tail)
                )
              )
            case _ =>
              Let(
                false,
                aliasVar,
                Sel(scrutineeReference, Var(field)).desugaredFrom(scrutinee.term),
                rec(scrutineeReference, tail)
              )
          }
      }
    rec(scrutinee.reference, fields)
  }

  private def buildCaseTree
    (paths: Ls[Conjunction -> Term])
    (implicit raise: Diagnostic => Unit,
              getScrutineeKey: Scrutinee => Str \/ Int,
              exhaustivenessMap: ExhaustivenessMap,
              superClassMap: SuperClassMap)
  : MutCaseOf = traceUCS("[buildCaseTree]") {
    paths match {
      case Nil => MissingCase
      case (conditions -> term) :: remaining =>
        val root = MutCaseOf.buildFirst(conditions, term)
        traceUCS("*** Initial tree ***") {
          MutCaseOf.show(root).foreach(printlnUCS(_))
        }()
        remaining.foreach { path =>
          root.merge(path)
          printlnUCS(s"*** Merging `${path._1} => ${path._2}` ***")
          traceUCS("*** Updated tree ***") {
            MutCaseOf.show(root).foreach(printlnUCS(_))
          }()
        }
        root
    }
  }(_ => "[buildCaseTree]")

  private def getClassHierarchy()(implicit ctx: Ctx): SuperClassMap =
    traceUCS("[getClassHierarchy]") {
      // ctx.tyDefs
      val superClassMap = ctx.tyDefs.iterator
        .filter(_._2.toLoc.isDefined)
        .map { case (className, td) =>
          className -> td.baseClasses.iterator.map(_.name).toList
        } |> Map.from
      Desugarer.transitiveClosure(superClassMap)
    }(_ => "[getClassHierarchy]")
}

object Desugarer {
  /**
    * A map from each scrutinee term to all its cases and the first `MutCase`.
    */
  type ExhaustivenessMap = Map[Str \/ Int, Map[Either[Int, SimpleTerm], Buffer[Loc]]]

  type SuperClassMap = Map[String, List[String]]

  type SubClassMap = Map[String, List[String]]

  def reverseGraph(graph: Map[String, List[String]]): Map[String, List[String]] = {
    graph.iterator.flatMap { case (source, targets) => targets.iterator.map(_ -> source) }
      .foldLeft(Map.empty[String, List[String]]) { case (map, target -> source) =>
        map.updatedWith(target) {
          case None => Some(source :: Nil)
          case Some(sources) => Some(source :: sources)
        }
      }
  }

  def transitiveClosure(graph: Map[String, List[String]]): Map[String, List[String]] = {
    def dfs(vertex: String, visited: Set[String]): Set[String] = {
      if (visited.contains(vertex)) visited
      else graph.getOrElse(vertex, List())
        .foldLeft(visited + vertex)((acc, v) => dfs(v, acc))
    }

    graph.keys.map { vertex =>
      val closure = dfs(vertex, Set())
      vertex -> (closure - vertex).toList
    }.toMap
  }

  def printGraph(graph: Map[String, List[String]], print: (=> Any) => Unit, title: String, arrow: String): Unit = {
    print(s"• $title")
    if (graph.isEmpty)
      print("  + <Empty>")
    else
      graph.foreach { case (source, targets) =>
        print(s"  + $source $arrow " + {
          if (targets.isEmpty) s"{}"
          else targets.mkString("{ ", ", ", " }")
        })
      }
  }
}