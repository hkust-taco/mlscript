package mlscript.ucs.old

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import scala.collection.immutable.Set
import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer}

import mlscript.ucs.helpers._
import MutCaseOf.Consequent
import scala.collection.immutable
import Desugarer.{ExhaustivenessMap, SuperClassMap}
import Clause.MatchAny

sealed abstract class MutCaseOf extends WithBindings {
  def kind: Str = {
    import MutCaseOf._
    this match {
      case Consequent(_) => "Consequent"
      case MissingCase => "MissingCase"
      case IfThenElse(_, _, _) => "IfThenElse"
      case Match(_, _, _) => "Match"
    }
  }

  def duplicate(): MutCaseOf

  def fill(subTree: MutCaseOf): Unit

  def describe: Str

  def isComplete: Bool

  def isExhaustive(implicit getScrutineeKey: Scrutinee => Str \/ Int,
                            exhaustivenessMap: ExhaustivenessMap): Bool

  def tryMerge
      (branch: Conjunction -> Term)
      (implicit raise: Diagnostic => Unit,
                getScrutineeKey: Scrutinee => Str \/ Int,
                exhaustivenessMap: ExhaustivenessMap,
                superClassMap: SuperClassMap): Unit =
    merge(branch)(_ => (), getScrutineeKey, exhaustivenessMap, superClassMap)

  def merge
    (branch: Conjunction -> Term)
    (implicit raise: Diagnostic => Unit,
              getScrutineeKey: Scrutinee => Str \/ Int,
              exhaustivenessMap: ExhaustivenessMap,
              superClassMap: SuperClassMap): Unit

  def mergeDefault
    (bindings: Ls[LetBinding], default: Term)
    (implicit raise: Diagnostic => Unit,
              getScrutineeKey: Scrutinee => Str \/ Int,
              exhaustivenessMap: ExhaustivenessMap,
              superClassMap: SuperClassMap): Int

  // TODO: Make it immutable.
  var locations: Ls[Loc] = Nil
}

object MutCaseOf {
  def showScrutinee(scrutinee: Scrutinee): Str =
    s"«${scrutinee.term.showDbg}»" + (scrutinee.local match {
      case N => ""
      case S(Var(alias)) => s" as $alias"
    })

  def show(t: MutCaseOf): Ls[Str] = {
    val lines = Buffer.empty[String]
    def rec(t: MutCaseOf, indent: Int): Unit = {
      val baseIndent = "  " * indent
      lazy val bindingLines = t.getBindings.iterator.map {
        case LetBinding(_, recursive, Var(name), term) =>
          // Show bindings
          s"[binding $name = ${term.showDbg}]"
      }.toList
      t match {
        case IfThenElse(condition, whenTrue, whenFalse) =>
          // Output the `whenTrue` with the prefix "if".
          bindingLines.foreach { lines += baseIndent + _ }
          lines += baseIndent + s"if «${condition.showDbg}»"
          rec(whenTrue, indent + 1)
          // Output the `whenFalse` case with the prefix "else".
          lines += s"${baseIndent}else"
          rec(whenFalse, indent + 1)
        case Match(scrutinee, branches, default) =>
          bindingLines.foreach { lines += baseIndent + _ }
          lines += baseIndent + showScrutinee(scrutinee) + " match"
          branches.foreach {
            case MutCase.Literal(literal, consequent) =>
              lines += s"$baseIndent  case ${literal.showDbg} =>"
              rec(consequent, indent + 1)
            case MutCase.Constructor(Var(className) -> fields, consequent) =>
              lines += s"$baseIndent  case $className =>"
              fields.foreach { case (field, Var(alias)) =>
                // Show pattern bindings.
                lines += s"$baseIndent    [pattern $alias = ${scrutinee.reference.showDbg}.$field]"
              }
              rec(consequent, indent + 2)
          }
          default.foreach { consequent =>
            lines += s"$baseIndent  default"
            rec(consequent, indent + 2)
          }
        case Consequent(term) =>
          bindingLines.foreach { lines += baseIndent + _ }
          lines += s"$baseIndent«${term.showDbg}»"
        case MissingCase =>
          bindingLines.foreach { lines += baseIndent + _ }
          lines += s"$baseIndent<missing case>"
      }
    }
    rec(t, 0)
    lines.toList
  }

  sealed abstract class MutCase {
    var consequent: MutCaseOf

    @inline
    def isComplete: Bool = consequent.isComplete

    def duplicate(): MutCase

    /**
      * Check whether this case can cover the expected class or literal.
      *
      * @param expected the expected class name or literal
      * @param superClassMap a map from each class to its super classes
      * @return whether the given pattern can be covered by this case
      */
    def covers(expected: SimpleTerm)(implicit superClassMap: SuperClassMap): Bool

    // Note 1
    // ======
    // A `MutCase` may come from one of two origins.
    // Direct patterns.
    // E.g. if x is Y then "aha" else "meh"
    //         ^^^^^^
    // Nested patterns.
    // E.g. if x is Right(Some(x)) then ...
    //                    ^^^^^^^
    // The goal is to accurately indicate where the pattern is declared.
    //
    // Note 2
    // ======
    // A `MutCase` may come from multiple locations.
    // That is why I'm using a `Set`.
    //
    val locations: MutSet[Loc] = MutSet.empty[Loc]
    def withLocation(locOpt: Opt[Loc]): MutCase = {
      locations ++= locOpt
      this
    }
    def withLocations(locs: IterableOnce[Loc]): MutCase = {
      locations ++= locs
      this
    }
  }

  object MutCase {
    final case class Literal(
      val literal: SimpleTerm,
      var consequent: MutCaseOf,
    ) extends MutCase {
      override def duplicate(): MutCase =
        Literal(literal, consequent.duplicate()).withLocations(locations)
      override def covers(expected: SimpleTerm)(implicit superClassMap: SuperClassMap): Bool =
        expected match {
          case _: Lit | Var("true") | Var("false") => expected === literal
          case Var(_) => false
        }
    }

    /**
      * MutCase is a _mutable_ representation of a case in `MutCaseOf.Match`.
      *
      * @param patternFields the alias to the fields
      * @param consequent the consequential `MutCaseOf`
      */
    final case class Constructor(
      val patternFields: Var -> Buffer[Str -> Var],
      var consequent: MutCaseOf,
    ) extends MutCase {
      override def duplicate(): MutCase =
        Constructor(patternFields.copy(_2 = patternFields._2.clone()), consequent.duplicate())
          .withLocations(locations)
      override def covers(expected: SimpleTerm)(implicit superClassMap: SuperClassMap): Bool =
        expected match {
          case lit: Lit => false
          case Var(tof) if tof === "true" || tof === "false" => false
          case Var(expectedClassName) if expectedClassName === patternFields._1.name => true
          case Var(expectedClassName) => 
            (superClassMap.get(expectedClassName) match {
              case Some(superClasses) => superClasses.contains(patternFields._1.name)
              case None =>
                // Should we raise?
                false
            })
        }
      def addFields(fields: Iterable[Str -> Var]): Unit =
        patternFields._2 ++= fields.iterator.filter(!patternFields._2.contains(_))
    }
  }

  import Clause.{MatchLiteral, MatchAny, MatchClass, MatchTuple, BooleanTest, Binding}

  // A short-hand for pattern matchings with only true and false branches.
  final case class IfThenElse(condition: Term, var whenTrue: MutCaseOf, var whenFalse: MutCaseOf) extends MutCaseOf {
    def describe: Str =
      s"IfThenElse(${condition.showDbg}, whenTrue = ${whenTrue.kind}, whenFalse = ${whenFalse.kind})"

    def duplicate(): MutCaseOf =
      IfThenElse(condition, whenTrue.duplicate(), whenFalse.duplicate())
        .withBindings(getBindings)

    override def fill(subTree: MutCaseOf): Unit = {
      whenTrue.fill(subTree)
      if (whenFalse === MissingCase)
        whenFalse = subTree
      else
        whenFalse.fill(subTree)
    }

    def isComplete: Bool = whenTrue.isComplete && whenFalse.isComplete

    def isExhaustive(implicit getScrutineeKey: Scrutinee => Str \/ Int,
                              exhaustivenessMap: ExhaustivenessMap): Bool =
      whenTrue.isExhaustive && whenFalse.isExhaustive

    def merge(branch: Conjunction -> Term)
        (implicit raise: Diagnostic => Unit,
                  getScrutineeKey: Scrutinee => Str \/ Int,
                  exhaustivenessMap: ExhaustivenessMap,
                  superClassMap: SuperClassMap): Unit =
      branch match {
        // The CC is a wildcard. So, we call `mergeDefault`.
        case Conjunction(Nil, trailingBindings) -> term =>
          if (mergeDefault(trailingBindings, term) === 0) {
            import Message.MessageContext
            raise(WarningReport(
              msg"Found a redundant else branch" -> term.toLoc :: Nil, newDefs = true))
          }
        // The CC is an if-then-else. We create a pattern match of true/false.
        case Conjunction((head @ BooleanTest(test)) :: tail, trailingBindings) -> term if test === condition =>
          // If the test is the same. So, we can insert the path to the true branch.
          whenTrue.addBindings(head.bindings)
          whenTrue.merge(Conjunction(tail, trailingBindings) -> term)
        // Otherwise, we try to insert to the true branch.
        case Conjunction(head :: _, _) -> _ =>
          whenTrue.tryMerge(branch)
          whenFalse match {
            case Consequent(_) =>
              raise(WarningReport(Message.fromStr("duplicated else in the if-then-else") -> N :: Nil,
                newDefs = true))
            case MissingCase =>
              whenFalse = buildFirst(branch._1, branch._2)
              whenFalse.addBindings(head.bindings)
            case _ => whenFalse.merge(branch)
          }
      }

    def mergeDefault(bindings: Ls[LetBinding], default: Term)
        (implicit raise: Diagnostic => Unit,
                  getScrutineeKey: Scrutinee => Str \/ Int,
                  exhaustivenessMap: ExhaustivenessMap,
                  superClassMap: SuperClassMap): Int = {
      whenTrue.mergeDefault(bindings, default) + {
        whenFalse match {
          case Consequent(term) => 0
          case MissingCase =>
            whenFalse = Consequent(default).withBindings(bindings)
            1
          case _: IfThenElse | _: Match => whenFalse.mergeDefault(bindings, default)
        }
      }
    }
  }
  final case class Match(
    scrutinee: Scrutinee,
    val branches: Buffer[MutCase],
    var wildcard: Opt[MutCaseOf]
  ) extends MutCaseOf {
    def describe: Str = {
      val n = branches.length
      s"Match($scrutinee, ${"branch".pluralize(n, true, true)}, ${
        wildcard.fold("no wildcard")(n => s"wildcard = ${n.kind}")
      })"
    }

    def duplicate(): MutCaseOf =
      Match(scrutinee, branches.map(_.duplicate()), wildcard.map(_.duplicate()))
        .withBindings(getBindings)

    override def fill(subTree: MutCaseOf): Unit = {
      branches.foreach(_.consequent.fill(subTree))
      wildcard.foreach(_.fill(subTree))
    }

    def isComplete: Bool =
      branches.forall(_.consequent.isComplete) && wildcard.forall(_.isComplete)

    def isExhaustive(implicit getScrutineeKey: Scrutinee => Str \/ Int,
                              exhaustivenessMap: ExhaustivenessMap): Bool = {
      exhaustivenessMap.get(getScrutineeKey(scrutinee)) match {
        case None => ??? // TODO: Raise.
        case Some(patternLocationsMap) =>
          // Find patterns that are not included in `branches`.
          patternLocationsMap.keysIterator.filterNot {
            case L(tupleArity) => branches.iterator.exists {
              case MutCase.Literal(_, _) => false
              case MutCase.Constructor(Var(className) -> _, _) =>
                className === s"Tuple#$tupleArity"
            }
            case R(litOrCls) => branches.iterator.exists {
              case MutCase.Literal(lit, _) => litOrCls === lit
              case MutCase.Constructor(cls -> _, _) => litOrCls === cls
            }
          }.isEmpty
      }
    }

    def merge(originalBranch: Conjunction -> Term)
        (implicit raise: Diagnostic => Unit,
                  getScrutineeKey: Scrutinee => Str \/ Int,
                  exhaustivenessMap: ExhaustivenessMap,
                  superClassMap: SuperClassMap): Unit = {
      // Remove let bindings that already has been declared.
      val branch = originalBranch._1.copy(clauses = originalBranch._1.clauses.filter {
        case Binding(name, value, false) if (getBindings.exists {
          case LetBinding(LetBinding.Kind.ScrutineeAlias, _, n, v) =>
            n === name && v === value
          case _ => false
        }) => false
        case _ => true
      }) -> originalBranch._2
      // Promote the match against the same scrutinee.
      branch._1.findClauseMatches(scrutinee) match {
        // No conditions against the same scrutinee.
        case N =>
          branch match {
            case Conjunction((head @ MatchTuple(scrutinee2, arity, fields)) :: tail, trailingBindings) -> term
                if scrutinee2 === scrutinee => // Same scrutinee!
              val tupleClassName = Var(s"Tuple#$arity") // TODO: Find a name known by Typer.
              branches.find(_.covers(tupleClassName)) match {
                // No such pattern. We should create a new one.
                case N | S(MutCase.Literal(_, _)) =>
                  val newBranch = buildFirst(Conjunction(tail, trailingBindings), term)
                  newBranch.addBindings(head.bindings)
                  branches += MutCase.Constructor(tupleClassName -> Buffer.from(fields), newBranch)
                    .withLocations(head.locations)
                // Found existing pattern.
                case S(branch: MutCase.Constructor) =>
                  branch.consequent.addBindings(head.bindings)
                  branch.addFields(fields)
                  branch.consequent.merge(Conjunction(tail, trailingBindings) -> term)
              }
            // A wild card case. We should propagate wildcard to every default positions.
            case Conjunction(Nil, trailingBindings) -> term =>
              if (mergeDefault(trailingBindings, term) === 0) {
                import Message.MessageContext
                raise(WarningReport(
                  msg"Found a redundant else branch" -> term.toLoc :: Nil,
                  newDefs = true))
              }
            // The conditions to be inserted does not overlap with me.
            case conjunction -> term =>
              branches.foreach {
                _.consequent.tryMerge(conjunction -> term)
              }
              wildcard match {
                // No wildcard. We will create a new one.
                case N => wildcard = S(buildFirst(conjunction, term))
                // There is a wildcard case. Just merge!
                case S(consequent) => consequent.merge(conjunction -> term)
              }
          }
        // Found a match condition against the same scrutinee
        case S((head @ MatchClass(_, className, fields)) -> remainingConditions) =>
          // Find all branches which can cover the `className`.
          val inclusiveBranches = branches.iterator.filter(_.covers(className))
          if (inclusiveBranches.isEmpty) {
            // No such pattern. We should create a new one.
            wildcard match {
              // If the wildcard branch is incomplete, there might be some
              // preemptive branches in front of this branch.
              case Some(default) if !default.isComplete =>
                val subTree = default.duplicate()
                subTree.fill(buildFirst(remainingConditions, branch._2))
                subTree.addBindings(head.bindings)
                branches += MutCase.Constructor(className -> Buffer.from(fields), subTree)
                  .withLocations(head.locations)
              case Some(_) | None =>
                val newBranch = buildFirst(remainingConditions, branch._2)
                newBranch.addBindings(head.bindings)
                branches += MutCase.Constructor(className -> Buffer.from(fields), newBranch)
                  .withLocations(head.locations)
            }
          } else {
            // Found some branches that can cover the `className`.
            inclusiveBranches.foreach {
              case MutCase.Literal(_, _) => () // This shouldn't happen.
              case matchedCase @ MutCase.Constructor(Var(branchClassName) -> _, _) =>
                if (branchClassName === className.name) {
                  // This branch exactly matches the given class name.
                  // So, we just do a simple merge.
                  // Merge interleaved bindings.
                  matchedCase.consequent.addBindings(head.bindings)
                  matchedCase.addFields(fields)
                  matchedCase.consequent.merge(remainingConditions -> branch._2)
                } else {
                  // This branch matches the super classes of the given class name.
                  // There will be refinement matches inside the consequent.
                  // Therefore, we should not merge with `remainingConditions`.
                  // Instead, we should use the original conjunction.
                  matchedCase.consequent.addBindings(head.bindings)
                  matchedCase.addFields(fields)
                  matchedCase.consequent.merge(branch)
                }
            }
          }
        case S((head @ MatchLiteral(_, literal)) -> remainingConditions) =>
          branches.find(_.covers(literal)) match {
            // No such pattern. We should create a new one.
            case N | S(MutCase.Constructor(_, _)) =>
              val newConsequent = buildFirst(remainingConditions, branch._2)
              newConsequent.addBindings(head.bindings)
              branches += MutCase.Literal(literal, newConsequent)
                .withLocations(head.locations)
            case S(matchCase: MutCase.Literal) =>
              // Merge interleaved bindings.
              matchCase.consequent.addBindings(head.bindings)
              matchCase.consequent.merge(remainingConditions -> branch._2)
          }
        case S((head @ MatchAny(_)) -> remainingConditions) =>
          // Existing branches may be complete but not exhaustive.
          // Find inexhaustiveness branches and try to merge.
          branches.iterator.filterNot(_.consequent.isExhaustive).foreach { 
            _.consequent.tryMerge(remainingConditions -> branch._2)
          }
          // Then, let's consider the wildcard branch.
          wildcard match {
            // No wildcard. We will create a new one.
            case N => wildcard = S(buildFirst(remainingConditions, branch._2))
            // There is a wildcard case. Just merge!
            case S(consequent) => consequent.merge(remainingConditions -> branch._2)
          }
      }
    }

    def mergeDefault(bindings: Ls[LetBinding], default: Term)
        (implicit raise: Diagnostic => Unit,
                  getScrutineeKey: Scrutinee => Str \/ Int,
                  exhaustivenessMap: ExhaustivenessMap,
                  superClassMap: SuperClassMap): Int = {
      branches.iterator.map {
        case MutCase.Constructor(_, consequent) => consequent.mergeDefault(bindings, default)
        case MutCase.Literal(_, consequent) => consequent.mergeDefault(bindings, default)
      }.sum + {
        wildcard match {
          case N =>
            wildcard = S(Consequent(default).withBindings(bindings))
            1
          case S(consequent) => consequent.mergeDefault(bindings, default)
        }
      }
    }
  }
  final case class Consequent(term: Term) extends MutCaseOf {
    def describe: Str = s"Consequent(${term.showDbg})"

    override def fill(subTree: MutCaseOf): Unit = ()

    override def duplicate(): MutCaseOf = Consequent(term).withBindings(getBindings)

    def isComplete: Bool = true

    def isExhaustive(implicit getScrutineeKey: Scrutinee => Str \/ Int,
                              exhaustivenessMap: ExhaustivenessMap): Bool = true

    def merge(branch: Conjunction -> Term)
        (implicit raise: Diagnostic => Unit,
                  getScrutineeKey: Scrutinee => Str \/ Int,
                  exhaustivenessMap: ExhaustivenessMap,
                  superClassMap: SuperClassMap): Unit =
      raise {
        import scala.collection.mutable.ListBuffer
        val buffer = ListBuffer.empty[Message -> Opt[Loc]]
        buffer += Message.fromStr("Found a duplicated branch") -> N
        buffer += Message.fromStr("This branch") -> {
          val (Conjunction(clauses, _) -> consequent) = branch
          consequent.toLoc
          // TODO: Make a complete location. 
          // clauses match {
          //   case head :: _ => head.
          //   case Nil => consequent.toLoc
          // }
        }
        buffer += Message.fromStr("is subsumed by the branch here.") -> term.toLoc
        WarningReport(buffer.toList, newDefs = true)
      }

    def mergeDefault(bindings: Ls[LetBinding], default: Term)
       (implicit raise: Diagnostic => Unit,
                  getScrutineeKey: Scrutinee => Str \/ Int,
                  exhaustivenessMap: ExhaustivenessMap,
                  superClassMap: SuperClassMap): Int = 0
  }
  final case object MissingCase extends MutCaseOf {
    def describe: Str = "MissingCase"

    override def duplicate() = MissingCase

    override def fill(subTree: MutCaseOf): Unit = ()

    def isComplete: Bool = false

    def isExhaustive(implicit getScrutineeKey: Scrutinee => Str \/ Int,
                              exhaustivenessMap: ExhaustivenessMap): Bool = false

    def merge(branch: Conjunction -> Term)
      (implicit raise: Diagnostic => Unit,
                getScrutineeKey: Scrutinee => Str \/ Int,
                exhaustivenessMap: ExhaustivenessMap,
                superClassMap: SuperClassMap): Unit =
      lastWords("`MissingCase` is a placeholder and cannot be merged")

    def mergeDefault(bindings: Ls[LetBinding], default: Term)
      (implicit raise: Diagnostic => Unit,
                getScrutineeKey: Scrutinee => Str \/ Int,
                exhaustivenessMap: ExhaustivenessMap,
                superClassMap: SuperClassMap): Int = 0
  }

  def buildFirst(conjunction: Conjunction, term: Term)
      (implicit getScrutineeKey: Scrutinee => Str \/ Int,
                exhaustivenessMap: ExhaustivenessMap,
                superClassMap: SuperClassMap): MutCaseOf = {
    def rec(conjunction: Conjunction): MutCaseOf = conjunction match {
      case Conjunction(head :: tail, trailingBindings) =>
        lazy val (beforeHeadBindings, afterHeadBindings) = head.bindings.partition {
          case LetBinding(LetBinding.Kind.InterleavedLet, _, _, _) => false
          case LetBinding(_, _, _, _) => true
        }
        val consequentTree = rec(Conjunction(tail, trailingBindings))
        (head match {
          case MatchLiteral(scrutinee, literal) =>
            val branches = Buffer[MutCase](
              MutCase.Literal(literal, consequentTree.withBindings(afterHeadBindings)).withLocation(literal.toLoc)
            )
            Match(scrutinee, branches, N)
              .withBindings(beforeHeadBindings)
          case MatchAny(scrutinee) =>
            Match(scrutinee, Buffer.empty, S(consequentTree.withBindings(afterHeadBindings)))
              .withBindings(beforeHeadBindings)
          case MatchClass(scrutinee, className, fields) =>
            val branches = Buffer[MutCase](
              MutCase.Constructor(className -> Buffer.from(fields), consequentTree.withBindings(afterHeadBindings))
                .withLocations(head.locations)
            )
            Match(scrutinee, branches, N).withBindings(beforeHeadBindings)
          case MatchTuple(scrutinee, arity, fields) =>
            val branches = Buffer[MutCase](
              MutCase.Constructor(Var(s"Tuple#$arity") -> Buffer.from(fields), consequentTree.withBindings(afterHeadBindings))
                .withLocations(head.locations)
            )
            Match(scrutinee, branches, N).withBindings(beforeHeadBindings)
          case BooleanTest(test) =>
            IfThenElse(test, consequentTree, MissingCase)
              .withBindings(beforeHeadBindings)
              .withBindings(afterHeadBindings)
          case Binding(name, term, isField) =>
            val kind = if (isField)
              LetBinding.Kind.FieldExtraction
            else
              LetBinding.Kind.ScrutineeAlias
            consequentTree
              .withBindings(beforeHeadBindings)
              .withBindings(LetBinding(kind, false, name, term) :: Nil)
              .withBindings(afterHeadBindings)
        })
      case Conjunction(Nil, trailingBindings) =>
        Consequent(term).withBindings(trailingBindings)
    }

    rec(conjunction)
  }
}
