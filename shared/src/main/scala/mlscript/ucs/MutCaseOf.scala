package mlscript.ucs

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import scala.collection.mutable.Buffer
import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer}

import helpers._

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
  import Clause.Conjunction

  def merge
    (branch: Conjunction -> Term)
    (implicit raise: Diagnostic => Unit): Unit
  def mergeDefault
    (bindings: Ls[(Bool, Var, Term)], default: Term)
    (implicit raise: Diagnostic => Unit): Unit
  def toTerm: Term

  // TODO: Make it immutable.
  var locations: Ls[Loc] = Nil
}

object MutCaseOf {
  def toTerm(t: MutCaseOf): Term = {
    val term = t.toTerm
    mkBindings(t.getBindings.toList, term)
  }

  /**
    * A map from each scrutinee term to all its cases and the first `MutCase`.
    */
  type ExhaustivenessMap = MutMap[Term, MutMap[Var, MutCase]]

  def checkExhaustive(t: MutCaseOf, parentOpt: Opt[MutCaseOf])(implicit scrutineePatternMap: ExhaustivenessMap): Unit = {
    t match {
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
        scrutineePatternMap.get(scrutinee.term) match {
          // Should I call `die` here?
          case N => throw new Error(s"unreachable case: unknown scrutinee ${scrutinee.term}")
          case S(patternMap) =>
            // Filter out missing cases in `branches`.
            val missingCases = patternMap.subtractAll(branches.iterator.map {
              case MutCase(classNameVar -> _, _) => classNameVar
            })
            if (!missingCases.isEmpty) {
              throw DesugaringException.Multiple({
                import Message.MessageContext
                val numMissingCases = missingCases.size
                (msg"The match is not exhaustive." -> scrutinee.matchRootLoc) ::
                  (msg"The pattern at this position misses ${numMissingCases.toString} ${
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
        default.foreach(checkExhaustive(_, S(t)))
        branches.foreach { case MutCase(_, consequent) =>
          checkExhaustive(consequent, S(t))
        }
    }
  }

  def summarizePatterns(t: MutCaseOf): ExhaustivenessMap = {
    val m = MutMap.empty[Term, MutMap[Var, MutCase]]
    def rec(t: MutCaseOf): Unit =
      t match {
        case Consequent(term) => ()
        case MissingCase => ()
        case IfThenElse(_, whenTrue, whenFalse) =>
          rec(whenTrue)
          rec(whenFalse)
        case Match(scrutinee, branches, _) =>
          branches.foreach { mutCase =>
            val patternMap = m.getOrElseUpdate(scrutinee.term, MutMap.empty)
            if (!patternMap.contains(mutCase.patternFields._1)) {
              patternMap += ((mutCase.patternFields._1, mutCase))
            }
            rec(mutCase.consequent)
          }
      }
    rec(t)
    m
  }

  def showScrutinee(scrutinee: Scrutinee): Str =
    s"«${scrutinee.term}»" + (scrutinee.local match {
      case N => ""
      case S(Var(alias)) => s" as $alias"
    })

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
          branches.foreach { case MutCase(Var(className) -> fields, consequent) =>
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

  /**
    * MutCase is a _mutable_ representation of a case in `MutCaseOf.Match`.
    *
    * @param patternFields the alias to the fields
    * @param consequent the consequential `MutCaseOf`
    */
  final case class MutCase(
    val patternFields: Var -> Buffer[Str -> Var],
    var consequent: MutCaseOf,
  ) {
    def matches(expected: Var): Bool = matches(expected.name)
    def matches(expected: Str): Bool = patternFields._1.name === expected
    def addFields(fields: Iterable[Str -> Var]): Unit =
      patternFields._2 ++= fields.iterator.filter(!patternFields._2.contains(_))

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
    def withLocations(locs: Ls[Loc]): MutCase = {
      locations ++= locs
      this
    }
  }

  import Clause.{Conjunction, MatchClass, MatchTuple, BooleanTest}

  // A short-hand for pattern matchings with only true and false branches.
  final case class IfThenElse(condition: Term, var whenTrue: MutCaseOf, var whenFalse: MutCaseOf) extends MutCaseOf {
    override def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit =
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
    val branches: Buffer[MutCase],
    var wildcard: Opt[MutCaseOf]
  ) extends MutCaseOf {
    override def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit = {
      Conjunction.separate(branch._1, scrutinee) match {
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
                  branches += MutCase(tupleClassName -> Buffer.from(fields), newBranch)
                    .withLocations(head.locations)
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
              branches += MutCase(className -> Buffer.from(fields), newBranch)
                .withLocations(head.locations)
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
        case MutCase(_, consequent) => consequent.mergeDefault(bindings, default)
      }
      wildcard match {
        case N => wildcard = S(Consequent(default).withBindings(bindings))
        case S(consequent) => consequent.mergeDefault(bindings, default)
      }
    }

    override def toTerm: Term = {
      def rec(xs: Ls[MutCase]): CaseBranches =
        xs match {
          case MutCase(className -> fields, cases) :: next =>
            // TODO: expand bindings here
            Case(className, mkLetFromFields(scrutinee, fields.toList, cases.toTerm), rec(next))
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
    override def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit =
      raise(WarningReport(Message.fromStr("duplicated branch") -> N :: Nil))

    override def mergeDefault(bindings: Ls[(Bool, Var, Term)], default: Term)(implicit raise: Diagnostic => Unit): Unit = ()

    override def toTerm: Term = term
  }
  final case object MissingCase extends MutCaseOf {
    override def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit = ???

    override def mergeDefault(bindings: Ls[(Bool, Var, Term)], default: Term)(implicit raise: Diagnostic => Unit): Unit = ()

    override def toTerm: Term = {
      import Message.MessageContext
      throw DesugaringException.Single(msg"missing a default branch", N)
    }
  }

  private def buildFirst(conditions: Conjunction, term: Term): MutCaseOf = {
    def rec(conditions: Conjunction): MutCaseOf = conditions match {
      case (head :: tail, trailingBindings) =>
        val realTail = (tail, trailingBindings)
        val res = head match {
          case BooleanTest(test) => IfThenElse(test, rec(realTail), MissingCase)
          case MatchClass(scrutinee, className, fields) =>
            val branches = Buffer(
              MutCase(className -> Buffer.from(fields), rec(realTail))
                .withLocations(head.locations)
            )
            Match(scrutinee, branches, N)
          case MatchTuple(scrutinee, arity, fields) =>
            val branches = Buffer(
              MutCase(Var(s"Tuple#$arity") -> Buffer.from(fields), rec(realTail))
                .withLocations(head.locations)
            )
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
    (cnf: Ls[Conjunction -> Term])
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
