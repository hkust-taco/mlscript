package mlscript.ucs

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import scala.collection.immutable.Set
import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer}

import helpers._
import mlscript.ucs.MutCaseOf.Consequent

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
  def kind: Str = {
    import MutCaseOf._
    this match {
      case Consequent(_) => "Consequent"
      case MissingCase => "MissingCase"
      case IfThenElse(_, _, _) => "IfThenElse"
      case Match(_, _, _) => "Match"
    }
  }

  def describe: Str

  def merge
    (branch: Conjunction -> Term)
    (implicit raise: Diagnostic => Unit): Unit
  def mergeDefault
    (bindings: Ls[(Bool, Var, Term)], default: Term)
    (implicit raise: Diagnostic => Unit): Unit
  def toTerm(defs: Set[Var]): Term

  // TODO: Make it immutable.
  var locations: Ls[Loc] = Nil
}

object MutCaseOf {
  def toTerm(t: MutCaseOf): Term = {
    val term = t.toTerm(Set.from(t.getBindings.iterator.map(_._2)))
    mkBindings(t.getBindings.toList, term, Set.empty)
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

  import Clause.{MatchClass, MatchTuple, BooleanTest}

  // A short-hand for pattern matchings with only true and false branches.
  final case class IfThenElse(condition: Term, var whenTrue: MutCaseOf, var whenFalse: MutCaseOf) extends MutCaseOf {
    def describe: Str =
      s"IfThenElse($condition, whenTrue = ${whenTrue.kind}, whenFalse = ${whenFalse.kind})"

    def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit =
      branch match {
        // The CC is a wildcard. So, we call `mergeDefault`.
        case Conjunction(Nil, trailingBindings) -> term =>
          this.mergeDefault(trailingBindings, term)
        // The CC is an if-then-else. We create a pattern match of true/false.
        case Conjunction((head @ BooleanTest(test)) :: tail, trailingBindings) -> term =>
          // If the test is the same. So, we merge.
          if (test === condition) {
            whenTrue.addBindings(head.bindings)
            whenTrue.merge(Conjunction(tail, trailingBindings) -> term)
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
        case Conjunction(head :: _, _) -> _ =>
          whenFalse match {
            case Consequent(_) =>
              raise(WarningReport(Message.fromStr("duplicated else in the if-then-else") -> N :: Nil))
            case MissingCase =>
              whenFalse = buildFirst(branch._1, branch._2)
              whenFalse.addBindings(head.bindings)
            case _ => whenFalse.merge(branch)
          }
      }

    def mergeDefault(bindings: Ls[(Bool, Var, Term)], default: Term)(implicit raise: Diagnostic => Unit): Unit = {
      whenTrue.mergeDefault(bindings, default)
      whenFalse match {
        case Consequent(term) =>
          import Message.MessageContext
          raise(WarningReport(
            msg"Found a duplicated else branch" -> default.toLoc ::
            (msg"The first else branch was declared here." -> term.toLoc) ::
              Nil))
        case MissingCase =>
          whenFalse = Consequent(default).withBindings(bindings)
        case _: IfThenElse | _: Match => whenFalse.mergeDefault(bindings, default)
      }
    }

    def toTerm(defs: Set[Var]): Term = {
      val falseBody = mkBindings(whenFalse.getBindings.toList, whenFalse.toTerm(defs ++ whenFalse.getBindings.iterator.map(_._2)), defs)
      val trueBody = mkBindings(whenTrue.getBindings.toList, whenTrue.toTerm(defs ++ whenTrue.getBindings.iterator.map(_._2)), defs)
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
    def describe: Str = {
      val n = branches.length
      s"Match($scrutinee, $n ${"branch".pluralize(n, true)}, ${
        wildcard.fold("no wildcard")(n => s"wildcard = ${n.kind}")
      })"
    }

    def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit = {
      branch._1.separate(scrutinee) match {
        // No conditions against the same scrutinee.
        case N =>
          branch match {
            case Conjunction((head @ MatchTuple(scrutinee2, arity, fields)) :: tail, trailingBindings) -> term
                if scrutinee2 === scrutinee => // Same scrutinee!
              val tupleClassName = Var(s"Tuple#$arity") // TODO: Find a name known by Typer.
              branches.find(_.matches(tupleClassName)) match {
                // No such pattern. We should create a new one.
                case N =>
                  val newBranch = buildFirst(Conjunction(tail, trailingBindings), term)
                  newBranch.addBindings(head.bindings)
                  branches += MutCase(tupleClassName -> Buffer.from(fields), newBranch)
                    .withLocations(head.locations)
                // Found existing pattern.
                case S(branch) =>
                  branch.consequent.addBindings(head.bindings)
                  branch.addFields(fields)
                  branch.consequent.merge(Conjunction(tail, trailingBindings) -> term)
              }
            // A wild card case. We should propagate wildcard to every default positions.
            case Conjunction(Nil, trailingBindings) -> term => mergeDefault(trailingBindings, term)
            // The conditions to be inserted does not overlap with me.
            case conjunction -> term =>
              wildcard match {
                // No wildcard. We will create a new one.
                case N => wildcard = S(buildFirst(conjunction, term))
                // There is a wildcard case. Just merge!
                case S(consequent) => consequent.merge(conjunction -> term)
              }
          }
        // Found a match condition against the same scrutinee
        case S((head @ MatchClass(_, className, fields), remainingConditions)) =>
          branches.find(_.matches(className)) match {
            // No such pattern. We should create a new one.
            case N =>
              val newBranch = buildFirst(remainingConditions, branch._2)
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

    def mergeDefault(bindings: Ls[(Bool, Var, Term)], default: Term)(implicit raise: Diagnostic => Unit): Unit = {
      branches.foreach {
        case MutCase(_, consequent) => consequent.mergeDefault(bindings, default)
      }
      wildcard match {
        case N => wildcard = S(Consequent(default).withBindings(bindings))
        case S(consequent) => consequent.mergeDefault(bindings, default)
      }
    }

    def toTerm(defs: Set[Var]): Term = {
      def rec(xs: Ls[MutCase]): CaseBranches =
        xs match {
          case MutCase(className -> fields, cases) :: next =>
            // TODO: expand bindings here
            val consequent = cases.toTerm(defs ++ fields.iterator.map(_._2))
            Case(className, mkLetFromFields(scrutinee, fields.toList, consequent), rec(next))
          case Nil =>
            wildcard.fold[CaseBranches](NoCases)(_.toTerm(defs) |> Wildcard)
        }
      val cases = rec(branches.toList)
      val resultTerm = scrutinee.local match {
        case N => CaseOf(scrutinee.term, cases)
        case S(aliasVar) => Let(false, aliasVar, scrutinee.term, CaseOf(aliasVar, cases))
      }
      // Collect let bindings from case branches.
      val bindings = branches.iterator.flatMap(_.consequent.getBindings).toList
      mkBindings(bindings, resultTerm, defs)
    }
  }
  final case class Consequent(term: Term) extends MutCaseOf {
    def describe: Str = s"Consequent($term)"

    def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit =
      raise(WarningReport(Message.fromStr("duplicated branch") -> N :: Nil))

    def mergeDefault(bindings: Ls[(Bool, Var, Term)], default: Term)(implicit raise: Diagnostic => Unit): Unit = ()

    def toTerm(defs: Set[Var]): Term = term
  }
  final case object MissingCase extends MutCaseOf {
    def describe: Str = "MissingCase"

    def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit =
      lastWords("`MissingCase` is a placeholder and cannot be merged")

    def mergeDefault(bindings: Ls[(Bool, Var, Term)], default: Term)(implicit raise: Diagnostic => Unit): Unit = ()

    def toTerm(defs: Set[Var]): Term = {
      import Message.MessageContext
      throw new DesugaringException(msg"missing a default branch", N)
    }
  }

  private def buildFirst(conjunction: Conjunction, term: Term): MutCaseOf = {
    def rec(conjunction: Conjunction): MutCaseOf = conjunction match {
      case Conjunction(head :: tail, trailingBindings) =>
        val realTail = Conjunction(tail, trailingBindings)
        (head match {
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
        }).withBindings(head.bindings)
      case Conjunction(Nil, trailingBindings) =>
        Consequent(term).withBindings(trailingBindings)
    }

    rec(conjunction)
  }

  def build
    (cnf: Ls[Conjunction -> Term])
    (implicit raise: Diagnostic => Unit)
  : MutCaseOf = {
    cnf match {
      case Nil => MissingCase
      case (conditions -> term) :: next =>
        val root = MutCaseOf.buildFirst(conditions, term)
        next.foreach(root.merge(_))
        root
    }
  }
}
