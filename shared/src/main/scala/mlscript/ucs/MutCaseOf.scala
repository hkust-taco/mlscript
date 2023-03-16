package mlscript.ucs

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import scala.collection.immutable.Set
import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer}

import helpers._
import mlscript.ucs.MutCaseOf.Consequent
import scala.collection.immutable

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
    (bindings: Ls[LetBinding], default: Term)
    (implicit raise: Diagnostic => Unit): Int

  // TODO: Make it immutable.
  var locations: Ls[Loc] = Nil
}

object MutCaseOf {
  def showScrutinee(scrutinee: Scrutinee): Str =
    s"«${scrutinee.term}»" + (scrutinee.local match {
      case N => ""
      case S(Var(alias)) => s" as $alias"
    })

  def show(t: MutCaseOf): Ls[Str] = {
    val lines = Buffer.empty[String]
    def rec(t: MutCaseOf, indent: Int): Unit = {
      val baseIndent = "  " * indent
      lazy val bindingLines = t.getBindings.iterator.map {
        case LetBinding(_, recursive, name, term) =>
          // Show bindings
          s"[binding $name = $term]"
      }.toList
      t match {
        case IfThenElse(condition, whenTrue, whenFalse) =>
          // Output the `whenTrue` with the prefix "if".
          bindingLines.foreach { lines += baseIndent + _ }
          lines += baseIndent + s"if «$condition»"
          rec(whenTrue, indent + 1)
          // Output the `whenFalse` case with the prefix "else".
          lines += s"${baseIndent}else"
          rec(whenFalse, indent + 1)
        case Match(scrutinee, branches, default) =>
          bindingLines.foreach { lines += baseIndent + _ }
          lines += baseIndent + showScrutinee(scrutinee) + " match"
          branches.foreach {
            case MutCase.Literal(literal, consequent) =>
              lines += s"$baseIndent  case $literal =>"
              rec(consequent, indent + 1)
            case MutCase.Constructor(Var(className) -> fields, consequent) =>
              lines += s"$baseIndent  case $className =>"
              fields.foreach { case (field, Var(alias)) =>
                // Show pattern bindings.
                lines += s"$baseIndent    [pattern $alias = ${scrutinee.reference}.$field]"
              }
              rec(consequent, indent + 2)
          }
          default.foreach { consequent =>
            lines += s"$baseIndent  default"
            rec(consequent, indent + 2)
          }
        case Consequent(term) =>
          bindingLines.foreach { lines += baseIndent + _ }
          lines += s"$baseIndent«$term»"
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

    def matches(expected: Var): Bool
    def matches(expected: Str): Bool
    def matches(expected: Lit): Bool

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

  object MutCase {
    final case class Literal(
      val literal: SimpleTerm,
      var consequent: MutCaseOf,
    ) extends MutCase {
      override def matches(expected: Var): Bool = literal match {
        case tof @ Var(n) if n === "true" || n === "false" => expected === tof
        case _ => false
      }
      override def matches(expected: Str): Bool = false
      override def matches(expected: Lit): Bool = literal === expected
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
      override def matches(expected: Var): Bool = matches(expected.name)
      override def matches(expected: Str): Bool = patternFields._1.name === expected
      override def matches(expected: Lit): Bool = false
      def addFields(fields: Iterable[Str -> Var]): Unit =
        patternFields._2 ++= fields.iterator.filter(!patternFields._2.contains(_))
    }
  }

  import Clause.{MatchLiteral, MatchClass, MatchTuple, BooleanTest, Binding}

  // A short-hand for pattern matchings with only true and false branches.
  final case class IfThenElse(condition: Term, var whenTrue: MutCaseOf, var whenFalse: MutCaseOf) extends MutCaseOf {
    def describe: Str =
      s"IfThenElse($condition, whenTrue = ${whenTrue.kind}, whenFalse = ${whenFalse.kind})"

    def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit =
      branch match {
        // The CC is a wildcard. So, we call `mergeDefault`.
        case Conjunction(Nil, trailingBindings) -> term =>
          if (mergeDefault(trailingBindings, term) == 0) {
            import Message.MessageContext
            raise(WarningReport(
              msg"Found a redundant else branch" -> term.toLoc :: Nil
            ))
          }
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

    def mergeDefault(bindings: Ls[LetBinding], default: Term)(implicit raise: Diagnostic => Unit): Int = {
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
      s"Match($scrutinee, $n ${"branch".pluralize(n, true)}, ${
        wildcard.fold("no wildcard")(n => s"wildcard = ${n.kind}")
      })"
    }

    def merge(originalBranch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit = {
      // Remove let bindings that already has been declared.
      val branch = originalBranch._1.copy(clauses = originalBranch._1.clauses.filter {
        case Binding(name, value, false) if (getBindings.exists {
          case LetBinding(LetBinding.Kind.ScrutineeAlias, _, n, v) =>
            n === name && v === value
          case _ => false
        }) => false
        case _ => true
      }) -> originalBranch._2
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
              mergeDefault(trailingBindings, term) // TODO: Handle the int result here.
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
        case S(L(head @ MatchClass(_, className, fields)) -> remainingConditions) =>
          branches.find(_.matches(className)) match {
            // No such pattern. We should create a new one.
            case N =>
              val newBranch = buildFirst(remainingConditions, branch._2)
              newBranch.addBindings(head.bindings)
              branches += MutCase.Constructor(className -> Buffer.from(fields), newBranch)
                .withLocations(head.locations)
            // Found existing pattern.
            case S(matchCase: MutCase.Constructor) =>
              // Merge interleaved bindings.
              matchCase.consequent.addBindings(head.bindings)
              matchCase.addFields(fields)
              matchCase.consequent.merge(remainingConditions -> branch._2)
          }
        case S(R(head @ MatchLiteral(_, literal)) -> remainingConditions) =>
          branches.find(branch => literal match {
            case v: Var => branch.matches(v)
            case l: Lit => branch.matches(l)
          }) match {
            // No such pattern. We should create a new one.
            case N =>
              val newConsequent = buildFirst(remainingConditions, branch._2)
              newConsequent.addBindings(head.bindings)
              branches += MutCase.Literal(literal, newConsequent)
                .withLocations(head.locations)
            case S(matchCase: MutCase.Literal) =>
              // Merge interleaved bindings.
              matchCase.consequent.addBindings(head.bindings)
              matchCase.consequent.merge(remainingConditions -> branch._2)
          }
      }
    }

    def mergeDefault(bindings: Ls[LetBinding], default: Term)(implicit raise: Diagnostic => Unit): Int = {
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
    def describe: Str = s"Consequent($term)"

    def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit =
      raise {
        import scala.collection.mutable.ListBuffer
        val buffer = ListBuffer.empty[Message -> Opt[Loc]]
        buffer += Message.fromStr("Found duplicated branch") -> N
        buffer += Message.fromStr("This decision path tries to fit") -> {
          val (Conjunction(clauses, _) -> consequent) = branch
          consequent.toLoc
          // TODO: Make a complete location. 
          // clauses match {
          //   case head :: _ => head.
          //   case Nil => consequent.toLoc
          // }
        }
        buffer += Message.fromStr("But there is already a consequent term") -> term.toLoc
        WarningReport(buffer.toList)
      }

    def mergeDefault(bindings: Ls[LetBinding], default: Term)(implicit raise: Diagnostic => Unit): Int = 0
  }
  final case object MissingCase extends MutCaseOf {
    def describe: Str = "MissingCase"

    def merge(branch: Conjunction -> Term)(implicit raise: Diagnostic => Unit): Unit =
      lastWords("`MissingCase` is a placeholder and cannot be merged")

    def mergeDefault(bindings: Ls[LetBinding], default: Term)(implicit raise: Diagnostic => Unit): Int = 0
  }

  def buildFirst(conjunction: Conjunction, term: Term): MutCaseOf = {
    def rec(conjunction: Conjunction): MutCaseOf = conjunction match {
      case Conjunction(head :: tail, trailingBindings) =>
        lazy val (beforeHeadBindings, afterHeadBindings) = head.bindings.partition {
          case LetBinding(LetBinding.Kind.InterleavedLet, _, _, _) => false
          case LetBinding(_, _, _, _) => true
        }
        val consequentTree = rec(Conjunction(tail, trailingBindings))
        (head match {
          case MatchLiteral(scrutinee, literal) =>
            val branches = Buffer(
              MutCase.Literal(literal, consequentTree.withBindings(afterHeadBindings)).withLocation(literal.toLoc)
            )
            Match(scrutinee, branches, N)
              .withBindings(beforeHeadBindings)
          case BooleanTest(test) =>
            IfThenElse(test, consequentTree, MissingCase)
              .withBindings(beforeHeadBindings)
              .withBindings(afterHeadBindings)
          case MatchClass(scrutinee, className, fields) =>
            val branches = Buffer(
              MutCase.Constructor(className -> Buffer.from(fields), consequentTree.withBindings(afterHeadBindings))
                .withLocations(head.locations)
            )
            Match(scrutinee, branches, N).withBindings(beforeHeadBindings)
          case MatchTuple(scrutinee, arity, fields) =>
            val branches = Buffer(
              MutCase.Constructor(Var(s"Tuple#$arity") -> Buffer.from(fields), consequentTree.withBindings(afterHeadBindings))
                .withLocations(head.locations)
            )
            Match(scrutinee, branches, N).withBindings(beforeHeadBindings)
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
