package mlscript.ucs

import mlscript.{Loc, Term, Var}
import mlscript.utils.shorthands._

// The point is to remember where does the scrutinee come from.
// Is it from nested patterns? Or is it from a `IfBody`?
// TODO: Replace `isMultiLineMatch` with `Scrutinee.Source`.
final case class Scrutinee(local: Opt[Var], term: Term) {
  def reference: Var = local.getOrElse(term match {
    case v: Var => v
    case _      => ???
  })

  var isMultiLineMatch: Bool = false
  var matchRootLoc: Opt[Loc] = N
  var localPatternLoc: Opt[Loc] = N

  override def toString: String =
    (local match {
      case N => ""
      case S(Var(alias)) => s"$alias @ "
    }) + s"$term"
}

object Scrutinee {
  import mlscript._

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
  abstract class Source {
    protected def computeLoc: Opt[Loc]
    
    lazy val toLoc: Opt[Loc] = computeLoc
  }

  object Source {
    /**
      * The scrutinee is from a term.
      *
      * @param app the double applications
      */
    final case class Term(app: App) extends Source {
      override protected def computeLoc: Opt[Loc] = app.toLoc // TODO
    }

    final case class OpApp(body: IfOpApp) extends Source {
      override protected def computeLoc: Opt[Loc] =
        (body.lhs.toLoc, body.op.toLoc) match {
          case (S(lhs), S(rhs)) => S(lhs ++ rhs)
          case (_, _)           => N
        }
    }

    final case class OpsApp(body: IfOpsApp, line: Var -> IfBody) extends Source {
      override protected def computeLoc: Opt[Loc] = ???
    }

    final case class Nested(app: App) extends Source {
      override protected def computeLoc: Opt[Loc] = ???
    }
  }
}