package mlscript.compiler.ir

import mlscript.utils.shorthands._
import mlscript.compiler.ir._

import Node._

private final class DefnRefInSet(defs: Set[Defn]):
  private def f(x: Node): Unit = x match
    case Result(res) => 
    case Jump(defn, args) =>
    case Case(scrut, cases) => cases map { (_, body) => f(body) }
    case LetExpr(name, expr, body) => f(body)
    case LetCall(res, defnref, args, _, body) =>
      defnref.getDefn match {
        case Some(real_defn) => if (!defs.exists(_ eq real_defn)) throw IRError("ref is not in the set")
        case _ =>
      }
      f(body)
  def run(node: Node) = f(node)
  def run(defn: Defn) = f(defn.body)

def validateDefnRefInSet(entry: Node, defs: Set[Defn]): Unit =
  val dris = DefnRefInSet(defs)
  defs.foreach(dris.run(_))

def validate(entry: Node, defs: Set[Defn]): Unit =
  validateDefnRefInSet(entry, defs)

