package mlscript.compiler.ir

import mlscript.utils.shorthands._
import mlscript.compiler.ir._

import Node._

private final class Relink(defs: Set[Defn], allow_inline_jp: Bool):
  private def f(x: Node): Unit = x match
    case Result(res) =>
    case Case(scrut, cases) => cases map { (_, body) => f(body) }
    case LetExpr(name, expr, body) => f(body)
    case LetCall(resultNames, defnref, args, body) =>
      defs.find{_.getName == defnref.getName} match
        case Some(defn) => defnref.defn = Left(defn)
        case None => throw IRError(f"unknown function ${defnref.getName} in ${defs.map{_.getName}.mkString(",")}")
        f(body)
    case Jump(defnref, _) =>
      // maybe not promoted yet
      defs.find{_.getName == defnref.getName} match
        case Some(defn) => defnref.defn = Left(defn)
        case None =>
          if (!allow_inline_jp)
            throw IRError(f"unknown function ${defnref.getName} in ${defs.map{_.getName}.mkString(",")}")
  def run(node: Node) = f(node)
  def run(node: Defn) = f(node.body)


def relink(entry: Node, defs: Set[Defn], allow_inline_jp: Bool = false): Unit  =
  val rl = Relink(defs, allow_inline_jp)
  rl.run(entry)
  defs.foreach(rl.run(_))