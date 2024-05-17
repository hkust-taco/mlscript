package mlscript.compiler.ir

import mlscript.utils.shorthands._
import mlscript.compiler.ir._

import Node._

// Resolves the definition references by turning them from Right(name) to Left(Defn).
private final class DefnRefResolver(defs: Set[Defn], allowInlineJp: Bool):
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
          if (!allowInlineJp)
            throw IRError(f"unknown function ${defnref.getName} in ${defs.map{_.getName}.mkString(",")}")
  def run(node: Node) = f(node)
  def run(node: Defn) = f(node.body)


def resolveDefnRef(entry: Node, defs: Set[Defn], allowInlineJp: Bool = false): Unit  =
  val rl = DefnRefResolver(defs, allowInlineJp)
  rl.run(entry)
  defs.foreach(rl.run(_))
