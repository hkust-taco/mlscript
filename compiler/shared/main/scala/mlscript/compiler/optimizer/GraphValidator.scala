package mlscript.compiler.optimizer

import mlscript.utils.shorthands._
import mlscript.compiler.optimizer._

import GONode._

private final class DefRefInSet(defs: Set[GODef]):
  private def f(x: GONode): Unit = x match
    case Result(res) => 
    case Jump(defn, args) =>
    case Case(scrut, cases) => cases map { (_, body) => f(body) }
    case LetExpr(name, expr, body) => f(body)
    case LetCall(res, defnref, args, body) =>
      defnref.getDefn match {
        case Some(real_defn) => if (!defs.exists(_ eq real_defn)) throw GraphOptimizingError("ref is not in the set")
        case _ =>
      }
      f(body)
  def run(node: GONode) = f(node)
  def run(defn: GODef) = f(defn.body)

def validateDefRefInSet(entry: GONode, defs: Set[GODef]): Unit =
  val dris = DefRefInSet(defs)
  defs.foreach(dris.run(_))

private object ParamsArgsAreConsistent extends GOIterator:
  private def f(x: GONode): Unit = x match
    case Result(res) => 
    case Case(scrut, cases) => cases map { (_, body) => f(body) }
    case LetExpr(name, expr, body) => f(body)
    case LetCall(res, defnref, args, body) => 
      defnref.getDefn match {
        case Some(real_defn) =>
          if (real_defn.params.length != args.length) 
            val x = real_defn.params.length
            val y = args.length
            throw GraphOptimizingError(s"inconsistent arguments($y) and parameters($x) number in a call to ${real_defn.name}")
        case _ =>
      }
    case Jump(defnref, xs) => 
      defnref.getDefn match {
        case Some(jdef) =>
          val x = xs.length
          val y = jdef.params.length
          if (x != y)
            throw GraphOptimizingError(s"inconsistent arguments($x) and parameters($y) number in a jump to ${jdef.getName}")
        case _ =>
      }
  def run(node: GONode) = f(node)
  def run(defn: GODef) = f(defn.body)
      
def validateParamsArgsConsistent(entry: GONode, defs: Set[GODef]): Unit =
  val paac = ParamsArgsAreConsistent
  paac.run(entry)
  defs.foreach(paac.run(_))

def validate(entry: GONode, defs: Set[GODef]): Unit =
  validateDefRefInSet(entry, defs)
  validateParamsArgsConsistent(entry, defs)

