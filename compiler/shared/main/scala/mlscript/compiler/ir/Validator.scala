package mlscript.compiler.ir

import mlscript.utils.shorthands._
import mlscript.compiler.ir._


private final class DefnRefInSet(defs: Set[Defn], classes: Set[ClassInfo]):
  import Node._
  import Expr._
  
  private def f(x: Expr): Unit = x match
    case Ref(name) => 
    case Literal(lit) =>
    case CtorApp(name, args) =>
    case Select(name, clsref, field) => clsref.getClass match {
      case Some(real_class) => if (!classes.exists(_ eq real_class)) throw IRError("ref is not in the set")
      case _ =>
    }
    case BasicOp(name, args) =>
    case AssignField(assignee, clsref, _, value) => clsref.getClass match {
      case Some(real_class) => if (!classes.exists(_ eq real_class)) throw IRError("ref is not in the set")
      case _ =>
    }
  
  private def f(x: Node): Unit = x match
    case Result(res) => 
    case Jump(defn, args) =>
    case Case(scrut, cases, default) => cases foreach { (_, body) => f(body) }; default foreach f
    case LetExpr(name, expr, body) => f(body)
    case LetMethodCall(names, cls, method, args, body) => f(body)
    case LetCall(res, defnref, args, _, body) =>
      defnref.getDefn match {
        case Some(real_defn) => if (!defs.exists(_ eq real_defn)) throw IRError("ref is not in the set")
        case _ =>
      }
      f(body)
  def run(node: Node) = f(node)
  def run(defn: Defn) = f(defn.body)

def validateRefInSet(entry: Node, defs: Set[Defn], classes: Set[ClassInfo]): Unit =
  val dris = DefnRefInSet(defs, classes)
  defs.foreach(dris.run(_))

def validate(entry: Node, defs: Set[Defn], classes: Set[ClassInfo]): Unit =
  validateRefInSet(entry, defs, classes)

