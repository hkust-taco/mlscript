package hkmc2.codegen.llir

import hkmc2.utils._

private final class FuncRefInSet(defs: Set[Func], classes: Set[ClassInfo]):
  import Node._
  import Expr._
  
  private def f(x: Expr): Unit = x match
    case Ref(name) => 
    case Literal(lit) =>
    case CtorApp(name, args) =>
    case Select(name, ref, field) => ref.getClass match {
      case Some(real_class) => if !classes.exists(_ eq real_class) then throw LowLevelIRError("ref is not in the set")
      case _ =>
    }
    case BasicOp(name, args) =>
    case AssignField(assignee, ref, _, value) => ref.getClass match {
      case Some(real_class) => if !classes.exists(_ eq real_class) then throw LowLevelIRError("ref is not in the set")
      case _ =>
    }
  
  private def f(x: Node): Unit = x match
    case Result(res) => 
    case Jump(func, args) =>
    case Case(x, cases, default) => cases foreach { (_, body) => f(body) }; default foreach f
    case Panic(_) =>
    case LetExpr(name, expr, body) => f(body)
    case LetMethodCall(names, cls, method, args, body) => f(body)
    case LetCall(res, ref, args, body) =>
      ref.getFunc match {
        case Some(real_func) => if !defs.exists(_ eq real_func) then throw LowLevelIRError("ref is not in the set")
        case _ =>
      }
      f(body)
  def run(node: Node) = f(node)
  def run(func: Func) = f(func.body)

def validateRefInSet(entry: Node, defs: Set[Func], classes: Set[ClassInfo]): Unit =
  val funcRefInSet = FuncRefInSet(defs, classes)
  defs.foreach(funcRefInSet.run(_))

def validate(entry: Node, defs: Set[Func], classes: Set[ClassInfo]): Unit =
  validateRefInSet(entry, defs, classes)

