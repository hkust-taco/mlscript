package hkmc2
package codegen
package llir

import scala.annotation.tailrec
import scala.collection.immutable.*
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.{HashMap => MutHMap}
import scala.collection.mutable.{HashSet => MutHSet, Set => MutSet}

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._

import syntax.Tree.UnitLit
import semantics.{BuiltinSymbol, InnerSymbol}

class UsefulnessAnalysis(verbose: Bool = false): 
  import Expr._
  import Node._

  def log(x: Any) = if verbose then println(x)
  
  val uses = MutHMap[(Local, Int), Int]()
  val defs = MutHMap[Local, Int]()

  private def addDef(x: Local) =
    defs.update(x, defs.getOrElse(x, 0) + 1)
  
  private def addUse(x: Local) =
    val def_count = defs.get(x) match
      case None => throw Exception(s"Use of undefined variable $x")
      case Some(value) => value
    val key = (x, defs(x))
    uses.update(key, uses.getOrElse(key, 0) + 1)
  
  private def f(x: TrivialExpr): Unit = x match
    case Ref(name) => addUse(name)
    case _ => ()

  private def f(x: Expr): Unit = x match
    case Ref(name) => addUse(name)
    case Literal(lit) =>
    case CtorApp(name, args) => args.foreach(f)
    case Select(name, cls, field) => addUse(name)
    case BasicOp(name, args) => args.foreach(f)
    case AssignField(assignee, _, _, value) =>
      addUse(assignee)
      f(value)
  
  private def f(x: Node): Unit = x match
    case Result(res) => res.foreach(f)
    case Jump(defn, args) => args.foreach(f)
    case Case(scrut, cases, default) => 
      scrut match
        case Ref(name) => addUse(name)
        case _ => ()
      cases.foreach { case (cls, body) => f(body) }; default.foreach(f)
    case LetMethodCall(names, cls, method, args, body) => addUse(method); args.foreach(f); names.foreach(addDef); f(body)
    case LetExpr(name, expr, body) => f(expr); addDef(name); f(body)
    case LetCall(names, defn, args, body) => args.foreach(f); names.foreach(addDef); f(body)
  
  def run(x: Func) =
    x.params.foreach(addDef)
    f(x.body)
    uses.toMap

class FreeVarAnalysis(ctx: Local => Func):
  import Expr._
  import Node._

  private val visited = MutHSet[Local]()
  private def f(using defined: Set[Local])(defn: Func, fv: Set[Local]): Set[Local] =
    val defined2 = defn.params.foldLeft(defined)((acc, param) => acc + param)
    f(using defined2)(defn.body, fv)
  private def f(using defined: Set[Local])(expr: Expr, fv: Set[Local]): Set[Local] = expr match
    case Ref(name) => if defined.contains(name) then fv else fv + name
    case Literal(lit) => fv
    case CtorApp(name, args) => args.foldLeft(fv)((acc, arg) => f(using defined)(arg.toExpr, acc))
    case Select(name, cls, field) => if defined.contains(name) then fv else fv + name
    case BasicOp(name, args) => args.foldLeft(fv)((acc, arg) => f(using defined)(arg.toExpr, acc))
    case AssignField(assignee, _, _, value) => f(using defined)(
      value.toExpr, 
      if defined.contains(assignee) then fv + assignee else fv
    ) 
  private def f(using defined: Set[Local])(node: Node, fv: Set[Local]): Set[Local] = node match
    case Result(res) => res.foldLeft(fv)((acc, arg) => f(using defined)(arg.toExpr, acc))
    case Jump(defn, args) =>
      args.foldLeft(fv)((acc, arg) => f(using defined)(arg.toExpr, acc))
    case Case(scrut, cases, default) =>
      val fv2 = scrut match
        case Ref(name) => if defined.contains(name) then fv else fv + name
        case _ => fv
      val fv3 = cases.foldLeft(fv2):
        case (acc, (cls, body)) => f(using defined)(body, acc)
      default match
        case Some(body) => f(using defined)(body, fv3)
        case None => fv3
    case Panic(msg) => fv
    case LetMethodCall(resultNames, cls, method, args, body) =>
      var fv2 = args.foldLeft(fv)((acc, arg) => f(using defined)(arg.toExpr, acc))
      val defined2 = resultNames.foldLeft(defined)((acc, name) => acc + name)
      f(using defined2)(body, fv2)
    case LetExpr(name, expr, body) =>
      val fv2 = f(using defined)(expr, fv)
      val defined2 = defined + name
      f(using defined2)(body, fv2)
    case LetCall(resultNames, defn, args, body) =>
      var fv2 = args.foldLeft(fv)((acc, arg) => f(using defined)(arg.toExpr, acc))
      val defined2 = resultNames.foldLeft(defined)((acc, name) => acc + name)
      f(using defined2)(body, fv2)
  def run(node: Node) = f(using Set.empty)(node, Set.empty)
  def run_with(node: Node, defined: Set[Local]) = f(using defined)(node, Set.empty)
