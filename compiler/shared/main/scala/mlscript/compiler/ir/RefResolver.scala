package mlscript.compiler.ir

import mlscript.utils.shorthands._
import mlscript.compiler.ir._

import Node._

// Resolves the definition references by turning them from Right(name) to Left(Defn).
private final class RefResolver(defs: Map[Str, Defn], classes: Map[Str, ClassInfo], allowInlineJp: Bool):
  private def f(x: Expr): Unit = x match
    case Expr.Ref(name) => 
    case Expr.Literal(lit) =>
    case Expr.CtorApp(cls, args) => classes.get(cls.name) match
      case None => throw IRError(f"unknown class ${cls.name} in ${classes.keySet.mkString(",")}")
      case Some(value) => cls.cls = Left(value)
    case Expr.Select(name, cls, field) => classes.get(cls.name) match
      case None => throw IRError(f"unknown class ${cls.name} in ${classes.keySet.mkString(",")}")
      case Some(value) => cls.cls = Left(value)
    case Expr.BasicOp(name, args) =>
    case Expr.AssignField(assigneee, cls, field, value) => classes.get(cls.name) match
      case None => throw IRError(f"unknown class ${cls.name} in ${classes.keySet.mkString(",")}")
      case Some(value) => cls.cls = Left(value)

  private def f(x: Pat): Unit = x match
    case Pat.Lit(lit) => 
    case Pat.Class(cls) => classes.get(cls.name) match
      case None => throw IRError(f"unknown class ${cls.name} in ${classes.keySet.mkString(",")}")
      case Some(value) => cls.cls = Left(value)
  
  private def f(x: Node): Unit = x match
    case Result(res) =>
    case Case(scrut, cases, default) => cases foreach { (_, body) => f(body) }; default foreach f
    case LetExpr(name, expr, body) => f(expr); f(body)
    case LetMethodCall(names, cls, method, args, body) => f(body)
    case LetCall(resultNames, defnref, args, _, body) =>
      defs.get(defnref.name) match
        case Some(defn) => defnref.defn = Left(defn)
        case None => throw IRError(f"unknown function ${defnref.name} in ${defs.keySet.mkString(",")}")
        f(body)
    case Jump(defnref, _) =>
      // maybe not promoted yet
      defs.get(defnref.name) match
        case Some(defn) => defnref.defn = Left(defn)
        case None =>
          if (!allowInlineJp)
            throw IRError(f"unknown function ${defnref.name} in ${defs.keySet.mkString(",")}")
  def run(node: Node) = f(node)
  def run(node: Defn) = f(node.body)

def resolveRef(entry: Node, defs: Set[Defn], classes: Set[ClassInfo], allowInlineJp: Bool = false): Unit  =
  val defsMap = defs.map(x => x.name -> x).toMap
  val classesMap = classes.map(x => x.name -> x).toMap
  val rl = RefResolver(defsMap, classesMap, allowInlineJp)
  rl.run(entry)
  defs.foreach(rl.run(_))
