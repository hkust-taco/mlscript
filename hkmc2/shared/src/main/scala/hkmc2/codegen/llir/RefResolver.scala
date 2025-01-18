package hkmc2.codegen.llir

import mlscript.utils.shorthands._

import Node._

// Resolves the definition references by turning them from Right(name) to Left(Func).
private final class RefResolver(defs: Map[Str, Func], classes: Map[Str, ClassInfo], allowInlineJp: Bool):
  private def f(x: Expr): Unit = x match
    case Expr.Ref(name) => 
    case Expr.Literal(lit) =>
    case Expr.CtorApp(cls, args) => classes.get(cls.name) match
      case None => throw LowLevelIRError(f"unknown class ${cls.name} in ${classes.keySet.mkString(",")}")
      case Some(value) => cls.cls = Left(value)
    case Expr.Select(name, cls, field) => classes.get(cls.name) match
      case None => throw LowLevelIRError(f"unknown class ${cls.name} in ${classes.keySet.mkString(",")}")
      case Some(value) => cls.cls = Left(value)
    case Expr.BasicOp(name, args) =>
    case Expr.AssignField(name, cls, field, value) => classes.get(cls.name) match
      case None => throw LowLevelIRError(f"unknown class ${cls.name} in ${classes.keySet.mkString(",")}")
      case Some(value) => cls.cls = Left(value)

  private def f(x: Pat): Unit = x match
    case Pat.Lit(lit) => 
    case Pat.Class(cls) => classes.get(cls.name) match
      case None => throw LowLevelIRError(f"unknown class ${cls.name} in ${classes.keySet.mkString(",")}")
      case Some(value) => cls.cls = Left(value)
  
  private def f(x: Node): Unit = x match
    case Result(res) =>
    case Case(scrut, cases, default) => cases foreach { (_, body) => f(body) }; default foreach f
    case LetExpr(name, expr, body) => f(expr); f(body)
    case LetMethodCall(names, cls, method, args, body) => f(body)
    case LetCall(resultNames, defnref, args, body) =>
      defs.get(defnref.name) match
        case Some(defn) => defnref.func = Left(defn)
        case None => throw LowLevelIRError(f"unknown function ${defnref.name} in ${defs.keySet.mkString(",")}")
        f(body)
    case Jump(defnref, _) =>
      // maybe not promoted yet
      defs.get(defnref.name) match
        case Some(defn) => defnref.func = Left(defn)
        case None =>
          if !allowInlineJp then
            throw LowLevelIRError(f"unknown function ${defnref.name} in ${defs.keySet.mkString(",")}")
    case Panic(_) =>
  def run(node: Node) = f(node)
  def run(node: Func) = f(node.body)

def resolveRef(entry: Node, defs: Set[Func], classes: Set[ClassInfo], allowInlineJp: Bool = false): Unit  =
  val defsMap = defs.map(x => x.name -> x).toMap
  val classesMap = classes.map(x => x.name -> x).toMap
  val rl = RefResolver(defsMap, classesMap, allowInlineJp)
  rl.run(entry)
  defs.foreach(rl.run(_))

