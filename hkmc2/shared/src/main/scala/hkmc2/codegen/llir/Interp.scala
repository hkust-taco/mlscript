package hkmc2
package codegen
package llir

import mlscript.*
import mlscript.utils.*
import scala.collection.immutable.*
import scala.collection.mutable.ListBuffer
import shorthands.*
import scala.util.boundary, boundary.break

import syntax.Tree
import hkmc2.utils.TraceLogger
import semantics.BuiltinSymbol

enum Stuck:
  case StuckExpr(expr: Expr, msg: Str)
  case StuckNode(node: Node, msg: Str)

  override def toString: String =
    this match
      case StuckExpr(expr, msg) => s"StuckExpr(${expr.show}, $msg)"
      case StuckNode(node, msg) => s"StuckNode(${node.show}, $msg)"

final case class InterpreterError(message: String) extends Exception(message)

class Interpreter(tl: TraceLogger):
  import tl.{trace, log, logs}
  import Stuck._

  private case class Configuration(
    var context: Ctx
  )

  private type Result[T] = Either[Stuck, T]

  private enum Value:
    case Class(cls: ClassInfo, var fields: Ls[Value])
    case Literal(lit: hkmc2.syntax.Literal)

    override def toString: String =
      import hkmc2.syntax.Tree.*
      this match
        case Class(cls, fields) => s"${cls.symbol.nme}(${fields.mkString(",")})"
        case Literal(IntLit(lit)) => lit.toString
        case Literal(BoolLit(lit)) => lit.toString 
        case Literal(DecLit(lit)) => lit.toString
        case Literal(StrLit(lit)) => lit.toString
        case Literal(UnitLit(isNullNotUndefined)) =>
          if isNullNotUndefined then "null" else "undefined"

  private final case class Ctx(
    bindingCtx: Map[Local, Value],
    classCtx: Map[Local, ClassInfo],
    funcCtx: Map[Local, Func],
    thisVal: Opt[Value],
  )
  
  import Node._
  import Expr._

  private def getTrue(using ctx: Ctx) = Value.Literal(hkmc2.syntax.Tree.BoolLit(true))
  private def getFalse(using ctx: Ctx) = Value.Literal(hkmc2.syntax.Tree.BoolLit(false))
  
  private def eval(op: Str, x1: Value, x2: Value)(using ctx: Ctx): Opt[Value] =
    import Value.{Literal => Li}
    import hkmc2.syntax.Tree.*
    (op, x1, x2) match
    case ("+", Li(IntLit(x)), Li(IntLit(y))) => S(Li(IntLit(x + y)))
    case ("-", Li(IntLit(x)), Li(IntLit(y))) => S(Li(IntLit(x - y)))
    case ("*", Li(IntLit(x)), Li(IntLit(y))) => S(Li(IntLit(x * y)))
    case ("/", Li(IntLit(x)), Li(IntLit(y))) => S(Li(IntLit(x / y)))
    case ("&&", Li(BoolLit(x)), Li(BoolLit(y))) => S(if x && y then getTrue else getFalse)
    case ("||", Li(BoolLit(x)), Li(BoolLit(y))) => S(if x || y then getTrue else getFalse)
    case ("==", Li(IntLit(x)), Li(IntLit(y))) => S(if x === y then getTrue else getFalse)
    case ("===", Li(IntLit(x)), Li(IntLit(y))) => S(if x === y then getTrue else getFalse)
    case ("!=", Li(IntLit(x)), Li(IntLit(y))) => S(if x != y then getTrue else getFalse)
    case ("<=", Li(IntLit(x)), Li(IntLit(y))) => S(if x <= y then getTrue else getFalse)
    case (">=", Li(IntLit(x)), Li(IntLit(y))) => S(if x >= y then getTrue else getFalse)
    case (">", Li(IntLit(x)), Li(IntLit(y))) => S(if x > y then getTrue else getFalse)
    case ("<", Li(IntLit(x)), Li(IntLit(y))) => S(if x < y then getTrue else getFalse)
    case _ => N

  private def evalArgs(using ctx: Ctx)(exprs: Ls[TrivialExpr]): Result[Ls[Value]] =
    var values = ListBuffer.empty[Value]
    var stuck: Opt[Stuck] = None
    exprs foreach { expr =>
      stuck match
        case None => eval_t(expr) match
          case L(x) => stuck = Some(x)
          case R(x) => values += x
        case _ => ()
    } 
    stuck.toLeft(values.toList)

  private def eval_t(expr: TrivialExpr)(using ctx: Ctx): Result[Value] = expr match
    case Ref(x: BuiltinSymbol) => x.nme match
      case "<this>" => ctx.thisVal.toRight(StuckExpr(expr.toExpr, s"undefined this value"))
      case _ => L(StuckExpr(expr.toExpr, s"undefined builtin ${x.nme}"))
    case Ref(x) => ctx.bindingCtx.get(x).toRight(StuckExpr(expr.toExpr, s"undefined variable $x"))
    case Literal(x) => R(Value.Literal(x))
  
  private def eval(expr: Expr)(using ctx: Ctx): Result[Value] = expr match
    case x: TrivialExpr => eval_t(x)
    case CtorApp(cls, args) =>
      for
        xs <- evalArgs(args)
        cls <- ctx.classCtx.get(cls).toRight(StuckExpr(expr, s"undefined class ${cls.nme}"))
      yield Value.Class(cls, xs)
    case Select(name, cls, field) if field.forall(_.isDigit) =>
      val nth = field.toInt
      ctx.bindingCtx.get(name).toRight(StuckExpr(expr, s"undefined variable $name")).flatMap {
        case Value.Class(cls2, xs) if cls === cls2.symbol =>
          xs.lift(nth) match
            case Some(x) => R(x)
            case None => L(StuckExpr(expr, s"unable to find selected field $field"))
        case Value.Class(cls2, xs) => L(StuckExpr(expr, s"unexpected class $cls2"))
        case x => L(StuckExpr(expr, s"unexpected value $x"))
      }
    case Select(name, cls, field) =>
      ctx.bindingCtx.get(name).toRight(StuckExpr(expr, s"undefined variable $name")).flatMap {
        case Value.Class(cls2, xs) if cls === cls2.symbol =>
          xs.zip(cls2.fields).find{_._2.nme === field} match
            case Some((x, _)) => R(x)
            case None => L(StuckExpr(expr, s"unable to find selected field $field"))
        case Value.Class(cls2, xs) => L(StuckExpr(expr, s"unexpected class $cls2"))
        case x => L(StuckExpr(expr, s"unexpected value $x"))
      }
    case BasicOp(name, args) => boundary:
      evalArgs(args).flatMap(
        xs => 
          name.nme match
            case "+" | "-" | "*" | "/" | "==" | "===" | "!=" | "<=" | ">=" | "<" | ">" => 
              if xs.length < 2 then break:
                L(StuckExpr(expr, s"not enough arguments for basic operation $name"))
              else eval(name.nme, xs.head, xs.tail.head).toRight(StuckExpr(expr, s"unable to evaluate basic operation"))
            case _ => L(StuckExpr(expr, s"unexpected basic operation $name")))
    case AssignField(assignee, cls, field, value) =>
      for
        x <- eval_t(Ref(assignee): TrivialExpr)
        y <- eval_t(value)
        res <- x match
          case obj @ Value.Class(cls2, xs) if cls === cls2 =>
            xs.zip(cls2.fields).find{_._2.nme === field} match
              case Some((_, _)) =>
                obj.fields = xs.map(x => if x === obj then y else x)
                // Ideally, we should return a unit value here, but here we return the assignee value for simplicity.
                R(obj)
              case None => L(StuckExpr(expr, s"unable to find selected field $field"))
          case Value.Class(cls2, xs) => L(StuckExpr(expr, s"unexpected class $cls2"))
          case x => L(StuckExpr(expr, s"unexpected value $x"))
      yield res

  private def eval(node: Node)(using ctx: Ctx): Result[Ls[Value]] = node match
    case Result(res) => evalArgs(res)
    case Jump(func, args) =>
      for
        xs <- evalArgs(args)
        func <- ctx.funcCtx.get(func).toRight(StuckNode(node, s"undefined function ${func.nme}"))
        ctx1 = ctx.copy(bindingCtx = ctx.bindingCtx ++ func.params.zip(xs))
        res <- eval(func.body)(using ctx1)
      yield res
    case Case(scrut, cases, default) =>
      eval_t(scrut) flatMap {
        case Value.Class(cls, fields) => 
          cases.find {
            case (Pat.Class(cls2), _) => cls.symbol === cls2
            case _ => false
          } match {
            case Some((_, x)) => eval(x)
            case None => 
              default match
                case S(x) => eval(x)
                case N => L(StuckNode(node, s"can not find the matched case, ${cls.symbol} expected"))
          }
        case Value.Literal(lit) => 
          cases.find {
            case (Pat.Lit(lit2), _) => lit === lit2
            case _ => false
          } match {
            case Some((_, x)) => eval(x)
            case None => 
              default match
                case S(x) => eval(x)
                case N => L(StuckNode(node, s"can not find the matched case, $lit expected"))
          }
      }
    case LetExpr(name, expr, body) =>
      for
        x <- eval(expr)
        ctx1 = ctx.copy(bindingCtx = ctx.bindingCtx + (name -> x))
        res <- eval(body)(using ctx1)
      yield res
    case LetMethodCall(names, cls, method, args, body) =>
      def lookup_method(cls: ClassInfo, method: Local): Option[Func] =
        // The methods with the same name in a subclass will override the method in the superclass.
        // But they have different symbols for the method definition.
        // So, we don't directly use the method symbol to find the method.
        // Instead, we fallback to use the method name.
        cls.methods.find(_._1.nme === method.nme).map(_._2)
      for
        ys <- evalArgs(args).flatMap {
          case (ths @ Value.Class(cls2, xs)) :: args =>
            lookup_method(cls2, method).toRight(StuckNode(node, s"undefined method ${method.nme}")).flatMap { method =>
              val ctx1 = ctx.copy(
                bindingCtx = ctx.bindingCtx ++ cls2.fields.zip(xs) ++ method.params.zip(args),
                thisVal = S(ths)
              )
              eval(method.body)(using ctx1)
            }
          case _ => L(StuckNode(node, s"not enough arguments for method call, or the first argument is not a class"))
        }
        ctx2 = ctx.copy(bindingCtx = ctx.bindingCtx ++ names.zip(ys))
        res <- eval(body)(using ctx2)
      yield res
    case LetCall(names, func, args, body) =>
      for
        xs <- evalArgs(args)
        func <- ctx.funcCtx.get(func).toRight(StuckNode(node, s"undefined function ${func.nme}"))
        ctx1 = ctx.copy(bindingCtx = ctx.bindingCtx ++ func.params.zip(xs))
        ys <- eval(func.body)(using ctx1)
        ctx2 = ctx.copy(bindingCtx = ctx.bindingCtx ++ names.zip(ys))
        res <- eval(body)(using ctx2)
      yield res
    case Panic(msg) => L(StuckNode(node, msg))

  private def f(prog: Program): Ls[Value] =
    val Program(classes, defs, entry) = prog
    given Ctx = Ctx(
      bindingCtx = Map.empty,
      classCtx = classes.map(cls => (cls.symbol, cls)).toMap,
      funcCtx = defs.map(func => (func.name, func)).toMap,
      thisVal = None,
    )
    val entryFunc = summon[Ctx].funcCtx.getOrElse(entry, throw InterpreterError("Entry doesn't exist"))
    assert(entryFunc.params.isEmpty, "Entry function should not have parameters")
    eval(entryFunc.body) match
      case R(x) => x
      case L(x) => throw InterpreterError("Stuck evaluation: " + x.toString)
    
  def interpret(prog: Program): Str =
    val node = f(prog) 
    node.map(_.toString).mkString(",")
