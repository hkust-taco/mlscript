package mlscript.compiler.ir

import mlscript._
import mlscript.compiler.ir._
import mlscript.compiler.utils._
import mlscript.compiler.optimizer._
import mlscript.utils._
import scala.collection.immutable._
import scala.annotation._
import shorthands._
import scala.collection.mutable.ListBuffer
import scala.util.boundary, boundary.break

enum Stuck:
  case StuckExpr(expr: Expr, msg: Str)
  case StuckNode(node: Node, msg: Str)

  override def toString: String =
    this match
      case StuckExpr(expr, msg) => s"StuckExpr(${expr.show}, $msg)"
      case StuckNode(node, msg) => s"StuckNode(${node.show}, $msg)"

final case class InterpreterError(message: String) extends Exception(message)

class Interpreter(verbose: Bool):
  private def log(x: Any) = if verbose then println(x)
  import Stuck._

  private case class Configuration(
    var context: Ctx
  )

  private type Result[T] = Either[Stuck, T]

  private enum Value:
    case Class(cls: ClassInfo, var fields: Ls[Value])
    case Literal(lit: Lit)

    override def toString: String = 
      this match
        case Class(cls, fields) => s"${cls.name}(${fields.mkString(",")})"
        case Literal(IntLit(lit)) => lit.toString
        case Literal(DecLit(lit)) => lit.toString
        case Literal(StrLit(lit)) => lit.toString
        case Literal(UnitLit(undefinedOrNull)) => if undefinedOrNull then "undefined" else "null"

  private final case class Ctx(
    bindingCtx: Map[Str, Value],
    classCtx: Map[Str, ClassInfo],
    defnCtx: Map[Str, Defn],
  )
  
  import Node._
  import Expr._

  private def getTrue(using ctx: Ctx) = Value.Class(ctx.classCtx("True"), Ls.empty)
  private def getFalse(using ctx: Ctx) = Value.Class(ctx.classCtx("False"), Ls.empty)
  
  private def eval(op: Str, x1: Value, x2: Value)(using ctx: Ctx): Opt[Value] =
    import Value.{Literal => Li}
    (op, x1, x2) match
    case ("+", Li(IntLit(x)), Li(IntLit(y))) => S(Li(IntLit(x + y)))
    case ("-", Li(IntLit(x)), Li(IntLit(y))) => S(Li(IntLit(x - y)))
    case ("*", Li(IntLit(x)), Li(IntLit(y))) => S(Li(IntLit(x * y)))
    case ("/", Li(IntLit(x)), Li(IntLit(y))) => S(Li(IntLit(x / y)))
    case ("==", Li(IntLit(x)), Li(IntLit(y))) => S(if x == y then getTrue else getFalse)
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
        case None => eval(expr) match
          case L(x) => stuck = Some(x)
          case R(x) => values += x
        case _ => ()
    } 
    stuck.toLeft(values.toList)

  private def eval(expr: TrivialExpr)(using ctx: Ctx): Result[Value] = expr match
    case e @ Ref(name) => ctx.bindingCtx.get(name.str).toRight(StuckExpr(e, s"undefined variable $name"))
    case Literal(lit) => R(Value.Literal(lit))
  
  private def eval(expr: Expr)(using ctx: Ctx): Result[Value] = expr match
    case Ref(Name(x)) => ctx.bindingCtx.get(x).toRight(StuckExpr(expr, s"undefined variable $x"))
    case Literal(x) => R(Value.Literal(x))
    case CtorApp(cls, args) => for {
        xs <- evalArgs(args)
        cls <- ctx.classCtx.get(cls.name).toRight(StuckExpr(expr, s"undefined class ${cls.name}"))
      } yield Value.Class(cls, xs)
    case Select(name, cls, field) =>
      ctx.bindingCtx.get(name.str).toRight(StuckExpr(expr, s"undefined variable $name")).flatMap {
        case Value.Class(cls2, xs) if cls.name == cls2.name =>
          xs.zip(cls2.fields).find{_._2 == field} match
            case Some((x, _)) => R(x)
            case None => L(StuckExpr(expr, s"unable to find selected field $field"))
        case Value.Class(cls2, xs) => L(StuckExpr(expr, s"unexpected class $cls2"))
        case x => L(StuckExpr(expr, s"unexpected value $x"))
      }
    case BasicOp(name, args) => boundary:
      evalArgs(args).flatMap(
        xs => 
          name match
            case "+" | "-" | "*" | "/" | "==" | "!=" | "<=" | ">=" | "<" | ">" => 
              if xs.length < 2 then break:
                L(StuckExpr(expr, s"not enough arguments for basic operation $name"))
              else eval(name, xs.head, xs.tail.head).toRight(StuckExpr(expr, s"unable to evaluate basic operation"))
            case _ => L(StuckExpr(expr, s"unexpected basic operation $name")))
    case AssignField(assignee, cls, field, value) =>
      for {
        x <- eval(Ref(assignee): TrivialExpr)
        y <- eval(value)
        res <- x match
          case obj @ Value.Class(cls2, xs) if cls.name == cls2.name =>
            xs.zip(cls2.fields).find{_._2 == field} match
              case Some((_, _)) =>
                obj.fields = xs.map(x => if x == obj then y else x)
                // Ideally, we should return a unit value here, but here we return the assignee value for simplicity.
                R(obj)
              case None => L(StuckExpr(expr, s"unable to find selected field $field"))
          case Value.Class(cls2, xs) => L(StuckExpr(expr, s"unexpected class $cls2"))
          case x => L(StuckExpr(expr, s"unexpected value $x"))
      } yield res

  private def eval(node: Node)(using ctx: Ctx): Result[Ls[Value]] = node match
    case Result(res) => evalArgs(res)
    case Jump(defn, args) => for {
        xs <- evalArgs(args)
        defn <- ctx.defnCtx.get(defn.name).toRight(StuckNode(node, s"undefined function ${defn.name}"))
        ctx1 = ctx.copy(bindingCtx = ctx.bindingCtx ++ defn.params.map{_.str}.zip(xs))
        res <- eval(defn.body)(using ctx1)
      } yield res
    case Case(scrut, cases, default) =>
      eval(Ref(scrut): Expr) flatMap {
        case Value.Class(cls, fields) => 
          cases.find {
            case (Pat.Class(cls2), _) => cls.name == cls2.name
            case _ => false
          } match {
            case Some((_, x)) => eval(x)
            case None => 
              default match
                case S(x) => eval(x)
                case N => L(StuckNode(node, s"can not find the matched case, ${cls.name} expected"))
          }
        case Value.Literal(lit) => 
          cases.find {
            case (Pat.Lit(lit2), _) => lit == lit2
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
      for {
        x <- eval(expr)
        ctx1 = ctx.copy(bindingCtx = ctx.bindingCtx + (name.str -> x))
        res <- eval(body)(using ctx1)
      } yield res
    case LetMethodCall(names, cls, method, args, body) =>
      for {
        ys <- evalArgs(args).flatMap {
          case Value.Class(cls2, xs) :: args =>
            cls2.methods.get(method.str).toRight(StuckNode(node, s"undefined method ${method.str}")).flatMap { method =>
              val ctx1 = ctx.copy(bindingCtx = ctx.bindingCtx ++ cls2.fields.zip(xs) ++ method.params.map{_.str}.zip(args))
              eval(method.body)(using ctx1)
            }
          case _ => L(StuckNode(node, s"not enough arguments for method call, or the first argument is not a class"))
        }
        ctx2 = ctx.copy(bindingCtx = ctx.bindingCtx ++ names.map{_.str}.zip(ys))
        res <- eval(body)(using ctx2)
      } yield res
    // case LetApply(names, fn, args, body) => eval(LetMethodCall(names, ClassRef(R("Callable")), Name("apply" + args.length), (Ref(fn): TrivialExpr) :: args, body))
    case LetCall(names, defn, args, _, body) =>
      for {
        xs <- evalArgs(args)
        defn <- ctx.defnCtx.get(defn.name).toRight(StuckNode(node, s"undefined function ${defn.name}"))
        ctx1 = ctx.copy(bindingCtx = ctx.bindingCtx ++ defn.params.map{_.str}.zip(xs))
        ys <- eval(defn.body)(using ctx1)
        ctx2 = ctx.copy(bindingCtx = ctx.bindingCtx ++ names.map{_.str}.zip(ys))
        res <- eval(body)(using ctx2)
      } yield res

  private def f(prog: Program): Ls[Value] =
    val Program(classes, defs, main) = prog
    given Ctx = Ctx(
      bindingCtx = Map.empty,
      classCtx = classes.map{cls => cls.name -> cls}.toMap,
      defnCtx = defs.map{defn => defn.name -> defn}.toMap,
    )
    eval(main) match
      case R(x) => x
      case L(x) => throw InterpreterError("Stuck evaluation: " + x.toString)
    
  def interpret(prog: Program): Str =
    val node = f(prog) 
    node.map(_.toString).mkString(",")
