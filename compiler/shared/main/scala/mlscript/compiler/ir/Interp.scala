package mlscript.compiler.ir

import mlscript._
import mlscript.compiler._
import mlscript.compiler.ir.{Node => INode, Expr => IExpr, Program => IProgram, Defn => IDefn, DefnRef => IDefnRef}
import mlscript.compiler.utils._
import mlscript.compiler.optimizer._
import mlscript.utils._
import scala.collection.immutable._
import scala.annotation._
import shorthands._

final case class IRInterpreterError(message: String) extends Exception(message)

class Interpreter(verbose: Bool):
  private def log(x: Any) = if verbose then println(x)

  // We have a similar definition of IR here to represent the result of the interpreter.
  // This is because IR itself is in A-normal form.
  // It represent terms, e.g. "Pair(True, False)", like:
  //   let x = CtorApp(True, []) in
  //   let y = CtorApp(False, []) in
  //   let z = CtorApp(Pair, [x, y]) in
  //   z
  // But I don't want the result of an interpreter to be like this.
  // So we release the limitation of the ANF IR here and allow expressions in argument position.

  private case class Program(
    classes: Set[ClassInfo],
    defs: Set[Defn],
    main: Node,
  )

  private case class Defn(
    val name: Str,
    val params: Ls[Name],
    val body: Node,
  )

  private enum Expr:
    case Ref(name: Name)
    case Literal(lit: Lit)
    case CtorApp(name: ClassInfo, args: Ls[Expr])
    case Select(name: Name, cls: ClassInfo, field: Str)
    case BasicOp(name: Str, args: Ls[Expr])
  
    def show: Str =
      document.print
  
    private def showArgs(args: Ls[Expr]) = args map { x => x.show } mkString ","

    def document: Document = this match
      case Ref(Name(s)) => s |> raw
      case Literal(IntLit(lit)) => s"$lit" |> raw
      case Literal(DecLit(lit)) => s"$lit" |> raw
      case Literal(StrLit(lit)) => s"$lit" |> raw
      case Literal(CharLit(lit)) => s"'$lit'" |> raw
      case Literal(UnitLit(lit)) => s"$lit" |> raw
      case CtorApp(ClassInfo(_, name, _), args) =>
        raw(name) <#> raw("(") <#> raw(args |> showArgs) <#> raw(")")
      case Select(Name(s), _, fld) =>
        raw(s) <#> raw(".") <#> raw(fld)
      case BasicOp(name: Str, args) =>
        raw(name) <#> raw("(") <#> raw(args |> showArgs) <#> raw(")")

  private enum Node:
    case Result(res: Ls[Expr])
    case Jump(defn: DefnRef, args: Ls[Expr])
    case Case(scrut: Name, cases: Ls[(Pat, Node)], default: Opt[Node])
    case LetExpr(name: Name, expr: Expr, body: Node)
    case LetApply(name: Ls[Name], fn: Name, args: Ls[Expr], body: Node)
    case LetCall(resultNames: Ls[Name], defn: DefnRef, args: Ls[Expr], body: Node)

    def show: Str =
      document.print

    private def showArgs(args: Ls[Expr]) = args map { x => x.show } mkString ","

    def document: Document = this match
      case Result(res) => raw(res |> showArgs)
      case Jump(jp, args) =>
        raw("jump")
        <:> raw(jp.name)
        <#> raw("(")
        <#> raw(args |> showArgs)
        <#> raw(")") 
      case Case(Name(x), Ls((tpat, tru), (fpat, fls)), N) if tpat.isTrue && fpat.isTrue =>
        val first = raw("if") <:> raw(x)
        val tru2 = indent(raw("true") <:> raw ("=>") <:> tru.document)
        val fls2 = indent(raw("false") <:> raw ("=>") <:> fls.document)
        Document.Stacked(Ls(first, tru2, fls2))
      case Case(Name(x), cases, default) =>
        val first = raw("case") <:> raw(x) <:> raw("of")
        val other = cases map {
          case (pat, node) =>
            raw(pat.toString) <:> raw("=>") <:> node.document
        }
        default match
          case N => stack(first, (Document.Stacked(other) |> indent))
          case S(dc) =>
            val default = raw("_") <:> raw("=>") <:> dc.document
            stack(first, (Document.Stacked(other :+ default) |> indent))
      case LetExpr(Name(x), expr, body) => 
        stack(
          raw("let")
            <:> raw(x)
            <:> raw("=")
            <:> expr.document,
          raw("in") <:> body.document |> indent)
      case LetApply(resultNames, Name(fn), rhs, body) =>
        stack(
          raw("let")
            <:> raw("(")
            <#> raw(resultNames.map{ x => x.toString }.mkString(","))
            <#> raw(")")
            <:> raw(fn),
          raw("in") <:> body.document |> indent)
      case LetCall(resultNames, defn, args, body) => 
        stack(
          raw("let*")
            <:> raw("(")
            <#> raw(resultNames.map{ x => x.toString }.mkString(","))
            <#> raw(")")
            <:> raw("=")
            <:> raw(defn.name)
            <#> raw("(")
            <#> raw(args.map{ x => x.toString }.mkString(","))
            <#> raw(")"),
          raw("in") <:> body.document |> indent
        )
  
  private class DefnRef(var defn: Either[Defn, Str]):
    def name = defn match
      case Left(defn) => defn.name
      case Right(name) => name

  import Node._
  import Expr._

  private def convert(texpr: ir.TrivialExpr): Expr = texpr match
    case IExpr.Ref(x) => Ref(x)
    case IExpr.Literal(x) => Literal(x)

  private def convertArgs(xs: Ls[ir.TrivialExpr]): Ls[Expr] = xs.map(convert)

  private def convert(expr: IExpr): Expr = expr match
    case IExpr.Ref(x) => Ref(x)
    case IExpr.Literal(x) => Literal(x)
    case IExpr.CtorApp(name, args) => CtorApp(name, args |> convertArgs)
    case IExpr.Select(name, cls, field) => Select(name, cls, field)
    case IExpr.BasicOp(name, args) => BasicOp(name, args |> convertArgs)

  private def convert(node: INode): Node = node match
    case INode.Result(xs) => Result(xs |> convertArgs)
    case INode.Jump(defnref, args) => Jump(DefnRef(Right(defnref.getName)), args |> convertArgs)
    case INode.Case(scrut, cases, default) => Case(scrut, cases.map{(cls, node) => (cls, node |> convert)}, default map convert)
    case INode.LetExpr(name, expr, body) => LetExpr(name, expr |> convert, body |> convert)
    case INode.LetApply(name, fn, args, body) => LetApply(name, fn, args |> convertArgs, body |> convert)
    case INode.LetCall(xs, defnref, args, body) =>
      LetCall(xs, DefnRef(Right(defnref.getName)), args |> convertArgs, body |> convert)

  private def convert(defn: IDefn): Defn =
    Defn(defn.name, defn.params, defn.body |> convert)

  private def resolveDefnRef(defs: Set[Defn], node: Node): Unit = node match
    case Case(_, cases, default) => cases.foreach { case (cls, node) => resolveDefnRef(defs, node) }; default.foreach(resolveDefnRef(defs, _))
    case LetExpr(name, expr, body) => resolveDefnRef(defs, body)
    case LetApply(_, _, _, body) => resolveDefnRef(defs, body)
    case Jump(defnref, args) => defnref.defn = Left(defs.find(_.name == defnref.name).get)
    case LetCall(xs, defnref, args, body) =>
      defnref.defn = Left(defs.find(_.name == defnref.name).get)
      resolveDefnRef(defs, body)
    case _ =>

  private def convert(prog: IProgram): Program =
    val classes = prog.classes
    val old_defs = prog.defs
    val old_main = prog.main

    val defs: Set[Defn] = old_defs.map(convert)
    defs.foreach {
      case Defn(_, _, body) => resolveDefnRef(defs, body)
    }

    val main = convert(old_main)
    resolveDefnRef(defs, main)

    Program(classes, defs, main)

  private final case class Ctx(
    val bindCtx: Map[Str, Expr],
    val classCtx: Map[Str, ClassInfo],
    val defnCtx: Map[Str, Defn],
  )

  private def getTrue(using ctx: Ctx) = CtorApp(ctx.classCtx("True"), Ls.empty)
  private def getFalse(using ctx: Ctx) = CtorApp(ctx.classCtx("False"), Ls.empty)

  private def eval(using ctx: Ctx)(op: Str, x1: Expr, x2: Expr): Opt[Expr] = (op, x1, x2) match
    case ("+", Literal(IntLit(x)), Literal(IntLit(y))) => Some(Literal(IntLit(x + y)))
    case ("-", Literal(IntLit(x)), Literal(IntLit(y))) => Some(Literal(IntLit(x - y)))
    case ("*", Literal(IntLit(x)), Literal(IntLit(y))) => Some(Literal(IntLit(x * y)))
    case ("/", Literal(IntLit(x)), Literal(IntLit(y))) => Some(Literal(IntLit(x / y)))
    case ("==", Literal(IntLit(x)), Literal(IntLit(y))) => Some(if x == y then getTrue else getFalse)
    case ("!=", Literal(IntLit(x)), Literal(IntLit(y))) => Some(if x != y then getTrue else getFalse)
    case ("<=", Literal(IntLit(x)), Literal(IntLit(y))) => Some(if x <= y then getTrue else getFalse)
    case (">=", Literal(IntLit(x)), Literal(IntLit(y))) => Some(if x >= y then getTrue else getFalse)
    case (">", Literal(IntLit(x)), Literal(IntLit(y))) => Some(if x > y then getTrue else getFalse)
    case ("<", Literal(IntLit(x)), Literal(IntLit(y))) => Some(if x < y then getTrue else getFalse)
    case _ => None

  private def unifyEvalResult[A](x: Either[A, A]) =
    x match
      case Left(expr) => expr
      case Right(expr) => expr 

  private def evalArgs(using ctx: Ctx)(exprs: Ls[Expr]): Either[Ls[Expr], Ls[Expr]] = 
    var changed = false
    val xs = exprs.map {
      arg => eval(arg) match
        case Left(expr) => changed = true; expr
        case Right(expr) => expr
    }
    if (changed) Left(xs) else Right(exprs)

  private def evalArgsMayNotProgress(using ctx: Ctx)(exprs: Ls[Expr]) = 
    exprs.map {
      arg => eval(arg) |> unifyEvalResult
    }

  private def evalMayNotProgress(using ctx: Ctx)(expr: Expr) = eval(expr) |> unifyEvalResult
    
  private def eval(using ctx: Ctx)(expr: Expr): Either[Expr, Expr] = expr match
    case Ref(Name(x)) => ctx.bindCtx.get(x).toLeft(expr)
    case Literal(x) => Right(expr)
    case CtorApp(name, args) =>
      evalArgs(args) match
        case Left(xs) => Left(CtorApp(name, xs)) 
        case _ => Right(expr)
    case Select(name, cls, field) => 
      ctx.bindCtx.get(name.str).map {
        case CtorApp(cls2, xs) if cls == cls2 =>
          xs.zip(cls2.fields).find{_._2 == field} match
            case Some((x, _)) => x
            case None => throw IRInterpreterError("unable to find selected field")
        case x @ _ => throw IRInterpreterError(s"unexpected node: select $field but got $x when eval $expr")
      }.toLeft(expr)
    case BasicOp(name, args) =>
      val xs = evalArgsMayNotProgress(args)
      val x = name match
        case "+" | "-" | "*" | "/" | "==" | "!=" | "<=" | ">=" | "<" | ">" => 
          eval(using ctx)(name, xs.head, xs.tail.head)
        case _ => throw IRInterpreterError("unexpected basic operation")
      x.toLeft(expr)

  private def expectDefn(r: DefnRef) = r.defn match
    case Left(value) => value
    case Right(value) => throw IRInterpreterError("only has the name of definition")

  private def evalMayNotProgress(using ctx: Ctx)(node: Node) = eval(node) |> unifyEvalResult

  @tailrec
  private def eval(using ctx: Ctx)(node: Node): Either[Node, Node] = node match
    case Result(xs) =>
      xs |> evalArgs match
        case Left(xs) => Left(Result(xs))
        case _ => Right(node)
    case Jump(defnref, args) =>
      val xs = args |> evalArgsMayNotProgress
      val defn = defnref |> expectDefn
      val ctx1 = ctx.copy(bindCtx = ctx.bindCtx ++ defn.params.map{_.str}.zip(xs))
      eval(using ctx1)(defn.body)
    case Case(scrut, cases, default) =>
      val arm = (Ref(scrut):Expr) |> evalMayNotProgress(using ctx) match {
        case CtorApp(cls, xs) =>
          cases.find{
            case (Pat.Class(cls2), _) => cls == cls2
            case _ => false
          } match {
            case Some((_, x)) => x
            case _ =>
              default match
                case S(x) => x
                case N =>throw IRInterpreterError(s"can not find the matched case, $cls expected")
          }
        case Literal(lit) =>
          cases.find{
            case (Pat.Lit(lit2), _) => lit == lit2
            case _ => false
          } match {
            case Some((_, x)) => x
            case _ => 
              default match
                case S(x) => x
                case N =>throw IRInterpreterError(s"can not find the matched case, $lit expected")
          }
        case x => throw IRInterpreterError(s"not a class $x")
      }
      eval(arm)
    case LetExpr(name, expr, body) =>
      val x = evalMayNotProgress(expr)
      val ctx1 = ctx.copy(bindCtx = ctx.bindCtx + (name.str -> x))
      eval(using ctx1)(body)
    case LetApply(xs, fn, args, body) =>
      val ys = args |> evalArgsMayNotProgress
      ctx.bindCtx.get(fn.str) match
        case None => throw IRInterpreterError(s"undefined function variable $fn")
        case Some(value) => 
          val defn = value match
            case Ref(Name(fn)) => ctx.defnCtx.get(fn) match
              case Some(defn) => defn
              case None => throw IRInterpreterError(s"undefined function $fn")
            case x @ _ => throw IRInterpreterError(s"undefined function $x")
          val ctx1 = ctx.copy(bindCtx = ctx.bindCtx ++ defn.params.map{_.str}.zip(ys))
          val res = evalMayNotProgress(using ctx1)(defn.body) match {
            case Result(xs) => xs
            case _ => throw IRInterpreterError("unexpected node")
          }
          val ctx2 = ctx1.copy(bindCtx = ctx1.bindCtx ++ xs.map{_.str}.zip(res))
          eval(using ctx2)(body)
       
    case LetCall(xs, defnref, args, body) =>
      val defn = defnref |> expectDefn
      val ys = args |> evalArgsMayNotProgress
      val ctx1 = ctx.copy(bindCtx = ctx.bindCtx ++ defn.params.map{_.str}.zip(ys))
      val res = evalMayNotProgress(using ctx1)(defn.body) match {
        case Result(xs) => xs
        case _ => throw IRInterpreterError("unexpected node")
      }
      val ctx2 = ctx1.copy(bindCtx = ctx1.bindCtx ++ xs.map{_.str}.zip(res))
      eval(using ctx2)(body)

  private def interpret(prog: Program): Node =
    val Program(classes, defs, main) = prog
    val clsctx = classes.map(x => x.ident -> x).toMap
    val defctx = defs.map(x => x.name -> x).toMap
    evalMayNotProgress(using Ctx(Map.empty, clsctx, defctx))(main)
    
  def interpret(irprog: ir.Program): Str =
    val prog = convert(irprog)
    val node = interpret(prog) 
    node.show
