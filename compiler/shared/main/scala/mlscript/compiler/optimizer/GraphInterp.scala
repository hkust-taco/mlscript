package mlscript.compiler.optimizer

import mlscript.*
import mlscript.compiler.*
import mlscript.compiler.optimizer.*
import mlscript.utils.*
import shorthands.*
import scala.collection.immutable.*
import scala.annotation.*

final case class GraphInterpreterError(message: String) extends Exception(message)

class GraphInterpreter(verbose: Bool):
  private def log(x: Any) = if verbose then println(x)
  private case class Program(
    classes: Set[ClassInfo],
    defs: Set[Def],
    main: Node,
  )

  private case class Def(
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
  
    private def show_args(args: Ls[Expr]) = args map { x => x.show } mkString ","

    def document: Document = this match
      case Ref(Name(s)) => s |> raw
      case Literal(IntLit(lit)) => s"$lit" |> raw
      case Literal(DecLit(lit)) => s"$lit" |> raw
      case Literal(StrLit(lit)) => s"$lit" |> raw
      case Literal(UnitLit(lit)) => s"$lit" |> raw
      case CtorApp(ClassInfo(_, name, _), args) =>
        raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")
      case Select(Name(s), _, fld) =>
        raw(s) <#> raw(".") <#> raw(fld)
      case BasicOp(name: Str, args) =>
        raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")

  private enum Node:
    case Result(res: Ls[Expr])
    case Jump(defn: DefRef, args: Ls[Expr])
    case Case(scrut: Name, cases: Ls[(ClassInfo, Node)])
    case LetExpr(name: Name, expr: Expr, body: Node)
    case LetJoin(joinName: Name, params: Ls[Name], rhs: Node, body: Node)
    case LetCall(resultNames: Ls[Name], defn: DefRef, args: Ls[Expr], body: Node)

    def show: Str =
      document.print

    private def show_args(args: Ls[Expr]) = args map { x => x.show } mkString ","

    def document: Document = this match
      case Result(res) => raw(res |> show_args)
      case Jump(jp, args) =>
        raw("jump")
        <:> raw(jp.name)
        <#> raw("(")
        <#> raw(args |> show_args)
        <#> raw(")") 
      case Case(Name(x), Ls((tcls, tru), (fcls, fls))) if tcls.ident == "True" && fcls.ident == "False" =>
        val first = raw("if") <:> raw(x)
        val tru2 = indent(raw("true") <:> raw ("=>") <:> tru.document)
        val fls2 = indent(raw("false") <:> raw ("=>") <:> fls.document)
        Document.Stacked(Ls(first, tru2, fls2))
      case Case(Name(x), cases) =>
        val first = raw("case") <:> raw(x) <:> raw("of")
        val other = cases map {
          case (ClassInfo(_, name, _), node) =>
            indent(raw(name) <:> raw("=>") <:> node.document)
        }
        Document.Stacked(first :: other)
      case LetExpr(Name(x), expr, body) => 
        stack(
          raw("let")
            <:> raw(x)
            <:> raw("=")
            <:> expr.document,
          raw("in") <:> body.document |> indent)
      case LetJoin(Name(x), params, rhs, body) =>
        stack(
          raw("let")
            <:> raw("join")
            <:> raw(x)
            <#> raw("(")
            <#> raw(params.map{ x => x.toString }.mkString(","))
            <#> raw(")")
            <:> raw("=")
            <:> (rhs.document |> indent |> indent),
          raw("in") <:> body.document |> indent
        )
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
  
  private class DefRef(var defn: Either[Def, Str]):
    def name = defn match
      case Left(defn) => defn.name
      case Right(name) => name

  import Node._
  import Expr._

  private def convert(texpr: TrivialExpr): Expr = texpr match
    case GOExpr.Ref(x) => Ref(x)
    case GOExpr.Literal(x) => Literal(x)

  private def convert_args(xs: Ls[TrivialExpr]): Ls[Expr] = xs.map(convert)

  private def convert(expr: GOExpr): Expr = expr match
    case GOExpr.Ref(x) => Ref(x)
    case GOExpr.Literal(x) => Literal(x)
    case GOExpr.CtorApp(name, args) => CtorApp(name, args |> convert_args)
    case GOExpr.Select(name, cls, field) => Select(name, cls, field)
    case GOExpr.BasicOp(name, args) => BasicOp(name, args |> convert_args)

  private def convert(node: GONode): Node = node match
    case GONode.Result(xs) => Result(xs |> convert_args)
    case GONode.Jump(defnref, args) => Jump(DefRef(Right(defnref.getName)), args |> convert_args)
    case GONode.Case(scrut, cases) => Case(scrut, cases.map{(cls, node) => (cls, node |> convert)})
    case GONode.LetExpr(name, expr, body) => LetExpr(name, expr |> convert, body |> convert)
    case GONode.LetCall(xs, defnref, args, body) =>
      LetCall(xs, DefRef(Right(defnref.getName)), args |> convert_args, body |> convert)

  private def convert(defn: GODef): Def =
    Def(defn.name, defn.params, defn.body |> convert)

  private def fix_cross_ref(defs: Set[Def], node: Node): Unit = node match
    case Case(_, cases) => cases.foreach { case (cls, node) => fix_cross_ref(defs, node) }
    case LetExpr(name, expr, body) => fix_cross_ref(defs, body)
    case LetJoin(joinName, params, rhs, body) => fix_cross_ref(defs, body)
    case Jump(defnref, args) => defnref.defn = Left(defs.find(_.name == defnref.name).get)
    case LetCall(xs, defnref, args, body) =>
      defnref.defn = Left(defs.find(_.name == defnref.name).get)
      fix_cross_ref(defs, body)
    case _ =>

  private def convert(prog: GOProgram): Program =
    val classes = prog.classes
    val old_defs = prog.defs
    val old_main = prog.main

    val defs: Set[Def] = old_defs.map(convert)
    defs.foreach {
      case Def(_, _, body) => fix_cross_ref(defs, body)
    }

    val main = convert(old_main)
    fix_cross_ref(defs, main)

    Program(classes, defs, main)

  private type Ctx = Map[Str, Expr]
  private type ClassCtx = Map[Str, ClassInfo]

  private def getTrue(using clsctx: ClassCtx) = CtorApp(clsctx("True"), Ls.empty)
  private def getFalse(using clsctx: ClassCtx) = CtorApp(clsctx("False"), Ls.empty)

  private def eval(using ctx: Ctx, clsctx: ClassCtx)(op: Str, x1: Expr, x2: Expr): Opt[Expr] = (op, x1, x2) match
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

  private def eval_args(using ctx: Ctx, clsctx: ClassCtx)(exprs: Ls[Expr]): Either[Ls[Expr], Ls[Expr]] = 
    var changed = false
    val xs = exprs.map {
      arg => eval(arg) match
        case Left(expr) => changed = true; expr
        case Right(expr) => expr
    }
    if (changed) Left(xs) else Right(exprs)

  private def eval_args_may_not_progress(using ctx: Ctx, clsctx: ClassCtx)(exprs: Ls[Expr]) = 
    exprs.map {
      arg => eval(arg) match
        case Left(expr) => expr
        case Right(expr) => expr
    }

  private def eval_may_not_progress(using ctx: Ctx, clsctx: ClassCtx)(expr: Expr) = eval(expr) match
    case Left(x) => x
    case Right(x) => x
    
  private def eval(using ctx: Ctx, clsctx: ClassCtx)(expr: Expr): Either[Expr, Expr] = expr match
    case Ref(Name(x)) => ctx.get(x).toLeft(expr)
    case Literal(x) => Right(expr)
    case CtorApp(name, args) =>
      eval_args(args) match
        case Left(xs) => Left(CtorApp(name, xs)) 
        case _ => Right(expr)
    case Select(name, cls, field) => 
      ctx.get(name.str).map {
        case CtorApp(cls2, xs) if cls == cls2 =>
          xs.zip(cls2.fields).find{_._2 == field} match
            case Some((x, _)) => x
            case None => throw GraphInterpreterError("unable to find selected field")
        case _ => throw GraphInterpreterError("unexpected node")
      }.toLeft(expr)
    case BasicOp(name, args) =>
      val xs = eval_args_may_not_progress(args)
      val x = name match
        case "+" | "-" | "*" | "/" | "==" | "!=" | "<=" | ">=" | "<" | ">" => 
          eval(using ctx, clsctx)(name, xs.head, xs.tail.head)
        case _ => throw GraphInterpreterError("unexpected basic operation")
      x.toLeft(expr)

  private def expect_def(r: DefRef) = r.defn match
    case Left(value) => value
    case Right(value) => throw GraphInterpreterError("only has the name of definition")

  private def eval_may_not_progress(using ctx: Ctx, clsctx: ClassCtx)(node: Node) = eval(node) match
    case Left(x) => x
    case Right(x) => x

  @tailrec
  private def eval(using ctx: Ctx, clsctx: ClassCtx)(node: Node): Either[Node, Node] = node match
    case Result(xs) =>
      xs |> eval_args match
        case Left(xs) => Left(Result(xs))
        case _ => Right(node)
    case Jump(defnref, args) =>
      val xs = args |> eval_args_may_not_progress
      val defn = defnref |> expect_def
      val ctx1 = ctx ++ defn.params.map{_.str}.zip(xs)
      eval(using ctx1, clsctx)(defn.body)
    case Case(scrut, cases) =>
      val CtorApp(cls, xs) = (Ref(scrut):Expr) |> eval_may_not_progress(using ctx, clsctx) match {
        case x: CtorApp => x
        case x => throw GraphInterpreterError(s"not a class $x")
      }
      val arm = cases.find{_._1 == cls} match {
        case Some((_, x)) => x
        case _ => throw GraphInterpreterError(s"can not find the matched case, $cls expected")
      }
      eval(arm)
    case LetExpr(name, expr, body) =>
      val x = eval_may_not_progress(expr)
      val ctx1 = ctx + (name.str -> x)
      eval(using ctx1, clsctx)(body)
    case LetCall(xs, defnref, args, body) =>
      val defn = defnref |> expect_def
      val ys = args |> eval_args_may_not_progress
      val ctx1 = ctx ++ defn.params.map{_.str}.zip(ys)
      val res = eval_may_not_progress(using ctx1, clsctx)(defn.body) match {
        case Result(xs) => xs
        case _ => throw GraphInterpreterError("unexpected node")
      }
      val ctx2 = ctx ++ xs.map{_.str}.zip(res)
      eval(using ctx2, clsctx)(body)
    case _ => throw GraphInterpreterError("unexpected node")

  private def interpret(prog: Program): Node =
    val Program(classes, defs, main) = prog
    val clsctx = classes.map(x => x.ident -> x).toMap
    eval_may_not_progress(using Map.empty, clsctx)(main)
    
  def interpret(goprog: GOProgram): Str =
    val prog = convert(goprog)
    val node = interpret(prog) 
    node.show
