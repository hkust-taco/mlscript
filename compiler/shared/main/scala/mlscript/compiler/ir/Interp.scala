package mlscript.compiler.ir

import mlscript._
import mlscript.compiler._
import mlscript.compiler.ir.{Node => INode, Expr => IExpr, Program => IProgram, Defn => IDefn, DefnRef => IDefnRef}
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
    case Jump(defn: DefnRef, args: Ls[Expr])
    case Case(scrut: Name, cases: Ls[(ClassInfo, Node)])
    case LetExpr(name: Name, expr: Expr, body: Node)
    case LetJoin(joinName: Name, params: Ls[Name], rhs: Node, body: Node)
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
    case INode.Case(scrut, cases) => Case(scrut, cases.map{(cls, node) => (cls, node |> convert)})
    case INode.LetExpr(name, expr, body) => LetExpr(name, expr |> convert, body |> convert)
    case INode.LetCall(xs, defnref, args, body) =>
      LetCall(xs, DefnRef(Right(defnref.getName)), args |> convertArgs, body |> convert)

  private def convert(defn: IDefn): Defn =
    Defn(defn.name, defn.params, defn.body |> convert)

  private def resolveDefnRef(defs: Set[Defn], node: Node): Unit = node match
    case Case(_, cases) => cases.foreach { case (cls, node) => resolveDefnRef(defs, node) }
    case LetExpr(name, expr, body) => resolveDefnRef(defs, body)
    case LetJoin(joinName, params, rhs, body) => resolveDefnRef(defs, body)
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

  private def unifyEvalResult[A](x: Either[A, A]) =
    x match
      case Left(expr) => expr
      case Right(expr) => expr 

  private def evalArgs(using ctx: Ctx, clsctx: ClassCtx)(exprs: Ls[Expr]): Either[Ls[Expr], Ls[Expr]] = 
    var changed = false
    val xs = exprs.map {
      arg => eval(arg) match
        case Left(expr) => changed = true; expr
        case Right(expr) => expr
    }
    if (changed) Left(xs) else Right(exprs)

  private def evalArgsMayNotProgress(using ctx: Ctx, clsctx: ClassCtx)(exprs: Ls[Expr]) = 
    exprs.map {
      arg => eval(arg) |> unifyEvalResult
    }

  private def evalMayNotProgress(using ctx: Ctx, clsctx: ClassCtx)(expr: Expr) = eval(expr) |> unifyEvalResult
    
  private def eval(using ctx: Ctx, clsctx: ClassCtx)(expr: Expr): Either[Expr, Expr] = expr match
    case Ref(Name(x)) => ctx.get(x).toLeft(expr)
    case Literal(x) => Right(expr)
    case CtorApp(name, args) =>
      evalArgs(args) match
        case Left(xs) => Left(CtorApp(name, xs)) 
        case _ => Right(expr)
    case Select(name, cls, field) => 
      ctx.get(name.str).map {
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
          eval(using ctx, clsctx)(name, xs.head, xs.tail.head)
        case _ => throw IRInterpreterError("unexpected basic operation")
      x.toLeft(expr)

  private def expectDefn(r: DefnRef) = r.defn match
    case Left(value) => value
    case Right(value) => throw IRInterpreterError("only has the name of definition")

  private def evalMayNotProgress(using ctx: Ctx, clsctx: ClassCtx)(node: Node) = eval(node) |> unifyEvalResult

  @tailrec
  private def eval(using ctx: Ctx, clsctx: ClassCtx)(node: Node): Either[Node, Node] = node match
    case Result(xs) =>
      xs |> evalArgs match
        case Left(xs) => Left(Result(xs))
        case _ => Right(node)
    case Jump(defnref, args) =>
      val xs = args |> evalArgsMayNotProgress
      val defn = defnref |> expectDefn
      val ctx1 = ctx ++ defn.params.map{_.str}.zip(xs)
      eval(using ctx1, clsctx)(defn.body)
    case Case(scrut, cases) =>
      val CtorApp(cls, xs) = (Ref(scrut):Expr) |> evalMayNotProgress(using ctx, clsctx) match {
        case x: CtorApp => x
        case x => throw IRInterpreterError(s"not a class $x")
      }
      val arm = cases.find{_._1 == cls} match {
        case Some((_, x)) => x
        case _ => throw IRInterpreterError(s"can not find the matched case, $cls expected")
      }
      eval(arm)
    case LetExpr(name, expr, body) =>
      val x = evalMayNotProgress(expr)
      val ctx1 = ctx + (name.str -> x)
      eval(using ctx1, clsctx)(body)
    case LetCall(xs, defnref, args, body) =>
      val defn = defnref |> expectDefn
      val ys = args |> evalArgsMayNotProgress
      val ctx1 = ctx ++ defn.params.map{_.str}.zip(ys)
      val res = evalMayNotProgress(using ctx1, clsctx)(defn.body) match {
        case Result(xs) => xs
        case _ => throw IRInterpreterError("unexpected node")
      }
      val ctx2 = ctx ++ xs.map{_.str}.zip(res)
      eval(using ctx2, clsctx)(body)
    case _ => throw IRInterpreterError("unexpected node")

  private def interpret(prog: Program): Node =
    val Program(classes, defs, main) = prog
    val clsctx = classes.map(x => x.ident -> x).toMap
    evalMayNotProgress(using Map.empty, clsctx)(main)
    
  def interpret(irprog: ir.Program): Str =
    val prog = convert(irprog)
    val node = interpret(prog) 
    node.show
