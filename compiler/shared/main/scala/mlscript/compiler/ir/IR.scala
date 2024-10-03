package mlscript.compiler.ir

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import mlscript.compiler.ir._
import mlscript.compiler.optimizer._

import collection.mutable.{Map as MutMap, Set as MutSet, HashMap, ListBuffer}
import annotation.unused
import util.Sorting
import scala.collection.immutable.SortedSet

final case class IRError(message: String) extends Exception(message)

case class Program(
  classes: Set[ClassInfo],
  defs: Set[Defn],
  main: Node,
):
  override def toString: String =
    val t1 = classes.toArray
    val t2 = defs.toArray
    Sorting.quickSort(t1)
    Sorting.quickSort(t2)
    s"Program({${t1.mkString(",")}}, {\n${t2.mkString("\n")}\n},\n$main)"

implicit object ClassInfoOrdering extends Ordering[ClassInfo] {
  def compare(a: ClassInfo, b: ClassInfo) = a.id.compare(b.id)
}

case class ClassInfo(
  id: Int,
  ident: Str,
  fields: Ls[Str],
):
  override def hashCode: Int = id
  override def toString: String =
    s"ClassInfo($id, $ident, [${fields mkString ","}])"

case class Name(str: Str):
  def copy: Name = Name(str)
  def trySubst(map: Map[Str, Name]) = map.getOrElse(str, this)
  
  override def toString: String =
    str

class DefnRef(var defn: Either[Defn, Str]):
  def getName: String = defn.fold(_.getName, x => x)
  def expectDefn: Defn = defn match {
    case Left(godef) => godef
    case Right(name) => throw Exception(s"Expected a def, but got $name")
  }
  def getDefn: Opt[Defn] = defn.left.toOption
  override def equals(o: Any): Bool = o match {
    case o: DefnRef => o.getName == this.getName
    case _ => false
  }


implicit object DefOrdering extends Ordering[Defn] {
  def compare(a: Defn, b: Defn) = a.id.compare(b.id)
}

case class Defn(
  val id: Int,
  val name: Str,
  val params: Ls[Name],
  val resultNum: Int,
  val body: Node
):
  override def hashCode: Int = id
  def getName: String = name

  override def toString: String =
    val ps = params.map(_.toString).mkString("[", ",", "]")
    s"Def($id, $name, $ps,\n$resultNum, \n$body\n)"

sealed trait TrivialExpr:
  import Expr._
  override def toString: String
  def show: String
  def toDocument: Document

  def mapNameOfTrivialExpr(f: Name => Name): TrivialExpr = this match
    case x: Ref => Ref(f(x.name))
    case x: Literal => x

  def toExpr: Expr = this match { case x: Expr => x }

private def show_args(args: Ls[TrivialExpr]) = args map (_.show) mkString ","

enum Expr:
  case Ref(name: Name) extends Expr, TrivialExpr 
  case Literal(lit: Lit) extends Expr, TrivialExpr
  case CtorApp(name: ClassInfo, args: Ls[TrivialExpr])
  case Select(name: Name, cls: ClassInfo, field: Str)
  case BasicOp(name: Str, args: Ls[TrivialExpr])
  
  override def toString: String = show

  def show: String =
    toDocument.print
  
  def toDocument: Document = this match
    case Ref(s) => s.toString |> raw
    case Literal(IntLit(lit)) => s"$lit" |> raw
    case Literal(DecLit(lit)) => s"$lit" |> raw
    case Literal(StrLit(lit)) => s"$lit" |> raw
    case Literal(UnitLit(lit)) => s"$lit" |> raw
    case CtorApp(ClassInfo(_, name, _), args) =>
      raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")
    case Select(s, _, fld) =>
      raw(s.toString) <#> raw(".") <#> raw(fld)
    case BasicOp(name: Str, args) =>
      raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")

  def mapName(f: Name => Name): Expr = this match
    case Ref(name) => Ref(f(name))
    case Literal(lit) => Literal(lit)
    case CtorApp(cls, args) => CtorApp(cls, args.map(_.mapNameOfTrivialExpr(f)))
    case Select(x, cls, field) => Select(f(x), cls, field)
    case BasicOp(name, args) => BasicOp(name, args.map(_.mapNameOfTrivialExpr(f)))

  def locMarker: LocMarker = this match
    case Ref(name) => LocMarker.MRef(name.str)
    case Literal(lit) => LocMarker.MLit(lit)
    case CtorApp(name, args) => LocMarker.MCtorApp(name, args.map(_.toExpr.locMarker))
    case Select(name, cls, field) => LocMarker.MSelect(name.str, cls, field)
    case BasicOp(name, args) => LocMarker.MBasicOp(name, args.map(_.toExpr.locMarker))
  

enum Node:
  // Terminal forms:
  case Result(res: Ls[TrivialExpr])
  case Jump(defn: DefnRef, args: Ls[TrivialExpr])
  case Case(scrut: Name, cases: Ls[(ClassInfo, Node)])
  // Intermediate forms:
  case LetExpr(name: Name, expr: Expr, body: Node)
  case LetCall(names: Ls[Name], defn: DefnRef, args: Ls[TrivialExpr], body: Node)

  var tag = DefnTag(-1)

  def attachTag(x: FreshInt): Node =
    this.tag = DefnTag(x.make)
    this
  def attachTagAs[V](x: FreshInt): V =
    attachTag(x).asInstanceOf[V]
  def copyTag(x: Node) =
    this.tag = x.tag
    this

  override def toString: String = show

  def show: String =
    toDocument.print

  def mapName(f: Name => Name): Node = this match
    case Result(res) => Result(res.map(_.mapNameOfTrivialExpr(f)))
    case Jump(defn, args) => Jump(defn, args.map(_.mapNameOfTrivialExpr(f)))
    case Case(scrut, cases) => Case(f(scrut), cases.map { (cls, arm) => (cls, arm.mapName(f)) })
    case LetExpr(name, expr, body) => LetExpr(f(name), expr.mapName(f), body.mapName(f))
    case LetCall(names, defn, args, body) => LetCall(names.map(f), defn, args.map(_.mapNameOfTrivialExpr(f)), body.mapName(f))  
  
  def copy(ctx: Map[Str, Name]): Node = this match
    case Result(res) => Result(res.map(_.mapNameOfTrivialExpr(_.trySubst(ctx))))
    case Jump(defn, args) => Jump(defn, args.map(_.mapNameOfTrivialExpr(_.trySubst(ctx))))
    case Case(scrut, cases) => Case(ctx(scrut.str), cases.map { (cls, arm) => (cls, arm.copy(ctx)) })
    case LetExpr(name, expr, body) => 
      val name_copy = name.copy
      LetExpr(name_copy, expr.mapName(_.trySubst(ctx)), body.copy(ctx + (name_copy.str -> name_copy)))
    case LetCall(names, defn, args, body) => 
      val names_copy = names.map(_.copy)
      LetCall(names_copy, defn, args.map(_.mapNameOfTrivialExpr(_.trySubst(ctx))), body.copy(ctx ++ names_copy.map(x => x.str -> x)))

  private def toDocument: Document = this match
    case Result(res) => raw(res |> show_args) <:> raw(s"-- $tag")
    case Jump(jp, args) =>
      raw("jump")
      <:> raw(jp.getName)
      <#> raw("(")
      <#> raw(args |> show_args)
      <#> raw(")")
      <:> raw(s"-- $tag") 
    case Case(x, Ls((tcls, tru), (fcls, fls))) if tcls.ident == "True" && fcls.ident == "False" =>
      val first = raw("if") <:> raw(x.toString) <:> raw(s"-- $tag") 
      val tru2 = indent(stack(raw("true") <:> raw ("=>"), tru.toDocument |> indent))
      val fls2 = indent(stack(raw("false") <:> raw ("=>"), fls.toDocument |> indent))
      Document.Stacked(Ls(first, tru2, fls2))
    case Case(x, cases) =>
      val first = raw("case") <:> raw(x.toString) <:> raw("of") <:> raw(s"-- $tag") 
      val other = cases map {
        case (ClassInfo(_, name, _), node) =>
          indent(stack(raw(name) <:> raw("=>"), node.toDocument |> indent))
      }
      Document.Stacked(first :: other)
    case LetExpr(x, expr, body) => 
      stack(
        raw("let")
          <:> raw(x.toString)
          <:> raw("=")
          <:> expr.toDocument
          <:> raw("in")
          <:> raw(s"-- $tag"),
        body.toDocument)
    case LetCall(xs, defn, args, body) => 
      stack(
        raw("let*")
          <:> raw("(")
          <#> raw(xs.map(_.toString).mkString(","))
          <#> raw(")")
          <:> raw("=")
          <:> raw(defn.getName)
          <#> raw("(")
          <#> raw(args.map{ x => x.toString }.mkString(","))
          <#> raw(")")
          <:> raw("in") 
          <:> raw(s"-- $tag"),
        body.toDocument)

  def locMarker: LocMarker =
    val marker = this match
      case Result(res) => LocMarker.MResult(res.map(_.toExpr.locMarker))
      case Jump(defn, args) => LocMarker.MJump(defn.getName, args.map(_.toExpr.locMarker))
      case Case(scrut, cases) => LocMarker.MCase(scrut.str, cases.map(_._1))
      case LetExpr(name, expr, _) => LocMarker.MLetExpr(name.str, expr.locMarker)
      case LetCall(names, defn, args, _) => LocMarker.MLetCall(names.map(_.str), defn.getName, args.map(_.toExpr.locMarker))
    marker.tag = this.tag
    marker

case class DefnTag(inner: Int):
  def is_valid = inner >= 0
  override def equals(x: Any): Bool = x match
    case o: DefnTag =>
      (this, o) match
        case (DefnTag(a), DefnTag(b)) => this.is_valid && o.is_valid && a == b
    case _ => false
  override def toString(): String = if is_valid then s"#$inner" else "#x"

case class DefnLocMarker(val defn: Str, val marker: LocMarker):
  override def toString: String = s"$defn:$marker"
  def matches = marker.matches

enum LocMarker:
  case MRef(name: Str)
  case MLit(lit: Lit)
  case MCtorApp(name: ClassInfo, args: Ls[LocMarker])
  case MSelect(name: Str, cls: ClassInfo, field: Str)
  case MBasicOp(name: Str, args: Ls[LocMarker])
  case MResult(res: Ls[LocMarker])
  case MJump(name: Str, args: Ls[LocMarker])
  case MCase(scrut: Str, cases: Ls[ClassInfo])
  case MLetExpr(name: Str, expr: LocMarker)
  case MLetCall(names: Ls[Str], defn: Str, args: Ls[LocMarker])
  var tag = DefnTag(-1)

  def toDocument: Document = this match
    case MResult(res) => raw("...")
    case MJump(jp, args) =>
      raw("jump")
      <:> raw(jp)
      <:> raw("...")
    case MCase(x, Ls(tcls, fcls)) if tcls.ident == "True" && fcls.ident == "False" =>
      raw("if") <:> raw(x.toString) <:> raw("...")
    case MCase(x, cases) =>
      raw("case") <:> raw(x.toString) <:> raw("of") <:> raw("...")
    case MLetExpr(x, expr) => 
      raw("let")
        <:> raw(x.toString)
        <:> raw("=")
        <:> raw("...")
    case MLetCall(xs, defn, args) =>
      raw("let*")
        <:> raw("(")
        <#> raw(xs.map(_.toString).mkString(","))
        <#> raw(")")
        <:> raw("=")
        <:> raw(defn)
        <:> raw("...")
    case MRef(s) => s.toString |> raw
    case MLit(IntLit(lit)) => s"$lit" |> raw
    case MLit(DecLit(lit)) => s"$lit" |> raw
    case MLit(StrLit(lit)) => s"$lit" |> raw
    case MLit(UnitLit(lit)) => s"$lit" |> raw
    case _ => raw("...")

  def show = s"$tag-" + toDocument.print

  override def toString(): String = show

  def matches(x: Node): Bool = this.tag == x.tag
