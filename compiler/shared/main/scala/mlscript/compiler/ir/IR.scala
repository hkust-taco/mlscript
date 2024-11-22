package mlscript.compiler.ir

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import mlscript.compiler.utils._
import mlscript.compiler.optimizer._
import mlscript.compiler.ir._

import mlscript.Loc

import collection.mutable.{Map as MutMap, Set as MutSet, HashMap, ListBuffer}
import annotation.unused
import util.Sorting
import scala.collection.immutable.SortedSet
import scala.language.implicitConversions

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
    s"Program({${t1.mkString(",\n")}}, {\n${t2.mkString("\n")}\n},\n$main)"

  def show(hiddenNames: Set[Str] = Set.empty) = toDocument(hiddenNames).print

  def toDocument(hiddenNames: Set[Str] = Set.empty) : Document =
    val t1 = classes.toArray
    val t2 = defs.toArray
    Sorting.quickSort(t1)
    Sorting.quickSort(t2)
    given Conversion[String, Document] = raw
    stack(
      "Program:",
      stack_list(t1.filter(x => !hiddenNames.contains(x.name)).map(_.toDocument).toList) |> indent,
      stack_list(t2.map(_.toDocument).toList) |> indent,
      main.toDocument |> indent
    )

implicit object ClassInfoOrdering extends Ordering[ClassInfo] {
  def compare(a: ClassInfo, b: ClassInfo) = a.id.compare(b.id)
}

case class ClassInfo(
  id: Int,
  name: Str,
  fields: Ls[Str],
):
  var parents: Set[Str] = Set.empty
  var methods: Map[Str, Defn] = Map.empty
  override def hashCode: Int = id
  override def toString: String =
    s"ClassInfo($id, $name, [${fields mkString ","}], parents: ${parents mkString ","}, methods:\n${methods mkString ",\n"})"

  def show = toDocument.print
  def toDocument: Document =
    given Conversion[String, Document] = raw
    val extension = if parents.isEmpty then "" else " extends " + parents.mkString(", ")
    if methods.isEmpty then
      "class" <:> name <#> "(" <#> fields.mkString(",") <#> ")" <#> extension
    else
      stack(
        "class" <:> name <#> "(" <#> fields.mkString(",") <#> ")" <#> extension <:> "{",
        stack_list( methods.map { (_, defn) => defn.toDocument |> indent }.toList),
        "}"
      )

case class Name(val str: Str):
  def copy: Name = Name(str)
  def trySubst(map: Map[Str, Name]) = map.getOrElse(str, this)
  override def toString: String =
    str

class DefnRef(var defn: Either[Defn, Str]):
  def name: String = defn.fold(_.name, x => x)
  def expectDefn: Defn = defn match {
    case Left(defn) => defn
    case Right(name) => throw Exception(s"Expected a def, but got $name")
  }
  def getDefn: Opt[Defn] = defn.left.toOption
  override def equals(o: Any): Bool = o match {
    case o: DefnRef => o.name == this.name
    case _ => false
  }

class ClassRef(var cls: Either[ClassInfo, Str]):
  def name: String = cls.fold(_.name, x => x)
  def expectClass: ClassInfo = cls match {
    case Left(cls) => cls
    case Right(name) => throw Exception(s"Expected a class, but got $name")
  }
  def getClass: Opt[ClassInfo] = cls.left.toOption
  override def equals(o: Any): Bool = o match {
    case o: ClassRef => o.name == this.name
    case _ => false
  }

implicit object DefOrdering extends Ordering[Defn] {
  def compare(a: Defn, b: Defn) = a.id.compare(b.id)
}

case class Defn(
  id: Int,
  name: Str,
  params: Ls[Name],
  resultNum: Int,
  body: Node,
  isTailRec: Bool,
  loc: Opt[Loc] = None
):
  override def hashCode: Int = id

  override def toString: String =
    val ps = params.map(_.toString).mkString("[", ",", "]")
    s"Def($id, $name, $ps,\n$resultNum, \n$body\n)"

  def show = toDocument.print

  def toDocument: Document =
    given Conversion[String, Document] = raw
    stack(
      "def" <:> name <#> "(" <#> params.map(_.toString).mkString(",")  <#> ")" <:> "=",
      body.toDocument |> indent
    )

sealed trait TrivialExpr:
  import Expr._
  override def toString: String
  def show: String
  def toDocument: Document
  def mapNameOfTrivialExpr(f: Name => Name): TrivialExpr = this match
    case x: Ref => Ref(f(x.name))
    case x: Literal => x
  def toExpr: Expr = this match { case x: Expr => x }

private def showArguments(args: Ls[TrivialExpr]) = args map (_.show) mkString ","

enum Expr:
  case Ref(name: Name) extends Expr, TrivialExpr 
  case Literal(lit: Lit) extends Expr, TrivialExpr
  case CtorApp(cls: ClassRef, args: Ls[TrivialExpr])
  case Select(name: Name, cls: ClassRef, field: Str)
  case BasicOp(name: Str, args: Ls[TrivialExpr])
  case AssignField(assignee: Name, cls: ClassRef, field: Str, value: TrivialExpr)
  
  override def toString: String = show

  def show: String =
    toDocument.print
  
  def toDocument: Document = 
    given Conversion[String, Document] = raw
    this match
    case Ref(s) => s.toString
    case Literal(IntLit(lit)) => s"$lit"
    case Literal(DecLit(lit)) => s"$lit"
    case Literal(StrLit(lit)) => s"$lit"
    case Literal(UnitLit(lit)) => s"$lit"
    case CtorApp(cls, args) =>
      cls.name <#> "(" <#> (args |> showArguments) <#> ")"
    case Select(s, cls, fld) =>
      cls.name <#> "." <#> fld <#> "(" <#> s.toString <#> ")"
    case BasicOp(name: Str, args) =>
      name <#> "(" <#> (args |> showArguments) <#> ")"
    case AssignField(assignee, clsInfo, fieldName, value) => 
      stack(
        "assign"
        <:> (assignee.toString + "." + fieldName)
        <:> ":="
        <:> value.toDocument
      )

  def mapName(f: Name => Name): Expr = this match
    case Ref(name) => Ref(f(name))
    case Literal(lit) => Literal(lit)
    case CtorApp(cls, args) => CtorApp(cls, args.map(_.mapNameOfTrivialExpr(f)))
    case Select(x, cls, field) => Select(f(x), cls, field)
    case BasicOp(name, args) => BasicOp(name, args.map(_.mapNameOfTrivialExpr(f)))
    case AssignField(assignee, clsInfo, fieldName, value) => AssignField(f(assignee), clsInfo, fieldName, value.mapNameOfTrivialExpr(f))

  def locMarker: LocMarker = this match
    case Ref(name) => LocMarker.MRef(name.str)
    case Literal(lit) => LocMarker.MLit(lit)
    case CtorApp(cls, args) => LocMarker.MCtorApp(cls, args.map(_.toExpr.locMarker))
    case Select(name, cls, field) => LocMarker.MSelect(name.str, cls, field)
    case BasicOp(name, args) => LocMarker.MBasicOp(name, args.map(_.toExpr.locMarker))
    case AssignField(assignee, clsInfo, fieldName, value) => LocMarker.MAssignField(assignee.str, fieldName, value.toExpr.locMarker)

enum Pat:
  case Lit(lit: mlscript.Lit)
  case Class(cls: ClassRef)

  def isTrue = this match
    case Class(cls) => cls.name == "True"
    case _ => false
  
  def isFalse = this match
    case Class(cls) => cls.name == "False"
    case _ => false

  override def toString: String = this match
    case Lit(lit) => s"$lit"
    case Class(cls) => s"${cls.name}"

enum Node:
  // Terminal forms:
  case Result(res: Ls[TrivialExpr])
  case Jump(defn: DefnRef, args: Ls[TrivialExpr])
  case Case(scrut: Name, cases: Ls[(Pat, Node)], default: Opt[Node])
  // Intermediate forms:
  case LetExpr(name: Name, expr: Expr, body: Node)
  case LetMethodCall(names: Ls[Name], cls: ClassRef, method: Name, args: Ls[TrivialExpr], body: Node)
  // Deprecated:
  //   LetApply(names, fn, args, body) => LetMethodCall(names, ClassRef(R("Callable")), Name("apply" + args.length), (Ref(fn): TrivialExpr) :: args, body)
  // case LetApply(names: Ls[Name], fn: Name, args: Ls[TrivialExpr], body: Node)
  case LetCall(names: Ls[Name], defn: DefnRef, args: Ls[TrivialExpr], isTailRec: Bool, body: Node)(val loc: Opt[Loc] = None)

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
    case Case(scrut, cases, default) => Case(f(scrut), cases.map { (cls, arm) => (cls, arm.mapName(f)) }, default.map(_.mapName(f)))
    case LetExpr(name, expr, body) => LetExpr(f(name), expr.mapName(f), body.mapName(f))
    case LetMethodCall(names, cls, method, args, body) => LetMethodCall(names.map(f), cls, f(method), args.map(_.mapNameOfTrivialExpr(f)), body.mapName(f))
    case lc @ LetCall(names, defn, args, itr, body) => LetCall(names.map(f), defn, args.map(_.mapNameOfTrivialExpr(f)), itr, body.mapName(f))(lc.loc)
  
  def copy(ctx: Map[Str, Name]): Node = this match
    case Result(res) => Result(res.map(_.mapNameOfTrivialExpr(_.trySubst(ctx))))
    case Jump(defn, args) => Jump(defn, args.map(_.mapNameOfTrivialExpr(_.trySubst(ctx))))
    case Case(scrut, cases, default) => Case(ctx(scrut.str), cases.map { (cls, arm) => (cls, arm.copy(ctx)) }, default.map(_.copy(ctx)))
    case LetExpr(name, expr, body) => 
      val name_copy = name.copy
      LetExpr(name_copy, expr.mapName(_.trySubst(ctx)), body.copy(ctx + (name_copy.str -> name_copy)))
    case LetMethodCall(names, cls, method, args, body) =>
      val names_copy = names.map(_.copy)
      LetMethodCall(names_copy, cls, method.copy, args.map(_.mapNameOfTrivialExpr(_.trySubst(ctx))), body.copy(ctx ++ names_copy.map(x => x.str -> x)))
    case lc @ LetCall(names, defn, args, itr, body) =>
      val names_copy = names.map(_.copy)
      LetCall(names_copy, defn, args.map(_.mapNameOfTrivialExpr(_.trySubst(ctx))), itr, body.copy(ctx ++ names_copy.map(x => x.str -> x)))(lc.loc)

  def toDocument: Document =
    given Conversion[String, Document] = raw
    this match
    case Result(res) => (res |> showArguments) <:> s"-- $tag"
    case Jump(jp, args) =>
      "jump"
      <:> jp.name
      <#> "("
      <#> (args |> showArguments)
      <#> ")"
      <:> s"-- $tag" 
    case Case(x, Ls((tpat, tru), (fpat, fls)), N) if tpat.isTrue && fpat.isFalse =>
      val first = "if" <:> x.toString <:> s"-- $tag" 
      val tru2 = indent(stack("true" <:> "=>", tru.toDocument |> indent))
      val fls2 = indent(stack("false" <:> "=>", fls.toDocument |> indent))
      Document.Stacked(Ls(first, tru2, fls2))
    case Case(x, cases, default) =>
      val first = "case" <:> x.toString <:> "of" <:> s"-- $tag" 
      val other = cases flatMap {
        case (pat, node) =>
          Ls(pat.toString <:> "=>", node.toDocument |> indent)
      }
      default match
        case N => stack(first, (Document.Stacked(other) |> indent))
        case S(dc) =>
          val default = Ls("_" <:> "=>", dc.toDocument |> indent)
          stack(first, (Document.Stacked(other ++ default) |> indent))
    case LetExpr(x, expr, body) => 
      stack(
        "let"
          <:> x.toString
          <:> "="
          <:> expr.toDocument
          <:> "in"
          <:> s"-- $tag",
        body.toDocument)
    case LetMethodCall(xs, cls, method, args, body) =>
      stack(
        "let"
          <:> xs.map(_.toString).mkString(",")
          <:> "="
          <:> cls.name
          <#> "."
          <#> method.toString
          <#> "("
          <#> args.map{ x => x.toString }.mkString(",")
          <#> ")"
          <:> "in" 
          <:> s"-- $tag",
        body.toDocument)
    case LetCall(xs, defn, args, itr, body) => 
      stack(
        "let*"
          <:> "("
          <#> xs.map(_.toString).mkString(",")
          <#> ")"
          <:> "="
          <:> (if itr then "@tailcall " else "") + defn.name
          <#> "("
          <#> args.map{ x => x.toString }.mkString(",")
          <#> ")"
          <:> "in" 
          <:> s"-- $tag",
        body.toDocument)
  
  def locMarker: LocMarker =
    val marker = this match
      case Result(res) => LocMarker.MResult(res.map(_.toExpr.locMarker))
      case Jump(defn, args) => LocMarker.MJump(defn.name, args.map(_.toExpr.locMarker))
      case Case(scrut, cases, default) => LocMarker.MCase(scrut.str, cases.map(_._1), default.isDefined)
      case LetExpr(name, expr, _) => LocMarker.MLetExpr(name.str, expr.locMarker)
      case LetMethodCall(names, cls, method, args, _) => LocMarker.MLetMethodCall(names.map(_.str), cls, method.str, args.map(_.toExpr.locMarker))
      case LetCall(names, defn, args, _, _) => LocMarker.MLetCall(names.map(_.str), defn.name, args.map(_.toExpr.locMarker))
    marker.tag = this.tag
    marker


trait DefTraversalOrdering:
  def ordered(entry: Node, defs: Set[Defn]): Ls[Defn]
  def orderedNames(entry: Node, defs: Set[Defn]): Ls[Str]

object DefDfs:
  import Node._
  
  private object Successors:
    def find(node: Node)(using acc: Ls[Defn]): Ls[Defn] =
      node match
        case Result(res) => acc
        case Jump(defn, args) => defn.expectDefn :: acc
        case Case(scrut, cases, default) =>
          val acc2 = cases.map(_._2) ++ default.toList
          acc2.foldLeft(acc)((acc, x) => find(x)(using acc))
        case LetExpr(name, expr, body) => find(body)
        case LetMethodCall(names, cls, method, args, body) => find(body)
        case LetCall(names, defn, args, _, body) => find(body)(using defn.expectDefn :: acc)
      
    def find(defn: Defn)(using acc: Ls[Defn]): Ls[Defn] = find(defn.body)
    def findNames(node: Node)(using acc: Ls[Str]): Ls[Str] =
      node match
        case Result(res) => acc
        case Jump(defn, args) => defn.name :: acc
        case Case(scrut, cases, default) =>
          val acc2 = cases.map(_._2) ++ default.toList
          acc2.foldLeft(acc)((acc, x) => findNames(x)(using acc))
        case LetExpr(name, expr, body) => findNames(body)
        case LetMethodCall(names, cls, method, args, body) => findNames(body)
        case LetCall(names, defn, args, _, body) => findNames(body)(using defn.name :: acc)
      
    def findNames(defn: Defn)(using acc: Ls[Str]): Ls[Str] = findNames(defn.body)

  private def dfs(using visited: HashMap[Str, Bool], out: ListBuffer[Defn], postfix: Bool)(x: Defn): Unit =
    visited.update(x.name, true)
    if (!postfix)
      out += x
    Successors.find(x)(using Nil).foreach { y =>
      if (!visited(y.name))
        dfs(y)
    }
    if (postfix)
      out += x
  
  private def dfs(using visited: HashMap[Str, Bool], out: ListBuffer[Defn], postfix: Bool)(x: Node): Unit =
    Successors.find(x)(using Nil).foreach { y =>
      if (!visited(y.name))
        dfs(y)
    }

  private def dfsNames(using visited: HashMap[Str, Bool], defs: Set[Defn], out: ListBuffer[Str], postfix: Bool)(x: Defn): Unit =
    visited.update(x.name, true)
    if (!postfix)
      out += x.name
    Successors.findNames(x)(using Nil).foreach { y =>
      if (!visited(y))
        dfsNames(defs.find(_.name == y).get)
    }
    if (postfix)
      out += x.name
  
  private def dfsNames(using visited: HashMap[Str, Bool], defs: Set[Defn], out: ListBuffer[Str], postfix: Bool)(x: Node): Unit =
    Successors.findNames(x)(using Nil).foreach { y =>
      if (!visited(y))
        dfsNames(defs.find(_.name == y).get)
    }

  def dfs(entry: Node, defs: Set[Defn], postfix: Bool): Ls[Defn] =
    val visited = HashMap[Str, Bool]()
    visited ++= defs.map(_.name -> false)
    val out = ListBuffer[Defn]()
    dfs(using visited, out, postfix)(entry)
    out.toList

  def dfsNames(entry: Node, defs: Set[Defn], postfix: Bool): Ls[Str] =
    val visited = HashMap[Str, Bool]()
    visited ++= defs.map(_.name -> false)
    val out = ListBuffer[Str]()
    dfsNames(using visited, defs, out, postfix)(entry)
    out.toList
    
object DefRevPostOrdering extends DefTraversalOrdering:
  def ordered(entry: Node, defs: Set[Defn]): Ls[Defn] =
    DefDfs.dfs(entry, defs, true).reverse
  def orderedNames(entry: Node, defs: Set[Defn]): Ls[Str] =
    DefDfs.dfsNames(entry, defs, true).reverse

object DefRevPreOrdering extends DefTraversalOrdering:
  def ordered(entry: Node, defs: Set[Defn]): Ls[Defn] =
    DefDfs.dfs(entry, defs, false).reverse
  def orderedNames(entry: Node, defs: Set[Defn]): Ls[Str] =
    DefDfs.dfsNames(entry, defs, false).reverse



case class DefnTag(inner: Int):
  def is_valid = inner >= 0
  override def equals(x: Any): Bool = x match
    case o: DefnTag =>
      (this, o) match
        case (DefnTag(a), DefnTag(b)) => this.is_valid && o.is_valid && a == b
    case _ => false
  override def toString: String = if is_valid then s"#$inner" else "#x"

case class DefnLocMarker(val defn: Str, val marker: LocMarker):
  override def toString: String = s"$defn:$marker"
  def matches = marker.matches

enum LocMarker:
  case MRef(name: Str)
  case MLit(lit: Lit)
  case MCtorApp(name: ClassRef, args: Ls[LocMarker])
  case MSelect(name: Str, cls: ClassRef, field: Str)
  case MBasicOp(name: Str, args: Ls[LocMarker])
  case MAssignField(assignee: Str, field: Str, value: LocMarker)
  case MResult(res: Ls[LocMarker])
  case MJump(name: Str, args: Ls[LocMarker])
  case MCase(scrut: Str, cases: Ls[Pat], default: Bool)
  case MLetExpr(name: Str, expr: LocMarker)
  case MLetMethodCall(names: Ls[Str], cls: ClassRef, method: Str, args: Ls[LocMarker])
  case MLetCall(names: Ls[Str], defn: Str, args: Ls[LocMarker])
  var tag = DefnTag(-1)

  def toDocument: Document = 
    given Conversion[String, Document] = raw
    this match
    case MResult(res) => "..."
    case MJump(jp, args) =>
      "jump"
      <:> jp
      <:> "..."
    case MCase(x, Ls(tpat, fpat), false) if tpat.isTrue && fpat.isFalse =>
      "if" <:> x.toString <:> "..."
    case MCase(x, cases, default) =>
      "case" <:> x.toString <:> "of" <:> "..."
    case MLetExpr(x, expr) => 
      "let"
        <:> x.toString
        <:> "="
        <:> "..."
    case MLetMethodCall(xs, cls, method, args) =>
      "let"
        <:> xs.map(_.toString).mkString(",")
        <:> "="
        <:> cls.name
        <:> "."
        <:> method
        <:> "..."
    case MLetCall(xs, defn, args) =>
      "let*"
        <:> "("
        <#> xs.map(_.toString).mkString(",")
        <#> ")"
        <:> "="
        <:> defn
        <:> "..."
    case MRef(s) => s.toString
    case MLit(IntLit(lit)) => s"$lit"
    case MLit(DecLit(lit)) => s"$lit"
    case MLit(StrLit(lit)) => s"$lit"
    case MLit(UnitLit(undefinedOrNull)) => if undefinedOrNull then "undefined" else "null"
    case _ => "..."

  def show = s"$tag-" + toDocument.print

  override def toString: String = show

  def matches(x: Node): Bool = this.tag == x.tag
