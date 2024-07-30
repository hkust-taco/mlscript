package mlscript.compiler.ir

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import mlscript.compiler.utils._
import mlscript.compiler.optimizer._
import mlscript.compiler.ir._

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
    s"Program({${t1.mkString(",\n")}}, {\n${t2.mkString("\n")}\n},\n$main)"

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

case class Name(val str: Str):
  private var intro: Opt[Intro] = None
  private var elim: Set[Elim] = Set.empty

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
  specialized: Opt[Ls[Opt[Intro]]],
  body: Node
):
  // used by optimizer
  var activeInputs: Set[Ls[Opt[Intro]]] = Set()
  var activeResults: Ls[Opt[Intro]] = Ls.fill(resultNum)(None)
  var newActiveInputs: Set[Ls[Opt[IntroInfo]]] = Set()
  var newActiveParams: Ls[SortedSet[ElimInfo]] = Ls.fill(params.length)(SortedSet())
  var newActiveResults: Ls[Opt[IntroInfo]] = Ls.fill(resultNum)(None)
  var recBoundary: Opt[Int] = None
  override def hashCode: Int = id

  override def toString: String =
    val ps = params.map(_.toString).mkString("[", ",", "]")
    val naps = newActiveParams.map(_.toSeq.sorted.mkString("{", ",", "}")).mkString("[", ",", "]")
    val ais = activeInputs.map(_.toSeq.sorted.mkString("[", ",", "]")).mkString("[", ",", "]")
    val ars = activeResults.map(_.toString).mkString("[", ",", "]")
    s"Def($id, $name, $ps, $naps,\nI: $ais,\nR: $ars,\nRec: $recBoundary,\n$resultNum, \n$body\n)"

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
  
  override def toString: String = show

  def show: String =
    toDocument.print
  
  def toDocument: Document = this match
    case Ref(s) => s.toString |> raw
    case Literal(IntLit(lit)) => s"$lit" |> raw
    case Literal(DecLit(lit)) => s"$lit" |> raw
    case Literal(StrLit(lit)) => s"$lit" |> raw
    case Literal(CharLit(lit)) => s"$lit" |> raw
    case Literal(UnitLit(lit)) => s"$lit" |> raw
    case CtorApp(cls, args) =>
      raw(cls.name) <#> raw("(") <#> raw(args |> showArguments) <#> raw(")")
    case Select(s, cls, fld) =>
      raw(cls.name) <#> raw(".") <#> raw(fld) <#> raw("(") <#> raw(s.toString) <#> raw(")")
    case BasicOp(name: Str, args) =>
      raw(name) <#> raw("(") <#> raw(args |> showArguments) <#> raw(")")

  def mapName(f: Name => Name): Expr = this match
    case Ref(name) => Ref(f(name))
    case Literal(lit) => Literal(lit)
    case CtorApp(cls, args) => CtorApp(cls, args.map(_.mapNameOfTrivialExpr(f)))
    case Select(x, cls, field) => Select(f(x), cls, field)
    case BasicOp(name, args) => BasicOp(name, args.map(_.mapNameOfTrivialExpr(f)))

  def locMarker: LocMarker = this match
    case Ref(name) => LocMarker.MRef(name.str)
    case Literal(lit) => LocMarker.MLit(lit)
    case CtorApp(cls, args) => LocMarker.MCtorApp(cls, args.map(_.toExpr.locMarker))
    case Select(name, cls, field) => LocMarker.MSelect(name.str, cls, field)
    case BasicOp(name, args) => LocMarker.MBasicOp(name, args.map(_.toExpr.locMarker))

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
    case Case(scrut, cases, default) => Case(f(scrut), cases.map { (cls, arm) => (cls, arm.mapName(f)) }, default.map(_.mapName(f)))
    case LetExpr(name, expr, body) => LetExpr(f(name), expr.mapName(f), body.mapName(f))
    case LetMethodCall(names, cls, method, args, body) => LetMethodCall(names.map(f), cls, f(method), args.map(_.mapNameOfTrivialExpr(f)), body.mapName(f))
    case LetCall(names, defn, args, body) => LetCall(names.map(f), defn, args.map(_.mapNameOfTrivialExpr(f)), body.mapName(f))  
  
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
    case LetCall(names, defn, args, body) =>
      val names_copy = names.map(_.copy)
      LetCall(names_copy, defn, args.map(_.mapNameOfTrivialExpr(_.trySubst(ctx))), body.copy(ctx ++ names_copy.map(x => x.str -> x)))

  private def toDocument: Document = this match
    case Result(res) => raw(res |> showArguments) <:> raw(s"-- $tag")
    case Jump(jp, args) =>
      raw("jump")
      <:> raw(jp.name)
      <#> raw("(")
      <#> raw(args |> showArguments)
      <#> raw(")")
      <:> raw(s"-- $tag") 
    case Case(x, Ls((tpat, tru), (fpat, fls)), N) if tpat.isTrue && fpat.isFalse =>
      val first = raw("if") <:> raw(x.toString) <:> raw(s"-- $tag") 
      val tru2 = indent(stack(raw("true") <:> raw ("=>"), tru.toDocument |> indent))
      val fls2 = indent(stack(raw("false") <:> raw ("=>"), fls.toDocument |> indent))
      Document.Stacked(Ls(first, tru2, fls2))
    case Case(x, cases, default) =>
      val first = raw("case") <:> raw(x.toString) <:> raw("of") <:> raw(s"-- $tag") 
      val other = cases flatMap {
        case (pat, node) =>
          Ls(raw(pat.toString) <:> raw("=>"), node.toDocument |> indent)
      }
      default match
        case N => stack(first, (Document.Stacked(other) |> indent))
        case S(dc) =>
          val default = Ls(raw("_") <:> raw("=>"), dc.toDocument |> indent)
          stack(first, (Document.Stacked(other ++ default) |> indent))
    case LetExpr(x, expr, body) => 
      stack(
        raw("let")
          <:> raw(x.toString)
          <:> raw("=")
          <:> expr.toDocument
          <:> raw("in")
          <:> raw(s"-- $tag"),
        body.toDocument)
    case LetMethodCall(xs, cls, method, args, body) =>
      stack(
        raw("let")
          <:> raw(xs.map(_.toString).mkString(","))
          <:> raw("=")
          <:> raw(cls.name)
          <#> raw(".")
          <#> raw(method.toString)
          <#> raw("(")
          <#> raw(args.map{ x => x.toString }.mkString(","))
          <#> raw(")")
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
          <:> raw(defn.name)
          <#> raw("(")
          <#> raw(args.map{ x => x.toString }.mkString(","))
          <#> raw(")")
          <:> raw("in") 
          <:> raw(s"-- $tag"),
        body.toDocument)
  
  def locMarker: LocMarker =
    val marker = this match
      case Result(res) => LocMarker.MResult(res.map(_.toExpr.locMarker))
      case Jump(defn, args) => LocMarker.MJump(defn.name, args.map(_.toExpr.locMarker))
      case Case(scrut, cases, default) => LocMarker.MCase(scrut.str, cases.map(_._1), default.isDefined)
      case LetExpr(name, expr, _) => LocMarker.MLetExpr(name.str, expr.locMarker)
      case LetMethodCall(names, cls, method, args, _) => LocMarker.MLetMethodCall(names.map(_.str), cls, method.str, args.map(_.toExpr.locMarker))
      case LetCall(names, defn, args, _) => LocMarker.MLetCall(names.map(_.str), defn.name, args.map(_.toExpr.locMarker))
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
        case LetCall(names, defn, args, body) => find(body)(using defn.expectDefn :: acc)
      
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
        case LetCall(names, defn, args, body) => findNames(body)(using defn.name :: acc)
      
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


case class ElimInfo(elim: Elim, loc: DefnLocMarker):
  override def toString: String = s"<$elim@$loc>"

implicit object ElimInfoOrdering extends Ordering[ElimInfo]:
  override def compare(a: ElimInfo, b: ElimInfo) = a.toString.compare(b.toString)

enum Elim:
  case EDirect
  case EApp(n: Int)
  case EDestruct
  case EIndirectDestruct
  case ESelect(x: Str)

  override def toString: String = this match
    case EDirect => "EDirect"
    case EApp(n) => s"EApp($n)"
    case EDestruct => s"EDestruct"
    case EIndirectDestruct => s"EIndirectDestruct"
    case ESelect(x: Str) => s"ESelect($x)"

  def toShortString: String = this match
    case EDirect => "T"
    case EApp(n) => s"A$n"
    case EDestruct => s"D"
    case EIndirectDestruct => s"I"
    case ESelect(x: Str) => s"S($x)"
  

implicit object ElimOrdering extends Ordering[Elim]:
  override def compare(a: Elim, b: Elim) = a.toString.compare(b.toString)

case class IntroInfo(intro: Intro, loc: DefnLocMarker):
  override def toString: String = s"$intro"

enum Intro:
  case ICtor(c: Str)
  case ILam(n: Int)
  case IMulti(n: Int)
  case IMix(i: Set[Intro])

  override def toString: String = this match
    case ICtor(c) => s"ICtor($c)"
    case ILam(n) => s"ILam($n)"
    case IMulti(n) => s"IMulti($n)"
    case IMix(i) => s"IMix(${i.toSeq.sorted.mkString(",")})"

  def toShortString: String = this match
    case ICtor(c) => s"C($c)"
    case ILam(n) => s"L$n"
    case IMulti(n) => s"M$n"
    case IMix(i) => s"X(${i.toSeq.map(_.toShortString).sorted.mkString})"

  override def equals(o: Any): Boolean = o match
    case o: Intro if this.isInstanceOf[Intro] =>
      (o, this) match
        case (ICtor(c1), ICtor(c2)) => c1 == c2
        case (ILam(n1), ILam(n2)) => n1 == n2
        case (IMulti(n1), IMulti(n2)) => n1 == n2
        case (IMix(i1), IMix(i2)) => 
          i1 == i2
        case _ => false
    case _ => false

implicit object IntroOrdering extends Ordering[Intro]:
  override def compare(a: Intro, b: Intro) = a.toString.compare(b.toString)


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
  def matches = marker.matches _

enum LocMarker:
  case MRef(name: Str)
  case MLit(lit: Lit)
  case MCtorApp(name: ClassRef, args: Ls[LocMarker])
  case MSelect(name: Str, cls: ClassRef, field: Str)
  case MBasicOp(name: Str, args: Ls[LocMarker])
  case MResult(res: Ls[LocMarker])
  case MJump(name: Str, args: Ls[LocMarker])
  case MCase(scrut: Str, cases: Ls[Pat], default: Bool)
  case MLetExpr(name: Str, expr: LocMarker)
  case MLetMethodCall(names: Ls[Str], cls: ClassRef, method: Str, args: Ls[LocMarker])
  case MLetCall(names: Ls[Str], defn: Str, args: Ls[LocMarker])
  var tag = DefnTag(-1)

  def toDocument: Document = this match
    case MResult(res) => raw("...")
    case MJump(jp, args) =>
      raw("jump")
      <:> raw(jp)
      <:> raw("...")
    case MCase(x, Ls(tpat, fpat), false) if tpat.isTrue && fpat.isFalse =>
      raw("if") <:> raw(x.toString) <:> raw("...")
    case MCase(x, cases, default) =>
      raw("case") <:> raw(x.toString) <:> raw("of") <:> raw("...")
    case MLetExpr(x, expr) => 
      raw("let")
        <:> raw(x.toString)
        <:> raw("=")
        <:> raw("...")
    case MLetMethodCall(xs, cls, method, args) =>
      raw("let")
        <:> raw(xs.map(_.toString).mkString(","))
        <:> raw("=")
        <:> raw(cls.name)
        <:> raw(".")
        <:> raw(method)
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
    case MLit(CharLit(lit)) => s"$lit" |> raw
    case MLit(UnitLit(undefinedOrNull)) => (if undefinedOrNull then "undefined" else "null") |> raw
    case _ => raw("...")

  def show = s"$tag-" + toDocument.print

  override def toString: String = show

  def matches(x: Node): Bool = this.tag == x.tag
