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
  def accept_iterator(v: Iterator) = v.iterate(this)

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
  def accept_iterator(v: Iterator) = v.iterate(this)

case class Name(val str: Str):
  private var intro: Opt[Intro] = None
  private var elim: Set[Elim] = Set.empty

  def copy: Name = Name(str)
  def trySubst(map: Map[Str, Name]) = map.getOrElse(str, this)
  
  private def show_intro = intro match
    case Some(i) => "+" + i.toShortString
    case None => ""

  private def show_elim = elim match
    case e if e.isEmpty => ""
    case e => "-" + e.toSeq.sorted.map(_.toShortString).mkString

  private def toStringDbg = 
    val x = s"$show_intro$show_elim"
    if x != "" then s"$str[$x]" else str
  
  override def toString: String =
    str

  /* they will be deprecated soon. don't use */
  def accept_def_iterator(v: NameIterator) = v.iterate_name_def(this)
  def accept_use_iterator(v: NameIterator) = v.iterate_name_use(this)
  def accept_param_iterator(v: NameIterator) = v.iterate_param(this)

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

  /* they will be deprecated soon. don't use */
  def accept_iterator(v: Iterator) = v.iterate(this)

implicit object DefOrdering extends Ordering[Defn] {
  def compare(a: Defn, b: Defn) = a.id.compare(b.id)
}

case class Defn(
  val id: Int,
  val name: Str,
  val params: Ls[Name],
  val resultNum: Int,
  var specialized: Opt[Ls[Opt[Intro]]],
  val body: Node
):
  // used by optimizer
  var activeInputs: Set[Ls[Opt[Intro]]] = Set()
  var activeResults: Ls[Opt[Intro]] = Ls.fill(resultNum)(None)
  var newActiveInputs: Set[Ls[Opt[IntroInfo]]] = Set()
  var newActiveParams: Ls[SortedSet[ElimInfo]] = Ls.fill(params.length)(SortedSet())
  var newActiveResults: Ls[Opt[IntroInfo]] = Ls.fill(resultNum)(None)
  var recBoundary: Opt[Int] = None
  override def hashCode: Int = id
  def getName: String = name

  /* they will be deprecated soon. don't use */
  def accept_iterator(v: Iterator) = v.iterate(this)

  override def toString: String =
    val ps = params.map(_.toString).mkString("[", ",", "]")
    val naps = newActiveParams.map(_.toSeq.sorted.mkString("{", ",", "}")).mkString("[", ",", "]")
    val ais = activeInputs.map(_.toSeq.sorted.mkString("[", ",", "]")).mkString("[", ",", "]")
    val ars = activeResults.map(_.toString()).mkString("[", ",", "]")
    s"Def($id, $name, $ps, $naps,\nI: $ais,\nR: $ars,\nRec: $recBoundary,\n$resultNum, \n$body\n)"

sealed trait TrivialExpr:
  import Expr._
  override def toString: String
  def show: String
  def toDocument: Document

  /* they will be deprecated soon. don't use */
  def accept_iterator(v: TrivialExprIterator): Unit = this match
    case x: Ref => v.iterate(x)
    case x: Literal => v.iterate(x)

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

  /* they will be deprecated soon. don't use */
  def accept_iterator(v: Iterator): Unit = this match
    case x: Ref => v.iterate(x)
    case x: Literal => v.iterate(x)
    case x: CtorApp => v.iterate(x)
    case x: Select => v.iterate(x)
    case x: BasicOp => v.iterate(x)

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

  /* they will be deprecated soon. don't use */
  def accept_iterator(v: Iterator): Unit  = this match
    case x: Result => v.iterate(x)
    case x: Jump => v.iterate(x)
    case x: Case => v.iterate(x)
    case x: LetExpr => v.iterate(x)
    case x: LetCall => v.iterate(x)
  
  def locMarker: LocMarker =
    val marker = this match
      case Result(res) => LocMarker.MResult(res.map(_.toExpr.locMarker))
      case Jump(defn, args) => LocMarker.MJump(defn.getName, args.map(_.toExpr.locMarker))
      case Case(scrut, cases) => LocMarker.MCase(scrut.str, cases.map(_._1))
      case LetExpr(name, expr, _) => LocMarker.MLetExpr(name.str, expr.locMarker)
      case LetCall(names, defn, args, _) => LocMarker.MLetCall(names.map(_.str), defn.getName, args.map(_.toExpr.locMarker))
    marker.tag = this.tag
    marker


/* they will be deprecated soon. don't use */
trait NameIterator:
  def iterate_name_def(x: Name): Unit = ()
  def iterate_name_use(x: Name): Unit = ()
  def iterate_param(x: Name): Unit    = ()

/* they will be deprecated soon. don't use */
trait TrivialExprIterator extends NameIterator:
  import Expr._
  def iterate(x: Ref): Unit         = x.name.accept_use_iterator(this)
  def iterate(x: Literal): Unit     = ()

trait Iterator extends TrivialExprIterator:
  import Expr._
  import Node._
  def iterate(x: CtorApp): Unit        = x match
    case CtorApp(cls, xs)              => cls.accept_iterator(this); xs.foreach(_.accept_iterator(this))
  def iterate(x: Select): Unit         = x match
    case Select(x, cls, field)         => x.accept_use_iterator(this); cls.accept_iterator(this)
  def iterate(x: BasicOp): Unit        = x match
    case BasicOp(op, xs)               => xs.foreach(_.accept_iterator(this))
  def iterate(x: Result): Unit         = x match
    case Result(xs)                    => xs.foreach(_.accept_iterator(this))
  def iterate(x: Jump): Unit           = x match
    case Jump(jp, xs)                  => jp.accept_iterator(this); xs.foreach(_.accept_iterator(this))
  def iterate(x: Case): Unit           = x match
    case Case(x, cases)                => x.accept_use_iterator(this); cases foreach { (cls, arm) => arm.accept_iterator(this) }
  def iterate(x: LetExpr): Unit        = x match
    case LetExpr(x, e1, e2)            => x.accept_def_iterator(this); e1.accept_iterator(this); e2.accept_iterator(this)
  def iterate(x: LetCall): Unit        = x match
    case LetCall(xs, f, as, e2)        => xs.foreach(_.accept_def_iterator(this)); f.accept_iterator(this); as.foreach(_.accept_iterator(this)); e2.accept_iterator(this)
  def iterate(x: DefnRef): Unit       = ()
  def iterate(x: ClassInfo): Unit      = ()
  def iterate(x: Defn): Unit =
    x.params.foreach(_.accept_param_iterator(this))
    x.body.accept_iterator(this)
  def iterate(x: Program): Unit =
    x.classes.foreach(_.accept_iterator(this))
    x.defs.foreach(_.accept_iterator(this))
    x.main.accept_iterator(this)

trait DefTraversalOrdering:
  def ordered(entry: Node, defs: Set[Defn]): Ls[Defn]
  def ordered_names(entry: Node, defs: Set[Defn]): Ls[Str]

object DefDfs:
  import Node._
  private class Successors extends Iterator:
    var succ: ListBuffer[Defn] = ListBuffer()
    override def iterate(x: DefnRef) =
      succ += x.expectDefn

  private class SuccessorNames extends Iterator:
    var succ: ListBuffer[Str] = ListBuffer()
    override def iterate(x: DefnRef) =
      succ += x.getName

  private def dfs(using visited: HashMap[Str, Bool], out: ListBuffer[Defn], postfix: Bool)(x: Defn): Unit =
    visited.update(x.name, true)
    if (!postfix)
      out += x
    val succ = Successors()
    x.accept_iterator(succ)
    succ.succ.foreach { y =>
      if (!visited(y.name))
        dfs(y)
    }
    if (postfix)
      out += x
  
  private def dfs(using visited: HashMap[Str, Bool], out: ListBuffer[Defn], postfix: Bool)(x: Node): Unit =
    val succ = Successors()
    x.accept_iterator(succ)
    succ.succ.foreach { y =>
      if (!visited(y.name))
        dfs(y)
    }

  private def dfs_names(using visited: HashMap[Str, Bool], defs: Set[Defn], out: ListBuffer[Str], postfix: Bool)(x: Defn): Unit =
    visited.update(x.name, true)
    if (!postfix)
      out += x.name
    val succ = SuccessorNames()
    x.accept_iterator(succ)
    succ.succ.foreach { y =>
      if (!visited(y))
        dfs_names(defs.find(_.name == y).get)
    }
    if (postfix)
      out += x.name
  
  private def dfs_names(using visited: HashMap[Str, Bool], defs: Set[Defn], out: ListBuffer[Str], postfix: Bool)(x: Node): Unit =
    val succ = SuccessorNames()
    x.accept_iterator(succ)
    succ.succ.foreach { y =>
      if (!visited(y))
        dfs_names(defs.find(_.name == y).get)
    }

  def dfs(entry: Node, defs: Set[Defn], postfix: Bool): Ls[Defn] =
    val visited = HashMap[Str, Bool]()
    visited ++= defs.map(_.name -> false)
    val out = ListBuffer[Defn]()
    dfs(using visited, out, postfix)(entry)
    out.toList

  def dfs_names(entry: Node, defs: Set[Defn], postfix: Bool): Ls[Str] =
    val visited = HashMap[Str, Bool]()
    visited ++= defs.map(_.name -> false)
    val out = ListBuffer[Str]()
    dfs_names(using visited, defs, out, postfix)(entry)
    out.toList
    
object DefRevPostOrdering extends DefTraversalOrdering:
  def ordered(entry: Node, defs: Set[Defn]): Ls[Defn] =
    DefDfs.dfs(entry, defs, true).reverse
  def ordered_names(entry: Node, defs: Set[Defn]): Ls[Str] =
    DefDfs.dfs_names(entry, defs, true).reverse

object DefRevPreOrdering extends DefTraversalOrdering:
  def ordered(entry: Node, defs: Set[Defn]): Ls[Defn] =
    DefDfs.dfs(entry, defs, false).reverse
  def ordered_names(entry: Node, defs: Set[Defn]): Ls[Str] =
    DefDfs.dfs_names(entry, defs, false).reverse


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
  override def toString(): String = if is_valid then s"#$inner" else "#x"

case class DefnLocMarker(val defn: Str, val marker: LocMarker):
  override def toString: String = s"$defn:$marker"
  def matches = marker.matches _

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
