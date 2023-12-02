package mlscript
package compiler

import mlscript.utils.*
import mlscript.utils.shorthands.*

import collection.mutable.{Map as MutMap, Set as MutSet}
import mlscript.*

import scala.annotation.unused
import scala.util.Sorting
import scala.collection.mutable.HashMap
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.ListBuffer

// -----------------------------------------------

class GOProgram(
  val classes: Set[ClassInfo],
  val defs: Set[GODef],
  // TODO add a cache of split defs
  val main: GONode,
):
  override def equals(o: Any): Bool = o match {
    case o: GOProgram if this.isInstanceOf[GOProgram] =>
      o.classes == classes &&
      o.defs == defs &&
      o.main == main
    case _ => false
  }
  override def toString: String =
    val t1 = classes.toArray
    val t2 = defs.toArray
    Sorting.quickSort(t1)
    Sorting.quickSort(t2)
    s"GOProgram({${t1.mkString(",")}}, {\n${t2.mkString("\n")}\n},\n$main)"
  def accept_visitor(v: GOVisitor) = v.visit(this)
  def accept_iterator(v: GOIterator) = v.iterate(this)

implicit object ClassInfoOrdering extends Ordering[ClassInfo] {
  def compare(a: ClassInfo, b: ClassInfo) = a.id.compare(b.id)
}
implicit object GODefOrdering extends Ordering[GODef] {
  def compare(a: GODef, b: GODef) = a.id.compare(b.id)
}

case class ClassInfo(
  val id: Int,
  val ident: Str,
  val fields: Ls[Str],
):
  override def equals(o: Any): Bool = o match {
    case o: ClassInfo if this.isInstanceOf[ClassInfo] => o.id == id
    case _ => false
  }
  override def hashCode: Int = id
  override def toString: String =
    s"ClassInfo($id, $ident, [${fields mkString ","}])"
  def accept_visitor(v: GOVisitor) = v.visit(this)
  def accept_iterator(v: GOIterator) = v.iterate(this)

case class Name(val str: Str):
  override def equals(o: Any): Bool = o match {
    case Name(s2) => str == s2
    case _ => false
  }
  override def toString: String = str
  def accept_def_visitor(v: GONameVisitor) = v.visit_name_def(this)
  def accept_use_visitor(v: GONameVisitor) = v.visit_name_use(this)
  def accept_param_visitor(v: GONameVisitor) = v.visit_param(this)
  def accept_def_iterator(v: GONameIterator) = v.iterate_name_def(this)
  def accept_use_iterator(v: GONameIterator) = v.iterate_name_use(this)
  def accept_param_iterator(v: GONameIterator) = v.iterate_param(this)

class GODefRef(var defn: Either[GODef, Str]):
  def getName: String = defn match {
    case Left(godef) => godef.getName
    case Right(name) => name
  }
  def expectDefn: GODef = defn match {
    case Left(godef) => godef
    case Right(name) => throw Exception(s"Expected a def, but got $name")
  }
  
  def getDefn: Opt[GODef] = defn match {
    case Left(godef) => Some(godef)
    case Right(name) => None
  }

  override def equals(o: Any): Bool = o match {
    case o: GODefRef if this.isInstanceOf[GODefRef] =>
      o.getName == this.getName
    case _ => false
  }
  def accept_visitor(v: GOVisitor) = v.visit(this)
  def accept_iterator(v: GOIterator) = v.iterate(this)

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

implicit object ElimOrdering extends Ordering[Elim]:
  override def compare(a: Elim, b: Elim) = a.toString.compare(b.toString)

enum Intro:
  case ICtor(c: Str)
  case ILam(n: Int)
  case IMulti(n: Int)
  
  override def toString: String = this match
    case ICtor(c) => s"ICtor($c)"
    case ILam(n) => s"ILam($n)"
    case IMulti(n) => s"IMulti($n)"

implicit object IntroOrdering extends Ordering[Intro]:
  override def compare(a: Intro, b: Intro) = a.toString.compare(b.toString)

class GODef(
  val id: Int,
  val name: Str,
  val isjp: Bool,
  val params: Ls[Name],
  val resultNum: Int,
  var body: GONode,
  // TODO rec boundaries
):
  var activeParams: Ls[Set[Elim]] = Ls(Set())
  var activeInputs: Ls[Ls[Opt[Intro]]] = Ls()
  var activeResults: Ls[Opt[Intro]] = Ls(None)
  override def equals(o: Any): Bool = o match {
    case o: GODef if this.isInstanceOf[GODef] =>
      o.id == id &&
      o.name == name &&
      o.isjp == isjp
      o.params == params &&
      o.resultNum == resultNum &&
      o.body == body
    case _ => false
  }
  override def hashCode: Int = id
  def getName: String = name
  @unused
  def getBody: GONode = body
  def accept_visitor(v: GOVisitor) = v.visit(this)
  def accept_iterator(v: GOIterator) = v.iterate(this)
  override def toString: String =
    val name2 = if (isjp) s"@join $name" else s"$name"
    val ps = params.map(_.toString()).mkString("[", ",", "]")
    val aps = activeParams.map(_.toSeq.sorted.mkString("{", ",", "}")).mkString("[", ",", "]")
    val ais = activeInputs.map(_.toSeq.sorted.mkString("[", ",", "]")).mkString("[", ",", "]")
    val ars = activeResults.map(_.toString()).mkString("[", ",", "]")
    s"Def($id, $name2, $ps, $aps,\n$ais,\n$ars, $resultNum, \n$body\n)"

sealed trait TrivialExpr:
  override def toString: String
  def show: String
  def toDocument: Document
  def accept_visitor(v: GOTrivialExprVisitor): TrivialExpr = this match
    case x: GOExpr.Ref => v.visit(x)
    case x: GOExpr.Literal => v.visit(x)
  def accept_iterator(v: GOTrivialExprIterator): Unit = this match
    case x: GOExpr.Ref => v.iterate(x)
    case x: GOExpr.Literal => v.iterate(x)

  def to_expr: GOExpr = this match { case x: GOExpr => x }

private def show_args(args: Ls[TrivialExpr]) = args map { x => x.show } mkString ","

enum GOExpr:
  case Ref(name: Name) extends GOExpr, TrivialExpr
  case Literal(lit: Lit) extends GOExpr, TrivialExpr
  case CtorApp(name: ClassInfo, args: Ls[TrivialExpr]) extends GOExpr
  case Select(name: Name, cls: ClassInfo, field: Str)
  case BasicOp(name: Str, args: Ls[TrivialExpr])
  // TODO: depreceted: the following will be deleted
  case Lambda(name: Ls[Name], body: GONode)
  case Apply(name: Name, args: Ls[TrivialExpr])
  
  override def toString: String = show

  def show: String =
    toDocument.print
  
  def toDocument: Document = this match
    case Ref(Name(s)) => s |> raw
    case Literal(lit) => s"$lit" |> raw
    case CtorApp(ClassInfo(_, name, _), args) =>
      raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")
    case Select(Name(s), _, fld) =>
      raw(s) <#> raw(".") <#> raw(fld)
    case BasicOp(name: Str, args) =>
      raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")
    case Lambda(name, body) =>
      raw(name map { case Name(str) => str} mkString ",")
      <:> raw("=>")
      <:> raw(s"$body")
    case Apply(Name(name), args) =>
      raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")

  def accept_visitor(v: GOVisitor): GOExpr = this match
    case x: Ref => v.visit(x).to_expr
    case x: Literal => v.visit(x).to_expr
    case x: CtorApp => v.visit(x)
    case x: Select => v.visit(x)
    case x: BasicOp => v.visit(x)
    case x: Lambda => v.visit(x)
    case x: Apply => v.visit(x)

  def accept_iterator(v: GOIterator): Unit = this match
    case x: Ref => v.iterate(x)
    case x: Literal => v.iterate(x)
    case x: CtorApp => v.iterate(x)
    case x: Select => v.iterate(x)
    case x: BasicOp => v.iterate(x)
    case x: Lambda => v.iterate(x)
    case x: Apply => v.iterate(x)
    
enum GONode:
  // Terminal forms:
  case Result(res: Ls[TrivialExpr])
  case Jump(defn: GODefRef, args: Ls[TrivialExpr])
  case Case(scrut: Name, cases: Ls[(ClassInfo, GONode)])
  // Intermediate forms:
  case LetExpr(name: Name, expr: GOExpr, body: GONode)
  case LetJoin(joinName: Name, params: Ls[Name], rhs: GONode, body: GONode)
  case LetCall(resultNames: Ls[Name], defn: GODefRef, args: Ls[TrivialExpr], body: GONode)

  override def toString: String = show

  def show: String =
    toDocument.print

  private def toDocument: Document = this match
    case Result(res) => raw(res |> show_args)
    case Jump(jp, args) =>
      raw("jump")
      <:> raw(jp.getName)
      <#> raw("(")
      <#> raw(args |> show_args)
      <#> raw(")") 
    case Case(Name(x), Ls((tcls, tru), (fcls, fls))) if tcls.ident == "True" && fcls.ident == "False" =>
      val first = raw("if") <:> raw(x)
      val tru2 = indent(raw("true") <:> raw ("=>") <:> tru.toDocument)
      val fls2 = indent(raw("false") <:> raw ("=>") <:> fls.toDocument)
      Document.Stacked(Ls(first, tru2, fls2))
    case Case(Name(x), cases) =>
      val first = raw("case") <:> raw(x) <:> raw("of")
      val other = cases map {
        case (ClassInfo(_, name, _), node) =>
          indent(raw(name) <:> raw("=>") <:> node.toDocument)
      }
      Document.Stacked(first :: other)
    case LetExpr(Name(x), expr, body) => 
      stack(
        raw("let")
          <:> raw(x)
          <:> raw("=")
          <:> expr.toDocument,
        raw("in") <:> body.toDocument |> indent)
    case LetJoin(Name(x), params, rhs, body) =>
      stack(
        raw("let")
          <:> raw("join")
          <:> raw(x)
          <#> raw("(")
          <#> raw(params.map{ x => x.toString }.mkString(","))
          <#> raw(")")
          <:> raw("=")
          <:> (rhs.toDocument |> indent |> indent),
        raw("in") <:> body.toDocument |> indent
      )
    case LetCall(resultNames, defn, args, body) => 
      stack(
        raw("let*")
          <:> raw("(")
          <#> raw(resultNames.map{ x => x.toString }.mkString(","))
          <#> raw(")")
          <:> raw("=")
          <:> raw(defn.getName)
          <#> raw("(")
          <#> raw(args.map{ x => x.toString }.mkString(","))
          <#> raw(")"),
        raw("in") <:> body.toDocument |> indent
      )

  def accept_visitor(v: GOVisitor): GONode  = this match
    case x: Result => v.visit(x)
    case x: Jump => v.visit(x)
    case x: Case => v.visit(x)
    case x: LetExpr => v.visit(x)
    case x: LetJoin => v.visit(x)
    case x: LetCall => v.visit(x)

  def accept_iterator(v: GOIterator): Unit  = this match
    case x: Result => v.iterate(x)
    case x: Jump => v.iterate(x)
    case x: Case => v.iterate(x)
    case x: LetExpr => v.iterate(x)
    case x: LetJoin => v.iterate(x)
    case x: LetCall => v.iterate(x)

trait GONameVisitor:
  def visit_name_def(x: Name): Name = x
  def visit_name_use(x: Name): Name = x
  def visit_param(x: Name): Name    = x

trait GOTrivialExprVisitor extends GONameVisitor:
  import GOExpr._
  def visit(x: Ref): TrivialExpr     = Ref(x.name.accept_use_visitor(this))   
  def visit(x: Literal): TrivialExpr = x

trait GOVisitor extends GOTrivialExprVisitor:
  import GOExpr._
  import GONode._
  def visit(x: CtorApp): GOExpr      = x match
    case CtorApp(cls, xs)            => CtorApp(cls.accept_visitor(this), xs.map(_.accept_visitor(this)))
  def visit(x: Select): GOExpr       = x match
    case Select(x, cls, field)       => Select(x.accept_use_visitor(this), cls.accept_visitor(this), field)
  def visit(x: BasicOp): GOExpr      = x match
    case BasicOp(op, xs)             => BasicOp(op, xs.map(_.accept_visitor(this)))
  def visit(x: Lambda): GOExpr       = x match
    case Lambda(xs, body)            => ???
  def visit(x: Apply): GOExpr        = x match
    case Apply(f, xs)                => Apply(f.accept_use_visitor(this), xs.map(_.accept_visitor(this)))
  def visit(x: Result): GONode       = x match
    case Result(xs)                  => Result(xs.map(_.accept_visitor(this)))
  def visit(x: Jump): GONode         = x match
    case Jump(jp, xs)                => Jump(jp.accept_visitor(this), xs.map(_.accept_visitor(this)))
  def visit(x: Case): GONode         = x match
    case Case(x, cases)              => Case(x.accept_use_visitor(this), cases map { (cls, arm) => (cls, arm.accept_visitor(this)) })
  def visit(x: LetExpr): GONode      = x match
    case LetExpr(x, e1, e2)          => LetExpr(x.accept_def_visitor(this), e1.accept_visitor(this), e2.accept_visitor(this))
  def visit(x: LetJoin): GONode      = x match
    case LetJoin(jp, xs, e1, e2)     => LetJoin(jp, xs, e1.accept_visitor(this), e2.accept_visitor(this))
  def visit(x: LetCall): GONode      = x match
    case LetCall(xs, f, as, e2)      => LetCall(xs.map(_.accept_def_visitor(this)), f.accept_visitor(this), as.map(_.accept_visitor(this)), e2.accept_visitor(this))
  def visit(x: GODefRef): GODefRef   = x
  def visit(x: ClassInfo): ClassInfo = x
  def visit(x: GODef): GODef         =
    GODef(
      x.id,
      x.name,
      x.isjp,
      x.params.map(_.accept_param_visitor(this)),
      x.resultNum,
      x.body.accept_visitor(this))
  def visit(x: GOProgram): GOProgram =
    GOProgram(
      x.classes.map(_.accept_visitor(this)),
      x.defs.map(_.accept_visitor(this)),
      x.main.accept_visitor(this))

trait GONameIterator:
  def iterate_name_def(x: Name): Unit = ()
  def iterate_name_use(x: Name): Unit = ()
  def iterate_param(x: Name): Unit    = ()

trait GOTrivialExprIterator extends GONameIterator:
  import GOExpr._
  def iterate(x: Ref): Unit         = x.name.accept_use_iterator(this)
  def iterate(x: Literal): Unit     = ()

trait GOIterator extends GOTrivialExprIterator:
  import GOExpr._
  import GONode._
  def iterate(x: CtorApp): Unit        = x match
    case CtorApp(cls, xs)              => cls.accept_iterator(this); xs.foreach(_.accept_iterator(this))
  def iterate(x: Select): Unit         = x match
    case Select(x, cls, field)         => x.accept_use_iterator(this); cls.accept_iterator(this)
  def iterate(x: BasicOp): Unit        = x match
    case BasicOp(op, xs)               => xs.foreach(_.accept_iterator(this))
  def iterate(x: Lambda): Unit         = x match
    case Lambda(xs, body)              => ???
  def iterate(x: Apply): Unit          = x match
    case Apply(f, xs)                  => f.accept_use_iterator(this); xs.foreach(_.accept_iterator(this))
  def iterate(x: Result): Unit         = x match
    case Result(xs)                    => xs.foreach(_.accept_iterator(this))
  def iterate(x: Jump): Unit           = x match
    case Jump(jp, xs)                  => jp.accept_iterator(this); xs.foreach(_.accept_iterator(this))
  def iterate(x: Case): Unit           = x match
    case Case(x, cases)                => x.accept_use_iterator(this); cases foreach { (cls, arm) => arm.accept_iterator(this) }
  def iterate(x: LetExpr): Unit        = x match
    case LetExpr(x, e1, e2)            => x.accept_def_iterator(this); e1.accept_iterator(this); e2.accept_iterator(this)
  def iterate(x: LetJoin): Unit        = x match
    case LetJoin(jp, xs, e1, e2)       => e1.accept_iterator(this); e2.accept_iterator(this)
  def iterate(x: LetCall): Unit        = x match
    case LetCall(xs, f, as, e2)        => xs.foreach(_.accept_def_iterator(this)); f.accept_iterator(this); as.foreach(_.accept_iterator(this)); e2.accept_iterator(this)
  def iterate(x: GODefRef): Unit       = ()
  def iterate(x: ClassInfo): Unit      = ()
  def iterate(x: GODef): Unit =
    x.params.foreach(_.accept_param_iterator(this))
    x.body.accept_iterator(this)
  def iterate(x: GOProgram): Unit =
    x.classes.foreach(_.accept_iterator(this))
    x.defs.foreach(_.accept_iterator(this))
    x.main.accept_iterator(this)

trait GODefTraversalOrdering:
  def ordered(entry: GONode, defs: Set[GODef]): Ls[GODef]
  def ordered_names(entry: GONode, defs: Set[GODef]): Ls[Str]

object GODefDfs:
  import GONode._
  private class Successors extends GOIterator:
    var succ: ListBuffer[GODef] = ListBuffer()
    override def iterate(x: GODefRef) =
      succ += x.expectDefn

  private class SuccessorNames extends GOIterator:
    var succ: ListBuffer[Str] = ListBuffer()
    override def iterate(x: GODefRef) =
      succ += x.getName

  private def dfs(using visited: HashMap[Str, Bool], out: ListBuffer[GODef], postfix: Bool)(x: GODef): Unit =
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
  
  private def dfs(using visited: HashMap[Str, Bool], out: ListBuffer[GODef], postfix: Bool)(x: GONode): Unit =
    val succ = Successors()
    x.accept_iterator(succ)
    succ.succ.foreach { y =>
      if (!visited(y.name))
        dfs(y)
    }

  private def dfs_names(using visited: HashMap[Str, Bool], defs: Set[GODef], out: ListBuffer[Str], postfix: Bool)(x: GODef): Unit =
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
  
  private def dfs_names(using visited: HashMap[Str, Bool], defs: Set[GODef], out: ListBuffer[Str], postfix: Bool)(x: GONode): Unit =
    val succ = SuccessorNames()
    x.accept_iterator(succ)
    succ.succ.foreach { y =>
      if (!visited(y))
        dfs_names(defs.find(_.name == y).get)
    }

  def dfs(entry: GONode, defs: Set[GODef], postfix: Bool): Ls[GODef] =
    val visited = HashMap[Str, Bool]()
    visited ++= defs.map(_.name -> false)
    val out = ListBuffer[GODef]()
    dfs(using visited, out, postfix)(entry)
    out.toList

  def dfs_names(entry: GONode, defs: Set[GODef], postfix: Bool): Ls[Str] =
    val visited = HashMap[Str, Bool]()
    visited ++= defs.map(_.name -> false)
    val out = ListBuffer[Str]()
    dfs_names(using visited, defs, out, postfix)(entry)
    out.toList
    
object GODefRevPostOrdering extends GODefTraversalOrdering:
  def ordered(entry: GONode, defs: Set[GODef]): Ls[GODef] =
    GODefDfs.dfs(entry, defs, true).reverse
  def ordered_names(entry: GONode, defs: Set[GODef]): Ls[Str] =
    GODefDfs.dfs_names(entry, defs, true).reverse

object GODefRevPreOrdering extends GODefTraversalOrdering:
  def ordered(entry: GONode, defs: Set[GODef]): Ls[GODef] =
    GODefDfs.dfs(entry, defs, false).reverse
  def ordered_names(entry: GONode, defs: Set[GODef]): Ls[Str] =
    GODefDfs.dfs_names(entry, defs, false).reverse
