package mlscript
package compiler

import mlscript.utils.*
import mlscript.utils.shorthands.*

import collection.mutable.{Map as MutMap, Set as MutSet}
import mlscript.*

import scala.annotation.unused
import scala.util.Sorting

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
    Sorting.quickSort(t1)(ClassInfoOrdering)
    Sorting.quickSort(t2)(GODefOrdering)
    s"GOProgram({${t1.mkString(",")}}, {\n${t2.mkString("\n")}\n},\n$main)"
  def accept(v: GOVistor) = v.visit(this)
  def accept(v: GOIterator) = v.iterate(this)

object ClassInfoOrdering extends Ordering[ClassInfo] {
  def compare(a: ClassInfo, b: ClassInfo) = a.id.compare(b.id)
}
object GODefOrdering extends Ordering[GODef] {
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
  def accept(v: GOVistor) = v.visit(this)
  def accept(v: GOIterator) = v.iterate(this)

case class Name(val str: Str):
  override def equals(o: Any): Bool = o match {
    case Name(s2) => str == s2
    case _ => false
  }
  override def toString: String = str

class GODefRef(var defn: Either[GODef, Str]):
  def getName: String = defn match {
    case Left(godef) => godef.getName
    case Right(name) => name
  }
  override def equals(o: Any): Bool = o match {
    case o: GODefRef if this.isInstanceOf[GODefRef] =>
      o.getName == this.getName
    case _ => false
  }

enum Elim:
  case EDirect
  case EApp(n: Int)
  case EDestruct
  case ESelect(x: Str)

  override def toString: String = this match
    case EDirect => "EDirect"
    case EApp(n) => s"EApp($n)"
    case EDestruct => s"EDestruct"
    case ESelect(x: Str) => s"ESelect($x)"

enum Intro:
  case ICtor(c: Str)
  case ILam(n: Int)
  case IMulti(n: Int)
  
  override def toString: String = this match
    case ICtor(c) => s"ICtor($c)"
    case ILam(n) => s"ILam($n)"
    case IMulti(n) => s"IMulti($n)"

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
  var activeResults: Ls[Opt[Intro]] = Ls(None)
  var livein: Set[Str] = Set.empty
  var liveout: Set[Str] = Set.empty
  var isTrivial: Bool = false
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
  def accept(v: GOVistor) = v.visit(this)
  def accept(v: GOIterator) = v.iterate(this)
  override def toString: String =
    val name2 = if (isjp) s"@join $name" else s"$name" 
    s"Def($id, $name2, ${params.map(_.toString()).mkString("[", ",", "]")}, ${activeParams.map({ x => x.mkString("{", "，", "}")}).mkString("[", ",", "]")}, \n${activeResults.head.toString}, $resultNum, \n$body\n)"

sealed trait TrivialExpr:
  override def toString: String
  def show: String
  def toDocument: Document
  def accept(v: GOTrivialExprVistor): TrivialExpr = this match
    case x: GOExpr.Ref => v.visit(x)
    case x: GOExpr.Literal => v.visit(x)
  def accept(v: GOTrivialExprIterator): Unit = this match
    case x: GOExpr.Ref => v.iterate(x)
    case x: GOExpr.Literal => v.iterate(x)

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

  def accept(v: GOVistor): GOExpr = this match
    case x: Ref => v.visit(x)
    case x: Literal => v.visit(x)
    case x: CtorApp => v.visit(x)
    case x: Select => v.visit(x)
    case x: BasicOp => v.visit(x)
    case x: Lambda => v.visit(x)
    case x: Apply => v.visit(x)

  def accept(v: GOIterator): Unit = this match
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

  def accept(v: GOVistor): GONode  = this match
    case x: Result => v.visit(x)
    case x: Jump => v.visit(x)
    case x: Case => v.visit(x)
    case x: LetExpr => v.visit(x)
    case x: LetJoin => v.visit(x)
    case x: LetCall => v.visit(x)

  def accept(v: GOIterator): Unit  = this match
    case x: Result => v.iterate(x)
    case x: Jump => v.iterate(x)
    case x: Case => v.iterate(x)
    case x: LetExpr => v.iterate(x)
    case x: LetJoin => v.iterate(x)
    case x: LetCall => v.iterate(x)

trait GOTrivialExprVistor:
  import GOExpr._
  def visit(x: Ref): Ref                 = x
  def visit(x: Literal): Literal         = x
  def visit(x: TrivialExpr): TrivialExpr = x match
    case x: Ref                          => x.accept(this)
    case x: Literal                      => x.accept(this)

trait GOVistor extends GOTrivialExprVistor:
  import GOExpr._
  import GONode._
  def visit(x: CtorApp): GOExpr       = x match
    case CtorApp(cls, xs)                => CtorApp(cls, xs.map(_.accept(this)))
  def visit(x: Select): GOExpr           = x
  def visit(x: BasicOp): GOExpr         = x match
    case BasicOp(op, xs)                 => BasicOp(op, xs.map(_.accept(this)))
  def visit(x: Lambda): GOExpr          = x match
    case Lambda(name, body)              => Lambda(name, body.accept(this))
  def visit(x: Apply): GOExpr             = x match
    case Apply(f, xs)                    => Apply(f, xs.map(_.accept(this)))
  def visit(x: Result): GONode           = x match
    case Result(xs)                      => Result(xs.map(_.accept(this)))
  def visit(x: Jump): GONode               = x match
    case Jump(jp, xs)                    => Jump(jp, xs.map(_.accept(this)))
  def visit(x: Case): GONode               = x match
    case Case(scrut, cases)              => Case(scrut, cases map { (cls, arm) => (cls, arm.accept(this)) })
  def visit(x: LetExpr): GONode         = x match
    case LetExpr(x, e1, e2)              => LetExpr(x, e1.accept(this), e2.accept(this))
  def visit(x: LetJoin): GONode          = x match
    case LetJoin(jp, xs, e1, e2)         => LetJoin(jp, xs, e1.accept(this), e2.accept(this))
  def visit(x: LetCall): GONode         = x match
    case LetCall(xs, f, as, e2)          => LetCall(xs, f, as.map(_.accept(this)), e2.accept(this))
  def visit(x: ClassInfo): ClassInfo     = x
  def visit(x: GODef): GODef             =
    GODef(
      x.id,
      x.name,
      x.isjp,
      x.params,
      x.resultNum,
      x.body.accept(this))
  def visit(x: GOProgram): GOProgram     =
    GOProgram(
      x.classes.map(_.accept(this)),
      x.defs.map(_.accept(this)),
      x.main.accept(this))

trait GOTrivialExprIterator:
  import GOExpr._
  def iterate(x: Ref): Unit         = ()
  def iterate(x: Literal): Unit     = ()
  def iterate(x: TrivialExpr): Unit = x match
    case x: Ref                     => x.accept(this)
    case x: Literal                 => x.accept(this)

trait GOIterator extends GOTrivialExprIterator:
  import GOExpr._
  import GONode._
  def iterate(x: CtorApp): Unit     = x match { case CtorApp(cls, xs)        => xs.foreach(_.accept(this)) }
  def iterate(x: Select):  Unit     = ()
  def iterate(x: BasicOp): Unit     = x match { case BasicOp(op, xs)         => xs.foreach(_.accept(this)) }
  def iterate(x: Lambda): Unit      = x match { case Lambda(name, body)      => body.accept(this) }
  def iterate(x: Apply): Unit       = x match { case Apply(f, xs)            => xs.foreach(_.accept(this)) }
  def iterate(x: Result): Unit      = x match { case Result(xs)              => xs.foreach(_.accept(this)) }
  def iterate(x: Jump): Unit        = x match { case Jump(jp, xs)            => xs.foreach(_.accept(this)) }
  def iterate(x: Case): Unit        = x match { case Case(scrut, cases)      =>
    cases foreach { (cls, arm)      => (cls, arm.accept(this)) } }
  def iterate(x: LetExpr): Unit     = x match { case LetExpr(x, e1, e2)      => 
    e1.accept(this)
    e2.accept(this) }
  def iterate(x: LetJoin): Unit     = x match { case LetJoin(jp, xs, e1, e2) =>
    e1.accept(this)
    e2.accept(this) }
  def iterate(x: LetCall): Unit     = x match { case LetCall(xs, f, as, e2)  =>
    as.foreach(_.accept(this))
    e2.accept(this) }
  def iterate(x: ClassInfo): Unit   = ()
  def iterate(x: GODef): Unit       =
    x.body.accept(this)
  def iterate(x: GOProgram): Unit   =
    x.classes.foreach(_.accept(this))
    x.defs.foreach(_.accept(this))
    x.main.accept(this)

