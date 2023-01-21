package mlscript
package compiler

import mlscript.utils.*
import mlscript.utils.shorthands.*
import collection.mutable.{Map => MutMap, Set => MutSet}
import mlscript.*

// -----------------------------------------------

class GOProgram(
  val classes: Set[ClassInfo],
  val defs: Set[GODef],
  // TODO add a cache of split defs
  val main: Node,
):
  override def toString(): String =
    s"GOProgram({${classes.mkString(",")}}, {\n${defs.mkString("\n")}\n},\n${main})"


case class ClassInfo(
  val id: Int,
  val ident: Str,
  val fields: Ls[Str],
):
  override def equals(o: Any) = o match {
    case o: ClassInfo if this.isInstanceOf[ClassInfo] => o.id == id
    case _ => false
  }
  override def hashCode = id
  override def toString(): String =
    s"ClassInfo(${id}, ${ident}, [${fields mkString ","}])"

case class Name(val str: Str):
  override def toString(): String = str

// TODO
class GODefRef(var defn: Either[GODef, Str]):
  def getName(): String = defn match {
    case Left(godef) => godef.getName()
    case Right(name) => name
  }

enum Elim:
  case EDirect
  case EApp(n: Int)
  case EDestruct
  case ESelect(x: Str)

  override def toString(): String = this match
    case EDirect => "EDirect"
    case EApp(n) => s"EApp(${n})"
    case EDestruct => s"EDestruct"
    case ESelect(x: Str) => s"ESelect(${x})"

enum Intro:
  case ICtor
  case ILam(n: Int)
  case IMulti(n: Int)
  
  override def toString(): String = this match
    case ICtor => s"ICtor"
    case ILam(n) => s"ILam(${n})"
    case IMulti(n) => s"IMulti(${n})"

class GODef(
  val id: Int,
  val name: Str,
  val isjp: Bool,
  val params: Ls[Name],
  val resultNum: Int,
  var body: Node,
  // TODO rec boundaries
):
  var activeParams: Ls[Set[Elim]] = Ls(Set())
  var activeResults: Ls[Opt[Intro]] = Ls(None)
  override def equals(o: Any) = o match {
    case o: GODef if this.isInstanceOf[GODef] => o.id == id
    case _ => false
  }
  override def hashCode = id
  def getName(): String = name
  def getBody(): Node = body
  override def toString(): String =
    val name2 = if (isjp) s"@join ${name}" else s"${name}" 
    s"Def(${id}, ${name2}, ${params.map(_.toString()).mkString("[", ",", "]")}, ${activeParams.map({ x => x.mkString("{", "，", "}")}).mkString("[", ",", "]")}, \n${activeResults.head.toString()}, ${resultNum}, \n${body}\n)"


sealed trait TrivialExpr:
  override def toString(): String
  def show: String
  def toDocument: Document

private def show_args(args: Ls[TrivialExpr]) = args map { x => x.show } mkString(",")

enum GOExpr:
  case Ref(name: Name) extends GOExpr, TrivialExpr
  case Literal(lit: Lit) extends GOExpr, TrivialExpr
  case CtorApp(name: ClassInfo, args: Ls[TrivialExpr])
  case Select(name: Name, field: Str)
  case BasicOp(name: Str, args: Ls[TrivialExpr])
  // TODO: depreceted: the following will be deleted
  case Lambda(name: Ls[Name], body: Node)
  case Apply(name: Name, args: Ls[TrivialExpr])
  
  override def toString(): String = show

  def show: String =
    toDocument.print
  
  def toDocument: Document = this match
    case Ref(Name(s)) => s |> raw
    case Literal(lit) => s"${lit}" |> raw
    case CtorApp(ClassInfo(_, name, _), args) =>
      raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")
    case Select(Name(s), fld) =>
      raw(s) <#> raw(".") <#> raw(fld)
    case BasicOp(name: Str, args) =>
      raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")
    case Lambda(name, body) =>
      raw(name map { case Name(str) => str} mkString ",")
      <:> raw("=>")
      <:> raw(s"${body}")
    case Apply(Name(name), args) =>
      raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")
    

enum Node:
  // Terminal forms:
  case Result(res: Ls[TrivialExpr])
  case Jump(joinName: Name, args: Ls[TrivialExpr])
  case Case(scrut: Name, cases: Ls[(ClassInfo, Node)])
  // Intermediate forms:
  case LetExpr(name: Name, expr: GOExpr, body: Node)
  case LetJoin(joinName: Name, params: Ls[Name], rhs: Node, body: Node)
  case LetCall(resultNames: Ls[Name], var defn: GODefRef, args: Ls[TrivialExpr], body: Node)

  override def toString(): String = show

  def show: String =
    toDocument.print

  def toDocument: Document = this match
    case Result(res) => raw(res |> show_args)
    case Jump(Name(name), args) =>
      raw("jump")
      <:> raw(name)
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
          <#> raw(params.map{ x => x.toString() }.mkString(","))
          <#> raw(")")
          <:> raw("=")
          <:> (rhs.toDocument |> indent |> indent),
        raw("in") <:> body.toDocument |> indent
      )
    case LetCall(resultNames, defn, args, body) => 
      stack(
        raw("let*")
          <:> raw("(")
          <#> raw(resultNames.map{ x => x.toString() }.mkString(","))
          <#> raw(")")
          <:> raw("=")
          <:> raw(defn.getName())
          <#> raw("(")
          <#> raw(args.map{ x => x.toString() }.mkString(","))
          <#> raw(")"),
        raw("in") <:> body.toDocument |> indent
      )
  
