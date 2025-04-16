package hkmc2
package codegen.llir

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._

import syntax._
import Message.MessageContext
import document._
import codegen._

import util.Sorting
import collection.immutable.SortedSet
import language.implicitConversions
import collection.mutable.{Map as MutMap, Set as MutSet, HashMap, ListBuffer}
import hkmc2.semantics._

private def raw(x: String): Document = doc"$x"

final case class LowLevelIRError(message: String) extends Exception(message)

private def docSymWithUid(sym: Local): Document = doc"${sym.nme}$$${sym.uid.toString()}"

val hiddenPrefixes = Set("Tuple")

def defaultHidden(x: Str): Bool =
  hiddenPrefixes.exists(x.startsWith)

case class Program(
  classes: Set[ClassInfo],
  defs: Set[Func],
  entry: Local,
):
  override def toString: String =
    val t1 = classes.toArray
    val t2 = defs.toArray
    Sorting.quickSort(t1)
    Sorting.quickSort(t2)
    s"Program({${t1.mkString(",\n")}}, {\n${t2.mkString("\n")}\n},\n$entry)"

  def show(hide: Str => Bool = defaultHidden) = toDocument(hide).toString
  def toDocument(hide: Str => Bool = defaultHidden) : Document =
    val t1 = classes.iterator.filterNot(c => hide(c.symbol.nme)).toArray
    val t2 = defs.toArray
    Sorting.quickSort(t1)
    Sorting.quickSort(t2)
    given Conversion[String, Document] = raw
    val docClasses = t1.map(_.toDocument).toList.mkDocument(doc" # ")
    val docDefs = t2.map(_.toDocument).toList.mkDocument(doc" # ")
    val docMain = doc"entry = ${entry.nme}$$${entry.uid.toString()}"
    doc" #{ $docClasses\n$docDefs\n$docMain #} "

implicit object ClassInfoOrdering extends Ordering[ClassInfo] {
  def compare(a: ClassInfo, b: ClassInfo) = a.id.compare(b.id)
}

case class ClassInfo(
  id: Int,
  symbol: MemberSymbol[? <: ClassLikeDef],
  fields: Ls[VarSymbol],
  parents: Set[Local],
  methods: Map[Local, Func],
):
  override def hashCode: Int = id
  override def toString: String =
    s"ClassInfo($id, $symbol, [${fields mkString ","}], parents: ${parents mkString ","}, methods:\n${methods mkString ",\n"})"

  def show = toDocument.toString
  def toDocument: Document =
    given Conversion[String, Document] = raw
    val ext = if parents.isEmpty then "" else " extends " + parents.map(_.nme).mkString(", ")
    if methods.isEmpty then
      doc"class ${symbol.nme}(${fields.map(docSymWithUid).mkString(",")})$ext"
    else
      val docFirst = doc"class ${symbol.nme}(${fields.map(docSymWithUid).mkString(",")})$ext {"
      val docMethods = methods.map { (_, func) => func.toDocument }.toList.mkDocument(doc" # ")
      val docLast = doc"}"
      doc"$docFirst #{  # $docMethods #}  # $docLast"

class FuncRef(var func: Local):
  def name: String = func.nme
  override def equals(o: Any): Bool = o match {
    case o: FuncRef => o.name === this.name
    case _ => false
  }

implicit object FuncOrdering extends Ordering[Func] {
  def compare(a: Func, b: Func) = a.id.compare(b.id)
}

case class Func(
  id: Int,
  name: BlockMemberSymbol,
  params: Ls[Local],
  resultNum: Int,
  body: Node
):
  var recBoundary: Opt[Int] = None
  override def hashCode: Int = id

  override def toString: String =
    val ps = params.map(_.toString).mkString("[", ",", "]")
    s"Def($id, $name, $ps, \n$resultNum, \n$body\n)"

  def show = toDocument
  def toDocument: Document =
    given Conversion[String, Document] = raw
    val docFirst = doc"def ${docSymWithUid(name)}(${params.map(docSymWithUid).mkString(",")}) ="
    val docBody = body.toDocument
    doc"$docFirst #{  # $docBody #} "

sealed trait TrivialExpr:
  import Expr._
  override def toString: String
  def show: String
  def toDocument: Document
  def toExpr: Expr = this match { case x: Expr => x }
  def foldRef(f: Local => TrivialExpr): TrivialExpr = this match
    case Ref(sym) => f(sym)
    case _ => this
  def iterRef(f: Local => Unit): Unit = this match
    case Ref(sym) => f(sym)
    case _ => ()

private def showArguments(args: Ls[TrivialExpr]) = args map (_.show) mkString ","

enum Expr:
  case Ref(sym: Local) extends Expr, TrivialExpr 
  case Literal(lit: hkmc2.syntax.Literal) extends Expr, TrivialExpr
  case CtorApp(cls: MemberSymbol[? <: ClassLikeDef], args: Ls[TrivialExpr])
  case Select(name: Local, cls: Local, field: Str)
  case BasicOp(name: BuiltinSymbol, args: Ls[TrivialExpr])
  case AssignField(assignee: Local, cls: Local, field: Str, value: TrivialExpr)
  
  override def toString: String = show

  def show: String = toDocument.toString
  
  def toDocument: Document = 
    given Conversion[String, Document] = raw
    this match
      case Ref(s) => docSymWithUid(s)
      case Literal(Tree.BoolLit(lit)) => s"$lit"
      case Literal(Tree.IntLit(lit)) => s"$lit"
      case Literal(Tree.DecLit(lit)) => s"$lit"
      case Literal(Tree.StrLit(lit)) => s"${lit.escaped}"
      case Literal(Tree.UnitLit(isNullNotUndefined)) =>
        if isNullNotUndefined then "null" else "undefined"
      case CtorApp(cls, args) =>
        doc"${docSymWithUid(cls)}(${args.map(_.toString).mkString(",")})"
      case Select(s, cls, fld) =>
        doc"${docSymWithUid(s)}.<${docSymWithUid(cls)}:$fld>"
      case BasicOp(sym, args) =>
        doc"${sym.nme}(${args.map(_.toString).mkString(",")})"
      case AssignField(assignee, clsInfo, fieldName, value) => 
        doc"${docSymWithUid(assignee)}.${fieldName} := ${value.toString}"

enum Pat:
  case Lit(lit: hkmc2.syntax.Literal)
  case Class(cls: Local)

  override def toString: String = this match
    case Lit(lit) => s"$lit"
    case Class(cls) => s"${{docSymWithUid(cls)}}"

enum Node:
  // Terminal forms:
  case Result(res: Ls[TrivialExpr])
  case Jump(func: Local, args: Ls[TrivialExpr])
  case Case(scrutinee: TrivialExpr, cases: Ls[(Pat, Node)], default: Opt[Node])
  case Panic(msg: Str)
  // Intermediate forms:
  case LetExpr(name: Local, expr: Expr, body: Node)
  case LetMethodCall(names: Ls[Local], cls: Local, method: Local, args: Ls[TrivialExpr], body: Node)
  case LetCall(names: Ls[Local], func: Local, args: Ls[TrivialExpr], body: Node)

  override def toString: String = show

  def show: String = toDocument.toString

  def toDocument: Document =
    given Conversion[String, Document] = raw
    this match
    case Result(res) => (res |> showArguments)
    case Jump(jp, args) =>
      doc"jump ${docSymWithUid(jp)}(${args |> showArguments})"
    case Case(x, cases, default) =>
      val docFirst = doc"case ${x.toString} of"
      val docCases = cases.map {
        case (pat, node) => doc"${pat.toString} => #{  # ${node.toDocument} #} "
      }.mkDocument(doc" # ")
      default match
        case N => doc"$docFirst #{  # $docCases #} "
        case S(dc) =>
          val docDeft = doc"_ => #{  # ${dc.toDocument} #} "
          doc"$docFirst #{  # $docCases # $docDeft #} "
    case Panic(msg) =>
      doc"panic ${s"\"$msg\""}"
    case LetExpr(x, expr, body) => 
      doc"let ${docSymWithUid(x)} = ${expr.toString} in # ${body.toDocument}"
    case LetMethodCall(xs, cls, method, args, body) =>
      doc"let ${xs.map(docSymWithUid).mkString(",")} = ${cls.nme}.${docSymWithUid(method)}(${args.map(_.toString).mkString(",")}) in # ${body.toDocument}"
    case LetCall(xs, func, args, body) => 
      doc"let* (${xs.map(docSymWithUid).mkString(",")}) = ${func.nme}(${args.map(_.toString).mkString(",")}) in # ${body.toDocument}"

