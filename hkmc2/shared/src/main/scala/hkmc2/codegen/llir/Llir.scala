package hkmc2.codegen.llir

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._

import hkmc2.syntax._
import hkmc2.Message.MessageContext
import hkmc2.document._

import util.Sorting
import collection.immutable.SortedSet
import language.implicitConversions
import collection.mutable.{Map as MutMap, Set as MutSet, HashMap, ListBuffer}

private def raw(x: String): Document = doc"$x"

final case class LowLevelIRError(message: String) extends Exception(message)

case class Program(
  classes: Set[ClassInfo],
  defs: Set[Func],
  main: Node,
):
  override def toString: String =
    val t1 = classes.toArray
    val t2 = defs.toArray
    Sorting.quickSort(t1)
    Sorting.quickSort(t2)
    s"Program({${t1.mkString(",\n")}}, {\n${t2.mkString("\n")}\n},\n$main)"

  def show(hiddenNames: Set[Str] = Set.empty) = toDocument(hiddenNames).toString
  def toDocument(hiddenNames: Set[Str] = Set.empty) : Document =
    val t1 = classes.toArray
    val t2 = defs.toArray
    Sorting.quickSort(t1)
    Sorting.quickSort(t2)
    given Conversion[String, Document] = raw
    val docClasses = t1.filter(x => !hiddenNames.contains(x.name)).map(_.toDocument).toList.mkDocument(doc" # ")
    val docDefs = t2.map(_.toDocument).toList.mkDocument(doc" # ")
    val docMain = main.toDocument
    doc" #{ $docClasses\n$docDefs\n$docMain #} "

implicit object ClassInfoOrdering extends Ordering[ClassInfo] {
  def compare(a: ClassInfo, b: ClassInfo) = a.id.compare(b.id)
}

case class ClassInfo(
  id: Int,
  name: Str,
  fields: Ls[Str],
):
  var parents: Set[Str] = Set.empty
  var methods: Map[Str, Func] = Map.empty
  override def hashCode: Int = id
  override def toString: String =
    s"ClassInfo($id, $name, [${fields mkString ","}], parents: ${parents mkString ","}, methods:\n${methods mkString ",\n"})"

  def show = toDocument.toString
  def toDocument: Document =
    given Conversion[String, Document] = raw
    val ext = if parents.isEmpty then "" else " extends " + parents.mkString(", ")
    if methods.isEmpty then
      doc"class $name(${fields.mkString(",")})$ext"
    else
      val docFirst = doc"class $name (${fields.mkString(",")})$ext {"
      val docMethods = methods.map { (_, func) => func.toDocument }.toList.mkDocument(doc" # ")
      val docLast = doc"}"
      doc"$docFirst #{  # $docMethods #  #} $docLast"

case class Name(str: Str):
  def trySubst(map: Map[Str, Name]) = map.getOrElse(str, this)
  override def toString: String = str

object FuncRef:
  def fromName(name: Str) = FuncRef(Right(name))
  def fromName(name: Name) = FuncRef(Right(name.str))
  def fromFunc(func: Func) = FuncRef(Left(func))

class FuncRef(var func: Either[Func, Str]):
  def name: String = func.fold(_.name, x => x)
  def expectFn: Func = func.fold(identity, x => throw Exception(s"Expected a def, but got $x"))
  def getFunc: Opt[Func] = func.left.toOption
  override def equals(o: Any): Bool = o match {
    case o: FuncRef => o.name == this.name
    case _ => false
  }

object ClassRef:
  def fromName(name: Str) = ClassRef(Right(name))
  def fromName(name: Name) = ClassRef(Right(name.str))
  def fromClass(cls: ClassInfo) = ClassRef(Left(cls))

class ClassRef(var cls: Either[ClassInfo, Str]):
  def name: String = cls.fold(_.name, x => x) 
  def expectCls: ClassInfo = cls.fold(identity, x => throw Exception(s"Expected a class, but got $x"))
  def getClass: Opt[ClassInfo] = cls.left.toOption
  override def equals(o: Any): Bool = o match {
    case o: ClassRef => o.name == this.name
    case _ => false
  }

implicit object FuncOrdering extends Ordering[Func] {
  def compare(a: Func, b: Func) = a.id.compare(b.id)
}

case class Func(
  id: Int,
  name: Str,
  params: Ls[Name],
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
    val docFirst = doc"def $name(${params.map(_.toString).mkString(",")}) ="
    val docBody = body.toDocument
    doc"$docFirst #{  # $docBody #} "

sealed trait TrivialExpr:
  import Expr._
  override def toString: String
  def show: String
  def toDocument: Document
  def toExpr: Expr = this match { case x: Expr => x }

private def showArguments(args: Ls[TrivialExpr]) = args map (_.show) mkString ","

enum Expr:
  case Ref(name: Name) extends Expr, TrivialExpr 
  case Literal(lit: hkmc2.syntax.Literal) extends Expr, TrivialExpr
  case CtorApp(cls: ClassRef, args: Ls[TrivialExpr])
  case Select(name: Name, cls: ClassRef, field: Str)
  case BasicOp(name: Str, args: Ls[TrivialExpr])
  case AssignField(assignee: Name, cls: ClassRef, field: Str, value: TrivialExpr)
  
  override def toString: String = show

  def show: String = toDocument.toString
  
  def toDocument: Document = 
    given Conversion[String, Document] = raw
    this match
      case Ref(s) => s.toString
      case Literal(Tree.BoolLit(lit)) => s"$lit"
      case Literal(Tree.IntLit(lit)) => s"$lit"
      case Literal(Tree.DecLit(lit)) => s"$lit"
      case Literal(Tree.StrLit(lit)) => s"$lit"
      case Literal(Tree.UnitLit(undefinedOrNull)) => if undefinedOrNull then "undefined" else "null"
      case CtorApp(cls, args) =>
        doc"${cls.name}(${args.map(_.toString).mkString(",")})"
      case Select(s, cls, fld) =>
        doc"${s.toString}.<${cls.name}:$fld>"
      case BasicOp(name: Str, args) =>
        doc"$name(${args.map(_.toString).mkString(",")})"
      case AssignField(assignee, clsInfo, fieldName, value) => 
        doc"${assignee.toString}.${fieldName} := ${value.toString}"

enum Pat:
  case Lit(lit: hkmc2.syntax.Literal)
  case Class(cls: ClassRef)

  override def toString: String = this match
    case Lit(lit) => s"$lit"
    case Class(cls) => s"${cls.name}"

enum Node:
  // Terminal forms:
  case Result(res: Ls[TrivialExpr])
  case Jump(func: FuncRef, args: Ls[TrivialExpr])
  case Case(scrutinee: TrivialExpr, cases: Ls[(Pat, Node)], default: Opt[Node])
  case Panic(msg: Str)
  // Intermediate forms:
  case LetExpr(name: Name, expr: Expr, body: Node)
  case LetMethodCall(names: Ls[Name], cls: ClassRef, method: Name, args: Ls[TrivialExpr], body: Node)
  case LetCall(names: Ls[Name], func: FuncRef, args: Ls[TrivialExpr], body: Node)

  override def toString: String = show

  def show: String = toDocument.toString

  def toDocument: Document =
    given Conversion[String, Document] = raw
    this match
    case Result(res) => (res |> showArguments)
    case Jump(jp, args) =>
      doc"jump ${jp.name}(${args |> showArguments})"
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
      doc"let ${x.toString} = ${expr.toString} in # ${body.toDocument}"
    case LetMethodCall(xs, cls, method, args, body) =>
      doc"let ${xs.map(_.toString).mkString(",")} = ${cls.name}.${method.toString}(${args.map(_.toString).mkString(",")}) in # ${body.toDocument}"
    case LetCall(xs, func, args, body) => 
      doc"let* (${xs.map(_.toString).mkString(",")}) = ${func.name}(${args.map(_.toString).mkString(",")}) in # ${body.toDocument}"

