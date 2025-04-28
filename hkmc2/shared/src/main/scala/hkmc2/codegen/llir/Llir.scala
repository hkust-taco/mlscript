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

val hiddenPrefixes = Set("Tuple")

def defaultHidden(x: Str): Bool =
  hiddenPrefixes.exists(x.startsWith)

case class Program(
  classes: Set[ClassInfo],
  defs: Set[Func],
  entry: Local,
):
  def show = LlirDebugPrinter.mkDocument(this).toString

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
  def show = LlirDebugPrinter.mkDocument(this).toString

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
  def show = LlirDebugPrinter.mkDocument(this).toString

sealed trait TrivialExpr:
  import Expr._
  def toExpr: Expr = this match { case x: Expr => x }
  def foldRef(f: Local => TrivialExpr): TrivialExpr = this match
    case Ref(sym) => f(sym)
    case _ => this
  def iterRef(f: Local => Unit): Unit = this match
    case Ref(sym) => f(sym)
    case _ => ()
  def show: String

enum Expr:
  case Ref(sym: Local) extends Expr, TrivialExpr 
  case Literal(lit: hkmc2.syntax.Literal) extends Expr, TrivialExpr
  case CtorApp(cls: MemberSymbol[? <: ClassLikeDef], args: Ls[TrivialExpr])
  case Select(name: Local, cls: Local, field: Str)
  case BasicOp(name: BuiltinSymbol, args: Ls[TrivialExpr])
  case AssignField(assignee: Local, cls: Local, field: Str, value: TrivialExpr)
  def show = LlirDebugPrinter.mkDocument(this).toString

enum Pat:
  case Lit(lit: hkmc2.syntax.Literal)
  case Class(cls: Local)

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
  def show = LlirDebugPrinter.mkDocument(this).toString

abstract class LlirPrinting:
  import hkmc2.utils.*
  import hkmc2.semantics.Elaborator.State

  def mkDocument(local: Local): Document
  def mkDocument(lit: Literal): Document = doc"${lit.idStr}"
  def mkDocument(texpr: TrivialExpr): Document = texpr match
    case Expr.Ref(sym) => mkDocument(sym)
    case Expr.Literal(lit) => mkDocument(lit)

  def mkDocument(expr: Expr): Document =
    expr match
      case Expr.Ref(sym) => doc"${mkDocument(sym)}"
      case Expr.Literal(lit) => doc"${lit.idStr}"
      case Expr.CtorApp(cls, args) =>
        doc"${mkDocument(cls)}(${args.map(mkDocument).mkString(",")})"
      case Expr.Select(name, cls, field) =>
        doc"${mkDocument(name)}.<${mkDocument(cls)}:$field>"
      case Expr.BasicOp(sym, args) =>
        doc"${sym.nme}(${args.map(mkDocument).mkString(",")})"
      case Expr.AssignField(assignee, clsInfo, fieldName, value) => 
        doc"${mkDocument(assignee)}.${fieldName} := ${mkDocument(value)}"
  def mkDocument(node: Node): Document =
    node match
      case Node.Result(res) => doc"${res.map(mkDocument).mkString(",")}"
      case Node.Jump(func, args) =>
        doc"jump ${mkDocument(func)}(${args.map(mkDocument).mkString(",")})"
      case Node.Case(scrutinee, cases, default) =>
        val docFirst = doc"case ${mkDocument(scrutinee)} of"
        val docCases = cases.map {
          case (pat, node) => doc"${pat.toString} => #{  # ${mkDocument(node)} #} "
        }.mkDocument(doc" # ")
        default match
          case N => doc"$docFirst #{  # $docCases #} "
          case S(dc) =>
            val docDeft = doc"_ => #{  # ${mkDocument(dc)} #} "
            doc"$docFirst #{  # $docCases # $docDeft #} "
      case Node.Panic(msg) =>
        doc"panic ${s"\"$msg\""}"
      case Node.LetExpr(x, expr, body) => 
        doc"let ${mkDocument(x)} = ${mkDocument(expr)} in # ${mkDocument(body)}"
      case Node.LetMethodCall(xs, cls, method, args, body) =>
        doc"let ${xs.map(mkDocument).mkString(",")} = ${mkDocument(cls)}.${method.nme}(${args.map(mkDocument).mkString(",")}) in # ${mkDocument(body)}"
      case Node.LetCall(xs, func, args, body) => 
        doc"let* (${xs.map(mkDocument).mkString(",")}) = ${mkDocument(func)}(${args.map(mkDocument).mkString(",")}) in # ${mkDocument(body)}"
  def mkDocument(defn: Func): Document =
    def docParams(params: Ls[Local]): Document =
      params.map(mkDocument).mkString("(", ",", ")")
    given Conversion[String, Document] = raw
    val docFirst = doc"def ${mkDocument(defn.name)}${docParams(defn.params)} ="
    val docBody = mkDocument(defn.body)
    doc"$docFirst #{  # $docBody #} "
  def mkDocument(cls: ClassInfo): Document =
    given Conversion[String, Document] = raw
    val ext = if cls.parents.isEmpty then "" else " extends " + cls.parents.map(mkDocument).mkString(", ")
    val docFirst = doc"class ${mkDocument(cls.symbol)}(${cls.fields.map(_.nme).mkString(",")})$ext"
    if cls.methods.isEmpty then
      doc"$docFirst"
    else
      val docMethods = cls.methods.map { (_, func) => mkDocument(func) }.toList.mkDocument(doc" # ")
      doc"$docFirst { #{  # $docMethods #}  # }"
  def mkDocument(prog: Program, hide: Str => Bool = defaultHidden): Document =
    given Conversion[String, Document] = raw
    val t1 = prog.classes.iterator.filterNot(c => hide(c.symbol.nme)).toArray
    val t2 = prog.defs.toArray
    Sorting.quickSort(t1)
    Sorting.quickSort(t2)
    val docClasses = t1.filterNot(c => hide(c.symbol.nme)).map(mkDocument).toList.mkDocument(doc" # ")
    val docDefs = t2.map(mkDocument).toList.mkDocument(doc" # ")
    val docMain = doc"entry = ${mkDocument(prog.entry)}"
    doc" #{ $docClasses\n$docDefs\n$docMain #} "

class LlirPrinter(using Raise, hkmc2.utils.Scope) extends LlirPrinting:
  import hkmc2.utils.*
  import hkmc2.semantics.Elaborator.State

  def getVar(l: Local): String = l match
    case ts: hkmc2.semantics.TermSymbol =>
      ts.owner match
      case S(owner) => summon[Scope].lookup_!(ts)
      case N => summon[Scope].lookup_!(ts)
    case ts: hkmc2.semantics.InnerSymbol =>
      summon[Scope].lookup_!(ts)
    case _ => summon[Scope].lookup_!(l)
  def allocIfNew(l: Local): String =
    summon[Scope].lookup(l) match
      case S(_) => getVar(l)
      case N =>
        summon[Scope].allocateName(l)
  override def mkDocument(local: Local): Document = allocIfNew(local)
        
object LlirDebugPrinter extends LlirPrinting:
  import hkmc2.utils.*
  def docSymWithUid(sym: Local): Document = doc"${sym.nme}$$${sym.uid.toString()}"
  override def mkDocument(local: Local): Document = docSymWithUid(local)
