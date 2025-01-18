package hkmc2.codegen.cpp

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._

import hkmc2.Message.MessageContext
import hkmc2.document._

import scala.language.implicitConversions

private def raw(x: String): Document = doc"$x"
given Conversion[String, Document] = x => doc"$x"

enum Specifier:
  case Extern
  case Static
  case Inline

  def toDocument = 
    this match
    case Extern => "extern"
    case Static => "static"
    case Inline => "inline"

  override def toString: Str = toDocument

object Type:
  def toDocuments(args: Ls[Type], sep: Document, extraTypename: Bool = false): Document =
    args.map(_.toDocument(extraTypename)).mkDocument(sep)

  def toDocuments(args: Ls[(Str, Type)], sep: Document): Document =
    args.map(x => doc"${x._2.toDocument()} ${x._1}").mkDocument(sep)

enum Type:
  case Prim(name: Str)
  case Ptr(inner: Type)
  case Ref(inner: Type)
  case Array(inner: Type, size: Opt[Int])
  case FuncPtr(ret: Type, args: List[Type])
  case Struct(name: Str)
  case Enum(name: Str)
  case Template(name: Str, args: List[Type])
  case Var(name: Str)
  case Qualifier(inner: Type, qual: Str)

  def toDocument(extraTypename: Bool = false): Document =
    def aux(x: Type): Document = x match
      case Prim(name) => name
      case Ptr(inner) => doc"${aux(inner)}*" 
      case Ref(inner) => doc"${aux(inner)}&"
      case Array(inner, size) => 
        doc"${aux(inner)}[${size.fold("")(x => x.toString)}]"
      case FuncPtr(ret, args) => 
        doc"${aux(ret)}(${Type.toDocuments(args, sep = ", ")})"
      case Struct(name) => doc"struct $name"
      case Enum(name) => doc"enum $name"
      case Template(name, args) =>
        doc"$name<${Type.toDocuments(args, sep = ", ")}>"
      case Var(name) => name
      case Qualifier(inner, qual) => doc"${aux(inner)} $qual"
    aux(this)

  override def toString: Str = toDocument().toString

object Stmt:
  def toDocuments(decl: Ls[Decl], stmts: Ls[Stmt]): Document =
    (decl.map(_.toDocument) ++ stmts.map(_.toDocument)).mkDocument(doc" # ")

enum Stmt:
  case AutoBind(lhs: Ls[Str], rhs: Expr)
  case Assign(lhs: Str, rhs: Expr)
  case Return(expr: Expr)
  case If(cond: Expr, thenStmt: Stmt, elseStmt: Opt[Stmt])
  case While(cond: Expr, body: Stmt)
  case For(init: Stmt, cond: Expr, update: Stmt, body: Stmt)
  case ExprStmt(expr: Expr)
  case Break
  case Continue
  case Block(decl: Ls[Decl], stmts: Ls[Stmt])
  case Switch(expr: Expr, cases: Ls[(Expr, Stmt)])
  case Raw(stmt: Str)

  def toDocument: Document =
    def aux(x: Stmt): Document = x match
      case AutoBind(lhs, rhs) =>
        lhs match
          case Nil => rhs.toDocument
          case x :: Nil =>
            doc"auto $x = ${rhs.toDocument};"
          case _ =>
            doc"auto [${lhs.mkDocument(", ")}] = ${rhs.toDocument};"
      case Assign(lhs, rhs) =>
        doc"$lhs = ${rhs.toDocument};"
      case Return(expr) =>
        doc"return ${expr.toDocument};"
      case If(cond, thenStmt, elseStmt) =>
        doc"if (${cond.toDocument}) ${thenStmt.toDocument}${elseStmt.fold(doc" ")(x => doc" else ${x.toDocument}")}"
      case While(cond, body) =>
        doc"while (${cond.toDocument}) ${body.toDocument}"
      case For(init, cond, update, body) =>
        doc"for (${init.toDocument}; ${cond.toDocument}; ${update.toDocument}) ${body.toDocument}"
      case ExprStmt(expr) =>
        doc"${expr.toDocument};"
      case Break => "break;"
      case Continue => "continue;"
      case Block(decl, stmts) => 
        doc"{ #{  # ${Stmt.toDocuments(decl, stmts)} #}  # }"
      case Switch(expr, cases) =>
        val docCases = cases.map {
          case (cond, stmt) => doc"case ${cond.toDocument}: ${stmt.toDocument}"
        }.mkDocument(doc" # ")
        doc"switch (${expr.toDocument}) { #{  # ${docCases} #}  # }"
      case Raw(stmt) => stmt
    aux(this)

object Expr:
  def toDocuments(args: Ls[Expr], sep: Document): Document =
    args.map(_.toDocument).mkDocument(sep)
  
enum Expr:
  case Var(name: Str)
  case IntLit(value: BigInt)
  case DoubleLit(value: Double)
  case StrLit(value: Str)
  case CharLit(value: Char)
  case Call(func: Expr, args: Ls[Expr])
  case Member(expr: Expr, member: Str)
  case Index(expr: Expr, index: Expr)
  case Unary(op: Str, expr: Expr)
  case Binary(op: Str, lhs: Expr, rhs: Expr)
  case Initializer(exprs: Ls[Expr])
  case Constructor(name: Str, init: Expr)

  def toDocument: Document =
    def aux(x: Expr): Document = x match
      case Var(name) => name
      case IntLit(value) => value.toString
      case DoubleLit(value) => value.toString
      case StrLit(value) => s"\"$value\"" // need more reliable escape utils
      case CharLit(value) => value.toInt.toString
      case Call(func, args) =>
        doc"${func.toDocument}(${Expr.toDocuments(args, sep = ", ")})"
      case Member(expr, member) => 
        doc"${expr.toDocument}->$member"
      case Index(expr, index) =>
        doc"${expr.toDocument}[${index.toDocument}]"
      case Unary(op, expr) => 
        doc"($op${expr.toDocument})"
      case Binary(op, lhs, rhs) =>
        doc"(${lhs.toDocument} $op ${rhs.toDocument})"
      case Initializer(exprs) => 
        doc"{${Expr.toDocuments(exprs, sep = ", ")}}"
      case Constructor(name, init) =>
        doc"$name(${init.toDocument})"
    aux(this)

case class CompilationUnit(includes: Ls[Str], decls: Ls[Decl], defs: Ls[Def]):
  def toDocument: Document =
    (includes.map(raw) ++ decls.map(_.toDocument) ++ defs.map(_.toDocument)).mkDocument(doc" # ")
  def toDocumentWithoutHidden: Document =
    val hiddenNames: Set[Str] = Set()
    defs.filterNot { 
      case Def.StructDef(name, _, _, _) => hiddenNames.contains(name.stripPrefix("_mls_"))
      case _ => false
    }.map(_.toDocument).mkDocument(doc" # ")

enum Decl:
  case StructDecl(name: Str)
  case EnumDecl(name: Str)
  case FuncDecl(ret: Type, name: Str, args: Ls[Type])
  case VarDecl(name: Str, typ: Type)

  def toDocument: Document =
    def aux(x: Decl): Document = x match
      case StructDecl(name) => doc"struct $name;"
      case EnumDecl(name) => doc"enum $name;"
      case FuncDecl(ret, name, args) =>
        doc"${ret.toDocument()} $name(${Type.toDocuments(args, sep = ", ")});"
      case VarDecl(name, typ) => 
        doc"${typ.toDocument()} $name;"
    aux(this)

enum Def:
  case StructDef(name: Str, fields: Ls[(Str, Type)], inherit: Opt[Ls[Str]], methods: Ls[Def] = Ls.empty)
  case EnumDef(name: Str, fields: Ls[(Str, Opt[Int])])
  case FuncDef(specret: Type, name: Str, args: Ls[(Str, Type)], body: Stmt.Block, or: Bool = false, virt: Bool = false)
  case VarDef(typ: Type, name: Str, init: Opt[Expr])
  case RawDef(raw: Str)

  def toDocument: Document =
    def aux(x: Def): Document = x match
      case StructDef(name, fields, inherit, defs) =>
        val docFirst = doc"struct $name${inherit.fold(doc"")(x => doc": public ${x.mkDocument(doc", ")}")} {"
        val docFields = fields.map {
          case (name, typ) => doc"${typ.toDocument()} $name;"
        }.mkDocument(doc" # ")
        val docDefs = defs.map(_.toDocument).mkDocument(doc" # ")
        val docLast = "};"
        doc"$docFirst #{  # $docFields # $docDefs #}  # $docLast"
      case EnumDef(name, fields) =>
        val docFirst = doc"enum $name {"
        val docFields = fields.map {
          case (name, value) => value.fold(s"$name")(x => s"$name = $x")
        }.mkDocument(doc" # ")
        val docLast = "};"
        doc"$docFirst #{  # $docFields #}  # $docLast"
      case FuncDef(specret, name, args, body, or, virt) =>
        val docVirt = (if virt then doc"virtual " else doc"")
        val docSpecRet = specret.toDocument()
        val docArgs = Type.toDocuments(args, sep = ", ")
        val docOverride = if or then doc" override" else doc""
        val docBody = body.toDocument
        doc"$docVirt$docSpecRet $name($docArgs)$docOverride ${body.toDocument}"
      case VarDef(typ, name, init) =>
        val docTyp = typ.toDocument()
        val docInit = init.fold(raw(""))(x => doc" = ${x.toDocument}")
        doc"$docTyp $name$docInit;"
      case RawDef(x) => x
    aux(this)
