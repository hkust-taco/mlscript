package mlscript.compiler.codegen.cpp

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import mlscript.compiler.utils._

import scala.language.implicitConversions

given Conversion[String, Document] = raw

enum Specifier:
  case Extern
  case Static
  case Inline

  def toDocument = raw:
    this match
    case Extern => "extern"
    case Static => "static"
    case Inline => "inline"

  override def toString: Str = toDocument.print

object Type:
  def toDocuments(args: Ls[Type], sep: Document, extraTypename: Bool = false): Document =
    args.iterator.zipWithIndex.map {
      case (x, 0) =>
        x.toDocument(extraTypename)
      case (x, _) =>
        sep <#> x.toDocument(extraTypename)
    }.fold(raw(""))(_ <#> _)

  def toDocuments(args: Ls[(Str, Type)], sep: Document): Document =
    args.iterator.zipWithIndex.map {
      case (x, 0) =>
        x._2.toDocument() <:> raw(x._1)
      case (x, _) =>
        sep <#> x._2.toDocument() <:> raw(x._1)
    }.fold(raw(""))(_ <#> _)

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
      case Ptr(inner) => aux(inner) <#> "*" 
      case Ref(inner) => aux(inner) <#> "&"
      case Array(inner, size) => aux(inner) <#> "[" <#> size.fold(raw(""))(x => x.toString) <#> "]"
      case FuncPtr(ret, args) => aux(ret) <#> "(" <#> Type.toDocuments(args, sep = ", ") <#> ")"
      case Struct(name) => s"struct $name"
      case Enum(name) => s"enum $name"
      case Template(name, args) => s"$name" <#> "<" <#> Type.toDocuments(args, sep = ", ") <#> ">"
      case Var(name) => name
      case Qualifier(inner, qual) => aux(inner) <:> qual
    aux(this)

  override def toString: Str = toDocument().print

object Stmt:
  def toDocuments(decl: Ls[Decl], stmts: Ls[Stmt]): Document =
    stack_list(decl.map(_.toDocument) ++ stmts.map(_.toDocument))

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
          case x :: Nil => "auto" <:> x <:> "=" <:> rhs.toDocument <#> ";"
          case _ => "auto" <:> lhs.mkString("[", ",", "]") <:> "=" <:> rhs.toDocument <#> ";"
      case Assign(lhs, rhs) => lhs <#> " = " <#> rhs.toDocument <#> ";"
      case Return(expr) => "return " <#> expr.toDocument <#> ";"
      case If(cond, thenStmt, elseStmt) =>
        "if (" <#> cond.toDocument <#> ")" <#> thenStmt.toDocument <:> elseStmt.fold(raw(""))(x => "else" <:> x.toDocument)
      case While(cond, body) =>
        "while (" <#> cond.toDocument <#> ")" <#> body.toDocument
      case For(init, cond, update, body) =>
        "for (" <#> init.toDocument <#> "; " <#> cond.toDocument <#> "; " <#> update.toDocument <#> ")" <#> body.toDocument
      case ExprStmt(expr) => expr.toDocument <#> ";"
      case Break => "break;"
      case Continue => "continue;"
      case Block(decl, stmts) => 
        stack(
          "{",
          Stmt.toDocuments(decl, stmts) |> indent,
          "}")
      case Switch(expr, cases) =>
        "switch (" <#> expr.toDocument <#> ")" <#> "{" <#> stack_list(cases.map {
          case (cond, stmt) => "case " <#> cond.toDocument <#> ":" <#> stmt.toDocument
        }) <#> "}"
      case Raw(stmt) => stmt
    aux(this)

object Expr:
  def toDocuments(args: Ls[Expr], sep: Document): Document =
    args.zipWithIndex.map {
      case (x, i) =>
        if i == 0 then x.toDocument
        else sep <#> x.toDocument
    }.fold(raw(""))(_ <#> _)
  
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
      case Call(func, args) => aux(func) <#> "(" <#> Expr.toDocuments(args, sep = ", ") <#> ")"
      case Member(expr, member) => aux(expr) <#> "->" <#> member
      case Index(expr, index) => aux(expr) <#> "[" <#> aux(index) <#> "]"
      case Unary(op, expr) => "(" <#> op <#> aux(expr) <#> ")"
      case Binary(op, lhs, rhs) => "(" <#> aux(lhs) <#> op <#> aux(rhs) <#> ")"
      case Initializer(exprs) => "{" <#> Expr.toDocuments(exprs, sep = ", ") <#> "}"
      case Constructor(name, init) => name <#> init.toDocument
    aux(this)

case class CompilationUnit(includes: Ls[Str], decls: Ls[Decl], defs: Ls[Def]):
  def toDocument: Document =
    stack_list(includes.map(x => raw(x)) ++ decls.map(_.toDocument) ++ defs.map(_.toDocument))
  def toDocumentWithoutHidden: Document =
    val hiddenNames = Set(
      "HiddenTheseEntities", "True", "False", "Callable", "List", "Cons", "Nil", "Option", "Some", "None", "Pair", "Tuple2", "Tuple3", "Nat", "S", "O"
    )
    stack_list(defs.filterNot { 
      case Def.StructDef(name, _, _, _) => hiddenNames.contains(name.stripPrefix("_mls_"))
      case _ => false
    }.map(_.toDocument))

enum Decl:
  case StructDecl(name: Str)
  case EnumDecl(name: Str)
  case FuncDecl(ret: Type, name: Str, args: Ls[Type])
  case VarDecl(name: Str, typ: Type)

  def toDocument: Document =
    def aux(x: Decl): Document = x match
      case StructDecl(name) => s"struct $name;"
      case EnumDecl(name) => s"enum $name;"
      case FuncDecl(ret, name, args) => ret.toDocument() <#> s" $name(" <#> Type.toDocuments(args, sep = ", ")  <#> ");"
      case VarDecl(name, typ) => typ.toDocument() <#> s" $name;"
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
        stack(
          s"struct $name" <#> (if inherit.nonEmpty then ": public" <:> inherit.get.mkString(", ") else "" ) <:> "{",
            stack_list(fields.map {
                case (name, typ) => typ.toDocument() <#> " " <#> name <#> ";"
            }) |> indent,
            stack_list(defs.map(_.toDocument)) |> indent,
          "};"
        )
      case EnumDef(name, fields) =>
        s"enum $name" <:> "{" <#> stack_list(fields.map {
          case (name, value) => value.fold(s"$name")(x => s"$name = $x")
        }) <#> "};"
      case FuncDef(specret, name, args, body, or, virt) =>
        (if virt then "virtual " else "") 
        <#> specret.toDocument() <#> s" $name(" <#> Type.toDocuments(args, sep = ", ") <#> ")" <#> (if or then " override" else "") <#> body.toDocument
      case VarDef(typ, name, init) =>
        typ.toDocument() <#> s" $name" <#> init.fold(raw(""))(x => " = " <#> x.toDocument) <#> raw(";")
      case RawDef(x) => x
    aux(this)