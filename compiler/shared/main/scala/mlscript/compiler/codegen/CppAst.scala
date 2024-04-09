package mlscript.compiler.codegen.cpp

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import mlscript.compiler.utils._

enum Specifier:
  case Extern
  case Static
  case Inline

  def toDocument = this match
    case Extern => "extern" |> raw 
    case Static => "static" |> raw
    case Inline => "inline" |> raw

  override def toString(): Str = toDocument.print

object Type:
  def toDocuments(args: Ls[Type], sep: Document, extraTypename: Bool = false): Document =
    args.zipWithIndex.map {
      case (x, i) =>
        if i == 0 then
          x.toDocument(extraTypename)
        else
          sep <#> x.toDocument(extraTypename)
    }.fold(raw(""))(_ <#> _)

  def toDocuments(args: Ls[(Str, Type)], sep: Document): Document =
    args.zipWithIndex.map {
      case (x, i) =>
        if i == 0 then
          x._2.toDocument() <:> raw(x._1)
        else
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
      case Prim(name) => name |> raw
      case Ptr(inner) => aux(inner) <#> raw("*") 
      case Ref(inner) => aux(inner) <#> raw("&")
      case Array(inner, size) => aux(inner) <#> raw("[") <#> size.fold(raw(""))(x => x.toString |> raw) <#> raw("]")
      case FuncPtr(ret, args) => aux(ret) <#> raw("(") <#> Type.toDocuments(args, sep = raw(", ")) <#> raw(")")
      case Struct(name) => raw(s"struct $name")
      case Enum(name) => raw(s"enum $name")
      case Template(name, args) => raw(s"$name") <#> raw("<") <#> Type.toDocuments(args, sep = raw(", ")) <#> raw(">")
      case Var(name) => name |> raw
      case Qualifier(inner, qual) => aux(inner) <:> raw(qual)
    aux(this)

  override def toString(): Str = toDocument().print

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
          case x :: Nil => raw("auto") <:> raw(x) <:> raw("=") <:> rhs.toDocument <#> raw(";")
          case _ => raw("auto") <:> raw(lhs.mkString("[", ",", "]")) <:> raw("=") <:> rhs.toDocument <#> raw(";")
      case Assign(lhs, rhs) => raw(lhs) <#> raw(" = ") <#> rhs.toDocument <#> raw(";")
      case Return(expr) => raw("return ") <#> expr.toDocument <#> raw(";")
      case If(cond, thenStmt, elseStmt) =>
        raw("if (") <#> cond.toDocument <#> raw(")") <#> thenStmt.toDocument <:> elseStmt.fold(raw(""))(x => raw("else") <:> x.toDocument)
      case While(cond, body) =>
        raw("while (") <#> cond.toDocument <#> raw(")") <#> body.toDocument
      case For(init, cond, update, body) =>
        raw("for (") <#> init.toDocument <#> raw("; ") <#> cond.toDocument <#> raw("; ") <#> update.toDocument <#> raw(")") <#> body.toDocument
      case ExprStmt(expr) => expr.toDocument <#> raw(";")
      case Break => raw("break;")
      case Continue => raw("continue;")
      case Block(decl, stmts) => 
        stack(raw("{"),
          Stmt.toDocuments(decl, stmts) |> indent,
        raw("}"))
      case Switch(expr, cases) =>
        raw("switch (") <#> expr.toDocument <#> raw(")") <#> raw("{") <#> stack_list(cases.map {
          case (cond, stmt) => raw("case ") <#> cond.toDocument <#> raw(":") <#> stmt.toDocument
        }) <#> raw("}")
      case Raw(stmt) => stmt |> raw
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
  case FloatLit(value: Float)
  case StrLit(value: Str)
  case Call(func: Expr, args: Ls[Expr])
  case Member(expr: Expr, member: Str)
  case Index(expr: Expr, index: Expr)
  case Unary(op: Str, expr: Expr)
  case Binary(op: Str, lhs: Expr, rhs: Expr)
  case Initializer(exprs: Ls[Expr])
  case Constructor(name: Str, init: Expr)

  def toDocument: Document =
    def aux(x: Expr): Document = x match
      case Var(name) => name |> raw
      case IntLit(value) => value.toString |> raw
      case FloatLit(value) => value.toString |> raw
      case StrLit(value) => value |> raw
      case Call(func, args) => aux(func) <#> raw("(") <#> Expr.toDocuments(args, sep = raw(", ")) <#> raw(")")
      case Member(expr, member) => aux(expr) <#> raw("->") <#> raw(member)
      case Index(expr, index) => aux(expr) <#> raw("[") <#> aux(index) <#> raw("]")
      case Unary(op, expr) => raw("(") <#> raw(op) <#> aux(expr) <#> raw(")")
      case Binary(op, lhs, rhs) => raw("(") <#> aux(lhs) <#> raw(op) <#> aux(rhs) <#> raw(")")
      case Initializer(exprs) => raw("{") <#> Expr.toDocuments(exprs, sep = raw(", ")) <#> raw("}")
      case Constructor(name, init) => raw(name) <#> init.toDocument
    aux(this)

case class CompilationUnit(includes: Ls[Str], decls: Ls[Decl], defs: Ls[Def]):
  def toDocument: Document =
    stack_list(includes.map(x => raw(x)) ++ decls.map(_.toDocument) ++ defs.map(_.toDocument))

enum Decl:
  case StructDecl(name: Str)
  case EnumDecl(name: Str)
  case FuncDecl(ret: Type, name: Str, args: Ls[Type])
  case VarDecl(name: Str, typ: Type)

  def toDocument: Document =
    def aux(x: Decl): Document = x match
      case StructDecl(name) => raw(s"struct $name;")
      case EnumDecl(name) => raw(s"enum $name;")
      case FuncDecl(ret, name, args) => ret.toDocument() <#> raw(s" $name(") <#> Type.toDocuments(args, sep = raw(", "))  <#> raw(");")
      case VarDecl(name, typ) => typ.toDocument() <#> raw(s" $name;")
    aux(this)

enum Def:
  case StructDef(name: Str, fields: Ls[(Str, Type)], inherit: Opt[Ls[Str]], methods: Ls[Def] = Ls.empty)
  case EnumDef(name: Str, fields: Ls[(Str, Opt[Int])])
  case FuncDef(specret: Type, name: Str, args: Ls[(Str, Type)], body: Stmt.Block)
  case VarDef(typ: Type, name: Str, init: Opt[Expr])
  case RawDef(raw: Str)

  def toDocument: Document =
    def aux(x: Def): Document = x match
      case StructDef(name, fields, inherit, defs) =>
        stack(
          raw(s"struct $name") <#> (if inherit.nonEmpty then raw(": public") <:> raw(inherit.get.mkString(", ")) else raw("") ) <#> raw("{"),
            stack_list(fields.map {
                case (name, typ) => typ.toDocument() <#> raw(" ") <#> raw(name) <#> raw(";")
            }) |> indent,
            stack_list(defs.map(_.toDocument)) |> indent,
          raw("};")
        )
      case EnumDef(name, fields) =>
        raw(s"enum $name") <#> raw("{") <#> stack_list(fields.map {
          case (name, value) => value.fold(raw(s"$name"))(x => raw(s"$name = $x"))
        }) <#> raw("};")
      case FuncDef(specret, name, args, body) =>
        specret.toDocument() <#> raw(s" $name(") <#> Type.toDocuments(args, sep = raw(", ")) <#> raw(")") <#> body.toDocument
      case VarDef(typ, name, init) =>
        typ.toDocument() <#> raw(s" $name") <#> init.fold(raw(""))(x => raw(" = ") <#> x.toDocument) <#> raw(";")
      case RawDef(x) => x |> raw
    aux(this)