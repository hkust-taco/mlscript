package mlscript.compiler.codegen.cpp

import mlscript.compiler.ir.{Expr => IExpr, _}
import mlscript.compiler.utils._
import mlscript.utils._
import mlscript.utils.shorthands._


class CppCodeGen:
  private def mapName(name: Name): Str = "_mls_" + name.str.replace('$', '_')
  private def mapName(name: Str): Str = "_mls_" + name.replace('$', '_')
  private val freshName = Fresh(div = '_');
  private val mlsValType = Type.Prim("_mlsValue")
  private val mlsUnitValue = Expr.Var("_mlsValue::unit")
  private val mlsRetValue  = "_mls_retval"
  private val mlsRetValueDecl = Decl.VarDecl(mlsRetValue, mlsValType)
  private val mlsMainName = "_mlsMain"
  private val mlsPrelude = "#include \"mlsprelude.h\""
  private val mlsPreludeImpl = "#include \"mlsprelude.cpp\""
  private val mlsInternalClass = Set("True", "False", "Boolean")
  private val mlsObject = "_mlsObject"
  private val mlsEntryPoint = s"int main() { auto res = _mlsMain(); res.print(); }";
  private def mlsIntLit(x: BigInt) = Expr.Call(Expr.Var("_mlsValue::fromIntLit"), Ls(Expr.IntLit(x)))
  private def mlsStrLit(x: Str) = Expr.Call(Expr.Var("_mlsValue::fromStrLit"), Ls(Expr.StrLit(x)))
  private def mlsNewValue(cls: Str, args: Ls[Expr]) = Expr.Call(Expr.Var(s"_mlsValue::create<$cls>"), args)
  private def mlsIsValueOf(cls: Str, scrut: Expr) = Expr.Call(Expr.Var(s"_mlsValue::isValueOf<$cls>"), Ls(scrut))
  private def mlsDebugPrint(x: Expr) = Expr.Call(Expr.Var("_mlsValue::print"), Ls(x))
  private def mlsTupleValue(init: Expr) = Expr.Constructor("_mlsValue::tuple", init)
  private def mlsAs(name: Str, cls: Str) = Expr.Var(s"_mlsValue::as<$cls>($name)")
  private def mlsObjectNameMethod(name: Str) = s"constexpr static inline const char *typeName = \"${name}\";"
  private def mlsTypeTag(id: Int) = s"constexpr static inline uint32_t typeTag = $id;"
  private def mlsCommonCreateMethod(cls: Str, fields: Ls[Str], id: Int) =
    val parameters = fields.map{x => s"_mlsValue $x"}.mkString(", ")
    val fieldsAssignment = fields.map{x => s"_mlsVal->$x = $x; "}.mkString
    s"template <std::size_t align> static _mlsValue create($parameters) { auto _mlsVal = new (std::align_val_t(align)) $cls; _mlsVal->refCount = 1; _mlsVal->tag = $id; $fieldsAssignment return _mlsValue(_mlsVal); }"
  private def mlsCommonPrintMethod(cls: Str, fields: Ls[Str]) =
    if fields.isEmpty then s"virtual void print() const override { std::printf(\"%s\", typeName); }"
    else
      val fieldsPrint = fields.map{x => s"this->$x.print(); "}.mkString("std::printf(\", \"); ")
      s"virtual void print() const override { std::printf(\"%s\", typeName); std::printf(\"(\"); $fieldsPrint std::printf(\")\"); }"
  private def mlsCommonDestructorMethod(cls: Str, fields: Ls[Str]) = 
    val fieldsDeletion = fields.map{x => s"_mlsValue::destroy(this->$x); "}.mkString
    s"virtual void destroy() override { $fieldsDeletion operator delete (this); }"
  private def mlsThrowNonExhaustiveMatch = Stmt.Raw("throw std::runtime_error(\"Non-exhaustive match\");");

  private def codegenClassInfo(cls: ClassInfo): (Opt[Def], Decl) =
    val fields = cls.fields.map{x => (x |> mapName, mlsValType)}
    val parents = if cls.parents.nonEmpty then cls.parents.toList.map{x => x |> mapName} else mlsObject :: Nil
    val decl = Decl.StructDecl(cls.ident |> mapName)
    if mlsInternalClass.contains(cls.ident) then return (None, decl)
    val theDef = Def.StructDef(
      cls.ident |> mapName, fields,
      if parents.nonEmpty then Some(parents) else None,
      Ls(Def.RawDef(mlsObjectNameMethod(cls.ident)),
         Def.RawDef(mlsTypeTag(cls.id)),
         Def.RawDef(mlsCommonPrintMethod(cls.ident, cls.fields.map(mapName))),
         Def.RawDef(mlsCommonDestructorMethod(cls.ident |> mapName, cls.fields.map(mapName))),
         Def.RawDef(mlsCommonCreateMethod(cls.ident |> mapName, cls.fields.map(mapName), cls.id))))
    (S(theDef), decl)

  private def toExpr(texpr: TrivialExpr, reifyUnit: Bool = false): Opt[Expr] = texpr match
    case IExpr.Ref(name) => S(Expr.Var(name |> mapName))
    case IExpr.Literal(mlscript.IntLit(x)) => S(mlsIntLit(x))
    case IExpr.Literal(mlscript.StrLit(x)) => S(mlsStrLit(x))
    case IExpr.Literal(mlscript.UnitLit(_)) => if reifyUnit then S(mlsUnitValue) else None
  
  private def toExpr(texpr: TrivialExpr): Expr = texpr match
    case IExpr.Ref(name) => Expr.Var(name |> mapName)
    case IExpr.Literal(mlscript.IntLit(x)) => mlsIntLit(x)
    case IExpr.Literal(mlscript.StrLit(x)) => mlsStrLit(x)
    case IExpr.Literal(mlscript.UnitLit(_)) => mlsUnitValue
  

  private def wrapMultiValues(exprs: Ls[TrivialExpr]): Expr = exprs match
    case x :: Nil => toExpr(x, reifyUnit = true).get
    case _ => 
      val init = Expr.Initializer(exprs.map{x => toExpr(x)})
      mlsTupleValue(init)
  
  private def codegenCaseWithIfs(scrut: Name, cases: Ls[(ClassInfo, Node)], storeInto: Str)(using decls: Ls[Decl], stmts: Ls[Stmt]): (Ls[Decl], Ls[Stmt]) =
    val scrutName = mapName(scrut)
    val init: Opt[Stmt] = S(mlsThrowNonExhaustiveMatch)
    val stmt = cases.foldRight(init) {
      case ((cls, arm), nextarm) =>
        val (decls2, stmts2) = codegen(arm, storeInto)(using Ls.empty, Ls.empty[Stmt])
        val stmt = Stmt.If(mlsIsValueOf(cls.ident |> mapName, Expr.Var(scrutName)), Stmt.Block(decls2, stmts2), nextarm)
        S(stmt)
    }
    (decls, stmt.fold(stmts)(x => stmts :+ x))

  private def codegenJumpWithCall(defn: DefnRef, args: Ls[TrivialExpr], storeInto: Opt[Str])(using decls: Ls[Decl], stmts: Ls[Stmt]): (Ls[Decl], Ls[Stmt]) =
    val call = Expr.Call(Expr.Var(defn.getName |> mapName), args.map(toExpr))
    val stmts2 = stmts ++ Ls(storeInto.fold(Stmt.Return(call))(x => Stmt.Assign(x, call)))
    (decls, stmts2)

  private def codegenOps(op: Str, args: Ls[TrivialExpr]) = op match
    case "+" => Expr.Binary("+", toExpr(args(0)), toExpr(args(1)))
    case "-" => Expr.Binary("-", toExpr(args(0)), toExpr(args(1)))
    case "*" => Expr.Binary("*", toExpr(args(0)), toExpr(args(1)))
    case "/" => Expr.Binary("/", toExpr(args(0)), toExpr(args(1)))
    case "%" => Expr.Binary("%", toExpr(args(0)), toExpr(args(1)))
    case "==" => Expr.Binary("==", toExpr(args(0)), toExpr(args(1)))
    case "!=" => Expr.Binary("!=", toExpr(args(0)), toExpr(args(1)))
    case "<" => Expr.Binary("<", toExpr(args(0)), toExpr(args(1)))
    case "<=" => Expr.Binary("<=", toExpr(args(0)), toExpr(args(1)))
    case ">" => Expr.Binary(">", toExpr(args(0)), toExpr(args(1)))
    case ">=" => Expr.Binary(">=", toExpr(args(0)), toExpr(args(1)))
    case "&&" => Expr.Binary("&&", toExpr(args(0)), toExpr(args(1)))
    case "||" => Expr.Binary("||", toExpr(args(0)), toExpr(args(1)))
    case "!" => Expr.Unary("!", toExpr(args(0)))
    case _ => ???


  private def codegen(expr: IExpr): Expr = expr match
    case x @ (IExpr.Ref(_) | IExpr.Literal(_)) => toExpr(x, reifyUnit = true).get
    case IExpr.CtorApp(name, args) => mlsNewValue(name.ident |> mapName, args.map(toExpr))
    case IExpr.Select(name, cls, field) => Expr.Member(mlsAs(name |> mapName, cls.ident |> mapName), field |> mapName)
    case IExpr.BasicOp(name, args) => codegenOps(name, args)
  
  private def codegen(body: Node, storeInto: Str)(using decls: Ls[Decl], stmts: Ls[Stmt]): (Ls[Decl], Ls[Stmt]) = body match
    case Node.Result(res) => 
      val expr = wrapMultiValues(res)
      val stmts2 = stmts ++ Ls(Stmt.Assign(storeInto, expr))
      (decls, stmts2)
    case Node.Jump(defn, args) =>
      codegenJumpWithCall(defn, args, S(storeInto))
    case Node.LetExpr(name, expr, body) =>
      val stmts2 = stmts ++ Ls(Stmt.AutoBind(Ls(name |> mapName), codegen(expr)))
      codegen(body, storeInto)(using decls, stmts2)
    case Node.LetCall(names, defn, args, body) =>
      val call = Expr.Call(Expr.Var(defn.getName |> mapName), args.map(toExpr))
      val stmts2 = stmts ++ Ls(Stmt.AutoBind(names.map(mapName), call))
      codegen(body, storeInto)(using decls, stmts2)
    case Node.Case(scrut, cases) =>
      codegenCaseWithIfs(scrut, cases, storeInto)
    
  private def codegenDefn(defn: Defn): (Def, Decl) = defn match
    case Defn(id, name, params, resultNum, specialized, body) =>
      val decls = Ls(mlsRetValueDecl)
      val stmts = Ls.empty[Stmt]
      val (decls2, stmts2) = codegen(body, mlsRetValue)(using decls, stmts)
      val stmtsWithReturn = stmts2 :+ Stmt.Return(Expr.Var(mlsRetValue))
      val theDef = Def.FuncDef(mlsValType, name |> mapName, params.map(x => (x |> mapName, mlsValType)), Stmt.Block(decls2, stmtsWithReturn))
      val decl = Decl.FuncDecl(mlsValType, name |> mapName, params.map(x => mlsValType))
      (theDef, decl)

  private def codegenTopNode(node: Node): (Def, Decl) =
    val decls = Ls(mlsRetValueDecl)
    val stmts = Ls.empty[Stmt]
    val (decls2, stmts2) = codegen(node, mlsRetValue)(using decls, stmts)
    val stmtsWithReturn = stmts2 :+ Stmt.Return(Expr.Var(mlsRetValue))
    val theDef = Def.FuncDef(mlsValType, mlsMainName, Ls(), Stmt.Block(decls2, stmtsWithReturn))
    val decl = Decl.FuncDecl(mlsValType, mlsMainName, Ls())
    (theDef, decl)

  private def sortClasses(prog: Program): Ls[ClassInfo] =
    var depgraph = prog.classes.map(x => (x.ident, x.parents)).toMap
    var degree = depgraph.mapValues(_.size).toMap
    def removeNode(node: Str) =
      degree -= node
      depgraph -= node
      depgraph = depgraph.mapValues(_.filter(_ != node)).toMap
      degree = depgraph.mapValues(_.size).toMap
    var sorted = Ls.empty[ClassInfo]
    var work = degree.filter(_._2 == 0).keys.toSet
    while work.nonEmpty do
      val node = work.head
      work -= node
      sorted = sorted :+ prog.classes.find(_.ident == node).get
      removeNode(node)
      val next = degree.filter(_._2 == 0).keys
      work = work ++ next
    if depgraph.nonEmpty then
      val cycle = depgraph.keys.mkString(", ")
      throw new Exception(s"Cycle detected in class hierarchy: $cycle")
    sorted
  
  def codegen(prog: Program): CompilationUnit =
    val sortedClasses = sortClasses(prog)
    val (defs, decls) = sortedClasses.map(codegenClassInfo).unzip
    val (defs2, decls2) = prog.defs.map(codegenDefn).unzip
    val (defMain, declMain) = codegenTopNode(prog.main)
    CompilationUnit(Ls(mlsPrelude), decls ++ decls2 :+ declMain, defs.flatten ++ defs2 :+ defMain :+ Def.RawDef(mlsEntryPoint))
