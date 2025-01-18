package hkmc2.codegen.cpp

import mlscript.utils._
import mlscript.utils.shorthands._
import scala.collection.mutable.ListBuffer

import hkmc2.codegen.llir.{Expr => IExpr, _}
import hkmc2.codegen.cpp._

object CppCodeGen:
  def mapName(name: Name): Str = "_mls_" + name.str.replace('$', '_').replace('\'', '_')
  def mapName(name: Str): Str = "_mls_" + name.replace('$', '_').replace('\'', '_')
  val freshName = Fresh(div = '_');
  val mlsValType = Type.Prim("_mlsValue")
  val mlsUnitValue = Expr.Call(Expr.Var("_mlsValue::create<_mls_Unit>"), Ls());
  val mlsRetValue  = "_mls_retval"
  val mlsRetValueDecl = Decl.VarDecl(mlsRetValue, mlsValType)
  val mlsMainName = "_mlsMain"
  val mlsPrelude = "#include \"mlsprelude.h\""
  val mlsPreludeImpl = "#include \"mlsprelude.cpp\""
  val mlsInternalClass = Set("True", "False", "Boolean", "Callable")
  val mlsObject = "_mlsObject"
  val mlsBuiltin = "builtin"
  val mlsEntryPoint = s"int main() { return _mlsLargeStack(_mlsMainWrapper); }";
  def mlsIntLit(x: BigInt) = Expr.Call(Expr.Var("_mlsValue::fromIntLit"), Ls(Expr.IntLit(x)))
  def mlsStrLit(x: Str) = Expr.Call(Expr.Var("_mlsValue::fromStrLit"), Ls(Expr.StrLit(x)))
  def mlsCharLit(x: Char) = Expr.Call(Expr.Var("_mlsValue::fromIntLit"), Ls(Expr.CharLit(x)))
  def mlsNewValue(cls: Str, args: Ls[Expr]) = Expr.Call(Expr.Var(s"_mlsValue::create<$cls>"), args)
  def mlsIsValueOf(cls: Str, scrut: Expr) = Expr.Call(Expr.Var(s"_mlsValue::isValueOf<$cls>"), Ls(scrut))
  def mlsIsBoolLit(scrut: Expr, lit: hkmc2.syntax.Tree.BoolLit) = Expr.Call(Expr.Var("_mlsValue::isIntLit"), Ls(scrut, Expr.IntLit(if lit.value then 1 else 0)))
  def mlsIsIntLit(scrut: Expr, lit: hkmc2.syntax.Tree.IntLit) = Expr.Call(Expr.Var("_mlsValue::isIntLit"), Ls(scrut, Expr.IntLit(lit.value)))
  def mlsDebugPrint(x: Expr) = Expr.Call(Expr.Var("_mlsValue::print"), Ls(x))
  def mlsTupleValue(init: Expr) = Expr.Constructor("_mlsValue::tuple", init)
  def mlsAs(name: Str, cls: Str) = Expr.Var(s"_mlsValue::as<$cls>($name)")
  def mlsAsUnchecked(name: Str, cls: Str) = Expr.Var(s"_mlsValue::cast<$cls>($name)")
  def mlsObjectNameMethod(name: Str) = s"constexpr static inline const char *typeName = \"${name}\";"
  def mlsTypeTag() = s"constexpr static inline uint32_t typeTag = nextTypeTag();"
  def mlsTypeTag(n: Int) = s"constexpr static inline uint32_t typeTag = $n;"
  def mlsCommonCreateMethod(cls: Str, fields: Ls[Str], id: Int) =
    val parameters = fields.map{x => s"_mlsValue $x"}.mkString(", ")
    val fieldsAssignment = fields.map{x => s"_mlsVal->$x = $x; "}.mkString
    s"static _mlsValue create($parameters) { auto _mlsVal = new (std::align_val_t(_mlsAlignment)) $cls; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; $fieldsAssignment return _mlsValue(_mlsVal); }"
  def mlsCommonPrintMethod(fields: Ls[Str]) =
    if fields.isEmpty then s"virtual void print() const override { std::printf(\"%s\", typeName); }"
    else
      val fieldsPrint = fields.map{x => s"this->$x.print(); "}.mkString("std::printf(\", \"); ")
      s"virtual void print() const override { std::printf(\"%s\", typeName); std::printf(\"(\"); $fieldsPrint std::printf(\")\"); }"
  def mlsCommonDestructorMethod(cls: Str, fields: Ls[Str]) = 
    val fieldsDeletion = fields.map{x => s"_mlsValue::destroy(this->$x); "}.mkString
    s"virtual void destroy() override { $fieldsDeletion operator delete (this, std::align_val_t(_mlsAlignment)); }"
  def mlsThrowNonExhaustiveMatch = Stmt.Raw("_mlsNonExhaustiveMatch();");
  def mlsCall(fn: Str, args: Ls[Expr]) = Expr.Call(Expr.Var("_mlsCall"), Expr.Var(fn) :: args)
  def mlsMethodCall(cls: ClassRef, method: Str, args: Ls[Expr]) =
    Expr.Call(Expr.Member(Expr.Call(Expr.Var(s"_mlsMethodCall<${cls.name |> mapName}>"), Ls(args.head)), method), args.tail)
  def mlsFnWrapperName(fn: Str) = s"_mlsFn_$fn"
  def mlsFnCreateMethod(fn: Str) = s"static _mlsValue create() { static _mlsFn_$fn mlsFn alignas(_mlsAlignment); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }"
  def mlsNeverValue(n: Int) = if (n <= 1) then Expr.Call(Expr.Var(s"_mlsValue::never"), Ls()) else Expr.Call(Expr.Var(s"_mlsValue::never<$n>"), Ls())

  case class Ctx(
    defnCtx: Set[Str],
  )

  def codegenClassInfo(using ctx: Ctx)(cls: ClassInfo): (Opt[Def], Decl) =
    val fields = cls.fields.map{x => (x |> mapName, mlsValType)}
    val parents = if cls.parents.nonEmpty then cls.parents.toList.map(mapName) else mlsObject :: Nil
    val decl = Decl.StructDecl(cls.name |> mapName)
    if mlsInternalClass.contains(cls.name) then return (None, decl)
    val theDef = Def.StructDef(
      cls.name |> mapName, fields,
      if parents.nonEmpty then Some(parents) else None,
      Ls(Def.RawDef(mlsObjectNameMethod(cls.name)),
         Def.RawDef(mlsTypeTag()),
         Def.RawDef(mlsCommonPrintMethod(cls.fields.map(mapName))),
         Def.RawDef(mlsCommonDestructorMethod(cls.name |> mapName, cls.fields.map(mapName))),
         Def.RawDef(mlsCommonCreateMethod(cls.name |> mapName, cls.fields.map(mapName), cls.id)))
      ++ cls.methods.map{case (name, defn) => {
        val (theDef, decl) = codegenDefn(using Ctx(ctx.defnCtx + cls.name))(defn)
        theDef match
          case x @ Def.FuncDef(_, name, _, _, _, _) => x.copy(virt = true)
          case _ => theDef
      }}
    )
    (S(theDef), decl)
  
  def toExpr(texpr: TrivialExpr, reifyUnit: Bool = false)(using ctx: Ctx): Opt[Expr] = texpr match
    case IExpr.Ref(name) => S(Expr.Var(name |> mapName))
    case IExpr.Literal(hkmc2.syntax.Tree.BoolLit(x)) => S(mlsIntLit(if x then 1 else 0))
    case IExpr.Literal(hkmc2.syntax.Tree.IntLit(x)) => S(mlsIntLit(x))
    case IExpr.Literal(hkmc2.syntax.Tree.DecLit(x)) => S(mlsIntLit(x.toBigInt))
    case IExpr.Literal(hkmc2.syntax.Tree.StrLit(x)) => S(mlsStrLit(x))
    case IExpr.Literal(hkmc2.syntax.Tree.UnitLit(_)) => if reifyUnit then S(mlsUnitValue) else None
  
  def toExpr(texpr: TrivialExpr)(using ctx: Ctx): Expr = texpr match
    case IExpr.Ref(name) => Expr.Var(name |> mapName)
    case IExpr.Literal(hkmc2.syntax.Tree.BoolLit(x)) => mlsIntLit(if x then 1 else 0)
    case IExpr.Literal(hkmc2.syntax.Tree.IntLit(x)) => mlsIntLit(x)
    case IExpr.Literal(hkmc2.syntax.Tree.DecLit(x)) => mlsIntLit(x.toBigInt)
    case IExpr.Literal(hkmc2.syntax.Tree.StrLit(x)) => mlsStrLit(x)
    case IExpr.Literal(hkmc2.syntax.Tree.UnitLit(_)) => mlsUnitValue
  

  def wrapMultiValues(exprs: Ls[TrivialExpr])(using ctx: Ctx): Expr = exprs match
    case x :: Nil => toExpr(x, reifyUnit = true).get
    case _ => 
      val init = Expr.Initializer(exprs.map{x => toExpr(x)})
      mlsTupleValue(init)
  
  def codegenCaseWithIfs(scrut: TrivialExpr, cases: Ls[(Pat, Node)], default: Opt[Node], storeInto: Str)(using decls: Ls[Decl], stmts: Ls[Stmt])(using ctx: Ctx): (Ls[Decl], Ls[Stmt]) =
    val scrut2 = toExpr(scrut)
    val init: Stmt = 
      default.fold(mlsThrowNonExhaustiveMatch)(x => {
        val (decls2, stmts2) = codegen(x, storeInto)(using Ls.empty, Ls.empty[Stmt])
        Stmt.Block(decls2, stmts2)
      })
    val stmt = cases.foldRight(S(init)) {
      case ((Pat.Class(cls), arm), nextarm) =>
        val (decls2, stmts2) = codegen(arm, storeInto)(using Ls.empty, Ls.empty[Stmt])
        val stmt = Stmt.If(mlsIsValueOf(cls.name |> mapName, scrut2), Stmt.Block(decls2, stmts2), nextarm)
        S(stmt)
      case ((Pat.Lit(i @ hkmc2.syntax.Tree.IntLit(_)), arm), nextarm) =>
        val (decls2, stmts2) = codegen(arm, storeInto)(using Ls.empty, Ls.empty[Stmt])
        val stmt = Stmt.If(mlsIsIntLit(scrut2, i), Stmt.Block(decls2, stmts2), nextarm)
        S(stmt)
      case ((Pat.Lit(i @ hkmc2.syntax.Tree.BoolLit(_)), arm), nextarm) =>
        val (decls2, stmts2) = codegen(arm, storeInto)(using Ls.empty, Ls.empty[Stmt])
        val stmt = Stmt.If(mlsIsBoolLit(scrut2, i), Stmt.Block(decls2, stmts2), nextarm)
        S(stmt)
      case _ => ???
    }
    (decls, stmt.fold(stmts)(x => stmts :+ x))

  def codegenJumpWithCall(func: FuncRef, args: Ls[TrivialExpr], storeInto: Opt[Str])(using decls: Ls[Decl], stmts: Ls[Stmt])(using ctx: Ctx): (Ls[Decl], Ls[Stmt]) =
    val call = Expr.Call(Expr.Var(func.name |> mapName), args.map(toExpr))
    val stmts2 = stmts ++ Ls(storeInto.fold(Stmt.Return(call))(x => Stmt.Assign(x, call)))
    (decls, stmts2)

  def codegenOps(op: Str, args: Ls[TrivialExpr])(using ctx: Ctx) = op match
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
    case _ => TODO("codegenOps")


  def codegen(expr: IExpr)(using ctx: Ctx): Expr = expr match
    case x @ (IExpr.Ref(_) | IExpr.Literal(_)) => toExpr(x, reifyUnit = true).get
    case IExpr.CtorApp(cls, args) => mlsNewValue(cls.name |> mapName, args.map(toExpr))
    case IExpr.Select(name, cls, field) => Expr.Member(mlsAsUnchecked(name |> mapName, cls.name |> mapName), field |> mapName)
    case IExpr.BasicOp(name, args) => codegenOps(name, args)
    case IExpr.AssignField(assignee, cls, field, value) => TODO("codegen assign field")

  def codegenBuiltin(names: Ls[Name], builtin: Str, args: Ls[TrivialExpr])(using ctx: Ctx): Ls[Stmt] = builtin match
    case "error" => Ls(Stmt.Raw("throw std::runtime_error(\"Error\");"), Stmt.AutoBind(names.map(mapName), mlsNeverValue(names.size)))
    case _ => Ls(Stmt.AutoBind(names.map(mapName), Expr.Call(Expr.Var("_mls_builtin_" + builtin), args.map(toExpr))))

  def codegen(body: Node, storeInto: Str)(using decls: Ls[Decl], stmts: Ls[Stmt])(using ctx: Ctx): (Ls[Decl], Ls[Stmt]) = body match
    case Node.Result(res) => 
      val expr = wrapMultiValues(res)
      val stmts2 = stmts ++ Ls(Stmt.Assign(storeInto, expr))
      (decls, stmts2)
    case Node.Jump(defn, args) =>
      codegenJumpWithCall(defn, args, S(storeInto))
    case Node.Panic(msg) => (decls, stmts :+ Stmt.Raw(s"throw std::runtime_error(\"$msg\");"))
    case Node.LetExpr(name, expr, body) =>
      val stmts2 = stmts ++ Ls(Stmt.AutoBind(Ls(name |> mapName), codegen(expr)))
      codegen(body, storeInto)(using decls, stmts2)
    case Node.LetMethodCall(names, cls, method, IExpr.Ref(Name("builtin")) :: args, body) =>
      val stmts2 = stmts ++ codegenBuiltin(names, args.head.toString.replace("\"", ""), args.tail)
      codegen(body, storeInto)(using decls, stmts2)
    case Node.LetMethodCall(names, cls, method, args, body) =>
      val call = mlsMethodCall(cls, method.str |> mapName, args.map(toExpr))
      val stmts2 = stmts ++ Ls(Stmt.AutoBind(names.map(mapName), call))
      codegen(body, storeInto)(using decls, stmts2)
    case Node.LetCall(names, defn, args, body) =>
      val call = Expr.Call(Expr.Var(defn.name |> mapName), args.map(toExpr))
      val stmts2 = stmts ++ Ls(Stmt.AutoBind(names.map(mapName), call))
      codegen(body, storeInto)(using decls, stmts2)
    case Node.Case(scrut, cases, default) =>
      codegenCaseWithIfs(scrut, cases, default, storeInto)
    
  def codegenDefn(using ctx: Ctx)(defn: Func): (Def, Decl) = defn match
    case Func(id, name, params, resultNum, body) =>
      val decls = Ls(mlsRetValueDecl)
      val stmts = Ls.empty[Stmt]
      val (decls2, stmts2) = codegen(body, mlsRetValue)(using decls, stmts)
      val stmtsWithReturn = stmts2 :+ Stmt.Return(Expr.Var(mlsRetValue))
      val theDef = Def.FuncDef(mlsValType, name |> mapName, params.map(x => (x |> mapName, mlsValType)), Stmt.Block(decls2, stmtsWithReturn))
      val decl = Decl.FuncDecl(mlsValType, name |> mapName, params.map(x => mlsValType))
      (theDef, decl)

  def codegenTopNode(node: Node)(using ctx: Ctx): (Def, Decl) =
    val decls = Ls(mlsRetValueDecl)
    val stmts = Ls.empty[Stmt]
    val (decls2, stmts2) = codegen(node, mlsRetValue)(using decls, stmts)
    val stmtsWithReturn = stmts2 :+ Stmt.Return(Expr.Var(mlsRetValue))
    val theDef = Def.FuncDef(mlsValType, mlsMainName, Ls(), Stmt.Block(decls2, stmtsWithReturn))
    val decl = Decl.FuncDecl(mlsValType, mlsMainName, Ls())
    (theDef, decl)

  // Topological sort of classes based on inheritance relationships
  def sortClasses(prog: Program): Ls[ClassInfo] =
    var depgraph = prog.classes.map(x => (x.name, x.parents)).toMap
    var degree = depgraph.view.mapValues(_.size).toMap
    def removeNode(node: Str) =
      degree -= node
      depgraph -= node
      depgraph = depgraph.view.mapValues(_.filter(_ != node)).toMap
      degree = depgraph.view.mapValues(_.size).toMap
    val sorted = ListBuffer.empty[ClassInfo]
    var work = degree.filter(_._2 == 0).keys.toSet
    while work.nonEmpty do
      val node = work.head
      work -= node
      sorted.addOne(prog.classes.find(_.name == node).get)
      removeNode(node)
      val next = degree.filter(_._2 == 0).keys
      work ++= next
    if depgraph.nonEmpty then
      val cycle = depgraph.keys.mkString(", ")
      throw new Exception(s"Cycle detected in class hierarchy: $cycle")
    sorted.toList

  def codegen(prog: Program): CompilationUnit =
    val sortedClasses = sortClasses(prog)
    val defnCtx = prog.defs.map(_.name)
    val (defs, decls) = sortedClasses.map(codegenClassInfo(using Ctx(defnCtx))).unzip
    val (defs2, decls2) = prog.defs.map(codegenDefn(using Ctx(defnCtx))).unzip
    val (defMain, declMain) = codegenTopNode(prog.main)(using Ctx(defnCtx))
    CompilationUnit(Ls(mlsPrelude), decls ++ decls2 :+ declMain, defs.flatten ++ defs2 :+ defMain :+ Def.RawDef(mlsEntryPoint))

