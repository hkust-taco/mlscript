package hkmc2
package codegen
package cpp

import mlscript.utils._
import mlscript.utils.shorthands._
import scala.collection.mutable.ListBuffer

import llir.{Expr => IExpr, _}
import utils.{Scope, TraceLogger}
import semantics._

class CppCodeGen(builtinClassSymbols: Set[Local], tl: TraceLogger):
  import tl.{trace, log, logs}
  def mapName(name: Str): Str = "_mls_" + Scope.replaceInvalidCharacters(name)
  def mapClsLikeName(sym: Local)(using Raise, Scope): Str = 
    if builtinClassSymbols.contains(sym) then sym.nme |> mapName
    else allocIfNew(sym)
  def directName(sym: Local): Str = 
    sym.nme |> mapName
  val mlsValType = Type.Prim("_mlsValue")
  val mlsUnitValue = Expr.Call(Expr.Var("_mlsValue::create<_mls_Unit>"), Ls());
  val mlsRetValue  = "_mls_retval"
  def mlsRetValType(n: Int) =
    if n === 1 then
      mlsValType
    else
      Type.Template("std::tuple", Ls.fill(n)(mlsValType))
  def mlsRetValueDecl(n: Int) =
    if n === 1 then
      Decl.VarDecl(mlsRetValue, mlsValType)
    else
      Decl.VarDecl(mlsRetValue, mlsRetValType(n))
  val mlsMainName = "_mlsMain"
  val mlsPrelude = "#include \"mlsprelude.h\""
  val mlsPreludeImpl = "#include \"mlsprelude.cpp\""
  val builtinClassSymbolNames = Set("Callable", "Lazy")
  def mlsIsInternalClass(sym: Local) = builtinClassSymbolNames.contains(sym.nme)
  val mlsObject = "_mlsObject"
  val mlsBuiltin = "builtin"
  val mlsEntryPoint = s"int main() { return _mlsLargeStack(_mlsMainWrapper); }";
  def mlsCallEntry(s: Str) = s"_mlsValue _mlsMain() { return $s(); }"
  def mlsIntLit(x: BigInt) = Expr.Call(Expr.Var("_mlsValue::fromIntLit"), Ls(Expr.IntLit(x)))
  def mlsStrLit(x: Str) = Expr.Call(Expr.Var("_mlsValue::create<_mls_Str>"), Ls(Expr.StrLit(x)))
  def mlsDecLit(x: BigDecimal) = Expr.Call(Expr.Var("_mlsValue::create<_mls_Float>"), Ls(Expr.DoubleLit(x.toDouble)))
  def mlsCharLit(x: Char) = Expr.Call(Expr.Var("_mlsValue::fromIntLit"), Ls(Expr.CharLit(x)))
  def mlsNewValue(cls: Str, args: Ls[Expr]) = Expr.Call(Expr.Var(s"_mlsValue::create<$cls>"), args)
  def mlsIsValueOf(cls: Str, scrut: Expr) = Expr.Call(Expr.Var(s"_mlsValue::isValueOf<$cls>"), Ls(scrut))
  def mlsIsBoolLit(scrut: Expr, lit: hkmc2.syntax.Tree.BoolLit) = Expr.Call(Expr.Var("_mlsValue::isIntLit"), Ls(scrut, Expr.IntLit(if lit.value then 1 else 0)))
  def mlsIsIntLit(scrut: Expr, lit: hkmc2.syntax.Tree.IntLit) = Expr.Call(Expr.Var("_mlsValue::isIntLit"), Ls(scrut, Expr.IntLit(lit.value)))
  def mlsDebugPrint(x: Expr) = Expr.Call(Expr.Var("_mlsValue::print"), Ls(x))
  def mlsTupleValue(init: Ls[Expr]) = Expr.Call(Expr.Var("std::make_tuple"), init)
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
  def mlsMethodCall(cls: Local, method: Str, args: Ls[Expr])(using Raise, Scope) =
    Expr.Call(Expr.Member(Expr.Call(Expr.Var(s"_mlsMethodCall<${cls |> mapClsLikeName}>"), Ls(args.head)), method), args.tail)
  def mlsThisCall(cls: Local, method: Str, args: Ls[Expr])(using Raise, Scope) =
    Expr.Call(Expr.Member(Expr.Var("this"), method), args)
  def mlsFnWrapperName(fn: Str) = s"_mlsFn_$fn"
  def mlsFnCreateMethod(fn: Str) = s"static _mlsValue create() { static _mlsFn_$fn mlsFn alignas(_mlsAlignment); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }"
  def mlsNeverValue(n: Int) = if (n <= 1) then Expr.Call(Expr.Var(s"_mlsValue::never"), Ls()) else Expr.Call(Expr.Var(s"_mlsValue::never<$n>"), Ls())
  val mlsThis = Expr.Var("_mlsValue(this, _mlsValue::inc_ref_tag{})") // first construct a value, then incRef()

  case class Ctx(
    fieldCtx: Set[Local],
  )

  def getVar(l: Local)(using Raise, Scope): String = l match
    case ts: hkmc2.semantics.TermSymbol =>
      ts.owner match
      case S(owner) => summon[Scope].lookup_!(ts)
      case N => summon[Scope].lookup_!(ts)
    case ts: hkmc2.semantics.InnerSymbol =>
      summon[Scope].lookup_!(ts)
    case _ => summon[Scope].lookup_!(l)

  def allocIfNew(l: Local)(using Raise, Scope): Str =
    trace[Str](s"allocIfNew $l begin", r => s"allocIfNew $l end -> $r"):
      if summon[Scope].lookup(l).isDefined then
        getVar(l) |> mapName
      else
        summon[Scope].allocateName(l) |> mapName
  
  def codegenClassInfo(using Ctx, Raise, Scope)(cls: ClassInfo) =
    trace[(Opt[Def], Decl, Ls[Def])](s"codegenClassInfo ${cls.symbol} begin"):
      val fields = cls.fields.map{x => (x |> directName, mlsValType)}
      cls.fields.foreach(x => summon[Scope].allocateName(x))
      val parents = if cls.parents.nonEmpty then cls.parents.toList.map(mapClsLikeName) else mlsObject :: Nil
      val decl = Decl.StructDecl(cls.symbol |> mapClsLikeName)
      if mlsIsInternalClass(cls.symbol) then (None, decl, Ls.empty)
      else
        val methods = cls.methods.map:
          case (name, defn) =>
            val (cdef, decl) = codegenDefn(using Ctx(summon[Ctx].fieldCtx ++ cls.fields))(defn)
            val cdef2 = cdef match
              case x: Def.FuncDef if builtinApply.contains(defn.name.nme) => x.copy(name = defn.name |> directName, in_scope = Some(cls.symbol |> mapClsLikeName))
              case x: Def.FuncDef => x.copy(in_scope = Some(cls.symbol |> mapClsLikeName))
              case _ => throw new Exception(s"codegenClassInfo: unexpected def $cdef")
            val decl2 = decl match
              case x: Decl.FuncDecl if builtinApply.contains(defn.name.nme) => x.copy(isVirtual = true, name = defn.name |> directName)
              case x: Decl.FuncDecl => x.copy(isVirtual = true)
              case _ => throw new Exception(s"codegenClassInfo: unexpected decl $decl")
            log(s"codegenClassInfo: ${cls.symbol} method ${defn.name} $decl2")
            (cdef2, decl2)
        val theDef = Def.StructDef(
          cls.symbol |> mapClsLikeName, fields,
          if parents.nonEmpty then Some(parents) else None,
          Ls(Def.RawDef(mlsObjectNameMethod(cls.symbol.nme)),
            Def.RawDef(mlsTypeTag()),
            Def.RawDef(mlsCommonPrintMethod(cls.fields.map(directName))),
            Def.RawDef(mlsCommonDestructorMethod(cls.symbol |> mapClsLikeName, cls.fields.map(directName))),
            Def.RawDef(mlsCommonCreateMethod(cls.symbol |> mapClsLikeName, cls.fields.map(directName), cls.id))),
          methods.iterator.map(_._2).toList
        )
        (S(theDef), decl, methods.iterator.map(_._1).toList)
  
  def toExpr(texpr: TrivialExpr, reifyUnit: Bool = false)(using Ctx, Raise, Scope): Opt[Expr] = texpr match
    case IExpr.Ref(name) if summon[Ctx].fieldCtx.contains(name) => S(Expr.Var(name |> directName))
    case IExpr.Ref(name: BuiltinSymbol) if name.nme === "<this>" => S(mlsThis)
    case IExpr.Ref(name) => S(Expr.Var(name |> allocIfNew))
    case IExpr.Literal(hkmc2.syntax.Tree.BoolLit(x)) => S(mlsIntLit(if x then 1 else 0))
    case IExpr.Literal(hkmc2.syntax.Tree.IntLit(x)) => S(mlsIntLit(x))
    case IExpr.Literal(hkmc2.syntax.Tree.DecLit(x)) => S(mlsDecLit(x))
    case IExpr.Literal(hkmc2.syntax.Tree.StrLit(x)) => S(mlsStrLit(x))
    case IExpr.Literal(hkmc2.syntax.Tree.UnitLit(_)) => if reifyUnit then S(mlsUnitValue) else None
  
  def toExpr(texpr: TrivialExpr)(using Ctx, Raise, Scope): Expr = texpr match
    case IExpr.Ref(name) if summon[Ctx].fieldCtx.contains(name) => Expr.Var(name |> directName)
    case IExpr.Ref(name: BuiltinSymbol) if name.nme === "<this>" => mlsThis
    case IExpr.Ref(name) => Expr.Var(name |> allocIfNew)
    case IExpr.Literal(hkmc2.syntax.Tree.BoolLit(x)) => mlsIntLit(if x then 1 else 0)
    case IExpr.Literal(hkmc2.syntax.Tree.IntLit(x)) => mlsIntLit(x)
    case IExpr.Literal(hkmc2.syntax.Tree.DecLit(x)) => mlsDecLit(x)
    case IExpr.Literal(hkmc2.syntax.Tree.StrLit(x)) => mlsStrLit(x)
    case IExpr.Literal(hkmc2.syntax.Tree.UnitLit(_)) => mlsUnitValue
  

  def wrapMultiValues(exprs: Ls[TrivialExpr])(using Ctx, Raise, Scope): Expr = exprs match
    case x :: Nil => toExpr(x, reifyUnit = true).get
    case _ => 
      val init = exprs.map{x => toExpr(x)}
      mlsTupleValue(init)
  
  def codegenCaseWithIfs(scrut: TrivialExpr, cases: Ls[(Pat, Node)], default: Opt[Node], storeInto: Str)(using decls: Ls[Decl], stmts: Ls[Stmt])(using Ctx, Raise, Scope): (Ls[Decl], Ls[Stmt]) =
    val scrut2 = toExpr(scrut)
    val init: Stmt = 
      default.fold(mlsThrowNonExhaustiveMatch)(x => {
        val (decls2, stmts2) = codegen(x, storeInto)(using Ls.empty, Ls.empty[Stmt])
        Stmt.Block(decls2, stmts2)
      })
    val stmt = cases.foldRight(S(init)) {
      case ((Pat.Class(cls), arm), nextarm) =>
        val (decls2, stmts2) = codegen(arm, storeInto)(using Ls.empty, Ls.empty[Stmt])
        val stmt = Stmt.If(mlsIsValueOf(cls |> mapClsLikeName, scrut2), Stmt.Block(decls2, stmts2), nextarm)
        S(stmt)
      case ((Pat.Lit(i @ hkmc2.syntax.Tree.IntLit(_)), arm), nextarm) =>
        val (decls2, stmts2) = codegen(arm, storeInto)(using Ls.empty, Ls.empty[Stmt])
        val stmt = Stmt.If(mlsIsIntLit(scrut2, i), Stmt.Block(decls2, stmts2), nextarm)
        S(stmt)
      case ((Pat.Lit(i @ hkmc2.syntax.Tree.BoolLit(_)), arm), nextarm) =>
        val (decls2, stmts2) = codegen(arm, storeInto)(using Ls.empty, Ls.empty[Stmt])
        val stmt = Stmt.If(mlsIsBoolLit(scrut2, i), Stmt.Block(decls2, stmts2), nextarm)
        S(stmt)
      case _ => TODO("codegenCaseWithIfs doesn't support these patterns currently")
    }
    (decls, stmt.fold(stmts)(x => stmts :+ x))

  def codegenJumpWithCall(func: Local, args: Ls[TrivialExpr], storeInto: Opt[Str])(using decls: Ls[Decl], stmts: Ls[Stmt])(using Ctx, Raise, Scope): (Ls[Decl], Ls[Stmt]) =
    val call = Expr.Call(Expr.Var(func |> allocIfNew), args.map(toExpr))
    val stmts2 = stmts ++ Ls(storeInto.fold(Stmt.Return(call))(x => Stmt.Assign(x, call)))
    (decls, stmts2)

  def codegenOps(op: BuiltinSymbol, args: Ls[TrivialExpr])(using Ctx, Raise, Scope) = 
    trace[Expr](s"codegenOps $op begin"):
      var op2 = op.nme
      if op2 === "===" then
        op2 = "=="
      else if op2 === "!===" then
        op2 = "!="
      if op.binary && args.length === 2 then 
        Expr.Binary(op2, toExpr(args(0)), toExpr(args(1)))
      else if op.unary && args.length === 1 then
        Expr.Unary(op2, toExpr(args(0)))
      else
        TODO(s"codegenOps ${op.nme} ${args.size} ${op.binary} ${op.unary} ${args.map(_.show).mkString(", ")}")


  def codegen(expr: IExpr)(using Ctx, Raise, Scope): Expr = expr match
    case x @ (IExpr.Ref(_) | IExpr.Literal(_)) => toExpr(x, reifyUnit = true).get
    case IExpr.CtorApp(cls, args) => mlsNewValue(cls |> mapClsLikeName, args.map(toExpr))
    case IExpr.Select(name, cls, field) if field.forall(_.isDigit) => 
      Expr.Member(mlsAsUnchecked(name |> allocIfNew, cls |> mapClsLikeName), s"field${field}" |> mapName)
    case IExpr.Select(name, cls, field) => Expr.Member(mlsAsUnchecked(name |> allocIfNew, cls |> mapClsLikeName), field |> mapName)
    case IExpr.BasicOp(name, args) => codegenOps(name, args)
    case IExpr.AssignField(assignee, cls, field, value) => TODO("codegen assign field")

  def codegenBuiltin(names: Ls[Local], builtin: Str, args: Ls[TrivialExpr])(using Ctx, Raise, Scope): Ls[Stmt] = builtin match
    case "error" => Ls(Stmt.Raw("throw std::runtime_error(\"Error\");"), Stmt.AutoBind(names.map(allocIfNew), mlsNeverValue(names.size)))
    case _ => Ls(Stmt.AutoBind(names.map(allocIfNew), Expr.Call(Expr.Var("_mls_builtin_" + builtin), args.map(toExpr))))

  lazy val builtinApply = Set(
    "apply0",
    "apply1",
    "apply2",
    "apply3",
    "apply4",
    "apply5",
    "apply6",
    "apply7",
    "apply8",
    "apply9",
  )
  
  def codegen(body: Node, storeInto: Str)(using decls: Ls[Decl], stmts: Ls[Stmt])(using Ctx, Raise, Scope): (Ls[Decl], Ls[Stmt]) =
    trace[(Ls[Decl], Ls[Stmt])](s"codegen $body begin"):
      body match
      case Node.Result(res) => 
        val expr = wrapMultiValues(res)
        val stmts2 = stmts ++ Ls(Stmt.Assign(storeInto, expr))
        (decls, stmts2)
      case Node.Jump(defn, args) =>
        codegenJumpWithCall(defn, args, S(storeInto))
      case Node.Panic(msg) => (decls, stmts :+ Stmt.Raw(s"throw std::runtime_error(\"$msg\");"))
      case Node.LetExpr(name, expr, body) =>
        val stmts2 = stmts ++ Ls(Stmt.AutoBind(Ls(name |> allocIfNew), codegen(expr)))
        codegen(body, storeInto)(using decls, stmts2)
      case Node.LetCall(names, bin: BuiltinSymbol, IExpr.Literal(syntax.Tree.StrLit(s)) :: tail, body) if bin.nme === "<builtin>" =>
        val stmts2 = stmts ++ codegenBuiltin(names, s.replace("\"", ""), tail)
        codegen(body, storeInto)(using decls, stmts2)
      case Node.LetMethodCall(names, cls, method, IExpr.Ref(bin: BuiltinSymbol) :: args, body) if bin.nme === "<this>" =>
        val call = mlsThisCall(cls, method |> directName, args.map(toExpr))
        val stmts2 = stmts ++ Ls(Stmt.AutoBind(names.map(allocIfNew), call))
        codegen(body, storeInto)(using decls, stmts2)
      case Node.LetMethodCall(names, cls, method, args, body) if builtinApply.contains(method.nme) =>
        val call = mlsMethodCall(cls, method |> directName, args.map(toExpr))
        val stmts2 = stmts ++ Ls(Stmt.AutoBind(names.map(allocIfNew), call))
        codegen(body, storeInto)(using decls, stmts2)
      case Node.LetMethodCall(names, cls, method, args, body) =>
        val call = mlsMethodCall(cls, method |> allocIfNew, args.map(toExpr))
        val stmts2 = stmts ++ Ls(Stmt.AutoBind(names.map(allocIfNew), call))
        codegen(body, storeInto)(using decls, stmts2)
      case Node.LetCall(names, defn, args, body) =>
        val call = Expr.Call(Expr.Var(defn |> allocIfNew), args.map(toExpr))
        val stmts2 = stmts ++ Ls(Stmt.AutoBind(names.map(allocIfNew), call))
        codegen(body, storeInto)(using decls, stmts2)
      case Node.Case(scrut, cases, default) =>
        codegenCaseWithIfs(scrut, cases, default, storeInto)
    
  def codegenDefn(using Ctx, Raise, Scope)(defn: Func): (Def, Decl) = defn match
    case Func(id, name, params, resultNum, body) =>
      val decls = Ls(mlsRetValueDecl(resultNum))
      val stmts = Ls.empty[Stmt]
      val (decls2, stmts2) = codegen(body, mlsRetValue)(using decls, stmts)
      val stmtsWithReturn = stmts2 :+ Stmt.Return(Expr.Var(mlsRetValue))
      val theDef = Def.FuncDef(mlsRetValType(resultNum), name |> allocIfNew, params.map(x => (x |> allocIfNew, mlsValType)), Stmt.Block(decls2, stmtsWithReturn), false, false, None)
      val decl = Decl.FuncDecl(mlsRetValType(resultNum), name |> allocIfNew, params.map(x => mlsValType), false, false)
      (theDef, decl)

  // Topological sort of classes based on inheritance relationships
  def sortClasses(prog: Program)(using Raise, Scope): Ls[ClassInfo] =
    var depgraph = prog.classes.map(x => (x.symbol, x.parents)).toMap
      ++ builtinClassSymbols.map(x => (x, Set.empty[Symbol]))
    log(s"depgraph: $depgraph")
    var degree = depgraph.view.mapValues(_.size).toMap
    def removeNode(node: Symbol) =
      degree -= node
      depgraph -= node
      depgraph = depgraph.view.mapValues(_.filter(_ =/= node)).toMap
      degree = depgraph.view.mapValues(_.size).toMap
    val sorted = ListBuffer.empty[ClassInfo]
    given Ordering[Local] with
      def compare(x: Local, y: Local): Int = x.nme.compareTo(y.nme)
    var work = degree.filter(_._2 === 0).keys.toSortedSet()
    while work.nonEmpty do
      val node = work.head
      work -= node
      prog.classes.find(x => (x.symbol) === node).foreach(sorted.addOne)
      removeNode(node)
      val next = degree.filter(_._2 === 0).keys.toSortedSet()
      work ++= next
    if depgraph.nonEmpty then
      val cycle = depgraph.keys.mkString(", ")
      throw new Exception(s"Cycle detected in class hierarchy: $cycle")
    sorted.toList

  def codegen(prog: Program)(using Raise, Scope): CompilationUnit =
    val sortedClasses = sortClasses(prog)
    val fieldCtx = Set.empty[Local]
    given Ctx = Ctx(fieldCtx)
    val (defs, decls, methodsDef) = sortedClasses.map(codegenClassInfo).unzip3
    val (defs2, decls2) = prog.defs.map(codegenDefn).unzip
    CompilationUnit(Ls(mlsPrelude), decls ++ decls2, defs.flatten ++ defs2 ++ methodsDef.flatten :+ Def.RawDef(mlsCallEntry(prog.entry |> allocIfNew)) :+ Def.RawDef(mlsEntryPoint))

