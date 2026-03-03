package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*
import semantics.*
import syntax.Tree
import semantics.Elaborator.{ctx, State}
import hkmc2.Message.MessageContext

import collection.mutable.HashMap


class FirstClassFunctionTransformer(using Elaborator.State, Elaborator.Ctx, Raise) extends BlockTransformer(new SymbolSubst):
  class CheckNestedFunctions extends BlockTraverser:
    override def applyFunDefn(fun: FunDefn) =
      raise(ErrorReport(msg"Nested function ${fun.sym.nme} is not supported by lambda rewriting. Lambda lifting must be performed first." -> fun.sym.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))

  // Anonymous lambdas' parameter lists cannot be retrieved from the term symbol
  private val funDefns = HashMap.empty[BlockMemberSymbol, FunDefn] 
  class CollectFunDefns extends BlockTraverser:
    override def applyFunDefn(fun: FunDefn) = funDefns += (fun.sym -> fun)

  private def generateFCFunctionClass(callFunc: FunDefn, capturedVariables: List[VarSymbol]) =
    val clsSym = ClassSymbol(
      syntax.Tree.DummyTypeDef(syntax.Cls),
      syntax.Tree.Ident("Lambda$")
    )
    val defSym = new BlockMemberSymbol("Lambda$", Nil, false)
    val ctorParams = capturedVariables.map(v => new VarSymbol(v.id))
    val cvMems = capturedVariables.map(v => TermSymbol(syntax.MutVal, Some(clsSym), Tree.Ident(v.nme)))
    val ctor = ctorParams.zip(cvMems).foldRight[Block](End())((p, res) => Assign(p._2, Value.Ref(p._1), res))
    val body = new UpdateReference(using capturedVariables.zip(cvMems).toMap).applyBlock(callFunc.body)
    ClsLikeDefn(None, clsSym, defSym, None, syntax.Cls,
      None, PlainParamList(ctorParams.map(Param.simple)) :: Nil,
      Some(Select(Value.Ref(State.globalThisSymbol, Some(State.globalThisSymbol)), Tree.Ident("Function"))(Some(ctx.builtins.Function))),
      FunDefn.withFreshSymbol(Some(clsSym), callFunc.sym, callFunc.params, body)(callFunc.forceTailRec) :: Nil,
      Nil, Nil, Return(Call(Value.Ref(State.builtinOpsMap("super")), Nil)(false, false, false), true), ctor, None, None)

  private def generateCallAndClass(p: Path, params: ParamList) =
    val callDef = FunDefn.withFreshSymbol(None, new BlockMemberSymbol("call", Nil, true), params :: Nil,
      Return(Call(p, params.params.map(_.sym.asPath.asArg))(true, false, false), false))(false)
    generateFCFunctionClass(callDef, Nil)

  private def generateCallAndClass(params: List[ParamList], body: Block, fvs: List[VarSymbol]) =
    val callDef = FunDefn.withFreshSymbol(None, new BlockMemberSymbol("call", Nil, true), params, body)(false)
    generateFCFunctionClass(callDef, fvs)

  private def getParamList(l: BlockMemberSymbol): Option[ParamList] = funDefns.get(l) match
    case Some(fd) => fd.params.headOption
    case _ => l.tsym.flatMap(getParamList)

  private def getParamList(ts: TermSymbol): Option[ParamList] = ts.defn.flatMap(_.params.headOption)

  override def applyPath(p: Path)(k: Path => Block): Block = p match
    case ref @ Value.Ref(l: BlockMemberSymbol, disamb) => l.tsym match
      case Some(s: TermSymbol) if s.k is syntax.Fun =>
        val params = getParamList(l).getOrElse(lastWords(s"Cannot get ${l.nme}'s parameter list."))
        val clsDef = generateCallAndClass(ref, params)
        val tmp = new TempSymbol(None)
        val cls = Value.Ref(clsDef.sym, disamb)
        Scoped(Set(clsDef.sym, tmp), Define(clsDef, Assign(tmp, Instantiate(false, cls, Nil), k(Value.Ref(tmp, None)))))
      case Some(_) => k(p)
      case None => disamb match
          case Some(t: TermSymbol) if t.k is syntax.Fun =>
            val params = getParamList(l).getOrElse(lastWords(s"Cannot get ${t.nme}'s parameter list."))
            val clsDef = generateCallAndClass(ref, params)
            val tmp = new TempSymbol(None)
            val cls = Value.Ref(clsDef.sym, disamb)
            Scoped(Set(clsDef.sym, tmp), Define(clsDef, Assign(tmp, Instantiate(false, cls, Nil), k(Value.Ref(tmp, None)))))
          case Some(_) => k(p)
          case _ =>
            raise(ErrorReport(msg"Cannot determine if ${l.nme} is a function." -> ref.toLoc :: Nil,
              source = Diagnostic.Source.Compilation))
            k(p)
    case sel: Select => sel.symbol match
      case Some(s: TermSymbol) if (s.k is syntax.Fun) =>
        val params = getParamList(s).getOrElse(lastWords(s"Cannot get ${s.nme}'s parameter list."))
        val clsDef = generateCallAndClass(sel, params)
        val tmp = new TempSymbol(None)
        val cls = Value.Ref(clsDef.sym, None)
        Scoped(Set(clsDef.sym, tmp), Define(clsDef, Assign(tmp, Instantiate(false, cls, Nil), k(Value.Ref(tmp, None)))))
      case Some(_) => k(p)
      case _ =>
        raise(ErrorReport(msg"Cannot determine if ${sel.name.name} is a function." -> sel.toLoc :: Nil,
          source = Diagnostic.Source.Compilation))
        k(p)
    case _ => k(p)  

  override def applyResult(r: Result)(k: Result => Block): Block = r match
    case c @ Call(fun, args) => applyArgs(args): args2 =>
      def call(f: Path) = Call(f, args2)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall)
      fun match
        case ref @ Value.Ref(sym, _) => sym match
          case _: VarSymbol |  _: TempSymbol => k(call(ref.selSN("call")))
          case _ => k(call(fun))
        case sel: Select => sel.symbol match
          case Some(s: TermSymbol) =>
            if s.k is syntax.Fun then k(call(fun))
            else k(call(sel.selSN("call")))
          case _ =>
            raise(ErrorReport(msg"Cannot determine if ${sel.name.name} is a function object." -> fun.toLoc :: Nil,
              source = Diagnostic.Source.Compilation))
            k(call(fun))
        case s: DynSelect =>
          raise(ErrorReport(msg"Cannot determine if the dynamic selection is a function object." -> s.toLoc :: Nil,
              source = Diagnostic.Source.Compilation))
            k(call(fun))
        case _ => k(call(fun))
    case path: Path => applyPath(path)(k)
    case _: Lambda => lastWords("Lambda functions should be rewritten into function definitions first.")
    case _ => super.applyResult(r)(k)

  private def desugarMultipleParamList(fd: FunDefn, rest: Block) = fd.params match
    case Nil => Define(fd, rest)
    case _ :: Nil => Define(fd, rest)
    case head :: tail =>
      def rec(params: List[ParamList]): (Block, List[VarSymbol]) = params match
        case head :: Nil =>
          val fv: List[VarSymbol] = (fd.body.freeVars -- head.params.map(_.sym)).toList.collect {
            case v: VarSymbol => v
          }
          val clsDef = generateCallAndClass(head :: Nil, fd.body, fv)
          val cls = Value.Ref(clsDef.sym, Some(clsDef.isym))
          (Scoped(Set(clsDef.sym), Define(clsDef, Return(Instantiate(false, cls, fv.map(_.asPath.asArg)), false))), fv)
        case head :: rest =>
          val (newBody, fv) = rec(rest)
          val newFv = (fv.toSet -- head.params.map(_.sym)).toList
          val clsDef = generateCallAndClass(head :: Nil, newBody, newFv)
          val cls = Value.Ref(clsDef.sym, Some(clsDef.isym))
          (Scoped(Set(clsDef.sym), Define(clsDef, Return(Instantiate(false, cls, newFv.map(_.asPath.asArg)), false))), newFv)
        case Nil => lastWords("impossible because the length of parameter list must be more than 1.")
      val newFd = FunDefn.withFreshSymbol(fd.owner, fd.sym, head :: Nil, rec(tail)._1)(fd.forceTailRec)
      Define(newFd, rest)

  private def checkNestedFunctions(body: Block) =
    new CheckNestedFunctions().applyBlock(body)

  override def applyBlock(b: Block): Block = b match
    case Define(fd: FunDefn, rest) =>
      checkNestedFunctions(fd.body)
      super.applyBlock(desugarMultipleParamList(fd, rest))
    case _ => super.applyBlock(b)

  def transform(b: Block): Block =
    new CollectFunDefns().applyBlock(b)
    applyBlock(b)

  // Substitute captured symbols in anonymous lambda bodies with corresponding class fields
  class UpdateReference(using subst: Map[Symbol, Symbol]) extends BlockTransformer(new SymbolSubst):
    override def applyLocal(sym: Symbol): Symbol = subst.get(sym) match
      case Some(r) => r
      case _ => sym

    override def applyValue(v: Value)(k: Value => Block) = v match
      case Value.Ref(l, disamb) =>
        val l2 = applyLocal(l)
        k(Value.Ref(l2, disamb))
      case _ => super.applyValue(v)(k)
