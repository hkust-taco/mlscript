package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*
import semantics.*
import syntax.Tree
import semantics.Elaborator.{ctx, State}
import hkmc2.Message.MessageContext

import collection.mutable.{HashMap, HashSet, ListBuffer}


class FirstClassFunctionTransformer(using Elaborator.State, Raise) extends BlockTransformer(new SymbolSubst):

  // Function definitions
  private val funDefs: HashSet[BlockMemberSymbol] = HashSet.empty

  // modulePath: path of the current module
  // newFunDefs: new lambdas created by desugaring functions with multiple parameter lists
  // fwdFunDefs: cache the forwarding functions created to avoid duplications
  class ModuleTransformer(modulePath: Option[Path], newFunDefs: ListBuffer[FunDefn], fwdFunDefs: HashMap[Path, FunDefn]) extends BlockTransformer(new SymbolSubst):
    private def checkNestedFunctions(body: Block) =
      new CheckNestedFunctions().applyBlock(body)

    private def desugarMultipleParamList(fd: FunDefn) = fd.params match
      case Nil => (fd.params, fd.body)
      case _ :: Nil => (fd.params, fd.body)
      case head :: tail =>
        def rec(params: List[ParamList]): Block = params match
          case head :: Nil =>
            val lamClsSym = new BlockMemberSymbol("Lambda$" + newFunDefs.size.toString(), Nil, false)
            val newFd = FunDefn.withFreshSymbol(fd.owner, lamClsSym, params, super.applyBlock(fd.body))(false)
            newFunDefs += newFd
            val cls = modulePath.map(_.selSN(lamClsSym.nme)).getOrElse(Value.Ref(lamClsSym, None))
            Return(Instantiate(false, cls, newFd.capturedVariables.map(v => Value.Ref(v, None).asArg)), false)
          case head :: rest =>
            val newBody = rec(rest)
            val lamClsSym = new BlockMemberSymbol("Lambda$" + newFunDefs.size.toString(), Nil, false)
            val newFd = FunDefn.withFreshSymbol(fd.owner, lamClsSym, head :: Nil, newBody)(false)
            newFunDefs += newFd
            val cls = modulePath.map(_.selSN(lamClsSym.nme)).getOrElse(Value.Ref(lamClsSym, None))
            Return(Instantiate(false, cls, newFd.capturedVariables.map(v => Value.Ref(v, None).asArg)), false)
          case Nil => lastWords("impossible because the length of parameter list must be more than 1.")
        (head :: Nil, rec(tail))

    // Pack module methods together to do the transformation
    private def packMethods(ms: List[FunDefn]) = ms.foldRight[Block](End())((fd, rst) => Define(fd, rst))

    // Extract transformed methods
    private def unpackMethods(b: Block, rest: Block) =
      def rec(b: Block, acc1: List[FunDefn], acc2: Block): (List[FunDefn], Block) = b match
        case Define(fd: FunDefn, rest) => rec(rest, fd :: acc1, acc2)
        case f @ AssignField(lhs, nme, rhs, rest) => rec(rest, acc1, AssignField(lhs, nme, rhs, acc2)(f.symbol))
        case _ => (acc1.reverse, acc2)
      rec(b, Nil, rest)

    override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
      case ClsLikeDefn(own, isym, sym, ctorSym, kind, paramsOpt, auxParams, parentPath, methods,
        privateFields, publicFields, preCtor, ctor, mod, bufferable) => mod match
          case Some(mod) =>
            val newFunDefs = ListBuffer.empty[FunDefn]
            val fwdFunDefs = HashMap.empty[Path, FunDefn]
            val nestedPath = modulePath match
              case Some(p) => Some(p.selSN(sym.nme))
              case None => Some(Value.Ref(sym, Some(isym)))
            val msBlk = new ModuleTransformer(nestedPath, newFunDefs, fwdFunDefs).applyBlock(packMethods(mod.methods))
            val ctor2 = new ModuleTransformer(nestedPath, newFunDefs, fwdFunDefs).applyBlock(mod.ctor)
            val fcfCls = newFunDefs.toList ++ fwdFunDefs.map(_._2).toList
            val (mths, withClsDefs) = unpackMethods(msBlk, ctor2)
            k(ClsLikeDefn(own, isym, sym, ctorSym, kind, paramsOpt, auxParams, parentPath, methods, privateFields, publicFields, preCtor, ctor,
              Some(ClsLikeBody(mod.isym, mths, mod.privateFields, mod.publicFields, generateFCFunctionClasses(Some(mod.isym), fcfCls, withClsDefs))), bufferable))
          case _ => super.applyDefn(defn)(k)
      case fd @ FunDefn(owner, sym, dSym, params, body) =>
        funDefs += sym
        checkNestedFunctions(body)
        val (singleParamList, newBody) = desugarMultipleParamList(fd)
        super.applyDefn(FunDefn(owner, sym, dSym, singleParamList, newBody)(fd.forceTailRec))(k)
      case _ => super.applyDefn(defn)(k)

    private def createForwardFunc(p: Path) = fwdFunDefs.getOrElseUpdate(p, {
      val lamClsSym = new BlockMemberSymbol("Func$" + fwdFunDefs.size.toString(), Nil, false)
      val restParam = Param(FldFlags(false, true, false, false), VarSymbol(Tree.Ident("param")), None, Modulefulness.none)
      FunDefn.withFreshSymbol(None, lamClsSym, ParamList(ParamListFlags.empty, Nil, Some(restParam)) :: Nil,
        Return(Call(p, Arg(Some(true), Value.Ref(restParam.sym, None)) :: Nil)(true, false, false), false))(false)
    })

    // If the given path is non-anonymous and is called immediately, then do not substitute it
    private def updatePathWithInst(p: Path, isCalled: Boolean)(k: Path => Block) = p match
      case ref @ Value.Ref(l: BlockMemberSymbol, disamb) if (funDefs(l) || l.tsym.map(_.k is syntax.Fun).getOrElse(false)) && !isCalled =>
        val fd = createForwardFunc(p)
        val tmp = new TempSymbol(None)
        val cls = modulePath.map(_.selSN(fd.sym.nme)).getOrElse(Value.Ref(fd.sym, disamb))
        Scoped(Set(tmp), Assign(tmp, Instantiate(false, cls, Nil), k(Value.Ref(tmp, None))))
      case sel: Select => sel.symbol match
        case Some(s: TermSymbol) if (s.k is syntax.Fun) && !isCalled => // second-class functions as first-class function
          val fd = createForwardFunc(p)
          val tmp = new TempSymbol(None)
          val cls = modulePath.map(_.selSN(fd.sym.nme)).getOrElse(Value.Ref(fd.sym, None))
          Scoped(Set(tmp), Assign(tmp, Instantiate(false, cls, Nil), k(Value.Ref(tmp, None))))
        case _ => k(p)
      case _ => k(p)

    override def applyValDefn(defn: ValDefn)(k: ValDefn => Block): Block =
      updatePathWithInst(defn.rhs, false): v =>
        super.applyValDefn(ValDefn(defn.tsym, defn.sym, v))(k)

    override def applyRcdArg(rcdArg: RcdArg)(k: RcdArg => Block): Block =
      updatePathWithInst(rcdArg.value, false): v =>
        super.applyRcdArg(RcdArg(rcdArg.idx, v))(k)

    override def applyArg(arg: Arg)(k: Arg => Block): Block =
      updatePathWithInst(arg.value, false): v =>
        super.applyArg(Arg(arg.spread, v))(k)

    override def applyResult(r: Result)(k: Result => Block): Block = r match
      case c @ Call(fun, args) => updatePathWithInst(fun, true): fun2 =>
        applyArgs(args): args2 =>
          def call(f: Path) = Call(f, args2)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall)
          fun2 match
            case ref @ Value.Ref(sym, _) => sym match
              case _: VarSymbol |  _: TempSymbol => k(call(ref.selSN("call")))
              case _ => k(call(fun2))
            case sel: Select => sel.symbol match
              case Some(s: TermSymbol) =>
                if s.k is syntax.Fun then k(call(fun2))
                else k(call(sel.selSN("call")))
              case _ =>
                raise(ErrorReport(msg"Cannot determine if ${sel.name.name} is a function object." -> fun.toLoc :: Nil,
                  source = Diagnostic.Source.Compilation))
                k(call(fun2))
            case s: DynSelect =>
              raise(ErrorReport(msg"Cannot determine if the dynamic selection is a function object." -> s.toLoc :: Nil,
                  source = Diagnostic.Source.Compilation))
                k(call(fun2))
            case _ => k(call(fun2))
      case p: Path => updatePathWithInst(p, false)(k)
      case _: Lambda => lastWords("Lambda functions should be rewritten into function definitions first.")
      case _ => super.applyResult(r)(k)

  class CheckNestedFunctions extends BlockTraverser:
    override def applyFunDefn(fun: FunDefn) =
      raise(ErrorReport(msg"Nested function ${fun.sym.nme} is not supported by lambda rewriting. Lambda lifting must be performed first." -> fun.sym.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
  
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

  private def generateFCFunctionClasses(owner: Option[InnerSymbol], funcs: List[FunDefn], rest: Block): Block = funcs.foldRight(rest)(
    (func, res) =>
      val capturedVariables = func.capturedVariables
      val clsSym = ClassSymbol(
        syntax.Tree.DummyTypeDef(syntax.Cls),
        syntax.Tree.Ident(func.sym.nme)
      )
      val ctorParams = capturedVariables.map(v => new VarSymbol(v.id))
      val cvMems = capturedVariables.map(v => TermSymbol(syntax.MutVal, Some(clsSym), Tree.Ident(v.nme)))
      val ctor = ctorParams.zip(cvMems).foldRight[Block](End())((p, res) => Assign(p._2, Value.Ref(p._1), res))
      val body = new UpdateReference(using capturedVariables.zip(cvMems).toMap).applyBlock(func.body)
      val clsDef = ClsLikeDefn(owner, clsSym, func.sym, None, syntax.Cls,
        Some(PlainParamList(ctorParams.map(Param.simple))), Nil,
        Some(Value.Ref(State.globalThisSymbol).selSN("Function")),
        FunDefn.withFreshSymbol(Some(clsSym), new BlockMemberSymbol("call", Nil, true), func.params, body)(func.forceTailRec) :: Nil,
        Nil, Nil, Return(Call(Value.Ref(State.builtinOpsMap("super")), Nil)(false, false, false), true), ctor, None, None)
      Scoped(Set(func.sym), Define(clsDef, res))
  )

  override def applyBlock(b: Block): Block =
    val newFunDefs = ListBuffer.empty[FunDefn]
    val fwdFunDefs = HashMap.empty[Path, FunDefn]
    val noFirstClassFunc = new ModuleTransformer(None, newFunDefs, fwdFunDefs).applyBlock(b)
    val fcfCls = newFunDefs.toList ++ fwdFunDefs.map(_._2).toList
    generateFCFunctionClasses(None, fcfCls, noFirstClassFunc)

  extension (fd: FunDefn) {
    def capturedVariables: List[VarSymbol | TermSymbol] =
      (fd.body.freeVars -- fd.params.flatMap(p => p.params.map(e => e.sym) ++ p.restParam.toList.map(_.sym))).toList.collect {
        case v: VarSymbol => v
        case t: TermSymbol => t 
      }
  }
