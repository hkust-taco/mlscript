package hkmc2
package codegen

import utils.*
import semantics.*
import syntax.Tree
import semantics.Elaborator.{ctx, State}
import hkmc2.Message.MessageContext

import collection.mutable.HashMap


class FirstClassFunctionTransformer(using Elaborator.State, Raise) extends BlockTransformer(new SymbolSubst):

  // Collect functions in a single module and
  //  1. generate corresponding function classes with call function
  //  2. generate firstCls field for each non-anonymous function
  //  3. substitute all first-class functions with corresponding class instantiation.
  //  4. invoke the call function for each first-class function
  class ModuleTransformer(outModulePath: Option[Path], mapping: HashMap[BlockMemberSymbol, FunDefn]) extends BlockTransformer(new SymbolSubst):
    private def callFunc(fd: FunDefn) =
      val f = outModulePath.map(_.selSN(fd.sym.nme)).getOrElse(fd.asPath)
      val params = fd.params match
        case head :: Nil => head.params.map(p => Value.Ref(p.sym).asArg)
        case _ =>
          raise(ErrorReport(msg"Unsupported function form." -> fd.sym.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
          Nil
      
      Return(Call(f, params)(true, false, false), false)

    override def applyBlock(b: Block): Block = b match
      case Define(defn, rst) => defn match
        case fd @ FunDefn(owner, sym, dSym, params, body) if !sym.nameIsMeaningful => // Anonymous functions
          val lamClsSym = new BlockMemberSymbol("Lambda$" + mapping.size.toString(), Nil, false)
          mapping += (sym -> FunDefn.withFreshSymbol(owner, lamClsSym, params, body)(fd.forceTailRec))
          applyBlock(rst) // Also remove the original definition, since they cannot be invoked by name
        case fd @ FunDefn(owner, sym, dSym, params, body) => // Non-anonymous functions
          val lamClsSym = new BlockMemberSymbol("Lambda$" + sym.nme, Nil, false)
          mapping += (sym -> FunDefn.withFreshSymbol(owner, lamClsSym, params, callFunc(fd))(fd.forceTailRec))
          applyDefn(fd): fd2 =>
            val rst2 = applySubBlock(rst)
            Define(fd2, rst2)
        case _ => super.applyBlock(b)
      case _ => super.applyBlock(b)

    // Pack module methods together to defunctionalize them
    private def packMethods(ms: List[FunDefn]) = ms.foldRight[Block](End())((fd, rst) => Define(fd, rst))

    // Extract defunctionalized methods and corresponding firstCls assignments
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
            val fcfDefs = HashMap.empty[BlockMemberSymbol, FunDefn]
            val nestedPath = outModulePath match
              case Some(p) => Some(p.selSN(sym.nme))
              case None => Some(Value.Ref(sym, Some(isym)))
            val msBlk = new ModuleTransformer(nestedPath, fcfDefs).applyBlock(packMethods(mod.methods))
            val ctor2 = new ModuleTransformer(nestedPath, fcfDefs).applyBlock(mod.ctor)
            val fcfCls = fcfDefs.map(_._2).toList
            val (mths, withClsDefs) = unpackMethods(msBlk, ctor2)
            k(ClsLikeDefn(own, isym, sym, ctorSym, kind, paramsOpt, auxParams, parentPath, methods, privateFields, publicFields, preCtor, ctor,
              Some(ClsLikeBody(mod.isym, mths, mod.privateFields, mod.publicFields, generateFCFunctionClasses(Some(mod.isym), fcfCls, withClsDefs))), bufferable))
          case _ => super.applyDefn(defn)(k)
      case _ => super.applyDefn(defn)(k)

    // If the given path is non-anonymous and at LHS (i.e., mustBeAnonymous is true), then do not substitute it
    private def updatePathWithInst(p: Path, mustBeAnonymous: Boolean)(k: Path => Block) = p match
      case ref @ Value.Ref(l: BlockMemberSymbol, disamb) if !l.nameIsMeaningful || !mustBeAnonymous => mapping.get(l) match
        case Some(fd) =>
          val tmp = new TempSymbol(None, "tmp")
          val cls = outModulePath.map(_.selSN(fd.sym.nme)).getOrElse(Value.Ref(fd.sym, disamb))
          Scoped(Set(tmp),
            Assign(tmp,
              Instantiate(false, cls, fd.capturedVariables.map(v => Value.Ref(v, None).asArg)), k(Value.Ref(tmp, None))))
        case None if l.tsym.map(_.k == syntax.Fun).getOrElse(false) => // This symbol denotes a function and is defined in another module
          val tmp = new TempSymbol(None)
          val cls = Value.Ref(new BlockMemberSymbol("Lambda$" + l.nme, Nil, true), disamb)
          Scoped(Set(tmp),
            Assign(tmp,
              Instantiate(false, cls, Nil), k(Value.Ref(tmp, None))))
        case _ => k(p)
      case sel: Select => sel.symbol match
        case Some(s: TermSymbol) if s.k == syntax.Fun =>
          val blkSym = mapping.find(p => p._1.tsym match
            case Some(t) => t == s
            case _ => false
          )
          blkSym match
            case Some(p) => // we are selecting a function inside the current module
              k(outModulePath.map(_.selSN(p._1.nme)).getOrElse(Value.Ref(p._1, None)))
            case _ => s.owner match
              case Some(_: ModuleOrObjectSymbol) => // defined in another module
                val tmp = new TempSymbol(None)
                val cls = sel.qual.selSN("Lambda$" + s.nme)
                Scoped(Set(tmp),
                  Assign(tmp,
                    Instantiate(false, cls, Nil), k(Value.Ref(tmp, None))))
              case _ => k(p)
        case _ => k(p)
      case _ => k(p)

    override def applyRcdArg(rcdArg: RcdArg)(k: RcdArg => Block): Block =
      updatePathWithInst(rcdArg.value, false): v =>
        super.applyRcdArg(RcdArg(rcdArg.idx, v))(k)

    override def applyArg(arg: Arg)(k: Arg => Block): Block =
      updatePathWithInst(arg.value, false): v =>
        super.applyArg(Arg(arg.spread, v))(k)

    override def applyResult(r: Result)(k: Result => Block): Block = r match
      case c @ Call(fun, args) => updatePathWithInst(fun, true): fun2 =>
        applyArgs(args): args2 =>
          fun2 match
            case ref @ Value.Ref(sym, _) => sym match
              case _: VarSymbol |  _: TempSymbol =>
                k(Call(ref.selSN("call"), args2)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall))
              case _ => k(Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall))
            case sel: Select => sel.symbol match
              case Some(s: TermSymbol) if s.k != syntax.Fun =>
                k(Call(sel.selSN("call"), args2)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall))
              case _ => k(Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall))
            case _ => k(Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall))
      case p: Path => updatePathWithInst(p, false): p2 =>
        k(p2)
      case _ => super.applyResult(r)(k)
  
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
    val fcfDefs = HashMap.empty[BlockMemberSymbol, FunDefn]
    val noFirstClassFunc = new ModuleTransformer(None, fcfDefs).applyBlock(b)
    val fcfCls = fcfDefs.map(_._2).toList
    generateFCFunctionClasses(None, fcfCls, noFirstClassFunc)

  extension (fd: FunDefn) {
    def capturedVariables: List[VarSymbol | TermSymbol] =
      (fd.body.freeVars -- fd.params.flatMap(p => p.params.map(e => e.sym))).toList.collect {
        case v: VarSymbol => v
        case t: TermSymbol => t 
      }
  }
