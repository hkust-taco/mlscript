package hkmc2
package codegen

import utils.*
import semantics.*
import syntax.Tree
import semantics.Elaborator.{ctx, State}

import collection.mutable.HashMap


class Defunctionalization(using Elaborator.State, Elaborator.Ctx) extends BlockTransformer(new SymbolSubst):

  class CollectFirstClassFunctions(topLevelMod: Option[BlockMemberSymbol])(using mapping: HashMap[BlockMemberSymbol, FunDefn]) extends BlockTransformer(new SymbolSubst):
    private def callFunc(fd: FunDefn) =
      val f = topLevelMod.map(sym => Value.Ref(sym, None).selSN(fd.sym.nme)).getOrElse(fd.asPath)
      val params = fd.params.head.params.map(p => Value.Ref(p.sym).asArg) // TODO: remove head
      Return(Call(f, params)(true, false, false), false)

    override def applyBlock(b: Block): Block = b match
      case Define(defn, rst) => defn match
        case fd @ FunDefn(owner, sym, dSym, params, body) if !sym.nameIsMeaningful => // lambda functions are here
          val lamClsSym = new BlockMemberSymbol("Lambda$" + mapping.size.toString(), Nil, false)
          mapping += (sym -> FunDefn.withFreshSymbol(owner, lamClsSym, params, body)(fd.forceTailRec))
          applyBlock(rst)
        case fd @ FunDefn(owner, sym, dSym, params, body) =>
          val lamClsSym = new BlockMemberSymbol("Lambda$" + sym.nme + mapping.size.toString(), Nil, false)
          mapping += (sym -> FunDefn.withFreshSymbol(owner, lamClsSym, params, callFunc(fd))(fd.forceTailRec))
          applyDefn(fd): fd2 =>
            val lhs = topLevelMod.map(sym => Value.Ref(sym, None).selSN(fd.sym.nme)).getOrElse(fd.asPath)
            val rhs = topLevelMod.map(sym => Value.Ref(sym, None).selSN(lamClsSym.nme)).getOrElse(Value.Ref(lamClsSym, None))
            val rst2 = applySubBlock(AssignField(lhs, syntax.Tree.Ident("firstCls"), rhs, rst)(None))
            Define(fd2, rst2)
        case _ => super.applyBlock(b)
      case _ => super.applyBlock(b)

    override def applyObjBody(defn: ClsLikeBody): ClsLikeBody =
      val withFirstClsDefs = defn.methods.foldRight(defn.ctor)((fd, rst) => {
        val lamClsSym = new BlockMemberSymbol("Lambda$" + fd.sym.nme + mapping.size.toString(), Nil, false)
        val lhs = topLevelMod.map(sym => Value.Ref(sym, None).selSN(fd.sym.nme)).getOrElse(fd.asPath)
        val rhs = topLevelMod.map(sym => Value.Ref(sym, None).selSN(lamClsSym.nme)).getOrElse(Value.Ref(lamClsSym, None))
        mapping += (fd.sym -> FunDefn.withFreshSymbol(fd.owner, lamClsSym, fd.params, callFunc(fd))(fd.forceTailRec))
        AssignField(lhs, syntax.Tree.Ident("firstCls"), rhs, rst)(None)
      })
      super.applyObjBody(ClsLikeBody(defn.isym, defn.methods, defn.privateFields, defn.publicFields, applySubBlock(withFirstClsDefs)))
  
  class UpdateReference(using subst: Map[Symbol, Symbol]) extends BlockTransformer(new SymbolSubst):
    override def applyLocal(sym: Symbol): Symbol = subst.get(sym) match
      case Some(r) => r
      case _ => sym

    override def applyValue(v: Value)(k: Value => Block) = v match
      case Value.Ref(l, disamb) =>
        val l2 = applyLocal(l)
        k(Value.Ref(l2, disamb))
      case _ => super.applyValue(v)(k)
  
  class InsertInstance(topLevelMod: Option[BlockMemberSymbol])(using mapping: Map[BlockMemberSymbol, FunDefn]) extends BlockTransformer(new SymbolSubst):
    private def updateRHSPath(p: Path, mustBeAnonymous: Boolean)(k: Path => Block) = p match
      case ref @ Value.Ref(l: BlockMemberSymbol, disamb) if !l.nameIsMeaningful || !mustBeAnonymous => mapping.get(l) match
        case Some(fd) =>
          val tmp = new TempSymbol(None, "tmp")
          val cls = topLevelMod.map(sym => Value.Ref(sym, None).selSN(fd.sym.nme)).getOrElse(Value.Ref(fd.sym, disamb))
          Scoped(Set(tmp),
            Assign(tmp,
              Instantiate(false, cls, fd.capturedVariables.map(v => Value.Ref(v, None).asArg)), k(Value.Ref(tmp, None))))
        case None if l.trmTree.isDefined =>
          val tmp = new TempSymbol(None, "tmp")
          val cls = ref.selSN("firstCls")
          Scoped(Set(tmp),
            Assign(tmp,
              Instantiate(false, cls, Nil), k(Value.Ref(tmp, None))))
        case _ => k(p)
      case sel: Select => sel.symbol match
        case Some(s: TermSymbol) =>
          val blkSym = mapping.find(p => p._1.tsym match
            case Some(t) => t == s
            case _ => false
          )
          blkSym match
            case Some(p) =>
              k(topLevelMod.map(sym => Value.Ref(sym, None).selSN(p._1.nme)).getOrElse(Value.Ref(p._1, None)))
            case _ => s.owner match
              case Some(_: ModuleOrObjectSymbol) =>
                val tmp = new TempSymbol(None, "tmp")
                val cls = sel.selSN("firstCls")
                Scoped(Set(tmp),
                  Assign(tmp,
                    Instantiate(false, cls, Nil), k(Value.Ref(tmp, None))))
              case _ => k(p)
        case _ => k(p)
      case _ => k(p)

    override def applyRcdArg(rcdArg: RcdArg)(k: RcdArg => Block): Block =
      updateRHSPath(rcdArg.value, false): v =>
        super.applyRcdArg(RcdArg(rcdArg.idx, v))(k)

    override def applyArg(arg: Arg)(k: Arg => Block): Block =
      updateRHSPath(arg.value, false): v =>
        super.applyArg(Arg(arg.spread, v))(k)

    override def applyResult(r: Result)(k: Result => Block): Block = r match
      case c @ Call(fun, args) => updateRHSPath(fun, true): fun2 =>
        applyArgs(args): args2 =>
          k(Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall))
      case p: Path => updateRHSPath(p, false): p2 =>
        k(p2)
      case _ => super.applyResult(r)(k)

  class UpdateCall() extends BlockTransformer(new SymbolSubst):
    override def applyResult(r: Result)(k: Result => Block): Block = r match
      case r @ Call(fun, args) => fun match
        case ref @ Value.Ref(sym, _) => sym match
          case _: VarSymbol |  _: TempSymbol =>
            k(Call(ref.selSN("call"), args)(r.isMlsFun, r.mayRaiseEffects, r.explicitTailCall))
          case _ => super.applyResult(r)(k)
        case _ => super.applyResult(r)(k)
      case _ => super.applyResult(r)(k)
    

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
      val body =
        new UpdateReference(using capturedVariables.zip(cvMems).toMap).applyBlock(func.body)
      val clsDef = ClsLikeDefn(owner, clsSym, func.sym, None, syntax.Cls,
        Some(PlainParamList(ctorParams.map(Param.simple))), Nil,
        Some(Value.Ref(State.globalThisSymbol).selSN("Function")),
        FunDefn.withFreshSymbol(Some(clsSym), new BlockMemberSymbol("call", Nil, true), func.params, body)(func.forceTailRec) :: Nil,
        Nil, Nil, Return(Call(Value.Ref(State.builtinOpsMap("super")), Nil)(false, false, false), true), ctor, None, None)
      Scoped(Set(func.sym), Define(clsDef, res))
  )

  override def applyBlock(b: Block): Block =
    val topLevelMod = b match
      case Scoped(_, Define(cls: ClsLikeDefn, _)) if cls.companion.isDefined => Some(cls.sym)
      case _ => None
    val fcfDefs = HashMap.empty[BlockMemberSymbol, FunDefn]
    val noFirstClassFunc = new CollectFirstClassFunctions(topLevelMod)(using fcfDefs).applyBlock(b)
    val passInstance = new InsertInstance(topLevelMod)(using fcfDefs.toMap).applyBlock(noFirstClassFunc)
    // val called = new UpdateCall().applyBlock(passInstance)
    val fcfCls = fcfDefs.map(_._2).toList
    
    val withClasses = passInstance match
      case Scoped(syms, Define(ClsLikeDefn(owner, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
        privateFields, publicFields, preCtor, ctor, Some(ClsLikeBody(isym2, methods2, privateFields2, publicFields2, ctor2)), bufferable), rest)) =>
          Scoped(syms, Define(ClsLikeDefn(owner, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods, privateFields, publicFields, preCtor, ctor,
            Some(ClsLikeBody(isym2, methods2, privateFields2, publicFields2, generateFCFunctionClasses(Some(isym2), fcfCls, ctor2))), bufferable), rest))
      case _ => generateFCFunctionClasses(None, fcfCls, passInstance)
    new UpdateCall().applyBlock(withClasses)

  extension (fd: FunDefn) {
    def capturedVariables: List[VarSymbol | TermSymbol] =
      (fd.body.freeVars -- fd.params.flatMap(p => p.params.map(e => e.sym))).toList.collect {
        case v: VarSymbol => v
        case t: TermSymbol => t 
      }
  }
