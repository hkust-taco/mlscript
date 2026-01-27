package hkmc2
package codegen

import utils.*
import semantics.*
import syntax.Tree
import semantics.Elaborator.{ctx, State}

import collection.mutable.HashMap


class Defunctionalization(using Elaborator.State, Elaborator.Ctx) extends BlockTransformer(new SymbolSubst):

  class CollectFirstClassFunctions(using mapping: HashMap[BlockMemberSymbol, FunDefn | BlockMemberSymbol]) extends BlockTransformer(new SymbolSubst):
    override def applyBlock(b: Block): Block = b match
      case Define(defn, rst) => defn match
        case fd @ FunDefn(owner, sym, dSym, params, body) if !sym.nameIsMeaningful => // lambda functions are here
          val lamClsSym = new BlockMemberSymbol("Lambda$" + mapping.size.toString(), Nil, false)
          mapping += (sym -> FunDefn.withFreshSymbol(owner, lamClsSym, params, body)(fd.forceTailRec))
          applyBlock(rst)
        case _ => super.applyBlock(b)
      case _ => super.applyBlock(b)
  
    private def checkPaths(ps: List[Path]): Unit = ps.foreach {
      case Value.Ref(sym: BlockMemberSymbol, Some(disamb: TermSymbol)) if sym.nameIsMeaningful =>
        val lamClsSym = new BlockMemberSymbol("Lambda$" + sym.nme + mapping.size.toString(), Nil, false)
        mapping += (sym -> lamClsSym)
      case _ => ()
    }

    override def applyResult(r: Result)(k: Result => Block): Block = r match
      case Call(fun, args) =>
        checkPaths(args.map(_.value))
        super.applyResult(r)(k)
      case Instantiate(mut, cls, args) =>
        checkPaths(args.map(_.value))
        super.applyResult(r)(k)
      case Tuple(mut, elems) =>
        checkPaths(elems.map(_.value))
        super.applyResult(r)(k)
      case Record(mut, fields) =>
        checkPaths(fields.map(_.value))
        super.applyResult(r)(k)
      case p: Path =>
        checkPaths(p :: Nil)
        super.applyResult(r)(k)
      case _ => super.applyResult(r)(k)

  class UpdateReference(using subst: Map[Symbol, Symbol]) extends BlockTransformer(new SymbolSubst):
    override def applyLocal(sym: Symbol): Symbol = subst.get(sym) match
      case Some(r) => r
      case _ => sym

    override def applyValue(v: Value)(k: Value => Block) = v match
      case Value.Ref(l, disamb) =>
        val l2 = applyLocal(l)
        k(Value.Ref(l2, disamb))
      case _ => super.applyValue(v)(k)
  
  class InsertInstance(topLevelMod: Option[BlockMemberSymbol])(using mapping: Map[BlockMemberSymbol, FunDefn | BlockMemberSymbol]) extends BlockTransformer(new SymbolSubst):
    override def applyValue(v: Value)(k: Value => Block) = v match
      case Value.Ref(l: BlockMemberSymbol, disamb) => mapping.get(l) match
        case Some(fd: FunDefn) =>
          val tmp = new TempSymbol(None, "tmp")
          val cls = topLevelMod.map(sym => Value.Ref(sym, None).selSN(fd.sym.nme)).getOrElse(Value.Ref(fd.sym, disamb))
          Scoped(Set(tmp),
            Assign(tmp,
              Instantiate(false, cls, fd.capturedVariables.map(v => Value.Ref(v, None).asArg)), k(Value.Ref(tmp, None))))
        case Some(sym: BlockMemberSymbol) =>
          val tmp = new TempSymbol(None, "tmp")
          val cls = topLevelMod.map(s => Value.Ref(s, None).selSN(sym.nme)).getOrElse(Value.Ref(sym, disamb))
          Scoped(Set(tmp),
            Assign(tmp,
              Instantiate(false, Value.Ref(sym, disamb), Nil), k(Value.Ref(tmp, None))))
        case _ => super.applyValue(v)(k)
      case _ => super.applyValue(v)(k)

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
      val body = new UpdateReference(using capturedVariables.zip(cvMems).toMap).applyBlock(func.body)
      val clsDef = ClsLikeDefn(owner, clsSym, func.sym, None, syntax.Cls,
        Some(PlainParamList(ctorParams.map(Param.simple))), Nil,
        Some(Value.Ref(State.globalThisSymbol).selSN("Function")),
        FunDefn.withFreshSymbol(Some(clsSym), new BlockMemberSymbol("call", Nil, true), func.params, body)(func.forceTailRec) :: Nil,
        Nil, Nil, Return(Call(Value.Ref(State.builtinOpsMap("super")), Nil)(false, false, false), true), ctor, None, None)
      Scoped(Set(func.sym), Define(clsDef, res))
  )

  private def generateRHSFunctionClasses(owner: Option[InnerSymbol], funcs: List[(BlockMemberSymbol, BlockMemberSymbol)], rest: Block): Block = funcs.foldRight(rest)(
    (pair, res) =>
      val clsSym = ClassSymbol(
        syntax.Tree.DummyTypeDef(syntax.Cls),
        syntax.Tree.Ident(pair._2.nme)
      )
      val args = pair._1.trmTree match
        case Some(syntax.Tree.TermDef(syntax.Fun, syntax.Tree.App(_, syntax.Tree.Tup(fields)), _)) =>
          fields.zipWithIndex.map {
            case (name: syntax.Tree.Ident, _) => new VarSymbol(name)
            case (_, id) => new VarSymbol(syntax.Tree.Ident("arg" + id.toString()))
          }
        case _ => Nil // TODO: error here?
      val body = Return(Call(Value.Ref(pair._1, None), args.map(arg => Value.Ref(arg, None).asArg))(true, false, false), false)
      val clsDef = ClsLikeDefn(owner, clsSym, pair._2, None, syntax.Cls, None, Nil,
        Some(Value.Ref(State.globalThisSymbol).selSN("Function")),
        FunDefn.withFreshSymbol(Some(clsSym), new BlockMemberSymbol("call", Nil, true), PlainParamList(args.map(Param.simple)) :: Nil, body)(false) :: Nil,
        Nil, Nil, Return(Call(Value.Ref(State.builtinOpsMap("super")), Nil)(false, false, false), true), End(), None, None)
      Scoped(Set(pair._2), Define(clsDef, res))
  )

  override def applyBlock(b: Block): Block =
    val fcfDefs = HashMap.empty[BlockMemberSymbol, FunDefn | BlockMemberSymbol]
    val noFirstClassFunc = new CollectFirstClassFunctions(using fcfDefs).applyBlock(b)
    val topLevelMod = noFirstClassFunc match
      case Scoped(_, Define(cls: ClsLikeDefn, _)) if cls.companion.isDefined => Some(cls.sym)
      case _ => None
    val passInstance = new InsertInstance(topLevelMod)(using fcfDefs.toMap).applyBlock(noFirstClassFunc)
    val called = new UpdateCall().applyBlock(passInstance)
    val (fcfCls, rhsCls) = fcfDefs.toList.partitionMap {
      case (_, fd: FunDefn) => Left(fd)
      case (sym1, sym2: BlockMemberSymbol) => Right(sym1 -> sym2)
    }
    
    called match
      case Scoped(syms, Define(ClsLikeDefn(owner, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
        privateFields, publicFields, preCtor, ctor, Some(ClsLikeBody(isym2, methods2, privateFields2, publicFields2, ctor2)), bufferable), rest)) =>
          Scoped(syms, Define(ClsLikeDefn(owner, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods, privateFields, publicFields, preCtor, ctor,
            Some(ClsLikeBody(isym2, methods2, privateFields2, publicFields2,
              generateRHSFunctionClasses(Some(isym2), rhsCls, generateFCFunctionClasses(Some(isym2), fcfCls, ctor2)))), bufferable), rest))
      case _ =>
        generateRHSFunctionClasses(None, rhsCls, generateFCFunctionClasses(None, fcfCls, called))

  extension (fd: FunDefn) {
    def capturedVariables: List[VarSymbol | TermSymbol] =
      (fd.body.freeVars -- fd.params.flatMap(p => p.params.map(e => e.sym))).toList.collect {
        case v: VarSymbol => v
        case t: TermSymbol => t 
      }
  }
