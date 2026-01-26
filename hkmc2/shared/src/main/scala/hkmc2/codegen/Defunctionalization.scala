package hkmc2
package codegen

import utils.*
import semantics.*
import syntax.Tree
import semantics.Elaborator.{ctx, State}

import collection.mutable.HashMap


class Defunctionalization(using Elaborator.State, Elaborator.Ctx) extends BlockTransformer(new SymbolSubst):

  class CollectFirstClassFunctions(using mapping: HashMap[BlockMemberSymbol, FunDefn]) extends BlockTransformer(new SymbolSubst):
    override def applyBlock(b: Block): Block = b match
      case Define(defn, rst) => defn match
        case fd @ FunDefn(owner, sym, dSym, params, body) if !sym.nameIsMeaningful => // lambda functions are here
          val lamClsSym = new BlockMemberSymbol("Lambda$" + mapping.size.toString(), Nil, false)
          mapping += (sym -> FunDefn.withFreshSymbol(owner, lamClsSym, params, body)(fd.forceTailRec))
          applyBlock(rst)
        case _ => super.applyBlock(b)
      case _ => super.applyBlock(b)

  class UpdateReference(using subst: Map[Symbol, Symbol]) extends BlockTransformer(new SymbolSubst):
    override def applyLocal(sym: Symbol): Symbol = subst.get(sym) match
      case Some(r) => r
      case _ => sym

    override def applyValue(v: Value)(k: Value => Block) = v match
      case Value.Ref(l, disamb) =>
        val l2 = applyLocal(l)
        k(Value.Ref(l2, disamb))
      case _ => super.applyValue(v)(k)
  
  class InsertInstance(using mapping: Map[BlockMemberSymbol, FunDefn]) extends BlockTransformer(new SymbolSubst):
    override def applyValue(v: Value)(k: Value => Block) = v match
      case Value.Ref(l: BlockMemberSymbol, disamb) => mapping.get(l) match
        case Some(fd) =>
          val tmp = new TempSymbol(None, "tmp")
          Scoped(Set(tmp),
            Assign(tmp,
              Instantiate(false, Value.Ref(fd.sym, disamb), fd.capturedVariables.map(v => Value.Ref(v, None).asArg)), k(Value.Ref(tmp, None))))
        case _ => super.applyValue(v)(k)
      case _ => super.applyValue(v)(k)

  private def generateFunctionClasses(funcs: List[FunDefn], rest: Block): Block = funcs.foldRight(rest)(
    (func, res) =>
      val capturedVariables = func.capturedVariables
      val clsSym = ClassSymbol(
        syntax.Tree.DummyTypeDef(syntax.Cls),
        syntax.Tree.Ident(func.sym.nme)
      )
      val cvMems = capturedVariables.map(v => TermSymbol(syntax.MutVal, Some(clsSym), Tree.Ident(v.nme)))
      val cvMapping = capturedVariables.zip(cvMems)
      val ctor = cvMapping.foldRight[Block](End())((p, res) => Assign(p._2, Value.Ref(p._1), res))
      val body = new UpdateReference(using cvMapping.toMap).applyBlock(func.body)
      val clsDef = ClsLikeDefn(None, clsSym, func.sym, None, syntax.Cls,
        Some(PlainParamList(capturedVariables.map(Param.simple))), Nil,
        Some(Value.Ref(State.globalThisSymbol).selSN("Function")),
        FunDefn.withFreshSymbol(Some(clsSym), new BlockMemberSymbol("call", Nil, true), func.params, body)(func.forceTailRec) :: Nil,
        Nil, Nil, Return(Call(Value.Ref(State.builtinOpsMap("super")), Nil)(false, false, false), true), ctor, None, None) // TODO: avoid head
      Scoped(Set(func.sym), Define(clsDef, res))
  )

  override def applyBlock(b: Block): Block =
    val fcfDefs = HashMap.empty[BlockMemberSymbol, FunDefn]
    val noFirstClassFunc = new CollectFirstClassFunctions(using fcfDefs).applyBlock(b)
    val applied = new InsertInstance(using fcfDefs.toMap).applyBlock(noFirstClassFunc)
    // TODO: put things inside module
    generateFunctionClasses(fcfDefs.map(p => p._2).toList, applied)

  extension (fd: FunDefn) {
    def capturedVariables: List[VarSymbol] =
      (fd.body.freeVars -- fd.params.flatMap(p => p.params.map(e => e.sym))).toList.collect {
        case v: VarSymbol => v
      }
  }
