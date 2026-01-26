package hkmc2
package codegen

import utils.*
import semantics.*
import syntax.Tree
import semantics.Elaborator.{ctx, State}

import collection.mutable.HashMap


class Defunctionalization(using Elaborator.State, Elaborator.Ctx) extends BlockTransformer(new SymbolSubst):

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

  private def collectFCFunctionDefs(d: Defn)(using mapping: HashMap[BlockMemberSymbol, FunDefn]): Option[Defn] = d match
    case fd @ FunDefn(owner, sym, dSym, params, body) if !sym.nameIsMeaningful => // lambda functions are here
      val lamClsSym = new BlockMemberSymbol("Lambda$" + mapping.size.toString(), Nil, false)
      mapping += (sym -> FunDefn.withFreshSymbol(owner, lamClsSym, params, body)(fd.forceTailRec))
      None
    case fd @ FunDefn(owner, sym, dSym, params, body) =>
      Some(FunDefn(owner, sym, dSym, params, collectFCFunctionDefs(body))(fd.forceTailRec))
    case _: ValDefn => Some(d)
    case ClsLikeDefn(owner, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods, privateFields, publicFields, preCtor, ctor, companion, bufferable) =>
      Some(ClsLikeDefn(owner, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods, privateFields, publicFields,
        collectFCFunctionDefs(preCtor), collectFCFunctionDefs(ctor), companion.map {
          case ClsLikeBody(isym, methods, privateFields, publicFields, ctor) =>
            ClsLikeBody(isym, methods.flatMap(
              m => collectFCFunctionDefs(m) match
                case Some(f: FunDefn) => Some(f)
                case _ => None
            ), privateFields, publicFields, collectFCFunctionDefs(ctor))
        }, bufferable))
  

  private def collectFCFunctionDefs(b: Block)(using mapping: HashMap[BlockMemberSymbol, FunDefn]): Block = b match
    case _: End | _: Break | _: Continue | _: Return | _: Throw => b
    case Label(label, loop, body, rest) =>
      Label(label, loop, collectFCFunctionDefs(body), collectFCFunctionDefs(rest))
    case Scoped(syms, body) => Scoped(syms, collectFCFunctionDefs(body))
    case Begin(body, rest) =>
      Begin(collectFCFunctionDefs(body), collectFCFunctionDefs(rest))
    case Match(scrut, arms, dflt, rest) =>
      Match(scrut, arms.map(p => (p._1, collectFCFunctionDefs(p._2))), dflt.map(collectFCFunctionDefs), collectFCFunctionDefs(rest))
    case TryBlock(sub, finallyDo, rest) =>
      TryBlock(collectFCFunctionDefs(sub), collectFCFunctionDefs(finallyDo), collectFCFunctionDefs(rest))
    case Assign(lhs, rhs, rest) =>
      Assign(lhs, rhs, collectFCFunctionDefs(rest))
    case af @ AssignField(lhs, nme, rhs, rest) =>
      AssignField(lhs, nme, rhs, collectFCFunctionDefs(rest))(af.symbol)
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
      AssignDynField(lhs, fld, arrayIdx, rhs, collectFCFunctionDefs(rest))
    case Define(defn, rest) => collectFCFunctionDefs(defn) match
      case Some(d) => Define(d, collectFCFunctionDefs(rest))
      case _ => collectFCFunctionDefs(rest)
    case HandleBlock(lhs, res, par, args, cls, handlers, body, rest) =>
      HandleBlock(lhs, res, par, args, cls, handlers.map {
        case Handler(sym, resumeSym, params, body) => Handler(sym, resumeSym, params, collectFCFunctionDefs(body))
      }, collectFCFunctionDefs(body), collectFCFunctionDefs(rest))

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
    val noFirstClassFunc = collectFCFunctionDefs(b)(using fcfDefs)
    val applied = new InsertInstance(using fcfDefs.toMap).applyBlock(noFirstClassFunc)
    // TODO: put things inside module
    generateFunctionClasses(fcfDefs.map(p => p._2).toList, applied)

  extension (fd: FunDefn) {
    def capturedVariables: List[VarSymbol] =
      (fd.body.freeVars -- fd.params.flatMap(p => p.params.map(e => e.sym))).toList.collect {
        case v: VarSymbol => v
      }
  }
