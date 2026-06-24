package hkmc2

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*
import hkmc2.syntax.Tree
import hkmc2.codegen.HandlerLowering.FnOrCls

class StackSafeTransform(depthLimit: Int, paths: HandlerPaths)(using State, Config):
  private val STACK_DEPTH_IDENT: Tree.Ident = Tree.Ident("stackDepth")

  private val runtimePath: Path = State.runtimeSymbol.asSimpleRef
  private val checkDepthPath: Path = runtimePath.selN(Tree.Ident("checkDepth"))
  private val runStackSafePath: Path = runtimePath.selN(Tree.Ident("runStackSafe"))
  private val stackDepthPath: Path = runtimePath.selN(STACK_DEPTH_IDENT)

  private def intLit(n: BigInt) = Value.Lit(Tree.IntLit(n))
  
  private def op(op: String, a: Path, b: Path) =
    Call(State.builtinOpsMap(op).asSimpleRef, (a.asArg :: b.asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun)
  
  def wrapStackSafe(body: Block, resSym: Assignable, rest: Block) =
    val bodSym = BlockMemberSymbol("‹stack safe body›", Nil, false)
    val bodFun = FunDefn.withFreshSymbol(N, bodSym, ParamList(ParamListFlags.empty, Nil, N) :: Nil, body)(configOverride = N, annotations = Nil)
    Scoped(Set.single(bodSym),
      Define(bodFun, Assign(resSym, Call(runStackSafePath, (intLit(depthLimit).asArg :: bodSym.asMemberRef(bodSym.asPrincipal.get).asArg :: Nil) ne_:: Nil)(CallMetadata.mlsFunWithEffect), rest))
    )

  def extractResTopLevel(res: Result, isTailCall: Bool, f: Result => Block, sym: Assignable, curDepth: => LocalVarSymbol) =
    sym match
    case sym: LocalVarSymbol => wrapStackSafe(Ret(res), sym, f(sym.asSimpleRef))
    case NoSymbol => wrapStackSafe(Ret(res), sym, f(Value.Lit(Tree.UnitLit(false))))

  // Rewrites anything that can contain a Call to increase the stack depth
  def transform(b: Block, curDepth: => LocalVarSymbol): Block =

    val extract = extractResTopLevel
    
    val transform = new BlockTransformer(SymbolSubst.Id):
      
      override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
        case defn: ClsLikeDefn => k(rewriteCls(defn))
        case _: FunDefn | _: ValDefn => k(defn)

      override def applyBlock(b: Block): Block = b match
        case Return(res @ HandlerLowering.EffectfulResult()) =>
          val tmp = TempSymbol(N, "res")
          super.applyResult(res): res =>
            Scoped(Set.single(tmp), extract(res, true, Return(_), tmp, curDepth))
        // Optimization to avoid generation of unnecessary variables
        case Assign(lhs, r @ HandlerLowering.EffectfulResult(), rest) =>
          super.applyResult(r): r =>
            extract(r, false, _ => applyBlock(rest), lhs, curDepth)
        case _ => super.applyBlock(b)
        
      override def applyHandler(hdr: Handler): Handler = lastWords("HandleBlock in stack safe transformation")
      
      override def applyResult(r: Result)(k: Result => Block): Block =
        r match
        case r @ HandlerLowering.EffectfulResult() =>
          val tmp = TempSymbol(N, "res")
          Scoped(Set.single(tmp), extract(r, false, k, tmp, curDepth))
        case _ => super.applyResult(r)(k)
      
      override def applyLam(lam: Lambda): Lambda = lastWords("Lambda in stack safe transformation")
  
    transform.applyBlock(b)
  
  def rewriteCls(defn: ClsLikeDefn): ClsLikeDefn = defn.parentPath match
    case Some(value) if value eq paths.contClsPath => defn
    case _ =>
      val ClsLikeDefn(owner, isym, sym, ctorSym, k, paramsOpt, auxParams,
        parentPath, methods, privateFields, publicFields, preCtor, ctor, mod, bufferable) = defn
      ClsLikeDefn(
        owner, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath,
        methods,
        privateFields,
        publicFields, 
        preCtor,
        ctor,
        mod.map(rewriteObjBody(_)),
        bufferable,
      )(defn.configOverride, defn.annotations)
  
  def rewriteObjBody(defn: ClsLikeBody): ClsLikeBody =
    ClsLikeBody(
      defn.isym,
      defn.methods,
      defn.privateFields,
      defn.publicFields,
      if config.effectHandlers.exists(_.doNotInstrumentTopLevelModCtor) then defn.ctor else transformTopLevel(defn.ctor),
      defn.annotations,
    )

  def transformTopLevel(b: Block) = transform(b, TempSymbol(N))
