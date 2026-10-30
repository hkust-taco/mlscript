package hkmc2
package codegen

import scala.collection.mutable.{LinkedHashMap, Map as MutMap}

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.flowAnalysis.*
import semantics.*
import syntax.Tree
import hkmc2.syntax.Fun



abstract class FlowAnalysisSolverResult:
  def hasWorkToDo: Bool
  def polyInstIds: Iterator[InstantiationId]
end FlowAnalysisSolverResult


type RewrittenFunDefn = (signature: FunDefn.Signature, body: Block, annotations: Ls[Annot])


abstract class PolyInstantiationRewrite(val constraintSolver: FlowConstraintSolver):

  
  // ====== the abstract members ======
  // the solvers driving this rewrite
  def solvers: Iterable[FlowAnalysisSolverResult]
  
  // the subclass's rewriter
  protected type Rewriter <: InstantiationRewriter
  
  // the rewriter for the program as seen from `instId`: in place if `refreshSymbolMappingForCopy` is `N`,
  // otherwise into a copy whose symbols are refreshed by the map
  def mkRewriter(instId: InstantiationId, refreshSymbolMappingForCopy: Opt[collection.Map[Symbol, Symbol]]): Rewriter
  
  // the rewriter for the main block, which may change fun defns in place
  def mkRootRewriter(rewrittenInPlace: Map[TermSymbol, RewrittenFunDefn]): Rewriter
  
  // definitions this rewrite introduces besides the specialized copies
  def otherNewFunDefns: Iterable[FunDefn]
  
  // Updated representations of value bindings, including parameters retyped by fusion.
  def retypedVariables: LinkedHashMap[(InstantiationId, ValueSymbol), ErasedValueType]
  
  // Complete signatures after parameter removal, eta expansion, or representation changes. Copied and in-place definitions
  // must use the same convention without mutating the source symbol's write-once signature.
  def rewrittenSignatures: Map[(InstantiationId, TermSymbol), FunDefn.Signature]
  // ====== the abstract members ======
  
  
  val collector = constraintSolver.collector
  
  given tl: TraceLogger = constraintSolver.tl
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState
  given pre: FlowPreAnalyzer = constraintSolver.preAnalyzer
  
  // the instantiation id where the original definition of a root function is rewritten in place
  protected final def inPlaceInstId(fun: TermSymbol): InstantiationId =
    collector.synthesizedInstIdToFunSym.collectFirst:
      case (instId, f) if f is fun => instId
    .getOrElse(Nil)
  
  private lazy val sharedRetypedSymbols: LinkedHashMap[(InstantiationId, ValueSymbol), ValueSymbol] =
    retypedVariables.map((key, tpe) => key -> retypedSymbol(key._2, tpe))
  
  private def retypedSymbol(previous: Symbol, tpe: ErasedValueType): ValueSymbol = previous match
    case v: VarSymbol if v.erasedType.contains(tpe) => v
    case v: VarSymbol => SymbolRefresher.copyVarSymbol(v, S(tpe))
    case t: TempSymbol if t.erasedType.contains(tpe) => t
    case t: TempSymbol => SymbolRefresher.copyTempSymbol(t, S(tpe))
    case t: TermSymbol if t.erasure.contains(tpe) => t
    case t: TermSymbol => SymbolRefresher.copyTermSymbol(t, t.owner, S(tpe))
    case _ => lastWords(s"cannot give $previous the erased type $tpe")
  
  private def retypedSymbolsAt(instId: InstantiationId): Map[ValueSymbol, ValueSymbol] =
    def at(id: InstantiationId) = sharedRetypedSymbols.iterator.collect:
      case ((`id`, sym), retyped) => sym -> retyped
    (at(Nil) ++ at(instId)).toMap
  
  // Plan new parameter bindings together with their signature. Body rewriting uses the same
  // replacements; ordinary BlockTransformer parameter substitution only permits renaming.
  protected def retypedParams(instId: InstantiationId, params: Ls[LoweredParamList]): Ls[LoweredParamList] =
    val subst = SymbolRefresher.initSymbolSubst(Map.from[Symbol, Symbol](retypedSymbolsAt(instId)))
    def retype(p: Param): Param =
      val sym = subst.mapVarSym(p.sym)
      if sym is p.sym then p else p.copy(sym = sym)(p.toLoc)
    params.mapConserve: pl =>
      val params2 = pl.params.mapConserve(retype)
      val rest2 = pl.restParam.mapConserve(retype)
      if (params2 is pl.params) && (rest2 is pl.restParam) then pl
      else LoweredParamList(pl.flags, params2, rest2)(pl.toLoc)
  
  protected def signatureAt(instId: InstantiationId, fun: TermSymbol): FunDefn.Signature =
    rewrittenSignatures.get(instId -> fun).orElse(rewrittenSignatures.get(Nil -> fun))
      .getOrElse(pre.res.funSymToFunDefn(fun).signature)
  
  private lazy val rewrittenFunctionSymbols: Map[TermSymbol, TermSymbol] =
    pre.res.rootFunDefns.keysIterator.flatMap: sym =>
      val sig = signatureAt(inPlaceInstId(sym), sym)
      Option.when(sig.erasure isnt pre.res.funSymToFunDefn(sym).signature.erasure):
        sym -> SymbolRefresher.copyTermSymbol(sym, sym.owner, S(sig.erasure))
    .toMap
  
  // Nested definitions can also be rewritten in place; copied bodies override these identities below.
  private lazy val rewrittenNestedSymbols = rewrittenSignatures.collect:
    case ((instId, sym), sig) if !pre.res.rootFunDefns.contains(sym)
      && (sig.erasure isnt pre.res.funSymToFunDefn(sym).signature.erasure) =>
      (instId -> sym) -> SymbolRefresher.copyTermSymbol(sym, sym.owner, S(sig.erasure))
  
  private def nestedSymbolsAt(instId: InstantiationId): Map[TermSymbol, TermSymbol] =
    rewrittenNestedSymbols.collect { case ((id, sym), rewritten) if id == instId => sym -> rewritten }
  
  final def apply(): Program =
    if !solvers.exists(_.hasWorkToDo) then pre.pgrm
    else
      val newBody = mkNewProgramBody
      if newBody is pre.pgrm.main then pre.pgrm
      else Program(pre.pgrm.imports, newBody)
  
  lazy val newPolyFnSyms : LinkedHashMap[InstantiationId, Map[TermSymbol, (BlockMemberSymbol, TermSymbol)]] =
    val res = LinkedHashMap.empty[InstantiationId, Map[TermSymbol, (BlockMemberSymbol, TermSymbol)]]
    def funSymsToBeCopiedAt(path: InstantiationId): Iterator[TermSymbol] =
      collector.synthesizedInstIdToFunSym.get(path) match
      case S(entry) => collector.funToSccGroups(entry).iterator.filterNot(_ is entry)
      case N => collector.funToSccGroups(path.last.getReferredFun.get).iterator
    for
      // a call into an instance whose types change needs a copy even where none of its code changes,
      // as the original definition keeps the original types
      instId <- solvers.iterator.flatMap(_.polyInstIds) ++ retypedVariables.keysIterator.map(_._1) ++ rewrittenSignatures.keysIterator.map(_._1)
      path <- instId.inits
      if path.nonEmpty && !res.contains(path)
      copied = funSymsToBeCopiedAt(path)
      if copied.nonEmpty
    do
      res(path) = copied
        .map: f =>
          val name = path.mkFunName + s"$$${f.nme}"
          f -> (
            new BlockMemberSymbol(name, Nil, true),
            new TermSymbol(Fun, N, Tree.Ident(name), S(signatureAt(path, f).erasure)))
        .toMap
    res
  end newPolyFnSyms
  
  private def mkNewProgramBody: Block =
    
    val newPolyFuns =
      for
        (instId, funSymMap) <- newPolyFnSyms
        (referringFun, (bms, tSym)) <- funSymMap.toList.sortBy(_._1.uid)
      yield
        val original = pre.res.funSymToFunDefn(referringFun)
        val (signature, body, annotations) = mkCopyRewriter(instId, signatureAt(instId, referringFun).params, original.body, Map.empty).rewriteFunDefn(original)
        FunDefn(N, bms, tSym, signature, body)(original.configOverride, Annot.Private :: annotations)
    
    val newFuns = newPolyFuns ++ otherNewFunDefns
    
    val rewrittenInPlace = Map.from[TermSymbol, RewrittenFunDefn]:
      for (selfInstId, funSym) <- collector.synthesizedInstIdToFunSym yield
        funSym -> mkRewriter(selfInstId, N).rewriteFunDefn(pre.res.funSymToFunDefn(funSym))
    
    val newMainBody = Scoped(
      Set.from(newFuns.map(_.sym)),
      mkRootRewriter(rewrittenInPlace).applyBlock(pre.pgrm.main))
    
    newFuns.foldRight(newMainBody): (fdef, rest) =>
      Define(fdef, rest)
  
  end mkNewProgramBody
  
  // the rewriter of a copy of `params` and `body`, which maps symbol defined in `initMapping`
  // and refreshes symbols bound in `body` so that a copy never rebinds an original symbol
  protected final def mkCopyRewriter(instId: InstantiationId, params: Ls[LoweredParamList], body: Block, initMapping: Map[LocalVarSymbol, LocalVarSymbol]): Rewriter =
    val mapping = MutMap.from[Symbol, Symbol](initMapping)
    val walker = new SymbolRefresherWalker(mapping):
      override protected def functionSignature(fun: FunDefn): FunDefn.Signature = signatureAt(instId, fun.dSym)
    params.foreach(walker.refreshParamList)
    walker.applyBlock(body)
    for (sym, retyped) <- retypedSymbolsAt(instId).toList.sortBy(_._1.uid) do
      val tpe = retypedVariables.get(instId -> sym).orElse(retypedVariables.get(Nil -> sym)).get
      sym match
        case sym: LocalVarSymbol if initMapping.contains(sym) =>
          assert(initMapping(sym).erasedType.contains(tpe), s"$sym is mapped to ${initMapping(sym)}, which lacks its type $tpe")
        case _ => mapping.get(retyped).orElse(mapping.get(sym).map(retypedSymbol(_, tpe))).foreach: copied =>
          // A planned signature already binds the retyped parameter. References in the original
          // body still name its predecessor, so both must resolve to the same fresh binding.
          mapping(sym) = copied
    mkRewriter(instId, S(mapping))


  // rewrites the program as seen from one instantiation path `instId`: in place if `refreshSymbolMappingForCopy` is `N`,
  // otherwise into a copy whose symbols are refreshed by the map
  // helps subclass compute the symbol for the instantiated fun defns
  protected abstract class InstantiationRewriter(val instId: InstantiationId, val refreshSymbolMappingForCopy: Opt[collection.Map[Symbol, Symbol]])
    extends SymbolMapTransformer(
      Map.from[Symbol, Symbol](rewrittenFunctionSymbols)
      ++ retypedSymbolsAt(instId)
      ++ nestedSymbolsAt(Nil) ++ nestedSymbolsAt(instId)
      ++ refreshSymbolMappingForCopy.getOrElse(Map.empty)):
    
    def rewriteFunDefn(fun: FunDefn): RewrittenFunDefn
    
    extension (resId: ResultId) def concreteId = ConcreteId(resId, instId)
    
    private def newRefId(refId: ResultId, refSym: TermSymbol): InstantiationId =
      instId match
      case Nil => refId :: Nil
      case pathTo :+ called =>
        val lastRefedSymbol = called.getReferredFun.get
        val funToSccRepMap = collector.funToSccRep
        (funToSccRepMap(lastRefedSymbol), funToSccRepMap(refSym)) match
          case (S(a), S(b)) if a is b => instId
          case _ => instId :+ refId
      case _ => lastWords(s"newRefId: impossible InstantiationId shape $instId")
    
    object PolyFnRef:
      def unapply(p: Path): Opt[Value.MemberRef] = p match
        case ref@FunRef(f, _) =>
          val path = newRefId(ref.uid, f)
          for
            newSymsMap <- newPolyFnSyms.get(path)
            (bms, tSym) <- newSymsMap.get(f).orElse:
              if collector.synthesizedInstIdToFunSym.get(path).contains(f) then N
              else lastWords(s"no copy of ${f.nme} at an instantiation path of its group")
          yield
            bms.asMemberRef(tSym)
        case _ => N
  
  end InstantiationRewriter

end PolyInstantiationRewrite
