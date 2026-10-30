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


type RewrittenFunDefn = (params: Ls[LoweredParamList], body: Block, annotations: Ls[Annot])


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
  
  // Complete signatures after parameter removal or eta expansion. Copied and in-place definitions
  // must use the same convention without mutating the source symbol's write-once signature.
  def retypedFunctions: LinkedHashMap[(InstantiationId, TermSymbol), ErasedFuncSignature]
  // ====== the abstract members ======
  
  
  val collector = constraintSolver.collector
  
  given tl: TraceLogger = constraintSolver.tl
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState
  given pre: FlowPreAnalyzer = constraintSolver.preAnalyzer
  
  
  private def inPlaceInstId(fun: TermSymbol): InstantiationId =
    collector.synthesizedInstIdToFunSym.collectFirst:
      case (instId, f) if f is fun => instId
    .getOrElse(Nil)
  
  private lazy val rewrittenFunctionSymbols: Map[TermSymbol, TermSymbol] =
    pre.res.rootFunDefns.keysIterator.flatMap: sym =>
      retypedFunctions.get(inPlaceInstId(sym) -> sym).collect:
        case sig if !sym.erasedSignature.contains(sig) => sym -> SymbolRefresher.copyTermSymbol(sym, sym.owner, S(sig))
    .toMap
  
  // Nested definitions can also be rewritten in place; copied bodies override these identities below.
  private lazy val rewrittenNestedSymbols = retypedFunctions.collect:
    case ((instId, sym), sig) if !pre.res.rootFunDefns.contains(sym) =>
      (instId -> sym) -> SymbolRefresher.copyTermSymbol(sym, sym.owner, S(sig))
  
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
      instId <- solvers.iterator.flatMap(_.polyInstIds) ++ retypedFunctions.keysIterator.map(_._1)
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
            new TermSymbol(Fun, N, Tree.Ident(name), erasure =
              retypedFunctions.get(path -> f).orElse(f.erasure)))
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
        val (params, body, annotations) = mkCopyRewriter(instId, original.params, original.body, Map.empty).rewriteFunDefn(original)
        FunDefn(N, bms, tSym, params, body)(original.configOverride, Annot.Private :: annotations)
    
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
    val walker = SymbolRefresherWalker(mapping)
    params.foreach(walker.refreshParamList)
    walker.applyBlock(body)
    for
      case sym: TermSymbol <- mapping.keys.toList.sortBy(_.uid)
      sig <- retypedFunctions.get(instId -> sym).orElse(retypedFunctions.get(Nil -> sym))
      case copy: TermSymbol <- mapping.get(sym)
    do mapping(sym) = SymbolRefresher.copyTermSymbol(copy, copy.owner, S(sig))
    mkRewriter(instId, S(mapping))


  // rewrites the program as seen from one instantiation path `instId`: in place if `refreshSymbolMappingForCopy` is `N`,
  // otherwise into a copy whose symbols are refreshed by the map
  // helps subclass compute the symbol for the instantiated fun defns
  protected abstract class InstantiationRewriter(val instId: InstantiationId, val refreshSymbolMappingForCopy: Opt[collection.Map[Symbol, Symbol]])
    extends SymbolMapTransformer(
      Map.from[Symbol, Symbol](rewrittenFunctionSymbols)
      ++ rewrittenNestedSymbols.collect { case ((id, sym), rewritten) if id.isEmpty || id == instId => sym -> rewritten }
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
