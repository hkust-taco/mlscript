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


type RewrittenFunDefn = (params: Ls[LoweredParamList], body: Block)


abstract class PolyInstantiationRewrite(val constraintSolver: FlowConstraintSolver):

  
  // ====== the abstract members ======
  // the solvers driving this rewrite
  def solvers: Iterable[FlowAnalysisSolverResult]
  
  // the subclass's rewriter
  protected type Rewriter <: InstantiationRewriter
  
  // the rewriter for the program as seen from `instId`: in place if `refreshSymbolMappingForCopy` is `N`,
  // otherwise into a copy whose symbols are refreshed by the map
  def mkRewriter(instId: InstantiationId, refreshSymbolMappingForCopy: Opt[collection.Map[LocalVarSymbol, LocalVarSymbol]]): Rewriter
  
  // the rewriter for the main block, which may change fun defns in place
  def mkRootRewriter(rewrittenInPlace: Map[TermSymbol, RewrittenFunDefn]): Rewriter
  
  // definitions this rewrite introduces besides the specialized copies
  def otherNewFunDefns: Iterable[FunDefn]
  
  // updated erased value types
  def retypedVariables: LinkedHashMap[(InstantiationId, ValueSymbol), ErasedValueType]
  
  // updated erased function types
  def retypedFunctions: LinkedHashMap[(InstantiationId, TermSymbol), ErasedFuncType]
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
  
  private lazy val rewrittenFunctionSymbols: Map[TermSymbol, TermSymbol] =
    pre.res.rootFunDefns.keysIterator.flatMap: sym =>
      retypedFunctions.get(inPlaceInstId(sym) -> sym).collect:
        case tpe if !sym.erasedType.contains(tpe) => sym -> SymbolRefresher.copyTermSymbol(sym, sym.owner, S(tpe))
    .toMap
  
  private lazy val retypedLocals: LinkedHashMap[(InstantiationId, ValueSymbol), ErasedType] =
    LinkedHashMap.from[(InstantiationId, ValueSymbol), ErasedType](retypedVariables) ++ retypedFunctions.filterNot: (key, _) =>
      pre.res.rootFunDefns.contains(key._2)
  
  private lazy val sharedRetypedSymbols: LinkedHashMap[(InstantiationId, ValueSymbol), ValueSymbol] =
    retypedLocals.map((key, tpe) => key -> retypedSymbol(key._2, tpe))
  
  private def retypedSymbol(previous: Symbol, tpe: ErasedType): ValueSymbol = (previous, tpe) match
    case (v: VarSymbol, _) if v.erasedType.contains(tpe) => v
    case (v: VarSymbol, tpe: ErasedValueType) => SymbolRefresher.copyVarSymbol(v, S(tpe))
    case (t: TempSymbol, _) if t.erasedType.contains(tpe) => t
    case (t: TempSymbol, _) => SymbolRefresher.copyTempSymbol(t, S(tpe))
    case (t: TermSymbol, _) if t.erasedType.contains(tpe) => t
    case (t: TermSymbol, _) => SymbolRefresher.copyTermSymbol(t, t.owner, S(tpe))
    case _ => lastWords(s"cannot give $previous the erased type $tpe")
  
  
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
      instId <- solvers.iterator.flatMap(_.polyInstIds) ++ retypedVariables.keysIterator.map(_._1) ++ retypedFunctions.keysIterator.map(_._1)
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
            new TermSymbol(Fun, N, Tree.Ident(name), erasedType = retypedFunctions.get(path -> f).orElse(f.erasedType)))
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
        val (params, body) = mkCopyRewriter(instId, original.params, original.body, Map.empty).rewriteFunDefn(original)
        FunDefn(N, bms, tSym, params, body)(original.configOverride, Annot.Private :: original.annotations)
    
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
      case sym: ValueSymbol <- mapping.keys.toList.sortBy(_.uid)
      tpe <- retypedLocals.get(instId -> sym).orElse(retypedLocals.get(Nil -> sym))
    do sym match
      case sym: LocalVarSymbol if initMapping.contains(sym) =>
        assert(initMapping(sym).erasedType.contains(tpe), s"$sym is mapped to ${initMapping(sym)}, which lacks its type $tpe")
      case _ => mapping(sym) = retypedSymbol(mapping(sym), tpe)
    mkRewriter(instId, S(mapping.asInstanceOf[collection.Map[LocalVarSymbol, LocalVarSymbol]]))


  // rewrites the program as seen from one instantiation path `instId`: in place if `refreshSymbolMappingForCopy` is `N`,
  // otherwise into a copy whose symbols are refreshed by the map
  // helps subclass compute the symbol for the instantiated fun defns
  protected abstract class InstantiationRewriter(val instId: InstantiationId, val refreshSymbolMappingForCopy: Opt[collection.Map[LocalVarSymbol, LocalVarSymbol]])
    extends SymbolMapTransformer(
      Map.from[Symbol, Symbol](rewrittenFunctionSymbols)
      ++ sharedRetypedSymbols.collect { case ((id, sym), retyped) if id.isEmpty || id == instId => sym -> retyped }
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
