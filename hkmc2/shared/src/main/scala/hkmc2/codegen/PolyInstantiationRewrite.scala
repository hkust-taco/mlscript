package hkmc2
package codegen

import scala.collection.mutable.LinkedHashMap

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


type RewrittenFunDefn = (params: Ls[ParamList], body: Block)


abstract class PolyInstantiationRewrite(val constraintSolver: FlowConstraintSolver):

  
  // ====== the abstract members ======
  // the solvers driving this rewrite
  def solvers: Iterable[FlowAnalysisSolverResult]
  
  // the rewriter for the program as seen from `instId`
  def mkRewriter(instId: InstantiationId): InstantiationRewriter
  
  // the rewriter for the main block, which may change fun defns in place
  def mkRootRewriter(rewrittenInPlace: Map[TermSymbol, RewrittenFunDefn]): InstantiationRewriter
  
  // specialized function bodies with symbols refreshed as needed
  def mkPolyFunCopy(
    original: FunDefn,
    bms: BlockMemberSymbol,
    tSym: TermSymbol,
    rewritten: RewrittenFunDefn,
  ): FunDefn
  
  // definitions this rewrite introduces besides the specialized copies
  def otherNewFunDefns: Iterable[FunDefn]
  // ====== the abstract members ======
  
  
  val collector = constraintSolver.collector
  
  given tl: TraceLogger = constraintSolver.tl
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState
  given pre: FlowPreAnalyzer = constraintSolver.preAnalyzer
  
  
  final def apply(): Program =
    if !solvers.exists(_.hasWorkToDo) then pre.pgrm
    else
      val newBody = mkNewProgramBody
      if newBody is pre.pgrm.main then pre.pgrm
      else Program(pre.pgrm.imports, newBody)
  
  val newPolyFnSyms : LinkedHashMap[InstantiationId, Map[TermSymbol, (BlockMemberSymbol, TermSymbol)]] =
    val res = LinkedHashMap.empty[InstantiationId, Map[TermSymbol, (BlockMemberSymbol, TermSymbol)]]
    def funSymsToBeCopiedAt(path: InstantiationId): Iterator[TermSymbol] =
      collector.synthesizedInstIdToFunSym.get(path) match
      case S(entry) => collector.funToSccGroups(entry).iterator.filterNot(_ is entry)
      case N => collector.funToSccGroups(path.last.getReferredFun.get).iterator
    for
      instId <- solvers.iterator.flatMap(_.polyInstIds)
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
            new TermSymbol(Fun, N, Tree.Ident(name), erasedType = f.erasedType))
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
        mkPolyFunCopy(original, bms, tSym, mkRewriter(instId).rewriteFunDefn(original))
    
    val newFuns = newPolyFuns ++ otherNewFunDefns
    
    val rewrittenInPlace = Map.from[TermSymbol, RewrittenFunDefn]:
      for (selfInstId, funSym) <- collector.synthesizedInstIdToFunSym yield
        funSym -> mkRewriter(selfInstId).rewriteFunDefn(pre.res.funSymToFunDefn(funSym))
    
    val newMainBody = Scoped(
      Set.from(newFuns.map(_.sym)),
      mkRootRewriter(rewrittenInPlace).applyBlock(pre.pgrm.main))
    
    newFuns.foldRight(newMainBody): (fdef, rest) =>
      Define(fdef, rest)
  
  end mkNewProgramBody


  // rewrites the program as seen from one instantiation path `instId`
  // helps subclass compute the symbol for the instantiated fun defns
  protected abstract class InstantiationRewriter(val instId: InstantiationId)
    extends BlockTransformer(SymbolSubst.Id):
    
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
