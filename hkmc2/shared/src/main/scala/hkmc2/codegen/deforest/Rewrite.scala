package hkmc2
package codegen
package deforest

import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap}
import hkmc2.syntax.{ImmutVal, MutVal, LetBind, HandlerBind, ParamBind, Fun, Ins}



class DeforestRewriter(val solver: DeforestConstrainSolver):
  import solver.FinalDest
  given tl: TraceLogger = solver.tl
  given dState: Deforest.State = solver.dState
  given eState: Elaborator.State = solver.collector.elabState
  given pre: DeforestPreAnalyzer = solver.preAnalyzer
  
  private val _symSubst = new SymbolSubst()
  
  // C(1, 2)
  //  ~> let x = 1; y = 2 in (fvs) => branchBody(fvs, x, y)
  // if scrut is C then let a = scrut.x; b = scrut.y in body
  //  ~> scrut(fvs)
  //  ~> fun branchBody(fvs, x, y) = let a = x; b = y in body
  
  type BranchId = CtorDtorId -> Opt[CtorCls]
  
  val ctorFieldSyms = MutMap.empty[CtorDtorId, Ls[TempSymbol]] // the `a` and `b`
  val newPolyFnSyms = MutMap.empty[InstantiationId, (BlockMemberSymbol, TermSymbol)]
  val branchSelSyms = MutMap.empty[CtorDtorId, VarSymbol]
  val ctorWhichBranch = MutMap.empty[CtorDtorId, BranchId]
  val branchFnSyms = MutMap.empty[BranchId, (BlockMemberSymbol, TermSymbol)]
  
  // just so that we don't need to look up later
  private val branchBodies = MutMap.empty[ResultId -> Opt[CtorCls], Block]
  
  // compute new symbols
  locally {
    for (ctor, FinalDest(dest, sels)) <- solver.finalCtorDests do
      // create ctor field syms
      val ctorInfo = solver.fusingIdInfo(ctor).asInstanceOf[Ctor]
      ctorFieldSyms(ctor) =
        val clsNme = ctorInfo.ctor match
          case n: Int => s"tup$n"
          case c: (ClassSymbol | ModuleOrObjectSymbol) => c.name
        ctorInfo.args.unzip._1.map:
          case termSym: TermSymbol => new TempSymbol(N, s"${clsNme}_${termSym.nme}")
          case n: Int => new TempSymbol(N, s"${clsNme}_$n")
      // create poly fun syms
      for case ctorInstId@(referringTo :: _) <- List(ctor.instId, dest.instId) do
        newPolyFnSyms.getOrElseUpdate(
          ctorInstId,
          new BlockMemberSymbol(ctorInstId.mkFunName, Nil, true) ->
          new TermSymbol(Fun, N, Tree.Ident(ctorInstId.mkFunName)))
      // create branch sel syms
      for sel <- sels do
        branchSelSyms.getOrElseUpdate(
          sel,
          locally:
            val selInfo = solver.fusingIdInfo(sel).asInstanceOf[FieldSel]
            val clsNme = selInfo.isSelFromCls match
              case cls: ClassSymbol => cls.name
              case n: Int => s"tup$n"
            selInfo.field match
              case termSym: TermSymbol => new VarSymbol(Tree.Ident(s"${clsNme}_${termSym.nme}"))
              case ith: Int => new VarSymbol(Tree.Ident(s"${clsNme}_$ith"))
        )
      // identify branch for a ctor
      // keep track of the branch body for later use
      // create branch func syms
      val matchBlk = pre.res.matchScrutToMatchBlock(dest._1)
      val (whichBranch, whichBranchBody) =
        val tmp =
          val ctorCls = ctorInfo.ctor
          matchBlk.arms
            .find: (cse, _) =>
              cse match
              case Case.Cls(cls, path) => cls === ctorCls
              case Case.Tup(len, inf) => len === ctorCls
              case _ => die
            .map(b => ctorCls -> b._2)
        tmp.map(_._1) ->
        Begin(tmp.fold(matchBlk.dflt.get)(_._2), pre.res.getFullRestOfMatch(dest._1))
      ctorWhichBranch(ctor) = dest -> whichBranch
      branchBodies(dest._1 -> whichBranch) = whichBranchBody
      branchFnSyms.getOrElseUpdate(
        dest -> whichBranch,
        locally:
          val branchName = whichBranch.fold("_dflt"):
            case n: Int => s"_$n"
            case cls: ClassLikeSymbol => s"_${cls.nme}"
          val scrutName = dest._1.getReferredSym.nme
          val branchFnNme = s"$scrutName$branchName"
          (new BlockMemberSymbol(branchFnNme, Nil, true),
          new TermSymbol(Fun, N, Tree.Ident(branchFnNme)))
      )
  }

  // TODO: rewrite the program first, then refersh symbols (skip those new ones)
  
  // private class Rewriter(instId: InstantiationId) extends BlockTransformer(_symSubst):
  //   override def applyResult(r: Result)(k: Result => Block): Block =
  //     r match
  //     case ref@FunRef(f) if newPolyFuncs.isDefinedAt(ref.uid :: instId) =>
  //       val (bms, tSym) = newPolyFuncs(ref.uid :: instId)
  //       k(Value.Ref(bms, S(tSym)))
  //     case ctor@CtorCall(cls, args) if solver.finalCtorDests.isDefinedAt() =>
        
        
  
  
  
  
  
  
  for (instId, bms) <- newPolyFnSyms do
    tl.log(bms)
end DeforestRewriter

