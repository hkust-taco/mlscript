package hkmc2
package codegen
package deforest

import utils.*
import hkmc2.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap, LinkedHashSet, Buffer}
import hkmc2.syntax.Fun
import hkmc2.codegen.flowAnalysis.*



class DeforestRewriter(val solver: DeforestFusionSolver, additionalTopLevelSymbols: Set[LocalVarSymbol])(using Raise, Config, Elaborator.Ctx)
  extends PolyInstantiationRewrite(solver.constraintSolver):
  
  type MatchOrLabelId = ResultId | LabelSymbol
  // The producer determines the branch closure's field parameters even when several producers
  // select the same default body. Different constructor layouts cannot share that closure.
  type BranchId = CtorDtorId -> CtorCls
  type LabelId = LabelSymbol -> InstantiationId
  type RestFunId = CtorDtorId | LabelId
  
  extension (restFunId: RestFunId) def withoutInstId: MatchOrLabelId =
    restFunId match
    case ConcreteId(exprId, instId) => exprId
    case l: LabelId => l._1
  extension (restFunId: RestFunId) def getInstId = restFunId match
    case ConcreteId(exprId, instId) => instId
    case l: LabelId => l._2
  extension (matchOrLabelId: MatchOrLabelId) def withInstId(instId: InstantiationId): RestFunId =
    matchOrLabelId match
    case l: LabelSymbol => l -> instId
    case scrutId: ResultId => ConcreteId(scrutId, instId)
  extension (vs: Ls[VarSymbol]) def asParamList: LoweredParamList =
    LoweredParamList(ParamListFlags.empty, vs.map(Param.simple), N)(N)
  extension (c: CtorCls) def ctorClsName: String = c match
    case cls: ClassLikeSymbol => cls.nme
    case n: Int => s"tup$n"
  extension (f: SelField) def fieldName: String = f match
    case tSym: TermSymbol => tSym.nme
    case n: Int => n.toString

  
  private def isFused(p: ProdStrat): Bool = p match
    case c: Ctor => solver.finalCtorDests.contains(c.concreteId)
    case _: (ProdFun | MarkerProdStrat) => false
    case _: StratVar => lastWords("unexpected strat var")

  private def producersOf(values: ProdStrat): Ls[ProdStrat] = values match
    case v: StratVar => v.lowerBounds.toList
    case p => p :: Nil
  
  // compute the updated erased type of a local variable, a function param or a function return,
  // using all the concrete producers that flows into that slot
  private def slotTypeFromFlow(producers: Ls[ProdStrat], declared: Opt[ErasedValueType]): Opt[ErasedValueType] =
    def go(producers: Ls[ProdStrat], declared: Opt[ErasedValueType], seen: Set[Ctor]): Opt[ErasedValueType] =
      def producerType(p: ProdStrat): Opt[ErasedValueType] = p match
        case c: Ctor => solver.finalCtorDests.get(c.concreteId) match
          case S(_: FinalDestMatch) => S(ErasedType.Function(S(false)))
          case S(FinalDestSel(_, field)) =>
            val fieldType =
              if seen(c) then field.erasedFieldType
              else go(producersOf(c.args.find(_._1 == field).get._2), field.erasedFieldType, seen + c)
            S(fieldType.getOrElse(ErasedType.Unknown))
          case N => S(c.allocatedType)
        case _: ProdFun => S(ErasedType.Function(S(false)))
        case UnknownProd => N
        case _: StratVar => lastWords("unexpected strat var")
      val types = producers.map(producerType)
      if types.forall(_.isEmpty) then declared
      else S(ErasedType.Union.mk(types.map(_.orElse(declared).getOrElse(ErasedType.Unknown))))
    go(producers, declared, Set.empty)

  // N when the existing slot keeps its declaration, as no fused value reaches it
  private def retypedSlotType(producers: Ls[ProdStrat], declared: Opt[ErasedValueType]): Opt[ErasedValueType] =
    if producers.exists(isFused) then slotTypeFromFlow(producers, declared) else N

  // A proved cast can disappear when fusion changes its operand's representation.
  // Keep other casts: even a check known to succeed can still narrow a physical anyref
  // slot for Wasm. Unknown/failing casts expose their inputs and therefore prevent fusion.
  private val fusedCasts = constraintSolver.castsWithSrcs.iterator.collect:
    case c if c.succeeds && c.sources.exists(isFused) => c.concreteId
  .toSet

  private def getParentLabelOrMatchesAndRestBefore(
    matchOrLabelId: MatchOrLabelId
  ): (Iterator[Label | Match], Block) =
    val ctx = matchOrLabelId match
      case label: LabelSymbol => pre.res.labelSymToCtxOfLabel(label)
      case dtorId: ResultId => pre.res.matchScrutToCtxOfMatch(dtorId)
    val simpleRest = matchOrLabelId match
      case label: LabelSymbol => pre.res.labelSymToLabelBlk(label).rest
      case dtorId: ResultId => pre.res.matchScrutToMatchBlock(dtorId).rest
    def it = ctx.iterator
      .takeWhile:
        case _: (pre.InCtx.Fn | pre.InCtx.ModCtor | pre.InCtx.Cls | pre.InCtx.ClsPreCtor | pre.InCtx.ClsCtor | pre.InCtx.TopLvl) => false
        case _ => true
      .collect:
        case pre.InCtx.LblBody(l) => l
        case pre.InCtx.MtchBody(m, _) => m
        case pre.InCtx.BegnBody(b) => b
    val blockUntilParent = it
      .takeWhile(_.isInstanceOf[Begin])
      .collect:
        case b: Begin => b.rest
      .foldLeft(simpleRest)(Begin.apply)
    val parents = it
      .collect:
        case l: Label => l
        case m: Match => m
      .asInstanceOf[Iterator[Label | Match]]
    parents -> blockUntilParent

  private val PrivateModifier = Annot.Modifier(syntax.Keyword.`private`)(N)
  private val AffineAnnotForBranchFns = Annot.Affine(1)(N)
  
  val branchSelSyms = MutMap.empty[CtorDtorId, VarSymbol]
  // branch fun params for fields (which share the same symbol in `branchSelSyms`)
  val branchFunParamFieldSyms = MutMap.empty[BranchId, Ls[VarSymbol]]
  val ctorWhichBranch = MutMap.empty[CtorDtorId, BranchId]
  
  // Symbols of branch functions
  // the content of those functions should be
  // `<computation of the branch>; return match_rest(...)`
  val branchFunSyms = LinkedHashMap.empty[BranchId, (BlockMemberSymbol, TermSymbol)]
  
  // Symbols of rest functions for relevant matches or labels.
  // 1) Matches that will be fused or
  // 2) Matches or Labels that properly nest other fusing matches
  // should get their "rest"s extracted as functions,
  // and the content of those functions should be
  // `<computation of rests up to a parent>; return parent_rest(...)`
  val restFunSyms = LinkedHashMap.empty[RestFunId, (BlockMemberSymbol, TermSymbol)]
  
  // original bodies of a branch
  val branchOriginalBodies = MutMap.empty[ResultId -> CtorCls, Block]
  // original rest function bodies and their parent matches (if any)
  val restOriginalBodiesAndParentRest = MutMap.empty[MatchOrLabelId, Block -> Opt[MatchOrLabelId]]
  
  // compute new symbols for branch body functions and rest functions
  locally {
    for case (ctor, finalDest) <- solver.finalCtorDests do
      finalDest match
      case FinalDestSel(dtors, field) => ()
      case FinalDestMatch(dest, sels) =>
        val ctorInfo = solver.fusingCtorInfo(ctor)
        // create branch sel syms
        val fieldSym = MutMap.empty[SelField, VarSymbol]
        for sel <- sels.toList.sortBy(_._1.uid) do
          branchSelSyms.getOrElseUpdate(
            sel,
            locally:
              val selInfo = solver.fusingDtorInfo(sel).asInstanceOf[FieldSel]
              val clsNme = selInfo.selectsFrom.ctorClsName
              fieldSym.getOrElseUpdate(
                selInfo.field,
                new VarSymbol(Tree.Ident(s"${clsNme}_${selInfo.field.fieldName}")))
          )
        
        // ctor dest branch function computations
        val whichBranch = ctorInfo.ctor
        val whichBranchPreBody =
          solver.selectedBranch(ctorInfo.ctor, dest).getOrElse(
            lastWords("Fusion requires a statically determined match branch"))
        val destBranchId: BranchId = dest -> whichBranch
        // identify the dest branchid for a ctor
        ctorWhichBranch(ctor) = destBranchId
        // compute the function symbols for branch funs
        branchFunSyms.getOrElseUpdate(
          destBranchId,
          locally:
            val branchName = s"_${whichBranch.ctorClsName}"
            val scrutName = dest._1.getReferredSym.nme
            val branchFnNme = s"${dest.instId.mkFunName}$$$scrutName$branchName"
            new BlockMemberSymbol(branchFnNme, Nil, true)
            -> new TermSymbol(Fun, N, Tree.Ident(branchFnNme))
        )
        // compute the function parameters corresponding to ctor fields of branch funs
        branchFunParamFieldSyms.getOrElseUpdate(
          destBranchId,
          locally:
            val completeArgs: Ls[SelField] = ctorInfo.args.unzip._1
            val selsInfos: Map[SelField, CtorDtorId] = sels
              .iterator
              .map: sel =>
                solver.fusingDtorInfo(sel).asInstanceOf[FieldSel].field -> sel
              .toMap
            completeArgs.map: selField =>
              selsInfos.get(selField) match
              case Some(selId) => branchSelSyms(selId)
              case None => VarSymbol(Tree.Ident(s"_${selField.fieldName}"))
        )
        
        val (parents, _) = getParentLabelOrMatchesAndRestBefore(dest.exprId)
        for needRest <- Iterator.single(pre.res.matchScrutToMatchBlock(dest._1)) ++ parents do
          val (matchOrLabelId, nme): MatchOrLabelId -> Str = needRest match
            case Match(scrut, arms, dflt, rest) => scrut.uid -> scrut.uid.getReferredSym.nme
            case Label(label, loop, body, rest) => label -> label.nme
          val restFunId = matchOrLabelId.withInstId(dest.instId)
          restFunSyms.getOrElseUpdate(
            restFunId,
            locally:
              val restFunName = dest.instId.mkFunName + s"$$${nme}_rest"
              new BlockMemberSymbol(restFunName, Nil, true)
              -> new TermSymbol(Fun, N, Tree.Ident(restFunName))
          )
          val (ps, restBeforeParent) = getParentLabelOrMatchesAndRestBefore(matchOrLabelId)
          restOriginalBodiesAndParentRest.getOrElseUpdate(
            matchOrLabelId,
            restBeforeParent
            -> ps.nextOption().map:
              case Match(scrut, arms, dflt, rest) => scrut.uid
              case Label(label, loop, body, rest) => label
          )
        
        // compute the complete deforestable branch body of a fusing match
        branchOriginalBodies.getOrElseUpdate(
          dest._1 -> whichBranch,
          whichBranchPreBody
        )
  }
  
  // compute free vars after we know new symbols
  val dtorBranchFnFvs = MutMap.empty[CtorDtorId, Ls[LocalVarSymbol]]
  val restFnFvs = MutMap.empty[RestFunId, Ls[LocalVarSymbol]]
  locally {
    val allBranchesOfDtor = branchFunSyms.keys.groupBy(_._1)
    extension (b: Block)
      // ctx should be the branch fun parameters corresponding to ctor fields 
      def deforestFreeVars(
        ctx: collection.Set[LocalVarSymbol],
        instId: InstantiationId
      ): LinkedHashSet[LocalVarSymbol] =
        val traverser = new FreeVarTraverser(ctx, instId)
        traverser.applyBlock(b)
        traverser.freeVars
        
    class FreeVarTraverser(ctx: collection.Set[LocalVarSymbol], instId: InstantiationId) extends BlockTraverser:
      extension (resId: ResultId) def concreteId = ConcreteId(resId, instId)
      val inCtx = MutSet.from[LocalVarSymbol]:
        ctx
        ++ (eState.runtimeSymbol :: Nil : Ls[LocalVarSymbol])
        ++ pre.pgrm.main.match
          case Scoped(syms, _) => syms.iterator.collect{case s: LocalVarSymbol => s}
          case _ => Nil
        // for diff tests
        ++ additionalTopLevelSymbols
      val freeVars = LinkedHashSet.empty[LocalVarSymbol]
      
      private def handleTrackableSel(s: Result) =
        val toBeSubstSymbol = branchSelSyms(s.uid.concreteId)
        if !inCtx(toBeSubstSymbol) then freeVars.add(toBeSubstSymbol)
      
      override def applyValue(v: Value): Unit =
        v match
        case Value.SimpleRef(l) =>
          l match
          case l: LocalVarSymbol => if !inCtx(l) then freeVars.add(l)
          case _: BuiltinSymbol => super.applyValue(v)
        case _ => super.applyValue(v)
      
      override def applyResult(r: Result): Unit =
        r match
        case s@TrackableSelect(_, _, _) if branchSelSyms.isDefinedAt(s.uid.concreteId) =>
          handleTrackableSel(s)
        case Lambda(params, body) =>
          for p <- params.allParams do inCtx.add(p.sym)
          applyBlock(body)
          for p <- params.allParams do inCtx.remove(p.sym)
        case _ => super.applyResult(r)
      
      override def applyPath(p: Path): Unit =
        p match
        case s@TrackableSelect(_, _, _) if branchSelSyms.isDefinedAt(s.uid.concreteId) =>
          handleTrackableSel(s)
        case _ => super.applyPath(p)
      
      override def applyBlock(b: Block): Unit =
        b match
        case m: Match if solver.finalDtorSrcs.isDefinedAt(m.scrut.uid.concreteId) =>
          for
            fv <- fvsForDtor(m.scrut.uid.concreteId)
            if !inCtx(fv)
          do freeVars.add(fv)
          super.applyPath(m.scrut)
        case Assign(lhs: LocalVarSymbol, rhs, rest) =>
          if !inCtx(lhs) then freeVars.add(lhs)
          applyResult(rhs)
          applyBlock(rest)
        case Scoped(syms, body) =>
          for case s: LocalVarSymbol <- syms do inCtx.add(s)
          applyBlock(body)
          for case s: LocalVarSymbol <- syms do inCtx.remove(s)
        case _ => super.applyBlock(b)
      
      override def applyDefn(defn: Defn): Unit =
        softAssert(false, s"deforestation copying the definition ${defn.sym.nme}")
    end FreeVarTraverser
    
    def fvsForDtor(dtorId: CtorDtorId): Ls[LocalVarSymbol] =
      dtorBranchFnFvs.get(dtorId) match
      case Some(fvs) => fvs
      case None =>
        val fvsOfBranches = LinkedHashSet.empty[LocalVarSymbol]
        for branchId <- allBranchesOfDtor(dtorId) do
          fvsOfBranches.addAll:
            branchOriginalBodies(branchId._1._1 -> branchId._2)
              .deforestFreeVars(
                branchFunParamFieldSyms(branchId).toSet,
                branchId._1._2)
        val fvsOfRest = fvsForRest(dtorId)
        val fvs = fvsOfBranches.addAll(fvsOfRest).toList
        dtorBranchFnFvs(dtorId) = fvs
        fvs
    
    def fvsForRest(restFunId: RestFunId): Ls[LocalVarSymbol] =
      restFnFvs.get(restFunId) match
      case Some(fvs) => fvs
      case None =>
        val instId = restFunId.getInstId
        val (restBody, parentRest) = restOriginalBodiesAndParentRest(restFunId.withoutInstId)
        val fvOfRestBody = restBody.deforestFreeVars(Set.empty, restFunId.getInstId)
        val fvOfRestParent = parentRest.fold(List.empty)(pr => fvsForRest(pr.withInstId(instId)))
        val fvs = (fvOfRestBody.iterator ++ fvOfRestParent.iterator.filterNot(fvOfRestBody)).toList
        restFnFvs(restFunId) = fvs
        fvs
    
    allBranchesOfDtor.keysIterator.foreach(fvsForDtor)
  }

  // update the correct new erased type info to the new symbols before rewriting bodies that refer to them.
  // we do this after information like free variables are computed, as those are needed for branch function types
  locally {
    for (branchId, params) <- branchFunParamFieldSyms do
      val ctors = ctorWhichBranch.iterator.collect:
        case (id, branch) if branch == branchId => solver.fusingCtorInfo(id)
      .toList
      params.zipWithIndex.foreach: (param, index) =>
        val types = ctors.map: ctor =>
          val (field, prod) = ctor.args(index)
          slotTypeFromFlow(producersOf(prod), field.erasedFieldType)
        param.erasedType = if types.forall(_.isEmpty) then N
          else S(ErasedType.Union.mk(types.map(_.getOrElse(ErasedType.Unknown))))
    for (branchId, (_, sym)) <- branchFunSyms do
      sym.erasedType = S(ErasedType.FuncRef(S(false),
        branchFunParamFieldSyms(branchId).map(_.erasedType) ::
          dtorBranchFnFvs(branchId._1).map(s => retypedVariables.get(branchId._1.instId -> s).orElse(s.mapErasedValueType))
          :: Nil, N))
    for (restId, (_, sym)) <- restFunSyms do
      sym.erasedType = S(ErasedType.FuncRef(S(false),
        restFnFvs(restId).map(s => retypedVariables.get(restId.getInstId -> s).orElse(s.mapErasedValueType)) :: Nil, N))
  }

  // Rewrites the program under a specific instantiation id
  // from the polymorphic analysis
  protected class Rewriter(instId: InstantiationId, refreshSymbolMappingForCopy: Opt[collection.Map[LocalVarSymbol, LocalVarSymbol]]) extends InstantiationRewriter(instId, refreshSymbolMappingForCopy):
    
    // the result slot of the function whose body is being rewritten
    private type SlotType = (original: Opt[ErasedValueType], retyped: Opt[ErasedValueType])
    private var returnType: SlotType = (N, N)
    private def returningInto[A](tpe: SlotType)(rewrite: => A): A =
      val enclosing = returnType
      returnType = tpe
      try rewrite finally returnType = enclosing
    
    def rewriteFunDefn(fun: FunDefn): RewrittenFunDefn =
      val declared = fun.dSym.declaredResultType
      fun.params.mapConserve(applyParamList) ->
        returningInto(declared -> retypedFunctions.get(instId -> fun.dSym).fold(declared)(_.ret)):
          applyBlock(fun.body)
    
    override def applyFunDefn(fun: FunDefn): FunDefn =
      returningInto(fun.dSym.declaredResultType -> fun.dSym.subst.declaredResultType):
        super.applyFunDefn(fun)
    
    // the callee is a closure or an extracted function, whose results are unknown, so like any call to a
    // function value, the result is cast into the slot that the replaced `return`s wrote
    private def returnCall(call: Result): Block = Return(returnType.retyped.fold(call)(call.coerceTo(_, N)))
    
    // a slot that fusion retypes takes the type the flow gives it
    // the flow analysis proves the value has the slot's type, so the cast should never fail
    private def intoRetypedSlot[R <: Result](r: R, slot: SlotType)(k: (R | Path) => Block): Block =
      if slot.retyped == slot.original then k(r)
      else coerceIntoFlowTypedSlot(r, slot.retyped.getOrElse(ErasedType.Unknown))(k)
    
    // as the flow proves that a value reaching a slot typed from the flow has the slot's type, a value whose type is
    // unrelated to it is never produced (it is read in a dead branch, or is the result of a call that never
    // returns): its effects are kept, and `undefined` stands in for it
    private def coerceIntoFlowTypedSlot[R <: Result](r: R, tpe: ErasedType)(k: (R | Path) => Block): Block =
      r.coerceToOr(tpe, N)(k): (_, _) =>
        Assign.discard(r, k(Value.Lit(Tree.UnitLit(false))(N).coerceTo(tpe, N)))
    
    // calls `fun` with possibly remapped `args`
    def mkCall(fun: Path, args: Ls[LocalVarSymbol])(k: Result => Block): Block =
      applyArgs(args.map(s => Arg(N, s.asPath))): args2 =>
        k(Call(fun, args2 ne_:: Nil)(CallMetadata.defaultMlsFun, N))
    
    override def applyResult(r: Result)(k: Result => Block): Block =
      r match
      case c: Cast if fusedCasts(c.uid.concreteId) => applyResult(c.value)(k)
      case s@TrackableSelect(from, _, _) =>
        if branchSelSyms.isDefinedAt(s.uid.concreteId) then
          k(branchSelSyms(s.uid.concreteId).subst.asSimpleRef)
        else if solver.finalDtorSrcs.contains(s.uid.concreteId) then
          applyPath(from)(k)
        else
          super.applyResult(r)(k)
      case ctor@CtorProducer(cls, args, _) =>
        def mkCtorFieldSyms(ctorDtorId: CtorDtorId): Ls[TempSymbol] =
          val ctorInfo = solver.fusingCtorInfo(ctorDtorId)
          val clsNme = ctorInfo.ctor.ctorClsName
          ctorInfo.args.map: (field, prod) =>
            new TempSymbol(N, erasedType = slotTypeFromFlow(producersOf(prod), field.erasedFieldType), s"${clsNme}_${field.fieldName}")
        end mkCtorFieldSyms
        
        def fillFieldSyms(fieldSyms: Ls[TempSymbol], after: Block): Block =
          args.zip(fieldSyms).foldRight(after):
            case (Arg(N, a) -> fieldSym, rest) =>
              applyPath(a): fusedField =>
                coerceIntoFlowTypedSlot(fusedField, fieldSym.erasedType.getOrElse(ErasedType.Unknown)): value =>
                  Scoped(Set.single(fieldSym), Assign(fieldSym, value, rest))
            case _ => TODO("spread args are not supported")
        
        solver.finalCtorDests.get(ctor.uid.concreteId) match
        case None => super.applyResult(ctor)(k)
        case Some(FinalDestSel(_, field)) =>
          val ctorInfo = solver.fusingCtorInfo(ctor.uid.concreteId)
          val idx = ctorInfo.args.unzip._1.indexOf(field)
          val fieldSyms = mkCtorFieldSyms(ctor.uid.concreteId)
          fillFieldSyms(fieldSyms, k(fieldSyms(idx).asSimpleRef))
        case Some(_: FinalDestMatch) =>
          val fieldSyms = mkCtorFieldSyms(ctor.uid.concreteId)
          val (branchFunBms, branchFunTSym) = branchFunSyms(ctorWhichBranch(ctor.uid.concreteId))
          fillFieldSyms(fieldSyms, mkCall(branchFunBms.asMemberRef(branchFunTSym), fieldSyms)(k))
      case c @ Call(FunRef(f, _), _) => super.applyResult(c):
        // a copy that fusion does not retype keeps `f.erasedType` itself, even where that type is stale
        case Call(fun2 @ FunRef(f2, _), argss2) if f2.erasedType != f.erasedType =>
          // TODO: `original` should probably be `f.erasedType`'s parameter lists,
          // but the lifter does not seem to update type correctly now
          val original = pre.res.funSymToFunDefn(f).params.map(_.params.map(_.sym.erasedType))
          val retyped = f2.erasedType match
            case S(ft: ErasedFuncType) => ft.paramLists
            case _ => Nil
          val slotss = original.iterator.zip(retyped).map(_.iterator.zip(_))
          // truncating `slotss` only drops the lists a partial application leaves unapplied
          val argss3 = argss2.iterator.zip(slotss).map: (args, slots) =>
            if args.exists(_.spread.isDefined) then args.map(_ -> N)
            else args.map(_ -> slots.nextOption())
          .toList
          applyListOf(argss3, applyListOf(_, (arg, k2) => arg match
            case (a, S(slot)) => intoRetypedSlot(a.value, slot)(value => k2(Arg(N, value) -> N))
            case _ => k2(arg)
          )(_)): argss4 =>
            k(Call(fun2, argss4.map(_.map(_._1)).ne_!)(c.metadata, c.toLoc))
        case c2 => k(c2)
      case _ => super.applyResult(r)(k)
    
    override def applyPath(p: Path)(k: Path => Block): Block =
      p match
      case PolyFnRef(specializedRef) => k(specializedRef)
      case c: Cast if fusedCasts(c.uid.concreteId) =>
        applyResult(c.value):
          case p: Path => k(p)
          case r =>
            val tmp = TempSymbol(N, r.erasedValueType, "fused")
            Scoped(Set.single(tmp), Assign(tmp, r, k(tmp.asPath)))
      case ctor@CtorProducer(_, args, _) if solver.finalCtorDests.isDefinedAt(ctor.uid.concreteId) =>
        assert(args.isEmpty)
        val (branchFunBms, branchFunTSym) = branchFunSyms(ctorWhichBranch(ctor.uid.concreteId))
        mkCall(branchFunBms.asMemberRef(branchFunTSym), Nil): callBranchFun =>
          val lambdaSym = new TempSymbol(N, erasedType = callBranchFun.erasedValueType, "deforest$lam")
          Scoped(
            Set.single(lambdaSym),
            Assign(
              lambdaSym,
              callBranchFun,
              k(lambdaSym.asSimpleRef)
          ))
      case s@TrackableSelect(from, _, _) =>
        if branchSelSyms.isDefinedAt(s.uid.concreteId) then
          k(branchSelSyms(s.uid.concreteId).subst.asSimpleRef)
        else if solver.finalDtorSrcs.contains(s.uid.concreteId) then
          applyPath(from)(k)
        else
          super.applyPath(s)(k)
      case _ => super.applyPath(p)(k)
    
    // a free block member symbol of an extracted part becomes an `fv_` parameter, which needs a different node
    override def applyValue(v: Value)(k: Value => Block): Block = v match
      case Value.This(l) if refreshSymbolMappingForCopy.isDefined =>
        pre.res.modSymToBms.get(l) match
        case S(bms) => k(bms.asMemberRef(l.asMod.get))
        case N => super.applyValue(v)(k)
      case _ => super.applyValue(v)(k)
      
    override def applyBlock(b: Block): Block =
      b match
      case m@Match(scrut, _, _, _) if solver.finalDtorSrcs.isDefinedAt(scrut.uid.concreteId) =>
        applyPath(scrut): newScrut =>
          mkCall(newScrut, dtorBranchFnFvs(scrut.uid.concreteId))(returnCall)
      case Assign(l: LocalVarSymbol, r, rst) =>
        applyResult(r): r2 =>
          val l2 = applyAssignLhs(l)
          val slot = l2 match
            case l2: LocalVarSymbol => (l.mapErasedValueType, l2.mapErasedValueType)
            case NoSymbol => (N, N)
          intoRetypedSlot(r2, slot): r3 =>
            val rst2 = applySubBlock(rst)
            if (l2 is l) && (r3 is r) && (rst2 is rst) then b else Assign(l2, r3, rst2)
      case Return(res) =>
        applyResult(res): res2 =>
          intoRetypedSlot(res2, returnType): res3 =>
            if res3 is res then b else Return(res3)
      case Break(label) =>
        val labelRestFunId = label.withInstId(instId)
        restFunSyms.get(labelRestFunId) match
        case None => super.applyBlock(b)
        case Some((bms, tSym)) =>
          mkCall(bms.asMemberRef(tSym), restFnFvs(labelRestFunId))(returnCall)
      // copying a definition would need fresh symbols for it; lifting removes the nested ones beforehand
      case Define(defn, _) if refreshSymbolMappingForCopy.isDefined =>
        softAssert(false, s"deforestation copying the definition ${defn.sym.nme}")
        b
      case Label(sym, true, _, _) if refreshSymbolMappingForCopy.isDefined =>
        softAssert(false, s"unsupported loop $sym during rewriting")
        b
      case Continue(sym) if refreshSymbolMappingForCopy.isDefined =>
        softAssert(false, s"unsupported `continue` to $sym during rewriting")
        b
      case _ => super.applyBlock(b)
  end Rewriter
  

  
  // ====== start: implements the abstract members of `PolyInstantiationRewrite` ======
  def solvers: Iterable[FlowAnalysisSolverResult] = solver :: Nil
  
  def mkRewriter(instId: InstantiationId, refreshSymbolMappingForCopy: Opt[collection.Map[LocalVarSymbol, LocalVarSymbol]]) = new Rewriter(instId, refreshSymbolMappingForCopy)
  
  def otherNewFunDefns: Iterable[FunDefn] =
    
    // the rewriter of an extracted part (branch body functions and match rest functions),
    // whose free variables `fvs` become the `fv_` parameters it returns
    def mkExtractedBodyRewriter(instId: InstantiationId, body: Block, fvs: Ls[LocalVarSymbol]): (Rewriter, Ls[VarSymbol]) =
      val fvParams = fvs.map: s =>
        new VarSymbol(Tree.Ident(s"fv_${s.nme}"), erasedType = retypedVariables.get(instId -> s).orElse(s.mapErasedValueType))
      mkCopyRewriter(instId, Nil, body, Map.from(fvs.iterator.zip(fvParams))) -> fvParams
  
    // Functions for fused match branches; each runs one arm and then its rest
    val newBranchFuns =
      for (branchId@(dtorId, whichBranch), (bms, tSym)) <- branchFunSyms yield
        val instId = dtorId.getInstId
        val ogBody = branchOriginalBodies(dtorId.exprId -> whichBranch)
        val (restFunBms, restFunTSym) = restFunSyms(dtorId)
        val (rewriter, fvParams) = mkExtractedBodyRewriter(instId, ogBody, dtorBranchFnFvs(branchId._1))
        val actualBody = Begin(
          rewriter.applyBlock(ogBody),
          rewriter.mkCall(restFunBms.asMemberRef(restFunTSym), restFnFvs(dtorId))(Return(_)))
        FunDefn(N, bms, tSym,
          branchFunParamFieldSyms(branchId).asParamList :: fvParams.asParamList :: Nil,
          actualBody
        )(N, annotations = AffineAnnotForBranchFns :: PrivateModifier :: Nil)
    end newBranchFuns
    
    // Continuation functions for the code after fused matches or labels
    val newRestFuns =
      for (restFunId, (bms, tsym)) <- restFunSyms yield
        val instId = restFunId.getInstId
        val (ogBody, parent) = restOriginalBodiesAndParentRest(restFunId.withoutInstId)
        val (rewriter, fvParams) = mkExtractedBodyRewriter(instId, ogBody, restFnFvs(restFunId))
        val transformedOgBody = rewriter.applyBlock(ogBody)
        val actualBody = parent match
          case Some(parentRestId) =>
            val parentRestFunId = parentRestId.withInstId(instId)
            val (parentFunBms, parentFunTSym) = restFunSyms(parentRestFunId)
            val parentFunFvs = restFnFvs(parentRestFunId)
            Begin(
              transformedOgBody,
              rewriter.mkCall(parentFunBms.asMemberRef(parentFunTSym), parentFunFvs)(Return(_)))
          case None =>
            Begin(transformedOgBody, Return(Value.Lit(Tree.UnitLit(true))(N)))
        FunDefn(N, bms, tsym, fvParams.asParamList :: Nil, actualBody)(N, annotations = PrivateModifier :: Nil)
    end newRestFuns
    
    newBranchFuns ++ newRestFuns
    
  end otherNewFunDefns
  
  def mkRootRewriter(rewrittenInPlace: Map[TermSymbol, RewrittenFunDefn]) =
    new Rewriter(Nil, N):
      override def applyFunDefn(fun: FunDefn): FunDefn =
        rewrittenInPlace.get(fun.dSym) match
          case Some((params, rewrittenBody)) =>
            FunDefn(fun.owner, fun.sym, fun.dSym.subst, params, rewrittenBody)(fun.configOverride, fun.annotations)
          case None => super.applyFunDefn(fun)
  
  lazy val retypedVariables =
    val slots = LinkedHashMap.empty[(InstantiationId, ValueSymbol), ErasedValueType]
    for (sym, instId, v) <- collector.symbolFlows do sym match
      case sym: (VarSymbol | TempSymbol | TermSymbol) =>
        retypedSlotType(v.lowerBounds.toList, sym.mapErasedValueType).foreach:
          tpe => slots(instId -> sym) = tpe
      case _ => ()
    slots
  
  // a function is retyped if fusion retypes one of its parameters or changes what it returns
  lazy val retypedFunctions =
    val res = LinkedHashMap.empty[(InstantiationId, TermSymbol), ErasedFuncType]
    for pf <- constraintSolver.prodFunsWithDests do pf.exprId match
      case (fun: TermSymbol, idx) if idx == pre.res.funSymToFunDefn(fun).params.size - 1 =>
        val instId = pf.concreteId.instId
        val key = instId -> fun
        var newParams = false
        val paramsTypes = pre.res.funSymToFunDefn(fun).params.map:
          _.params.map: p =>
            retypedVariables.get(instId -> p.sym) match
            case N => p.sym.erasedType
            case S(newTpe) => newParams ||= true; S(newTpe)
        val maybeNewReturnType = retypedSlotType(producersOf(pf.res), fun.declaredResultType)
        if maybeNewReturnType.isDefined || newParams then
          val retType = maybeNewReturnType.orElse(fun.declaredResultType)
          val funType = ErasedType.FuncRef(S(false), paramsTypes, retType)
          res(key) = funType
      case _ => ()
    res
  // ====== end: implements the abstract members of `PolyInstantiationRewrite` ======
end DeforestRewriter
