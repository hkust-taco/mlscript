package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet, SortedMap => MutSortedMap}
import scala.collection.immutable.{SortedSet, SortedMap, List}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._
import scala.collection.immutable

class ConstraintSolver extends NormalForms { self: Typer =>
  def verboseConstraintProvenanceHints: Bool = verbose
  type ConCtx = Ls[ST] -> Ls[ST]
  val errorSimplifer: ErrorSimplifier = ErrorSimplifier()
  
  /** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. */
  def constrain(lhs: SimpleType, rhs: SimpleType)(implicit raise: Raise, prov: TypeProvenance, ctx: Ctx): Unit = {
    // We need a cache to remember the subtyping tests in process; we also make the cache remember
    // past subtyping tests for performance reasons (it reduces the complexity of the algoritghm):
    val cache: MutSet[(SimpleType, SimpleType)] = MutSet.empty
    
    println(s"CONSTRAIN $lhs <! $rhs")
    println(s"  where ${FunctionType(lhs, rhs)(noProv).showBounds}")
    
    
    def mkCase[A](str: Str)(k: Str => A)(implicit dbgHelp: Str): A = {
      val newStr = dbgHelp + "." + str
      println(newStr)
      k(newStr)
    }
    
    /* To solve constraints that are more tricky. */
    def goToWork(lhs: ST, rhs: ST)(implicit cctx: ConCtx): Unit =
      constrainDNF(DNF.mkDeep(lhs, true), DNF.mkDeep(rhs, false), rhs)
    
    def constrainDNF(lhs: DNF, rhs: DNF, oldRhs: ST)(implicit cctx: ConCtx): Unit =
    trace(s"ARGH  $lhs  <!  $rhs") {
      annoyingCalls += 1
      
      lhs.cs.foreach { case Conjunct(lnf, vars, rnf, nvars) =>
        
        def local(): Unit = { // * Used to return early in simple cases
          
          vars.headOption match {
            case S(v) =>
              rec(v, rhs.toType() | Conjunct(lnf, vars - v, rnf, nvars).toType().neg())
            case N =>
              implicit val etf: ExpandTupleFields = true
              val fullRhs = nvars.iterator.map(DNF.mkDeep(_, true))
                .foldLeft(rhs | DNF.mkDeep(rnf.toType(), false))(_ | _)
              println(s"Consider ${lnf} <: ${fullRhs}")
              
              // The following crutch is necessary because the pesky Without types may get stuck
              //  on type variables and type variable negations:
              lnf match {
                case LhsRefined(S(Without(NegType(tv: TV), ns)), tts, rcd, trs) =>
                  return rec((
                    fullRhs.toType() | LhsRefined(N, tts, rcd, trs).toType().neg()).without(ns).neg(), tv)
                case LhsRefined(S(Without(b, ns)), tts, rcd, trs) =>
                  assert(b.isInstanceOf[TV])
                  return rec(b, (
                    fullRhs.toType() | LhsRefined(N, tts, rcd, trs).toType().neg()).without(ns))
                case _ => ()
              }
              
              // First, we filter out those RHS alternatives that obviously don't match our LHS:
              val possible = fullRhs.cs.filter { r =>
                
                // Note that without this subtyping check,
                //  the number of constraints in the `eval1_ty_ugly = eval1_ty`
                //  ExprProb subsumption test case explodes.
                if ((r.rnf is RhsBot) && r.vars.isEmpty && r.nvars.isEmpty && lnf <:< r.lnf) {
                  println(s"OK  $lnf <: $r")
                  return ()
                }
                
                // println(s"Possible? $r ${lnf & r.lnf}")
                !vars.exists(r.nvars) && ((lnf & r.lnf)(ctx, etf = false)).isDefined && ((lnf, r.rnf) match {
                  case (LhsRefined(_, ttags, _, _), RhsBases(objTags, rest, trs))
                    if objTags.exists { case t: TraitTag => ttags(t); case _ => false }
                    => false
                  case (LhsRefined(S(ot: ClassTag), _, _, _), RhsBases(objTags, rest, trs))
                    => !objTags.contains(ot)
                  case _ => true
                })
              }
              
              println(s"Possible: " + possible)
              
              if (doFactorize) {
                // We try to factorize the RHS to help make subsequent solving take shortcuts:
                
                val fact = factorize(possible, sort = false)
                
                println(s"Factorized: " + fact)
                
                // Finally, we enter the "annoying constraint" resolution routine:
                annoying(Nil, lnf, fact, RhsBot)
                
              } else {
                // Alternatively, without factorization (does not actually make a difference most of the time):
                
                annoying(Nil, lnf, possible.map(_.toType()), RhsBot)
                
              }
              
          }
          
        }
        
        local()
        
      }
    }()
    
    /* Solve annoying constraints,
        which are those that involve either unions and intersections at the wrong polarities or negations.
        This works by constructing all pairs of "conjunct <: disjunct" implied by the conceptual
        "DNF <: CNF" form of the constraint. */
    def annoying(ls: Ls[SimpleType], done_ls: LhsNf, rs: Ls[SimpleType], done_rs: RhsNf)
          (implicit cctx: ConCtx, dbgHelp: Str = "Case"): Unit = {
        annoyingCalls += 1
        annoyingImpl(ls, done_ls, rs, done_rs) 
      }
    
    def annoyingImpl(ls: Ls[SimpleType], done_ls: LhsNf, rs: Ls[SimpleType], done_rs: RhsNf)
          (implicit cctx: ConCtx, dbgHelp: Str = "Case"): Unit = trace(s"A  $done_ls  %  $ls  <!  $rs  %  $done_rs") {
      def mkRhs(ls: Ls[SimpleType]): SimpleType = {
        def tys = (ls.iterator ++ done_ls.toTypes).map(_.neg()) ++ rs.iterator ++ done_rs.toTypes
        tys.reduceOption(_ | _).getOrElse(BotType)
      }
      def mkLhs(rs: Ls[SimpleType]): SimpleType = {
        def tys = ls.iterator ++ done_ls.toTypes ++ (rs.iterator ++ done_rs.toTypes).map(_.neg())
        tys.reduceOption(_ & _).getOrElse(TopType)
      }
      implicit val etf: ExpandTupleFields = false
      (ls, rs) match {
        // If we find a type variable, we can weasel out of the annoying constraint by delaying its resolution,
        // saving it as negations in the variable's bounds!

        // TODO: figure out how to handled nested provenance for this case. use default for now
        // case ((tv: TypeVariable) :: ls, _) => rec(tv, mkRhs(ls), done_ls.isTop && ls.forall(_.isTop))
        // case (_, (tv: TypeVariable) :: rs) => rec(mkLhs(rs), tv, done_rs.isBot && rs.forall(_.isBot))

        case ((tv: TypeVariable) :: ls, _) => rec(tv, mkRhs(ls))
        case (_, (tv: TypeVariable) :: rs) => rec(mkLhs(rs), tv)

        case (TypeBounds(lb, ub) :: ls, _) => annoying(ub :: ls, done_ls, rs, done_rs)
        case (_, TypeBounds(lb, ub) :: rs) => annoying(ls, done_ls, lb :: rs, done_rs)
        case (ComposedType(true, ll, lr) :: ls, _) =>
          mkCase("1"){ implicit dbgHelp => annoying(ll :: ls, done_ls, rs, done_rs) }
          mkCase("2"){ implicit dbgHelp => annoying(lr :: ls, done_ls, rs, done_rs) }
        case (_, ComposedType(false, rl, rr) :: rs) =>
          mkCase("1"){ implicit dbgHelp => annoying(ls, done_ls, rl :: rs, done_rs) }
          mkCase("2"){ implicit dbgHelp => annoying(ls, done_ls, rr :: rs, done_rs) }
        case (_, ComposedType(true, rl, rr) :: rs) =>
          annoying(ls, done_ls, rl :: rr :: rs, done_rs)
        case (ComposedType(false, ll, lr) :: ls, _) =>
          annoying(ll :: lr :: ls, done_ls, rs, done_rs)
        case (p @ ProxyType(und) :: ls, _) => annoying(und :: ls, done_ls, rs, done_rs)
        case (_, p @ ProxyType(und) :: rs) => annoying(ls, done_ls, und :: rs, done_rs)
        // ^ TODO retain the proxy provs wrapping each ConstructedType... for better errors later on?
        case (n @ NegType(ty) :: ls, _) => annoying(ls, done_ls, ty :: rs, done_rs)
        case (_, n @ NegType(ty) :: rs) => annoying(ty :: ls, done_ls, rs, done_rs)
        case (ExtrType(true) :: ls, rs) => () // Bot in the LHS intersection makes the constraint trivial
        case (ls, ExtrType(false) :: rs) => () // Top in the RHS union makes the constraint trivial
        case (ExtrType(false) :: ls, rs) => annoying(ls, done_ls, rs, done_rs)
        case (ls, ExtrType(true) :: rs) => annoying(ls, done_ls, rs, done_rs)
          
        // case ((tr @ TypeRef(_, _)) :: ls, rs) => annoying(tr.expand :: ls, done_ls, rs, done_rs)
        case ((tr @ TypeRef(_, _)) :: ls, rs) => annoying(ls, (done_ls & tr) getOrElse
          (return println(s"OK  $done_ls & $tr  =:=  ${BotType}")), rs, done_rs)
        
        // case (ls, (tr @ TypeRef(_, _)) :: rs) => annoying(ls, done_ls, tr.expand :: rs, done_rs)
        case (ls, (tr @ TypeRef(_, _)) :: rs) => annoying(ls, done_ls, rs, done_rs | tr getOrElse
          (return println(s"OK  $done_rs & $tr  =:=  ${TopType}")))
        
        /*
        // This logic is now in `constrainDNF`... and even if we got here,
        // the new BaseType `&` implementation can now deal with these.
        case (Without(b: TypeVariable, ns) :: ls, rs) => rec(b, mkRhs(ls).without(ns))
        case (Without(NegType(b: TypeVariable), ns) :: ls, rs) => rec(b, NegType(mkRhs(ls).without(ns))(noProv))
        case ((w @ Without(_, _)) :: ls, rs) =>
          lastWords(s"`pushPosWithout` should have removed Without type: ${w}")
        case (ls, (w @ Without(_, _)) :: rs) =>
          lastWords(s"unexpected Without in negative position not at the top level: ${w}")
        */
        
        case ((l: BaseTypeOrTag) :: ls, rs) => annoying(ls, (done_ls & l)(etf = true) getOrElse
          (return println(s"OK  $done_ls & $l  =:=  ${BotType}")), rs, done_rs)
        case (ls, (r: BaseTypeOrTag) :: rs) => annoying(ls, done_ls, rs, done_rs | r getOrElse
          (return println(s"OK  $done_rs | $r  =:=  ${TopType}")))
          
        case ((l: RecordType) :: ls, rs) => annoying(ls, done_ls & l, rs, done_rs)
        case (ls, (r @ RecordType(Nil)) :: rs) => ()
        case (ls, (r @ RecordType(f :: Nil)) :: rs) => annoying(ls, done_ls, rs, done_rs | f getOrElse
          (return println(s"OK  $done_rs | $f  =:=  ${TopType}")))
        case (ls, (r @ RecordType(fs)) :: rs) => annoying(ls, done_ls, r.toInter :: rs, done_rs)
          
        case (Nil, Nil) =>
          // TODO improve:
          //    Most of the `rec` calls below will yield ugly errors because we don't maintain
          //    the original constraining context!
          (done_ls, done_rs) match {
            case (LhsRefined(S(Without(b, _)), _, _, _), RhsBot) => rec(b, BotType)
            case (LhsTop, _) | (LhsRefined(N, empty(), RecordType(Nil), empty()), _) =>
              // TODO ^ actually get rid of LhsTop and RhsBot...? (might make constraint solving slower)
              reportError()
            case (LhsRefined(_, ts, _, trs), RhsBases(pts, _, _)) if ts.exists(pts.contains) => ()
            
            case (LhsRefined(bo, ts, r, trs), _) if trs.nonEmpty =>
              annoying(trs.valuesIterator.map(_.expand).toList, LhsRefined(bo, ts, r, SortedMap.empty), Nil, done_rs)
            
            case (_, RhsBases(pts, bf, trs)) if trs.nonEmpty =>
              annoying(Nil, done_ls, trs.valuesIterator.map(_.expand).toList, RhsBases(pts, bf, SortedMap.empty))
            
            // From this point on, trs should be empty!
            case (LhsRefined(_, _, _, trs), _) if trs.nonEmpty => die
            case (_, RhsBases(_, _, trs)) if trs.nonEmpty => die
            
            case (_, RhsBot) | (_, RhsBases(Nil, N, _)) =>
              reportError()
            
            case (LhsRefined(S(f0@FunctionType(l0, r0)), ts, r, _)
                , RhsBases(_, S(L(f1@FunctionType(l1, r1))), _)) =>
              rec(f0, f1)
            case (LhsRefined(S(f: FunctionType), ts, r, trs), RhsBases(pts, _, _)) =>
              annoying(Nil, LhsRefined(N, ts, r, trs), Nil, done_rs)
            case (LhsRefined(S(pt: ClassTag), ts, r, trs), RhsBases(pts, bf, trs2)) =>
              if (pts.contains(pt) || pts.exists(p => pt.parentsST.contains(p.id)))
                println(s"OK  $pt  <:  ${pts.mkString(" | ")}")
              // else f.fold(reportError())(f => annoying(Nil, done_ls, Nil, f))
              else annoying(Nil, LhsRefined(N, ts, r, trs), Nil, RhsBases(Nil, bf, trs2))
            case (lr @ LhsRefined(bo, ts, r, _), rf @ RhsField(n, t2)) =>
              // Reuse the case implemented below:  (this shortcut adds a few more annoying calls in stats)
              annoying(Nil, lr, Nil, RhsBases(Nil, S(R(rf)), SortedMap.empty))
            case (LhsRefined(bo, ts, r, _), RhsBases(ots, S(R(RhsField(n, t2))), trs)) =>
              r.fields.find(_._1 === n) match {
                case S(nt1) =>
                  recLb(t2, nt1._2)
                  rec(nt1._2.ub, t2.ub)
                case N =>
                  bo match {
                    case S(Without(b, ns)) =>
                      if (ns(n)) rec(b, RhsBases(ots, N, trs).toType())
                      else rec(b, done_rs.toType())
                    case _ => reportError()
                  }
              }
            case (LhsRefined(N, ts, r, _), RhsBases(pts, N | S(L(_: FunctionType | _: ArrayBase)), _)) =>
              reportError()
            case (LhsRefined(S(b: TupleType), ts, r, _), RhsBases(pts, S(L(ty: TupleType)), _))
              if b.fields.size === ty.fields.size =>
                (b.fields.unzip._2 lazyZip ty.fields.unzip._2).foreach { (l, r) =>
                  rec(l.ub, r.ub)
                  recLb(r, l)
                }
            case (LhsRefined(S(b: ArrayBase), ts, r, _), RhsBases(pts, S(L(ar: ArrayType)), _)) =>
              recLb(ar.inner, b.inner)
              rec(b.inner.ub, ar.inner.ub)
            case (LhsRefined(S(b: ArrayBase), ts, r, _), _) => reportError()
            case (LhsRefined(S(Without(b, ns)), ts, r, _), RhsBases(pts, N | S(L(_)), _)) =>
              rec(b, done_rs.toType())
            case (_, RhsBases(pts, S(L(Without(base, ns))), _)) =>
              // rec((pts.map(_.neg()).foldLeft(done_ls.toType())(_ & _)).without(ns), base)
              // ^ This less efficient version creates a slightly different error message
              //    (see test in Annoying.mls)
              annoying(pts.map(_.neg()), done_ls, base :: Nil, RhsBot)
          }
          
      }
    }()
    
    /** Helper function to constrain Field lower bounds. */
    def recLb(lhs: FieldType, rhs: FieldType, nestedProv: Option[NestedTypeProvenance] = None)
      (implicit raise: Raise, cctx: ConCtx): Unit = {
        (lhs.lb, rhs.lb) match {
          case (Some(l), Some(r)) => rec(l, r, nestedProv)
          case (Some(l), None) =>
            if (lhs.prov.loco.isEmpty || rhs.prov.loco.isEmpty) reportError()
            else reportError(S(msg"is not mutable"))(
              (rhs.ub.withProv(rhs.prov) :: l.withProv(lhs.prov) :: Nil, l.withProv(noProv) :: Nil)
            )
          case (None, Some(_)) | (None, None) => ()
        }
      }
    
    /**
      * Recursively constrain the given simple types. While constraining
      * keep tracking the provenance of the types in `cctx`. In case of
      * a constraining error chain can be used to generate error messages
      * and show the flow of types that lead to the error.
      * 
      * @param lhs
      * @param rhs
      * @param nestedProv
      * @param raise
      * @param cctx
      */
    def rec(lhs: SimpleType, rhs: SimpleType, nestedProv: Opt[NestedTypeProvenance] = N)
          (implicit raise: Raise, cctx: ConCtx): Unit = {
      constrainCalls += 1
      var sameLhs = cctx._1.headOption.exists(_.prov is lhs.prov)
      var sameRhs = cctx._2.headOption.exists(_.prov is rhs.prov)
      
      // check if these tuples are implicit
      // don't add them to chain
      (lhs, rhs) match {
        case (lt: TupleType, rt: TupleType) =>
          if (lt.implicitTuple || rt.implicitTuple)
            sameLhs = true
            sameRhs = true
        case _ => ()
      }
      
      val newCctx = nestedProv match {
        case N => 
          // add new simple type to the chain only if it's provenance
          // is different from current chain head
          ((if (sameLhs) cctx._1 else lhs :: cctx._1)
          ->
          // TODO: This operation is inefficient, it will be visible in large constrain calls
          // the rhs side of contstrain is reversed in the order provenance i.e. the type
          // is wrapped with provenances that go from consumer to producer. Since the producer
          // meets the lhs we need to store it in reverse
          // (rhs3, rhs2, rhs1) => (lhs0, lhs1, lhs2) ::: (rhs1, rhs2, rhs3)
          (if (sameRhs) cctx._2 else cctx._2 ::: (rhs :: Nil)))
        case S(nested) => 
          // the provenance chain for the constructor from the previous level
          // connects the provenances of lhs and rhs
          (lhs :: lhs.withProv(nested) :: Nil) -> (rhs :: Nil)
      }
      
      // show provenance chains from both contexts to emphasize the new node added
      if (explainErrors && verbose) {
        def printProv(prov: TP): Message =
            if (prov.isType) msg"type"
            else msg"${prov.desc} of type"
      
        def showNestingLevel(chain: Ls[ST], level: Int): Ls[Message -> Opt[Loc]] = {
          val levelIndicator = s"-${">"*level}"
          chain.flatMap { node =>
            node.prov match {
              case nestedProv: NestedTypeProvenance => 
                msg"$levelIndicator flowing into nested prov with desc: ${node.prov.desc}" -> nestedProv.loco ::
                  showNestingLevel(nestedProv.chain, level + 1)
              case tprov => 
                msg"$levelIndicator flowing from ${printProv(tprov)} `${node.toString}` with desc: ${node.prov.desc}" -> tprov.loco :: Nil
            }
          }
        }
        
        val oldProvFlow =
          msg"========= Previous type provenance flow below =========" -> N ::
          showNestingLevel(cctx._1, 1) :::
          showNestingLevel(cctx._2, 1)

        val newProvFlow =
          msg"========= New type provenance flow below =========" -> N ::
          showNestingLevel(newCctx._1, 1) :::
          showNestingLevel(newCctx._2, 1)

        raise(WarningReport(oldProvFlow))
        println(s"Prov flows before and after ${lhs} and ${rhs}")
        // println(s"Rhs and previous rhsChain head are same `cctx._2.headOption.exists(_ is rhs.prov)` ? - ${cctx._2.headOption.exists(_ is rhs.prov)}")
        raise(WarningReport(newProvFlow))
      }
      
      // Thread.sleep(10)  // useful for debugging constraint-solving explosions debugged on stdout
      recImpl(lhs, rhs)(raise, newCctx)
    }
    def recImpl(lhs: SimpleType, rhs: SimpleType, skipCache: Bool = false)
          (implicit raise: Raise, cctx: ConCtx): Unit =
    // trace(s"C $lhs <! $rhs") {
    trace(s"C $lhs <! $rhs    (${cache.size}) where ${lhs.getClass.getSimpleName} <: ${rhs.getClass.getSimpleName}}") {
    // trace(s"C $lhs <! $rhs    (${cache.size}) where ${lhs.getClass.getSimpleName} <: ${rhs.getClass.getSimpleName}} and prov ${lhs.prov} <: ${rhs.prov}") {
    // trace({
    //   errorSimplifer.reportInfo(S(cctx), 5)
    //   errorSimplifer.reportInfo(S(cctx), 6)
    //   s"C $lhs <! $rhs    (${cache.size}) where ${lhs.getClass.getSimpleName} <: ${rhs.getClass.getSimpleName}}"
    // }) {
    // trace(s"C $lhs <! $rhs  ${lhs.getClass.getSimpleName}  ${rhs.getClass.getSimpleName}") {
      // println(s"[[ ${cctx._1.map(_.prov).mkString(", ")}  <<  ${cctx._2.map(_.prov).mkString(", ")} ]]")
      // println(s"{{ ${cache.mkString(", ")} }}")
      
      // errorSimplifer.reportInfo(S(cctx), 3)
      lazy val provChain = Some(NestedTypeProvenance(cctx._1 ::: cctx._2))
      lazy val revProvChain = Some(NestedTypeProvenance(cctx._1 ::: cctx._2, NestingInfo().copy(reversed = true)))

      if (lhs === rhs) return ()
      
      // if (lhs <:< rhs) return () // * It's not clear that doing this here is worth it
      
      // println(s"  where ${FunctionType(lhs, rhs)(primProv).showBounds}")
      else {
        if (lhs is rhs) return
        val lhs_rhs = lhs -> rhs
        lhs_rhs match {
          case (_: ProvType, _) | (_, _: ProvType) => ()
          // * Note: contrary to Simple-sub, we do have to remember subtyping tests performed
          // *    between things that are not syntactically type variables or type references.
          // *  Indeed, due to the normalization of unions and intersections in the wriong polarity,
          // *    cycles in regular trees may only ever go through unions or intersections,
          // *    and not plain type variables.
          case _ =>
            if (cache(lhs_rhs)) return println(s"Cached!")
            cache += lhs_rhs
      }
        lhs_rhs match {
          case (ExtrType(true), _) => ()
          case (_, ExtrType(false) | RecordType(Nil)) => ()
          case (TypeBounds(lb, ub), _) => rec(ub, rhs)
          case (_, TypeBounds(lb, ub)) => rec(lhs, lb)
          case (p @ ProvType(und), _) => rec(und, rhs)
          case (_, p @ ProvType(und)) => rec(lhs, und)
          case (NegType(lhs), NegType(rhs)) => rec(rhs, lhs)
          case (lf @ FunctionType(l0, r0), rf @ FunctionType(l1, r1)) =>
            errorSimplifer.updateLevelCount(cctx, N)
            errorSimplifer.reportInfo(S(cctx))
            errorSimplifer.reportInfo(S(cctx), 3)
            rec(l1, l0, revProvChain.map(_.updateInfo("function lhs")))
            rec(r0, r1, provChain.map(_.updateInfo("function rhs")))
          case (prim: ClassTag, ot: ObjectTag)
            if prim.parentsST.contains(ot.id) =>
              errorSimplifer.updateLevelCount(cctx, N)
              errorSimplifer.updateChainCount(cctx, S(1, 0))
              errorSimplifer.reportInfo(S(cctx))
              errorSimplifer.reportInfo(S(cctx), 3)
              ()
          // for constraining type variables a new bound is created
          // the `newBound`'s provenance must record the whole flow
          // of the type variable from it's producer to it's consumer
          case (lhs: TypeVariable, rhs) if rhs.level <= lhs.level =>
            val newBound = (cctx._1 ::: cctx._2.reverse).foldRight(rhs)((c, ty) =>
              if (c.prov is noProv) ty else mkProxy(ty, c.prov))
            lhs.upperBounds ::= newBound // update the bound
            lhs.lowerBounds.foreach(rec(_, rhs)) // propagate from the bound
          case (lhs, rhs: TypeVariable) if lhs.level <= rhs.level =>
            val newBound = (cctx._1 ::: cctx._2.reverse).foldLeft(lhs)((ty, c) =>
              if (c.prov is noProv) ty else mkProxy(ty, c.prov))
            rhs.lowerBounds ::= newBound // update the bound
            rhs.upperBounds.foreach(rec(lhs, _)) // propagate from the bound
          case (_: TypeVariable, rhs0) =>
            val rhs = extrude(rhs0, lhs.level, false)
            println(s"EXTR RHS  $rhs0  ~>  $rhs  to ${lhs.level}")
            println(s" where ${rhs.showBounds}")
            println(s"   and ${rhs0.showBounds}")
            rec(lhs, rhs)
          case (lhs0, _: TypeVariable) =>
            val lhs = extrude(lhs0, rhs.level, true)
            println(s"EXTR LHS  $lhs0  ~>  $lhs  to ${rhs.level}")
            println(s" where ${lhs.showBounds}")
            println(s"   and ${lhs0.showBounds}")
            rec(lhs, rhs)
          // implicit tuples are function arguments that are wrapped temporarily
          // do not consider them as constructors call rec on their contained types
          case (ltup @ TupleType((N -> FieldType(N, lt)) :: Nil), rtup @ TupleType((N -> FieldType(N, rt)) :: Nil))
            if (ltup.implicitTuple || rtup.implicitTuple) =>
              rec(lt, rt)
          case (TupleType(fs0), TupleType(fs1)) if fs0.size === fs1.size => // TODO generalize (coerce compatible tuples)
            // TODO: handle error
            errorSimplifer.updateLevelCount(cctx, N)
            errorSimplifer.reportInfo(S(cctx))
            errorSimplifer.reportInfo(S(cctx), 3)
            fs0.lazyZip(fs1).foreach { case ((ln, l), (rn, r)) =>
              ln.foreach { ln => rn.foreach { rn =>
                if (ln =/= rn) err(
                  msg"Wrong tuple field name: found '${ln.name}' instead of '${rn.name}'",
                  lhs.prov.loco // TODO better loco
              )}}
              recLb(r, l, provChain.map(_.updateInfo("tuple lower bound")))
              rec(l.ub, r.ub, provChain.map(_.updateInfo("tuple upper bound")))
            }
          case (t: ArrayBase, a: ArrayType) =>
            recLb(a.inner, t.inner, provChain)
            rec(t.inner.ub, a.inner.ub, provChain)
          case (ComposedType(true, l, r), _) =>
            rec(l, rhs) // Q: really propagate the outerProv here?
            rec(r, rhs)
          case (_, ComposedType(false, l, r)) =>
            rec(lhs, l) // Q: really propagate the outerProv here?
            rec(lhs, r)
          case (p @ ProxyType(und), _) => rec(und, rhs)
          case (_, p @ ProxyType(und)) => rec(lhs, und)
          case (_, TupleType(f :: Nil)) if funkyTuples =>
            rec(lhs, f._2.ub) // FIXME actually needs reified coercion! not a true subtyping relationship
          case (err @ ClassTag(ErrTypeId, _), FunctionType(l1, r1)) =>
            rec(l1, err, provChain)
            rec(err, r1, provChain)
          case (FunctionType(l0, r0), err @ ClassTag(ErrTypeId, _)) =>
            rec(err, l0, provChain)
            rec(r0, err, provChain)
          case (RecordType(fs0), RecordType(fs1)) =>
            errorSimplifer.updateLevelCount(cctx, N)
            errorSimplifer.reportInfo(S(cctx))
            errorSimplifer.reportInfo(S(cctx), 3)
            fs1.foreach { case (n1, t1) =>
              fs0.find(_._1 === n1).fold {
                reportError()
              } { case (n0, t0) =>
                recLb(t1, t0, revProvChain.map(_.updateInfo("record field lower bound")))
                rec(t0.ub, t1.ub, provChain.map(_.updateInfo("record field upper bound")))
              }
            }
          case (tup: TupleType, _: RecordType) =>
            rec(tup.toRecord, rhs) // Q: really support this? means we'd put names into tuple reprs at runtime
          case (err @ ClassTag(ErrTypeId, _), RecordType(fs1)) =>
            fs1.foreach(f => rec(err, f._2.ub, provChain))
          case (RecordType(fs1), err @ ClassTag(ErrTypeId, _)) =>
            fs1.foreach(f => rec(f._2.ub, err, provChain))
            
          case (tr1: TypeRef, tr2: TypeRef) if tr1.defn.name =/= "Array" =>
            if (tr1.defn === tr2.defn) {
              assert(tr1.targs.sizeCompare(tr2.targs) === 0)
              val td = ctx.tyDefs(tr1.defn.name)
              val tvv = td.getVariancesOrDefault
              td.tparamsargs.unzip._2.lazyZip(tr1.targs).lazyZip(tr2.targs).foreach { (tv, targ1, targ2) =>
                val v = tvv(tv)
                if (!v.isContravariant) rec(targ1, targ2, provChain)
                if (!v.isCovariant) rec(targ2, targ1, provChain)
              }
            } else {
              (tr1.mkTag, tr2.mkTag) match {
                case (S(tag1), S(tag2)) if !(tag1 <:< tag2) =>
                  reportError()
                case _ =>
                  rec(tr1.expand, tr2.expand)
              }
            }
          case (tr: TypeRef, _) => rec(tr.expand, rhs)
          case (_, tr: TypeRef) => rec(lhs, tr.expand)
          
          case (ClassTag(ErrTypeId, _), _) => ()
          case (_, ClassTag(ErrTypeId, _)) => ()
          case (_, w @ Without(b, ns)) => rec(lhs.without(ns), b)
          case (_, n @ NegType(w @ Without(b, ns))) =>
            rec(Without(lhs, ns)(w.prov), NegType(b)(n.prov)) // this is weird... TODO check sound
          case (_, ComposedType(true, l, r)) =>
            goToWork(lhs, rhs)
          case (ComposedType(false, l, r), _) =>
            goToWork(lhs, rhs)
          case (_: NegType | _: Without, _) | (_, _: NegType | _: Without) =>
            goToWork(lhs, rhs)
          case _ =>
            reportError()
      }
    }}()
    
    def reportError(failureOpt: Opt[Message] = N)(implicit cctx: ConCtx): Unit = {
      errorSimplifer.addErrorChain(cctx)
      // completes counting current level of chain
      // then increments error count for all locations on the chain
      errorSimplifer.updateChainCount(cctx, N)
      errorSimplifer.updateChainCount(cctx, S(1, 1))
      // counts nested but counts extra
      // errorSimplifer.updateChainCount(cctx, (1, 1))
      // errorSimplifer.reportInfo(S(cctx))
      errorSimplifer.reportInfo(S(cctx))
      errorSimplifer.reportInfo(S(cctx), 3)
      
      val lhsChain: List[ST] = cctx._1
      val rhsChain: List[ST] = cctx._2
      val lhs = cctx._1.head
      val rhs = cctx._2.head
      
      // println(s"context part 1 -\n  $cctx._1\n and part 2 -\n $cctx._2\n")
      // println(s"CONSTRAINT FAILURE: $lhs <: $rhs")
      // println(s"CTX: ${cctx._1.zip(cctx._2).map(lr => s"${lr._1} <: ${lr._2} [${lr._1.prov}] [${lr._2.prov}]")}")
      
      def doesntMatch(ty: SimpleType) = msg"does not match type `${ty.expNeg}`"
      def doesntHaveField(n: Str) = msg"does not have field '$n'"
      
      val failure = failureOpt.getOrElse((lhs.unwrapProvs, rhs.unwrapProvs) match {
        // case (lunw, _) if lunw.isInstanceOf[TV] || lunw.isInstanceOf => doesntMatch(rhs)
        case (_: TV | _: ProxyType, _) => doesntMatch(rhs)
        case (RecordType(fs0), RecordType(fs1)) =>
          (fs1.map(_._1).toSet -- fs0.map(_._1).toSet)
            .headOption.fold(doesntMatch(rhs)) { n1 => doesntHaveField(n1.name) }
        case (lunw, obj: ObjectTag)
          if obj.id.isInstanceOf[Var]
          => msg"is not an instance of type `${
              if (primitiveTypes(obj.id.idStr)) obj.id.idStr else obj.id.idStr.capitalize}`"
        case (lunw, obj: TypeRef)
          => msg"is not an instance of `${obj.expNeg}`"
        case (lunw, TupleType(fs))
          if !lunw.isInstanceOf[TupleType] => msg"is not a ${fs.size.toString}-element tuple"
        case (lunw, FunctionType(_, _))
          if !lunw.isInstanceOf[FunctionType] => msg"is not a function"
        case (lunw, RecordType((n, _) :: Nil))
          if !lunw.isInstanceOf[RecordType] => doesntHaveField(n.name)
        case (lunw, RecordType(fs @ (_ :: _)))
          if !lunw.isInstanceOf[RecordType] =>
            msg"is not a record (expected a record with field${
              if (fs.sizeCompare(1) > 0) "s" else ""}: ${fs.map(_._1.name).mkString(", ")})"
        case _ => doesntMatch(rhs)
      })
      
      // The first located provenance coming from the left
      val lhsProv = lhsChain.iterator
        .filterNot(_.prov.isOrigin)
        .find(_.prov.loco.isDefined)
        .map(_.prov).getOrElse(lhs.prov)
      
      // The first located provenance coming from the right
      val rhsProv = rhsChain.iterator
        .filterNot(_.prov.isOrigin)
        .find(_.prov.loco.isDefined)
        .map(_.prov).getOrElse(rhs.prov)
      
      // The last located provenance coming from the right (this is a bit arbitrary)
      val rhsProv2 = rhsChain.reverseIterator
        .filterNot(_.prov.isOrigin)
        .find(_.prov.loco.isDefined)
        .map(_.prov).getOrElse(rhs.prov)
      
      // checks if location of type error is touched by or contains
      // a provenance location from the left chain of the context
      val relevantFailures = lhsChain.collect {
        case st
          if st.prov.loco =/= lhsProv.loco
          && st.prov.loco.exists(ll => prov.loco.forall(pl => (ll touches pl) || (pl covers ll)))
        => st
      }
      val tighestRelevantFailure = relevantFailures.headOption
      
      val shownLocos = MutSet.empty[Loc]
      def show(loco: Opt[Loc]): Opt[Loc] =
        loco.tap(_.foreach(shownLocos.+=))
      
      val originProvList = (lhsChain.headOption ++ rhsChain.lastOption).iterator
        .map(_.prov).collect {
            case tp @ TypeProvenance(loco, desc, S(nme), _) if loco.isDefined => nme -> tp
          }
        .toList.distinctBy(_._2.loco)
      
      def printProv(prov: TP): Message =
        if (prov.isType) msg"type"
        else msg"${prov.desc} of type"
      
      val mismatchMessage =
        msg"Type mismatch in ${prov.desc}:" -> show(prov.loco) :: (
          msg"${printProv(lhsProv)} `${lhs.expPos}` $failure"
        ) -> (if (lhsProv.loco === prov.loco) N else show(lhsProv.loco)) :: Nil
      
      // connects the current type error produced by rhs
      // to the most tight type error location. This is calculated
      // based on it's location intersecting or contained within
      // current error location
      val flowHint = 
        tighestRelevantFailure.map { l =>
          val expTyMsg = msg" with expected type `${rhs.expNeg}`"
          msg"but it flows into ${l.prov.desc}$expTyMsg" -> show(l.prov.loco) :: Nil
        }.toList.flatten
      
      // if first located provenance coming from right chain is
      // not the same as current error location. and the right chain
      // has a defined end. Then relate the start and end of the rhs
      // chain to show how the constraint arose.
      val constraintProvenanceHints = 
        if (rhsProv.loco.isDefined && rhsProv2.loco =/= prov.loco)
          msg"Note: constraint arises from ${rhsProv.desc}:" -> show(rhsProv.loco) :: (
            if (rhsProv2.loco.isDefined && rhsProv2.loco =/= rhsProv.loco && rhsProv2.loco =/= prov.loco)
              msg"from ${rhsProv2.desc}:" -> show(rhsProv2.loco) :: Nil
            else Nil
          )
        else Nil
      
      var first = true
      val originProvHints = originProvList.collect {
        case (nme, l) if l.loco.exists(!shownLocos.contains(_)) =>
          val msgHead =
            if (first)
                  msg"Note: ${l.desc} $nme"
            else  msg"      ${l.desc} $nme"
          first = false
          msg"${msgHead} is defined at:" -> l.loco 
      }
      
      val detailedContext =
        if (explainErrors)
          msg"========= Additional explanations below =========" -> N ::
          lhsChain.flatMap { lhs =>
            if (dbg) msg"[info] LHS >> ${lhs.prov.toString} : ${lhs.expPos}" -> lhs.prov.loco :: Nil
            else msg"[info] flowing from ${printProv(lhs.prov)} `${lhs.expPos}`" -> lhs.prov.loco :: Nil
          } ::: rhsChain.reverse.flatMap { rhs =>
            if (dbg) msg"[info] RHS << ${rhs.prov.toString} : ${rhs.expNeg}" -> rhs.prov.loco :: Nil
            else msg"[info] flowing into ${printProv(rhs.prov)} `${rhs.expNeg}`" -> rhs.prov.loco :: Nil
          }
        else Nil
      
      errorSimplifer.reportInfo(N, 2)
      val msgs = Ls[Ls[Message -> Opt[Loc]]](
        mismatchMessage,
        flowHint,
        constraintProvenanceHints,
        originProvHints,
        detailedContext,
      ).flatten
      
      raise(ErrorReport(msgs))
    }
    
    rec(lhs, rhs)(raise, Nil -> Nil)
  }
  
  
  def subsume(ty_sch: PolymorphicType, sign: PolymorphicType)
      (implicit ctx: Ctx, raise: Raise, prov: TypeProvenance): Unit = {
    constrain(ty_sch.instantiate, sign.rigidify)
  }
  
  
  /** Copies a type up to its type variables of wrong level (and their extruded bounds). */
  def extrude(ty: SimpleType, lvl: Int, pol: Boolean)
      (implicit ctx: Ctx, cache: MutMap[PolarVariable, TV] = MutMap.empty): SimpleType =
    if (ty.level <= lvl) ty else ty match {
      case t @ TypeBounds(lb, ub) => if (pol) extrude(ub, lvl, true) else extrude(lb, lvl, false)
      case t @ FunctionType(l, r) => FunctionType(extrude(l, lvl, !pol), extrude(r, lvl, pol))(t.prov)
      case t @ ComposedType(p, l, r) => ComposedType(p, extrude(l, lvl, pol), extrude(r, lvl, pol))(t.prov)
      case t @ RecordType(fs) =>
        RecordType(fs.mapValues(_.update(extrude(_, lvl, !pol), extrude(_, lvl, pol))))(t.prov)
      case t @ TupleType(fs) =>
        TupleType(fs.mapValues(_.update(extrude(_, lvl, !pol), extrude(_, lvl, pol))))(t.prov)
      case t @ ArrayType(ar) =>
        ArrayType(ar.update(extrude(_, lvl, !pol), extrude(_, lvl, pol)))(t.prov)
      case t @ SpliceType(fs) => 
        t.updateElems(extrude(_, lvl, pol), extrude(_, lvl, !pol), extrude(_, lvl, pol), t.prov)
      case w @ Without(b, ns) => Without(extrude(b, lvl, pol), ns)(w.prov)
      case tv: TypeVariable => cache.getOrElse(tv -> pol, {
        val nv = freshVar(tv.prov, tv.nameHint)(lvl)
        cache += tv -> pol -> nv
        if (pol) {
          tv.upperBounds ::= nv
          nv.lowerBounds = tv.lowerBounds.map(extrude(_, lvl, pol))
        } else {
          tv.lowerBounds ::= nv
          nv.upperBounds = tv.upperBounds.map(extrude(_, lvl, pol))
        }
        nv
      })
      case n @ NegType(neg) => NegType(extrude(neg, lvl, pol))(n.prov)
      case e @ ExtrType(_) => e
      case p @ ProvType(und) => ProvType(extrude(und, lvl, pol))(p.prov)
      case p @ ProxyType(und) => extrude(und, lvl, pol)
      case _: ClassTag | _: TraitTag => ty
      case tr @ TypeRef(d, ts) =>
        TypeRef(d, tr.mapTargs(S(pol)) {
          case (N, targ) =>
            TypeBounds(extrude(targ, lvl, false), extrude(targ, lvl, true))(noProv)
          case (S(pol), targ) => extrude(targ, lvl, pol)
        })(tr.prov)
    }
  
  
  def err(msg: Message, loco: Opt[Loc])(implicit raise: Raise): SimpleType = {
    err(msg -> loco :: Nil)
  }
  def err(msgs: List[Message -> Opt[Loc]])(implicit raise: Raise): SimpleType = {
    raise(ErrorReport(msgs))
    errType
  }
  def errType: SimpleType = ClassTag(ErrTypeId, Set.empty)(noProv)
  
  def warn(msg: Message, loco: Opt[Loc])(implicit raise: Raise): Unit =
    warn(msg -> loco :: Nil)

  def warn(msgs: List[Message -> Opt[Loc]])(implicit raise: Raise): Unit =
    raise(WarningReport(msgs))
  
  
  // Note: maybe this and `extrude` should be merged?
  def freshenAbove(lim: Int, ty: SimpleType, rigidify: Bool = false)(implicit lvl: Int): SimpleType = {
    val freshened = MutMap.empty[TV, SimpleType]
    def freshen(ty: SimpleType): SimpleType =
      if (!rigidify // Rigidification now also substitutes TypeBound-s with fresh vars;
                    // since these have the level of their bounds, when rigidifying
                    // we need to make sure to copy the whole type regardless of level...
        && ty.level <= lim) ty else ty match {
      case tv: TypeVariable => freshened.get(tv) match {
        case Some(tv) => tv
        case None if rigidify =>
          val rv = TraitTag( // Rigid type variables (ie, skolems) are encoded as TraitTag-s
            Var(tv.nameHint.getOrElse("_"+freshVar(noProv).toString)))(tv.prov)
          if (tv.lowerBounds.nonEmpty || tv.upperBounds.nonEmpty) {
            // The bounds of `tv` may be recursive (refer to `tv` itself),
            //    so here we create a fresh variabe that will be able to tie the presumed recursive knot
            //    (if there is no recursion, it will just be a useless type variable)
            val tv2 = freshVar(tv.prov, tv.nameHint)
            freshened += tv -> tv2
            // Assuming there were no recursive bounds, given L <: tv <: U,
            //    we essentially need to turn tv's occurrence into the type-bounds (rv | L)..(rv & U),
            //    meaning all negative occurrences should be interpreted as rv | L
            //    and all positive occurrences should be interpreted as rv & U
            //    where rv is the rigidified variables.
            // Now, since there may be recursive bounds, we do the same
            //    but through the indirection of a type variable tv2:
            tv2.lowerBounds ::= tv.lowerBounds.map(freshen).foldLeft(rv: ST)(_ & _)
            tv2.upperBounds ::= tv.upperBounds.map(freshen).foldLeft(rv: ST)(_ | _)
            tv2
          } else {
            freshened += tv -> rv
            rv
          }
        case None =>
          val v = freshVar(tv.prov, tv.nameHint)
          freshened += tv -> v
          v.lowerBounds = tv.lowerBounds.mapConserve(freshen)
          v.upperBounds = tv.upperBounds.mapConserve(freshen)
          v
      }
      case t @ TypeBounds(lb, ub) =>
        if (rigidify) {
          val tv = freshVar(t.prov)
          tv.lowerBounds ::= freshen(lb)
          tv.upperBounds ::= freshen(ub)
          tv
        } else TypeBounds(freshen(lb), freshen(ub))(t.prov)
      case t @ FunctionType(l, r) => FunctionType(freshen(l), freshen(r))(t.prov)
      case t @ ComposedType(p, l, r) => ComposedType(p, freshen(l), freshen(r))(t.prov)
      case t @ RecordType(fs) => RecordType(fs.mapValues(_.update(freshen, freshen)))(t.prov)
      case t @ TupleType(fs) => TupleType(fs.mapValues(_.update(freshen, freshen)))(t.prov)
      case t @ ArrayType(ar) => ArrayType(ar.update(freshen, freshen))(t.prov)
      case t @ SpliceType(fs) => t.updateElems(freshen, freshen, freshen, t.prov)
      case n @ NegType(neg) => NegType(freshen(neg))(n.prov)
      case e @ ExtrType(_) => e
      case p @ ProvType(und) => ProvType(freshen(und))(p.prov)
      case p @ ProxyType(und) => freshen(und)
      case _: ClassTag | _: TraitTag => ty
      case w @ Without(b, ns) => Without(freshen(b), ns)(w.prov)
      case tr @ TypeRef(d, ts) => TypeRef(d, ts.map(freshen(_)))(tr.prov)
    }
    freshen(ty)
  }
  
  /** Stores information related to errors occuring during the
  * constraining phase of type inference. It also implements
  * various methods to process the information and generate
  * better error messages.
  *
  * @param simplifyError
  *   Config flag to report error simplification info
  */
  case class ErrorSimplifier(var simplifyError: Bool = false) {
    /** Maps provenances locations to a counter. The counter tracks
     * the number of the times the location has been visited, and the
     * number of visits that have led to constraining failures.
    */
    type LocoCounter = MutMap[Loc, Opt[(Int, Int)]]
    val locoCounter: LocoCounter = MutMap();
    val strategy: Strategy = DStarStrategy();
    
    def updateCounter(loco: Loc, change: Opt[(Int, Int)]): Unit = {
      // initialize counter if there is no change
      change match {
        case Some(change) =>
          locoCounter.updateWith(loco) {
            case Some(Some((total, wrong))) => Some(Some((total + change._1, wrong + change._2)))
            // an interior location typically intialized by the flow of a higher order
            // constructor like function, tuple, record is now being counted
            // update with value with the changed amount
            case Some(None) => Some(Some(change))
            // a location that has never been visited
            case None => throw new Exception("Cannot update counter for uninitialized location")
          }
        // initialize location if it doesn't already exist
        case N =>
          locoCounter.getOrElseUpdate(loco, None)
      }
      ()
    }
    
    /** Get counter for location. If counter does not exist return (-1, -1)
      * to indicate invalid location. If it exists but has only been initialized
      * consider it counted only once.
      *
      * @param loco
      * @return
      */
    def getCounter(loco: Loc): (Int, Int) = {
      locoCounter.getOrElse(loco, S(-1, -1)).getOrElse((1, 0))
    }
    
    def updateCounter(st: ST, change: Opt[(Int, Int)]): Unit = st.prov match {
      case nested: NestedTypeProvenance => nested.chain.foreach(updateCounter(_, change))
      case simple: TypeProvenance => simple.loco.foreach(updateCounter(_, change))
    }
    
    /**
      * Updates total count for non-duplicated provenance locations at the current
      * level of the flow
      *
      * @param cctx
      * @param change
      */
    def updateLevelCount(cctx: ConCtx, change: Opt[(Int, Int)] = S(1, 0)): Unit = {
      flattenChainWithLevel(cctx)
        .distinctBy(_._1.loco)
        .foreach{case (prov, level) =>
          if (level === 0) prov.loco.foreach(loc => updateCounter(loc, change))
        }
    }
    
    /**
      * Updates error count for non-duplicated provenance locations in the current
      * flow
      *
      * @param cctx
      * @param change
      */
    def updateChainCount(cctx: ConCtx, change: Opt[(Int, Int)] = S(0, 1)): Unit = {
      flattenChainToProvList(cctx)
        .distinctBy(_.loco)
        .foreach(prov => prov.loco.foreach(loc => updateCounter(loc, change)))
    }
    
    /** Stores the chain of provenances that lead to a given constraint
      * for a constraint a <: b, the LHS and RHS indicate the chain of
      * provenances that leads to the type a and type b respectively.
      * 
      * The newest element in the list is the most recent provenance and
      * the last element is the oldest or starting/origin provenance.
      * 
      * Taken together as LHS reverse_::: RHS, we get the complete
      * flow of a type from a it's producer to it's consumer. LHS needs
      * to be reversed because the starting provenance is at the end of
      * the LHS list.
      */
    var chains: Ls[ConCtx] = List()
    /** Increment wrong counts of locations in current provenance chain
      * however consider only the initial non-nested locations as erroneous
      * because nested provenances show that a type flowed through a constructor
      * correctly from being consumed to being produced
      * Note: we have to reverse the rhs chain because the non-nested
      * provenances are near the tail i.e. the 
      * store chain for later strategy based reporting
      * @param errorChain
      */
    def addErrorChain(errorChain: ConCtx): Unit = {
      chains ::= errorChain
      // updateError(errorChain)
    }
    
    def flattenChainToLoc(chain: ConCtx): Ls[Loc] = {
      def inner(chain: Ls[ST]): Ls[Loc] = {
        chain.flatMap(st => st.prov match {
          case nested: NestedTypeProvenance => inner(nested.chain)
          case simple: TypeProvenance => simple.loco match {
            case None => Ls.empty
            case Some(value) => value :: Nil
          }
        })
      }
      inner(chain._1 ::: chain._2)
    }
    
    def flattenChainWithLevel(chain: ConCtx): Ls[TypeProvenance -> Int] = {
      def inner(chain: Ls[ST], level: Int = 0, reverse: Bool = false): Ls[TypeProvenance -> Int] = {
        val provIter = if (reverse) chain.reverseIterator else chain.iterator
        provIter.flatMap(st => st.prov match {
          case nested: NestedTypeProvenance => inner(nested.chain, level + 1, nested.nestingInfo.reversed ^ reverse)
          case simple: TypeProvenance => if (simple.loco.isDefined) (simple, level) :: Nil else Nil
        }).toList
      }
      inner(chain._1 ::: chain._2)
    }
    
    def flattenChainToProvList(chain: ConCtx): Ls[TypeProvenance] = {
      def inner(chain: Ls[ST], level: Int = 0, reverse: Bool = false): Ls[TypeProvenance] = {
        val provIter = if (reverse) chain.reverseIterator else chain.iterator
        provIter.flatMap(st => st.prov match {
          case nested: NestedTypeProvenance => inner(nested.chain, level + 1, nested.nestingInfo.reversed ^ reverse)
          case simple: TypeProvenance => if (simple.loco.isDefined) simple.copy(desc = s"${simple.desc} at nesting: $level, rev: $reverse") :: Nil else Nil
          // case simple: TypeProvenance => simple.copy(desc = s"${simple.desc} at nesting: $level") :: Nil
        }).toList
      }
      inner(chain._1 ::: chain._2)
    }
    
    /**
      * Deduplicate consecutive locations that point to the same location
      *
      * @param chain
      * @return
      */
    def dedupChain(chain: Ls[TP]): Ls[TP] = chain match {
      case head :: _ => head :: chain.sliding(2).collect { case Seq(prev, next) if prev.loco =/= next.loco => next }.toList
      case Nil => Nil
    }
    def dedupChain(chain: => Ls[TP -> Int]): Ls[TP -> Int] = chain match {
      case head :: _ => head :: chain.sliding(2).collect { case Seq(prev, next) if prev._1.loco =/= next._1.loco => next }.toList
      case Nil => Nil
    }
    
    /**
      * Finds all the elements in the chain at a given level of nesting
      *
      * @param chain
      * @param level
      */
    def levelElements(cctx: ConCtx, level: Int = 0): Ls[ST] = {
      def inner(chain: Ls[ST], currentLevel: Int = 0, level: Int = 0): Ls[ST] = {
        if (level > currentLevel) Nil
        else if (level === currentLevel)
          chain.flatMap(st => st.prov match {
            case nested: NestedTypeProvenance => inner(nested.chain, level + 1)
            case _ => st :: Nil
          })
        else
          chain.flatMap(st => st.prov match {
            case nested: NestedTypeProvenance => inner(nested.chain, level + 1)
            case _ => Nil
          })
      }
      inner(cctx._1 ::: cctx._2, 0, level)
    }
    
    /**
      * Display a chain of provenances with nested levels where
      * a provenances is wrapped into a nested provenance
      *
      * @param chain
      * @param level
      * @param ctx
      * @return
      */
    def showNestingLevel(chain: Ls[ST], level: Int)(implicit ctx: Ctx): Ls[Message -> Opt[Loc]] = {
      val levelIndicator = s"-${">"*level}"
      chain.flatMap { node =>
        node.prov match {
          case nestedProv: NestedTypeProvenance => 
            // msg"$levelIndicator flowing into nested prov with desc: ${node.prov.desc}" -> nestedProv.loco ::
            msg"$levelIndicator with desc: ${node.prov.desc}" -> nestedProv.loco ::
              showNestingLevel(nestedProv.chain, level + 1)
          case tprov => 
            val locCount =
              tprov.loco.map(loc => locoCounter.getOrElse(loc, (-1, -1)))
                .getOrElse((-1, -1))
            val provInfo = if (tprov.isType) msg"type" else msg"${tprov.desc} of type"
            // msg"$levelIndicator flowing from ${provInfo} expanded: `${node.expPos}` raw: `${node.toString}` counter: ${locCount.toString} prov: ${tprov.loco.toString}" -> tprov.loco :: Nil
            msg"$levelIndicator ${provInfo} `${node.expPos}`" -> tprov.loco :: Nil
        }
      }
    }
    
    def nestedTypeProvFlow(chain: ConCtx)(implicit ctx: Ctx): Ls[Message -> Opt[Loc]] =
      if (explainErrors)
        msg"========= Nested type provenance flow below =========" -> N ::
        // showNestingLevel(filterChain(chain._1 ::: chain._2, N), 1)
        showNestingLevel(chain._1 ::: chain._2, 1)
      else Nil
    
    /**
      * Filter chain based on rules
      *
      * @param chain lhs and rhs sides of chain joined together
      * @param prev last visited accpted link in the chain
      * @return
      */
    def filterChain(chain: Ls[ST], prev: Opt[ST]): Ls[ST] = chain match {
      case tprov :: rest =>
        val hasLoco = tprov.prov.loco.isDefined
        val prevLocoSame = prev.map(_.prov.loco is tprov.prov.loco).getOrElse(false)
        (tprov.prov, hasLoco, prevLocoSame) match {
          case (ntprov: NestedTypeProvenance, _, _) =>
            val nestedChain = filterChain(ntprov.chain, prev)
            val restChain = filterChain(rest, nestedChain.lastOption)
            // ntprov.chain = nestedChain  // update chain of nested prov with filtered chain
            tprov :: restChain
          case (_, false, _) => filterChain(rest, prev)
          case (_, true, false) => tprov :: filterChain(rest, Some(tprov))
          case (_, true, true) => filterChain(rest, Some(tprov))
        }
      case Nil => Nil
    }
    
    /** Report error simplification information by raising error/warning messages
      *
      * @param infoLevel
      *   Level of detail for error simplification reporting
      *   * 0 - most suspect locations for a chain
      *   * 1 - all locations ranked in descending order of suspicion
      *   * 2 - all locations and their counts in the location counter mapping
      *   * 3 - all chain locations with their counts in flow order from producer to consumer
      *   * 4 - current level chain locations with their counts in flow order from producer to consumer
      *   * 5 - all chain locations on the lhs side with their counts in flow order from producer to consumer
      *   * 6 - all chain locations on the rhs side with their counts in flow order from producer to consumer
      */
    def reportInfo(chain: Opt[ConCtx], infoLevel: Int = 4, strategy: Strategy = strategy)
      (implicit raise: Raise): Unit =
    {
      if (!simplifyError && infoLevel =/= 8) return
      
      val messages: Ls[Message -> Opt[Loc]] = infoLevel match {
        // most suspect locations in a given chain
        case 0 =>
          val locations = flattenChainToLoc(chain.getOrElse(Nil -> Nil)).distinct
          val ranking = strategy.debugLocationRanking(strategy.rankLocations(locations))
          val name = strategy.name
          msg"========= Most suspicious locations ($name) =========" -> N ::
          ranking.iterator
          .filter { case (_, 0.0) => false; case _ => true}
          .map { case (loc, ranking) =>
            val counter = getCounter(loc)
            msg"Ranking ${ranking.toString()} with total and wrong count: ${counter.toString()}" -> Some(loc)
          }.toList
        // all chain locations in descending order of suspicion
        case 1 =>
          val locations = flattenChainToLoc(chain.getOrElse(Nil -> Nil)).distinct
          val ranking = strategy.debugLocationRanking(strategy.rankLocations(locations))
          val name = strategy.name
          msg"========= All suspicious locations ($name) =========" -> N ::
          ranking.iterator
          .map { case (loc, ranking) =>
            val counter = getCounter(loc)
            msg"Ranking ${ranking.toString()} with total and wrong count: ${counter.toString()}" -> Some(loc)
          }.toList
        // all locations in the mapping in descending order of counter
        case 2 =>
          msg"========= All locations and counts =========" -> N ::
          locoCounter.keys.toSortedSet.iterator
          .map { loc =>
            val counter = getCounter(loc)
            msg"(total, wrong): ${counter.toString()}" -> Some(loc)
          }.toList
        // all chain locations with their counts in flow order from producer to consumer
        case 3 =>
          msg"========= All chain provenances with location and count =========" -> N ::
          flattenChainToProvList(chain.getOrElse(Nil -> Nil))
          .collect {
            case TypeProvenance(S(loco), desc, _, _) =>
              val counter = getCounter(loco)
              msg"(total, wrong): ${counter.toString()} with $desc" -> Some(loco)
          }
        // all chain locations chain locations at the current level
        case 4 =>
          val flatChain = chain.map(cctx => levelElements(cctx, 0)).getOrElse(Nil)
          msg"========= All 0 level chain provenances with location and count =========" -> N ::
          flatChain.collect(st => st.prov match {
            case t @ TypeProvenance(S(loco), desc, _, _) if !(t.isInstanceOf[NestedTypeProvenance]) =>
              val counter = getCounter(loco)
              msg"(total, wrong): ${counter.toString()} with $desc" -> Some(loco)
          })
        // all chain locations on the lhs side
        case 5 =>
          msg"========= All location provenances on the lhs =========" -> N ::
          flattenChainToProvList(chain.getOrElse(Nil -> Nil)._1 -> Nil)
          .collect {
            case TypeProvenance(S(loco), desc, _, _) =>
              val counter = getCounter(loco)
              msg"(total, wrong): ${counter.toString()} with $desc" -> Some(loco)
          }
        // all chain locations on the rhs
        case 6 =>
          msg"========= All chain provenance on the rhs =========" -> N ::
          flattenChainToProvList(chain.getOrElse(Nil -> Nil)._2 -> Nil)
          .collect {
            case TypeProvenance(S(loco), desc, _, _) =>
              val counter = getCounter(loco)
              msg"(total, wrong): ${counter.toString()} with $desc" -> Some(loco)
          }
        case 7 =>
          msg"========= Unique locations on chain =========" -> N ::
          dedupChain(flattenChainToProvList(chain.getOrElse(Nil -> Nil)))
          .collect {
            case TypeProvenance(S(loco), desc, _, _) =>
              val counter = getCounter(loco)
              msg"(total, wrong): ${counter.toString()} with $desc and ${loco.toString}" -> Some(loco)
          }
        case 8 =>
          val locChain = locoCounter.keys.toSortedSet.toList
          val ranking = strategy.debugLocationRanking(strategy.rankLocations(locChain))
          val name = strategy.name
          msg"========= All suspicious locations ($name) and value =========" -> N ::
          ranking.filter(_._2 =/= 0.0).sortBy(_._2).reverseIterator
          .map { case (loc, ranking) =>
            val counter = getCounter(loc)
            msg"Suspicion score ${ranking.toString()} with total and wrong: ${counter.toString()}" -> Some(loc)
          }.toList
        case _ => Nil
      }
      
      raise(WarningReport(messages))
    }
    
    /** Strategy for guessing suspicious-ness of a location as the cause
      * of the fault. Higher score indicates more suspicious location.
      * 
      * Concrete classes are expected to implement specific heuristics, using
      * location counter and error chains attributes of super class.
      */
    trait Strategy {
      def score(loco: Loc): Double
      val ordering: Ordering[Loc]
      val name: Str
      // rank locations in descending order of suspicion i.e. higher score first
      def rankLocations(chain: Ls[Loc]): Ls[Loc] =
        chain.sorted(ordering).reverse
      def debugLocationRanking(chain: Ls[Loc]): Ls[Loc -> Double] =
        chain.map(loc => (loc, score(loc)))
    }
    
    case class SimpleStrategy() extends Strategy {
      override def score(loco: Loc): Double = {
        getCounter(loco) match {
          case (-1, -1) => 0
          case (total, wrong) =>
            if (total =/= 0) wrong.toDouble / total else 0
        }
      }

      override val ordering: Ordering[Loc] = new Ordering[Loc] {
        override def compare(x: Loc, y: Loc): Int = score(x).compare(score(y))
      }
      
      val name: Str = "Simple"

    }
    
    case class OchiaiStrategy() extends Strategy {
      override def score(loco: Loc): Double = {
        getCounter(loco) match {
          case (-1, -1) => 0
          case (total, wrong) =>
            val totalWrong = chains.length
            val denom = math.sqrt(totalWrong * (wrong + (total - wrong)))
            
            if (denom =/= 0) wrong / denom else 0
        }
      }

      override val ordering: Ordering[Loc] = new Ordering[Loc] {
        override def compare(x: Loc, y: Loc): Int = score(x).compare(score(y))
      }
      
      val name: Str = "Ochiai"
    }

    case class DStarStrategy() extends Strategy {
      val exponent: Int = 2
      override def score(loco: Loc): Double = {
        getCounter(loco) match {
          case (-1, -1) => 0
          case (total, wrong) =>
            val totalWrong = chains.length
            val denom = math.sqrt(totalWrong * (wrong + (total - wrong)))
            
            if (denom =/= 0) scala.math.pow(wrong, exponent) / denom else 0
        }
      }

      override val ordering: Ordering[Loc] = new Ordering[Loc] {
        override def compare(x: Loc, y: Loc): Int = score(x).compare(score(y))
      }
      
      val name: Str = s"DStar $exponent"
    }
  }
}
