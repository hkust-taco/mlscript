package mlscript

import scala.collection.mutable.{Map => MutMap, SortedMap => MutSortMap, Set => MutSet, Stack => MutStack, Buffer}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class ConstraintSolver extends NormalForms { self: Typer =>
  
  def stopConstrainingOnFirstFailure: Bool = false
  def verboseConstraintProvenanceHints: Bool = verbose
  def defaultStartingFuel: Int =
    // 5000
    10000 // necessary for fat definitions in OCamlList.mls
  var startingFuel: Int = defaultStartingFuel
  def depthLimit: Int =
    // 150
    // 200
    250
  
  type ExtrCtx = MutSortMap[TV, Buffer[(Bool, ST)]] // tv, is-lower, bound
  
  protected var currentConstrainingRun = 0
  
  
  private def noSuchMember(info: DelayedTypeInfo, fld: Var): Diagnostic =
    ErrorReport(
      msg"${info.decl.kind.str.capitalize} `${info.decl.name}` does not contain member `${fld.name}`" -> fld.toLoc :: Nil, newDefs)
  
  def lookupMember(clsNme: Str, rfnt: Var => Opt[FieldType], fld: Var)
        (implicit ctx: Ctx, raise: Raise)
        : Either[Diagnostic, NuMember]
        = {
    val info = ctx.tyDefs2.getOrElse(clsNme, ???/*TODO*/)
    
    if (info.isComputing) {
      
      ??? // TODO support?
      
    } else info.complete() match {
      
      case cls: TypedNuCls =>
        cls.members.get(fld.name) match {
          case S(m) => R(m)
          case N => L(noSuchMember(info, fld))
        }
        
      case _ => ??? // TODO
      
    }
    
  }
  
  
  /** Note: `mkType` is just for reporting errors. */
  def lookupField(mkType: () => ST, clsNme: Opt[Str], rfnt: Var => Opt[FieldType],
        tags: SortedSet[AbstractTag], _fld: Var)
        (implicit ctx: Ctx, raise: Raise)
        : FieldType
        = trace(s"Looking up field ${_fld.name} in $clsNme & ${tags} & {...}") {
    
    // * Field selections with field names starting with `#` are a typer hack to access private members.
    val (fld, allowPrivateAccess) =
      if (_fld.name.startsWith("#")) (Var(_fld.name.tail).withLocOf(_fld), true)
      else (_fld, false)
    
    val fromRft = rfnt(fld)
    
    var foundRec: Opt[Diagnostic] = N
    
    def getFieldType(info: DelayedTypeInfo): Opt[FieldType] = {
      
      // * The raw type of this member, with original references to the class' type variables/type parameters
      val raw = (if (info.isComputed) N else info.typedFields.get(fld)) match {
        
        case S(fty) =>
          if (info.privateParams.contains(fld) && !allowPrivateAccess)
            err(msg"Parameter '${fld.name}' cannot be accessed as a field" -> fld.toLoc :: Nil)
          S(fty)
        
        case N if info.isComputing =>
          
          if (info.allFields.contains(fld)) // TODO don't report this if the field can be found somewhere else!
            foundRec = S(ErrorReport(
              msg"Indirectly-recursive member should have a type signature" -> fld.toLoc :: Nil, newDefs))
          
          N
        
        case N =>
          
          def handle(virtualMembers: Map[Str, NuMember]): Opt[FieldType] =
            virtualMembers.get(fld.name) match {
              case S(d: TypedNuFun) =>
                if (d.fd.isLetOrLetRec)
                  err(msg"Let binding '${d.name}' cannot tbe accessed as a field" -> fld.toLoc ::
                    msg"Use a `val` declaration to make it a field" -> d.fd.toLoc ::
                    Nil)
                val ty = d.typeSignature
                S(
                  if (d.fd.isMut) FieldType(S(ty), ty)(d.prov)
                  else ty.toUpper(d.prov)
                )
              case S(p: NuParam) =>
                if (!allowPrivateAccess && !p.isPublic)
                  err(msg"Parameter '${p.nme.name}' cannot be accessed as a field" -> fld.toLoc ::
                    msg"Either make the parameter a `val` or access it through destructuring" -> p.nme.toLoc ::
                    Nil)
                S(p.ty)
              case S(m) =>
                S(err(msg"Access to ${m.kind.str} member not yet supported", fld.toLoc).toUpper(noProv))
              case N => N
            }
          
          info.complete() match {
            case cls: TypedNuCls => handle(cls.virtualMembers)
            case trt: TypedNuTrt => handle(trt.virtualMembers)
            case mxn: TypedNuMxn => handle(mxn.virtualMembers)
            case TypedNuDummy(d) => N
            case _ => ??? // TODO
          }
          
      }
      
      println(s"Lookup ${info.decl.name}.${fld.name} : $raw where ${raw.fold("")(_.ub.showBounds)}")
      
      val freshenedRaw = raw.map { raw =>
        
        implicit val freshened: MutMap[TV, ST] = MutMap.empty
        implicit val shadows: Shadows = Shadows.empty
        
        info.tparams.foreach { case (tn, _tv, vi) =>
          val targ = rfnt(Var(info.decl.name + "#" + tn.name)) match {
            // * TODO to avoid infinite recursion due to ever-expanding type args,
            // *  we should set the shadows of the targ to be the same as that of the parameter it replaces... 
            case S(fty) if vi === S(VarianceInfo.co) => fty.ub
            case S(fty) if vi === S(VarianceInfo.contra) => fty.lb.getOrElse(BotType)
            case S(fty) =>
              TypeBounds.mk(
                fty.lb.getOrElse(BotType),
                fty.ub,
              )
            case N =>
              TypeBounds(
                // _tv.lowerBounds.foldLeft(BotType: ST)(_ | _),
                // _tv.upperBounds.foldLeft(TopType: ST)(_ & _),
                _tv.lowerBounds.foldLeft(
                  Extruded(true, SkolemTag(_tv)(provTODO))(provTODO, Nil): ST
                  // ^ TODO provide extrusion reason?
                )(_ | _),
                _tv.upperBounds.foldLeft(
                  Extruded(false, SkolemTag(_tv)(provTODO))(provTODO, Nil): ST
                  // ^ TODO provide extrusion reason?
                )(_ & _),
              )(_tv.prov)
          }
          freshened += _tv -> targ
        }
        
        raw.freshenAbove(info.level, rigidify = false)
      }
      
      println(s"Fresh[${info.level}] ${info.decl.name}.${fld.name} : $freshenedRaw where ${freshenedRaw.map(_.ub.showBounds)}")
      
      freshenedRaw
    }
    
    val fromCls = clsNme.flatMap(clsNme => getFieldType(ctx.tyDefs2(clsNme)))
    
    val fromTrts = tags.toList.collect {
      case TraitTag(nme, iht) =>
        getFieldType(ctx.tyDefs2(nme.name))
    }.flatten
    
    val fields = fromRft.toList ::: fromCls.toList ::: fromTrts
    
    println(s"  & ${fromRft}  (from refinement)")
    
    fields match {
      case x :: xs =>
        xs.foldRight(x)(_ && _)
      case Nil =>
        foundRec match {
          case S(d) => err(d).toBoth(noProv)
          case N =>
            err(msg"Type `${mkType().expPos}` does not contain member `${fld.name}`" ->
              fld.toLoc :: Nil).toBoth(noProv)
        }
    }
    
  }()
  
  
  // * Each type has a shadow which identifies all variables created from copying
  // * variables that existed at the start of constraining.
  // * The intent is to make the total number of shadows in a given constraint
  // * resolution run finite, so we can avoid divergence with a "cyclic-lookign constraint" error.
  type ShadowSet = Set[ST -> ST]
  case class Shadows(current: ShadowSet, previous: ShadowSet) {
    def size: Int = current.size + previous.size
  }
  object Shadows { val empty: Shadows = Shadows(Set.empty, Set.empty) }
  
  /** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. */
  def constrain(lhs: SimpleType, rhs: SimpleType)
        (implicit raise: Raise, prov: TypeProvenance, ctx: Ctx, shadows: Shadows = Shadows.empty)
        : Unit = {
    currentConstrainingRun += 1
    if (stopConstrainingOnFirstFailure)
      constrainImpl(lhs, rhs)(err => {
        raise(err)
        return()
      }, prov, ctx, shadows)
    else constrainImpl(lhs, rhs)
  }
  def constrainImpl(lhs: SimpleType, rhs: SimpleType)
        (implicit raise: Raise, prov: TypeProvenance, ctx: Ctx, shadows: Shadows)
        : Unit = { val outerCtx = ctx ; {
    val ctx = ()
    
    // We need a cache to remember the subtyping tests in process; we also make the cache remember
    // past subtyping tests for performance reasons (it reduces the complexity of the algoritghm):
    val cache: MutSet[(SimpleType, SimpleType)] = MutSet.empty
    val startingFuel = self.startingFuel
    var fuel = startingFuel
    val stack = MutStack.empty[ST -> ST]
    
    println(s"CONSTRAIN $lhs <! $rhs")
    println(s"  where ${FunctionType(lhs, rhs)(noProv).showBounds}")
    
    type ConCtx = Ls[SimpleType] -> Ls[SimpleType]
    
    
    val abort = () => return
    
    def abbreviate(msgs: Ls[Message -> Opt[Loc]]) = {
      val treshold = 15
      if (msgs.sizeCompare(treshold) <= 0) msgs
      else msgs.take(treshold) :::
        msg"......" -> N :: msg"......" -> N :: msgs.reverseIterator.take(treshold).toList.reverse
    }
    
    def consumeFuel()(implicit cctx: ConCtx, ctx: Ctx) = {
      def msgHead = msg"Subtyping constraint of the form `${lhs.expPos} <: ${rhs.expNeg}`"
      if (stack.sizeIs > depthLimit) {
        err(
          msg"$msgHead exceeded recursion depth limit (${depthLimit.toString})" -> prov.loco
          :: (
            if (!explainErrors) msg"Note: use flag `:ex` to see internal error info." -> N :: Nil
            else if (verbose) stack.toList.filterOutConsecutive().flatMap { case (l, r) =>
              msg"while constraining:  ${s"$l"}" -> l.prov.loco ::
              msg"                       <!<  ${s"$r"}" -> r.prov.loco ::
              Nil
            } else abbreviate(stack.toList.filterOutConsecutive().map(c =>
              msg"while constraining:  ${s"${c._1}  <!<  ${c._2}"}" -> N))
          )
        )
        abort()
      } else
      if (fuel <= 0) {
        err(
          msg"$msgHead took too many steps and ran out of fuel (${startingFuel.toString})" -> prov.loco
          :: (
          if (!explainErrors) msg"Note: use flag `:ex` to see internal error info." -> N :: Nil
          else cctx._1.map(c => msg" + ${s"$c"}" -> c.prov.loco)
            ::: cctx._2.map(c => msg" - ${s"$c"}" -> c.prov.loco))
        )
        abort()
      } else fuel -= 1
    }
    
    def mkCase[A](str: Str)(k: Str => A)(implicit dbgHelp: Str): A = {
      val newStr = dbgHelp + "." + str
      println(newStr)
      k(newStr)
    }
    
    /** This is used in the context of constrained types.
      * We "unstash" all constraints that were currently stashed/saved for later
      * due to a polymorphism level mismatch. */
    def unstash(oldCtx: Ctx)(implicit ctx: Ctx, cctx: ConCtx, prevCctxs: Ls[ConCtx]): Unit = {
      val ec = ctx.extrCtx
      trace(s"UNSTASHING...") {
        implicit val ctx: Ctx = oldCtx
        ec.foreach { case (tv, bs) => 
          println(s"where($tv) ${tv.showBounds}")
          bs.foreach {
          case (true, b) => println(s"UNSTASH ${b} <: $tv where ${b.showBounds}"); rec(b, tv, false)
          case (false, b) => println(s"UNSTASH ${tv} <: $b where ${b.showBounds}"); rec(tv, b, false)
        }}
        ec.clear()
      }()
    } // ensuring ctx.extrCtx.isEmpty
    
    /* To solve constraints that are more tricky. */
    def goToWork(lhs: ST, rhs: ST)(implicit cctx: ConCtx, prevCctxs: Ls[ConCtx], ctx: Ctx, shadows: Shadows): Unit = {
      val lhsDNF = DNF.mkDeep(MaxLevel, Nil, lhs, true)
      val rhsDNF = DNF.mkDeep(MaxLevel, Nil, rhs, false)
      
      val oldCtx = ctx
      
      if (!rhsDNF.isPolymorphic) {
        
        constrainDNF(lhsDNF, rhsDNF)
        
      } else ctx.nextLevel { implicit ctx =>
        
        implicit val state: MutMap[TV, ST] = MutMap.empty
        val rigid = DNF(MaxLevel,
          rhsDNF.cons.mapKeys(_.freshenAbove(rhsDNF.polymLevel, rigidify = true)),
          rhsDNF.cs.map(_.freshenAbove(rhsDNF.polymLevel, rigidify = true)),
        )
        
        println(s"DNF BUMP TO LEVEL ${lvl}  -->  $rigid")
        // println(s"where ${rigid.showBounds}")
        
        constrainDNF(lhsDNF, rigid)
        
        unstash(oldCtx)
        
      }
    }
    
    def constrainDNF(_lhs: DNF, rhs: DNF)(implicit cctx: ConCtx, prevCctxs: Ls[ConCtx], ctx: Ctx, shadows: Shadows): Unit =
    trace(s"${lvl}. ARGH  ${_lhs}  <!  $rhs") {
      annoyingCalls += 1
      consumeFuel()
      
      require(!rhs.isPolymorphic)
      if (rhs.cons.nonEmpty) ??? // TODO handle when the RHS has first-class constraints
      
      val (lhsCons, lhsCs) = _lhs.instantiate
      
      // * Discharge all first-class constraints found in the LHS
      trace(s"DNF DISCHARGE CONSTRAINTS") {
        lhsCons.foreach(c => rec(c._1, c._2, false))
      }()
      
      // * Same remark as in the `rec` method [note:1]
      // assert(lvl >= rhs.level)
      
      lhsCs.foreach { case Conjunct(lnf, vars, rnf, nvars) =>
        
        def local(): Unit = { // * Used to return early in simple cases
          
          vars.headOption match {
            case S(v) =>
              rec(v, rhs.toType() | Conjunct(lnf, vars - v, rnf, nvars).toType().neg(), true)
            case N =>
              implicit val etf: ExpandTupleFields = true
              val fullRhs = nvars.iterator.map(DNF.mkDeep(MaxLevel, Nil, _, true))
                .foldLeft(rhs | DNF.mkDeep(MaxLevel, Nil, rnf.toType(), false))(_ | _)
              println(s"Consider ${lnf} <: ${fullRhs}")
              
              // The following crutch is necessary because the pesky Without types may get stuck
              //  on type variables and type variable negations:
              lnf match {
                case LhsRefined(S(Without(NegType(tv: TV), ns)), tts, rcd, trs) =>
                  return rec((
                    fullRhs.toType() | LhsRefined(N, tts, rcd, trs).toType().neg()).without(ns).neg(), tv, true)
                case LhsRefined(S(Without(b, ns)), tts, rcd, trs) =>
                  assert(b.isInstanceOf[TV])
                  return rec(b, (
                    fullRhs.toType() | LhsRefined(N, tts, rcd, trs).toType().neg()).without(ns), true)
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
                !vars.exists(r.nvars) && ((lnf & (r.lnf, pol = false))(ctx, etf = false)).isDefined && ((lnf, r.rnf) match {
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
          (implicit cctx: ConCtx, prevCctxs: Ls[ConCtx], shadows: Shadows, ctx: Ctx, dbgHelp: Str = "Case")
          : Unit =
    {
      annoyingCalls += 1
      consumeFuel()
      annoyingImpl(ls, done_ls, rs, done_rs)
    }
    
    // TODO improve by moving things to the right side *before* branching out in the search!
    def annoyingImpl(ls: Ls[SimpleType], done_ls: LhsNf, rs: Ls[SimpleType], done_rs: RhsNf)
          (implicit cctx: ConCtx, prevCctxs: Ls[ConCtx], ctx: Ctx, shadows: Shadows, dbgHelp: Str = "Case")
          : Unit =
    trace(s"${lvl}. A  $done_ls  %  $ls  <!  $rs  %  $done_rs") {
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
        case ((tv: TypeVariable) :: ls, _) => rec(tv, mkRhs(ls), done_ls.isTop && ls.forall(_.isTop))
        case (_, (tv: TypeVariable) :: rs) => rec(mkLhs(rs), tv, done_rs.isBot && rs.forall(_.isBot))
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
        case ((tr @ TypeRef(_, _)) :: ls, rs) => annoying(ls, (done_ls & (tr, pol = true)) getOrElse
          (return println(s"OK  $done_ls & $tr  =:=  ${BotType}")), rs, done_rs)
        
        // case (ls, (tr @ TypeRef(_, _)) :: rs) => annoying(ls, done_ls, tr.expand :: rs, done_rs)
        case (ls, (tr @ TypeRef(_, _)) :: rs) => annoying(ls, done_ls, rs, done_rs | (tr, pol = false) getOrElse
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
        
        case ((l: BaseTypeOrTag) :: ls, rs) => annoying(ls, (done_ls & (l, pol = true))(ctx, etf = true) getOrElse
          (return println(s"OK  $done_ls & $l  =:=  ${BotType}")), rs, done_rs)
        case (ls, (r: BaseTypeOrTag) :: rs) => annoying(ls, done_ls, rs, done_rs | r getOrElse
          (return println(s"OK  $done_rs | $r  =:=  ${TopType}")))
          
        case ((l: RecordType) :: ls, rs) => annoying(ls, done_ls & l, rs, done_rs)
        case (ls, (r @ RecordType(Nil)) :: rs) => ()
        case (ls, (r @ RecordType(f :: Nil)) :: rs) => annoying(ls, done_ls, rs, done_rs | f getOrElse
          (return println(s"OK  $done_rs | $f  =:=  ${TopType}")))
        case (ls, (r @ RecordType(fs)) :: rs) => annoying(ls, done_ls, r.toInter :: rs, done_rs)
          
        // TODO statically prevent these cases by refining `annoyingImpl`'s parameter types
        case (_, (_: PolymorphicType) :: _) | ((_: PolymorphicType) :: _, _) => die
        case (_, (_: ConstrainedType) :: _) | ((_: ConstrainedType) :: _, _) => die
          
        case (Nil, Nil) =>
          // TODO improve:
          //    Most of the `rec` calls below will yield ugly errors because we don't maintain
          //    the original constraining context!
          (done_ls, done_rs) match {
            case (LhsRefined(S(Without(b, _)), _, _, _), RhsBot) => rec(b, BotType, true)
            case (LhsTop, _) | (LhsRefined(N, EmptyColl(), RecordType(Nil), EmptyColl()), _) =>
              // TODO ^ actually get rid of LhsTop and RhsBot...? (might make constraint solving slower)
              reportError()
            case (LhsRefined(_, ts, _, trs), RhsBases(pts, _, _)) if ts.exists(pts.contains) => ()
            
            case (LhsRefined(bo, ts, r, trs), _) if trs.nonEmpty =>
              annoying(trs.valuesIterator.map { tr => tr.expand }.toList,
                LhsRefined(bo, ts, r, SortedMap.empty), Nil, done_rs)
            
            case (_, RhsBases(pts, bf, trs)) if trs.nonEmpty =>
              annoying(Nil, done_ls, trs.valuesIterator.map(_.expand).toList, RhsBases(pts, bf, SortedMap.empty))
            
            case (_, RhsBases(pts, S(L(ov: Overload)), trs)) =>
              ov.alts.foreach(alt => annoying(Nil, done_ls, Nil, RhsBases(pts, S(L(alt)), trs)))
            
            // From this point on, trs should be empty!
            case (LhsRefined(_, _, _, trs), _) if trs.nonEmpty => die
            case (_, RhsBases(_, _, trs)) if trs.nonEmpty => die
            
            case (_, RhsBot) | (_, RhsBases(Nil, N, _)) =>
              reportError()
            
            case (LhsRefined(S(f0@FunctionType(l0, r0)), ts, r, _)
                , RhsBases(_, S(L(f1@FunctionType(l1, r1))), _)) =>
              rec(f0, f1, true)
            case (LhsRefined(S(f: FunctionType), ts, r, trs), RhsBases(pts, _, _)) =>
              annoying(Nil, LhsRefined(N, ts, r, trs), Nil, done_rs)
            
            // * Note: We could avoid the need for this rule by adding `Eql` to *all* class tag parent sets,
            // *  but I chose not to for performance reasons (better keep parent sets small).
            case (LhsRefined(S(ct: ClassTag), ts, r, trs0),
                  RhsBases(ots, _, trs)) if EqlTag in ots =>
              println(s"OK ~ magic Eql ~")
            
            // * These deal with the implicit Eql type member in primitive types.
            // * (Originally I added this to all such types,
            // *  but it requires not expanding primitive type refs,
            // *  which causes regressions in simplification
            // *  because we don't yet simplify unexpanded type refs...)
            case (LhsRefined(S(ct @ ClassTag(lit: Lit, _)), ts, r, trs0),
                  RhsBases(ots, S(R(RhsField(Var("Eql#A"), fldTy))), trs)) =>
              lit match {
                case _: IntLit |  _: DecLit => rec(fldTy.lb.getOrElse(TopType), DecType, false)
                case _: StrLit => rec(fldTy.lb.getOrElse(TopType), StrType, false)
                case _: UnitLit => reportError()
              }
              
            // * This deals with the implicit Eql type member for user-defined classes.
            case (LhsRefined(S(ClassTag(Var(nme), _)), ts, r, trs0),
                  RhsBases(ots, S(R(RhsField(fldNme, fldTy))), trs))
            if ctx.tyDefs2.contains(nme) => if (newDefs && nme =/= "Eql" && fldNme.name === "Eql#A") {
              val info = ctx.tyDefs2(nme)
              if (info.typedParams.isEmpty && !primitiveTypes.contains(nme))
                // TODO shoudl actually reject all non-data classes...
                err(msg"${info.decl.kind.str.capitalize} '${info.decl.name
                  }' does not support equality comparison because it does not have a parameter list", prov.loco)
              info.typedParams
                .getOrElse(Nil) // FIXME?... prim type
                .foreach { p =>
                  val fty = lookupField(() => done_ls.toType(sort = true), S(nme), r.fields.toMap.get, ts, p._1)
                  rec(fldTy.lb.getOrElse(die), RecordType(p._1 -> TypeRef(TypeName("Eql"),
                      fty.ub // FIXME check mutable?
                      :: Nil
                    )(provTODO).toUpper(provTODO) :: Nil)(provTODO), false)
                }
            } else {
              val fty = lookupField(() => done_ls.toType(sort = true), S(nme), r.fields.toMap.get, ts, fldNme)
              rec(fty.ub, fldTy.ub, false)
              recLb(fldTy, fty)
            }
            case (l @ LhsRefined(S(pt: ClassTag), ts, r, trs), RhsBases(pts, bf, trs2)) =>
              println(s"class checking $pt $pts")
              if (pts.exists(p => (p.id === pt.id) || l.allTags.contains(p.id)))
                println(s"OK  $pt  <:  ${pts.mkString(" | ")}")
              // else f.fold(reportError())(f => annoying(Nil, done_ls, Nil, f))
              else annoying(Nil, LhsRefined(N, ts, r, trs), Nil, RhsBases(Nil, bf, trs2))
            case (lr @ LhsRefined(bo, ts, r, _), rf @ RhsField(n, t2)) =>
              // Reuse the case implemented below:  (this shortcut adds a few more annoying calls in stats)
              annoying(Nil, lr, Nil, RhsBases(Nil, S(R(rf)), SortedMap.empty))
            case (LhsRefined(N, ts, r, _), RhsBases(ots, S(R(RhsField(fldNme, fldTy))), trs)) if newDefs =>
              val fty = lookupField(() => done_ls.toType(sort = true), N, r.fields.toMap.get, ts, fldNme)
              rec(fty.ub, fldTy.ub, false)
              recLb(fldTy, fty)
            case (LhsRefined(bo, ts, r, _), RhsBases(ots, S(R(RhsField(n, t2))), trs)) =>
              // TODO simplify - merge with above?
              r.fields.find(_._1 === n) match {
                case S(nt1) =>
                  recLb(t2, nt1._2)
                  rec(nt1._2.ub, t2.ub, false)
                case N =>
                  bo match {
                    case S(Without(b, ns)) =>
                      if (ns(n)) rec(b, RhsBases(ots, N, trs).toType(), true)
                      else rec(b, done_rs.toType(), true)
                    case _ => reportError()
                  }
              }
            case (LhsRefined(N, ts, r, trs), RhsBases(pts, N, trs2))  =>
              println(s"Tag checking ${ts} ${pts}")
              if (pts.exists(p => ts.iterator.flatMap {
                case TraitTag(n, h) => n :: h.toList.map(n => Var(n.name))
                case _ => Nil
              }.contains(p.id)))
                println(s"OK $ts <: $pts")
              else reportError()
            case (LhsRefined(N, ts, r, _), RhsBases(pts, S(L(_: FunctionType | _: ArrayBase)), _)) =>
              reportError()
            case (LhsRefined(S(b: TupleType), ts, r, _), RhsBases(pts, S(L(ty: TupleType)), _))
              if b.fields.size === ty.fields.size =>
                (b.fields.unzip._2 lazyZip ty.fields.unzip._2).foreach { (l, r) =>
                  rec(l.ub, r.ub, false)
                  recLb(r, l)
                }
            case (LhsRefined(S(b: ArrayBase), ts, r, _), RhsBases(pts, S(L(ar: ArrayType)), _)) =>
              recLb(ar.inner, b.inner)
              rec(b.inner.ub, ar.inner.ub, false)
            case (LhsRefined(S(b: ArrayBase), ts, r, _), _) => reportError()
            case (LhsRefined(S(ov: Overload), ts, r, trs), RhsBases(_, S(L(f: FunctionType)), _)) if noApproximateOverload =>
              TupleSetConstraints.mk(ov, f) match {
                case S(tsc) =>
                  if (tsc.tvs.nonEmpty) {
                    tsc.tvs.mapValuesIter(_.unwrapProxies).zipWithIndex.flatMap {
                      case ((true, tv: TV), i) => tv.lowerBounds.iterator.map((_,tv,i,true))
                      case ((false, tv: TV), i) => tv.upperBounds.iterator.map((_,tv,i,false))
                      case _ => Nil
                    }.find {
                      case (b,_,i,_) =>
                        tsc.updateImpl(i,b)
                        tsc.constraints.isEmpty
                    }.foreach {
                      case (b,tv,_,p) => if (p) rec(b,tv,false) else rec(tv,b,false)
                    }
                    if (tsc.constraints.sizeCompare(1) === 0) {
                      tsc.tvs.values.map(_.unwrapProxies).foreach {
                        case tv: TV => tv.tsc.remove(tsc)
                        case _ => ()
                      }
                      tsc.constraints.head.iterator.zip(tsc.tvs).foreach {
                        case (c, (pol, t)) =>
                          if (!pol) rec(c, t, false)
                          if (pol) rec(t, c, false)
                      }
                    }
                  }
                case N => reportError(S(msg"is not an instance of `${f.expNeg}`"))
              }
            case (LhsRefined(S(ov: Overload), ts, r, trs), _) =>
              annoying(Nil, LhsRefined(S(ov.approximatePos), ts, r, trs), Nil, done_rs) // TODO remove approx. with ambiguous constraints
            case (LhsRefined(S(Without(b, ns)), ts, r, _), RhsBases(pts, N | S(L(_)), _)) =>
              rec(b, done_rs.toType(), true)
            case (_, RhsBases(pts, S(L(Without(base, ns))), _)) =>
              // rec((pts.map(_.neg()).foldLeft(done_ls.toType())(_ & _)).without(ns), base)
              // ^ This less efficient version creates a slightly different error message
              //    (see test in Annoying.mls)
              annoying(pts.map(_.neg()), done_ls, base :: Nil, RhsBot)
          }
          
      }
    }()
    
    /** Helper function to constrain Field lower bounds. */
    def recLb(lhs: FieldType, rhs: FieldType)
      (implicit raise: Raise, cctx: ConCtx, prevCctxs: Ls[ConCtx], ctx: Ctx, shadows: Shadows): Unit = {
        (lhs.lb, rhs.lb) match {
          case (Some(l), Some(r)) => rec(l, r, false)
          case (Some(l), None) =>
            println(s"RHS not mutable! in $lhs <- $rhs")
            reportError(
              if (lhs.prov.loco.isEmpty || rhs.prov.loco.isEmpty)
                S(msg"cannot be reassigned")
              else S(msg"is not mutable")
            )(
              (rhs.ub.withProv(rhs.prov) :: l.withProv(lhs.prov) :: Nil, l.withProv(noProv) :: Nil), ctx
            )
          case (None, Some(_)) | (None, None) => ()
        }
      }
    
    /** Extrudes and also checks type variable avoidance (which widens skolems to top/bot)
      * did not introduce bad bounds. To do this, we reconstrain the bounds of all new variables.
      * This is a bit of a sledgehammer approach that could be improved – it will duplicate TV bounds!
      * For instance, it would be better to accumulate new TVs' future bounds first
      * and add them by constraining later. */
    def extrudeAndCheck(ty: SimpleType, lowerLvl: Int, pol: Boolean, upperLvl: Level, reason: Ls[Ls[ST]])
          (implicit raise: Raise, cctx: ConCtx, prevCctxs: Ls[ConCtx], ctx: Ctx, shadows: Shadows)
          : SimpleType =
    {
      val originalVars = ty.getVars
      val res = extrude(ty, lowerLvl, pol, upperLvl)(ctx, MutMap.empty, MutSortMap.empty, reason)
      val newVars = res.getVars -- originalVars
      if (newVars.nonEmpty) trace(s"RECONSTRAINING TVs") {
        newVars.foreach {
          case tv @ AssignedVariable(bnd) =>
            println(s"No need to reconstrain assigned $tv")
            // * This is unlikely to happen, but it should be fine anyway,
            // * as all bounds of vars being assigned are checked against the assigned type.
            ()
          case tv =>
            println(s"Reconstraining $tv")
            if (tv.level > lowerLvl) tv.lowerBounds.foreach(lb =>
              // * Q: is it fine to constrain with the current ctx's level?
              tv.upperBounds.foreach(ub => rec(lb, ub, false)))
        }
      }()
      res
    }
    
    /** `cctx` accumulates the types that have been compared up to this point;
      * it is reset when going through a nested position (sameLevel = false).
      * `prevCctxs` accumulate the previous `cctx`s that led to this constraint.
      * Currently `prevCctxs` is just used to show possibly-helpful type annotation
      * locations upon skolem extrusion. */
    def rec(lhs: SimpleType, rhs: SimpleType, sameLevel: Bool)
          (implicit raise: Raise, cctx: ConCtx, prevCctxs: Ls[ConCtx], ctx: Ctx, shadows: Shadows)
          : Unit =
    {
      constrainCalls += 1
      val lhs_rhs = lhs -> rhs
      stack.push(lhs_rhs)
      consumeFuel()
      // Thread.sleep(10)  // useful for debugging constraint-solving explosions piped to stdout
      recImpl(lhs, rhs)(raise,
        if (sameLevel)
          (if (cctx._1.headOption.exists(_ is lhs)) cctx._1 else lhs :: cctx._1)
          ->
          (if (cctx._2.headOption.exists(_ is rhs)) cctx._2 else rhs :: cctx._2)
        else (lhs :: Nil) -> (rhs :: Nil),
        if (sameLevel || prevCctxs.isEmpty) prevCctxs // * See [note:2] below
        else cctx :: prevCctxs,
        ctx,
        if (sameLevel) shadows else shadows.copy(current = Set.empty)
      )
      stack.pop()
      ()
    }
    
    def recImpl(lhs: SimpleType, rhs: SimpleType)
          (implicit raise: Raise, cctx: ConCtx, prevCctxs: Ls[ConCtx], ctx: Ctx, shadows: Shadows)
          : Unit =
    // trace(s"$lvl. C $lhs <! $rhs") {
    // trace(s"$lvl. C $lhs <! $rhs    (${cache.size})") {
    trace(s"$lvl. C $lhs <! $rhs    (${shadows.size})") {
    // trace(s"$lvl. C $lhs <! $rhs  ${lhs.getClass.getSimpleName}  ${rhs.getClass.getSimpleName}") {
      
      // shadows.previous.foreach { sh =>
      //   println(s">> $sh   ${sh.hashCode}")
      // }
      
      // println(s"[[ ${cctx._1.map(_.prov).mkString(", ")}  <<  ${cctx._2.map(_.prov).mkString(", ")} ]]")
      // println(s"{{ ${cache.mkString(", ")} }}")
      
      // if (!lhs.mentionsTypeBounds && lhs === rhs) return ()
      // * ^ The check above is mostly good enough but it leads to slightly worse simplified type outputs
      // *    in corner cases.
      // * v The check below is a bit more precise but it incurs a lot more subtyping checks,
      // *    especially in complex comparisons like those done in the `ExprProb` test family.
      // *    Therefore this subtyping check may not be worth it.
      // *    In any case, we make it more lightweight by not traversing type variables
      // *    and not using a subtyping cache (cf. `CompareRecTypes = false`).
      if ({ implicit val ctr: CompareRecTypes = false; lhs <:< rhs })
        println(s"Already a subtype by <:<")
      
      // println(s"  where ${FunctionType(lhs, rhs)(primProv).showBounds}")
      else {
        val lhs_rhs = lhs -> rhs
        (lhs_rhs match {
          case (_: ProvType, _) | (_, _: ProvType) => shadows
          // * Note: contrary to Simple-sub, we do have to remember subtyping tests performed
          // *    between things that are not syntactically type variables or type references.
          // *  Indeed, due to the normalization of unions and intersections in the wrong polarity,
          // *    cycles in regular trees may only ever go through unions or intersections,
          // *    and not plain type variables.
          case _ =>
            if (!noRecursiveTypes && cache(lhs_rhs)) return println(s"Cached!")
            val shadow = lhs.shadow -> rhs.shadow
            // println(s"SH: $shadow")
            // println(s"ALLSH: ${shadows.iterator.map(s => s._1 + "<:" + s._2).mkString(", ")}")
            
            if (shadows.current.contains(lhs_rhs))
              return println(s"Spurious cycle involving $lhs_rhs") // * Spurious cycle, like alpha <: beta <: alpha
            
            else if (!noCycleCheck && shadows.previous.contains(shadow)
              && !shadows.current.contains(shadow)
            ) {
              println(s"SHADOWING DETECTED!")
              
              if (!lhs_rhs.matches{ case (ClassTag(ErrTypeId, _), _) | (_, ClassTag(ErrTypeId, _)) => true })
                err(msg"Cyclic-looking constraint while typing ${
                  prov.desc}; a type annotation may be required" -> prov.loco :: (
                    if (!explainErrors)
                      msg"Note: use flag `:ex` to see internal error info." -> N :: Nil
                    else
                      // msg"this constraint:  ${lhs.expPos}  <:  ${rhs.expNeg}" -> N ::
                      // msg" ... looks like:  ${shadow._1.expPos}  <:  ${shadow._2.expNeg}" -> N ::
                      msg"————————— Additional debugging info: —————————" -> N ::
                      msg"this constraint:  ${lhs.toString}  <:  ${rhs.toString}    ${lhs.getClass.getSimpleName}  ${rhs.getClass.getSimpleName}" -> N ::
                      msg" ... looks like:  ${shadow._1.toString}  <:  ${shadow._2.toString}" -> N ::
                      Nil
                    ))
              
              return ()
            }
            
            if (!noRecursiveTypes) cache += lhs_rhs
            
            Shadows(shadows.current + lhs_rhs + shadow, // * FIXME this conflation is not quite correct
              shadows.previous + shadow)
            
        }) |> { implicit shadows: Shadows =>
        lhs_rhs match {
          case (ExtrType(true), _) => ()
          case (_, ExtrType(false) | RecordType(Nil)) => ()
          case (TypeBounds(lb, ub), _) => rec(ub, rhs, true)
          case (_, TypeBounds(lb, ub)) => rec(lhs, lb, true)
          case (p @ ProvType(und), _) => rec(und, rhs, true)
          case (_, p @ ProvType(und)) => rec(lhs, und, true)
          case (_: TypeTag, _: TypeTag) if lhs === rhs => ()
          case (NegType(lhs), NegType(rhs)) => rec(rhs, lhs, true)
          
          case (ClassTag(Var(nme), _), rt: RecordType) if newDefs && nme.isCapitalized =>
            val lti = ctx.tyDefs2(nme)
            rt.fields.foreach {
              case (fldNme @ Var("Eql#A"), fldTy) =>
                goToWork(lhs, RecordType(fldNme -> fldTy :: Nil)(noProv))
              case (fldNme, fldTy) =>
                val fty = lookupField(() => lhs, S(nme), _ => N, SortedSet.empty, fldNme)
                rec(fty.ub, fldTy.ub, false)
                recLb(fldTy, fty)
            }
          
          // * Note: at this point, it could be that a polymorphic type could be distribbed
          // *  out of `r1`, but this would likely not result in something useful, since the
          // *  LHS is a normal non-polymorphic function type...
          case (FunctionType(l0, r0), FunctionType(l1, r1)) =>
            rec(l1, l0, false)
            rec(r0, r1, false)
          
          case (prim: ClassTag, ot: TypeTag)
            if prim.parentsST.contains(ot.id) => ()
            
          case (tv @ AssignedVariable(lhs), rhs) =>
            rec(lhs, rhs, true)
          case (lhs, tv @ AssignedVariable(rhs)) =>
            rec(lhs, rhs, true)
            
            
          case (lhs: TypeVariable, rhs) if rhs.level <= lhs.level =>
            println(s"NEW $lhs UB (${rhs.level})")
            val newBound = (cctx._1 ::: cctx._2.reverse).foldRight(rhs)((c, ty) =>
              if (c.prov is noProv) ty else mkProxy(ty, c.prov))
            lhs.upperBounds ::= newBound // update the bound
            if (noApproximateOverload) {
              lhs.tsc.foreachEntry { (tsc, v) =>
                v.foreach { i =>
                  if (!tsc.tvs(i)._1) {
                    tsc.updateOn(i, rhs)
                    if (tsc.constraints.isEmpty) reportError()
                  }
                }
              }
              val u = lhs.tsc.keysIterator.filter(_.constraints.sizeCompare(1)===0).duplicate
              u._1.foreach { k =>
                k.tvs.mapValuesIter(_.unwrapProxies).foreach {
                  case (_,tv: TV) => tv.tsc.remove(k)
                  case _ => ()
                }
              }
              u._2.foreach { k =>
                k.constraints.head.iterator.zip(k.tvs).foreach {
                  case (c, (pol, t)) => if (pol) rec(t, c, false) else rec(c, t, false)
                }
              }
            }
            lhs.lowerBounds.foreach(rec(_, rhs, true)) // propagate from the bound
            
          case (lhs, rhs: TypeVariable) if lhs.level <= rhs.level =>
            println(s"NEW $rhs LB (${lhs.level})")
            val newBound = (cctx._1 ::: cctx._2.reverse).foldLeft(lhs)((ty, c) =>
              if (c.prov is noProv) ty else mkProxy(ty, c.prov))
            rhs.lowerBounds ::= newBound // update the bound
            if (noApproximateOverload) {
              rhs.tsc.foreachEntry { (tsc, v) =>
                v.foreach { i =>
                  if(tsc.tvs(i)._1) {
                    tsc.updateOn(i, lhs)
                    if (tsc.constraints.isEmpty) reportError()
                  }
                }
              }
              val u = rhs.tsc.keysIterator.filter(_.constraints.sizeCompare(1)===0).duplicate
              u._1.foreach { k =>
                k.tvs.mapValuesIter(_.unwrapProxies).foreach {
                  case (_,tv: TV) => tv.tsc.remove(k)
                  case _ => ()
                }
              }
              u._2.foreach { k =>
                k.constraints.head.iterator.zip(k.tvs).foreach {
                  case (c, (pol, t)) => if (pol) rec(t, c, false) else rec(c, t, false)
                }
              }
            }
            rhs.upperBounds.foreach(rec(lhs, _, true)) // propagate from the bound
            
            
          case (lhs: TypeVariable, rhs) =>
            val tv = lhs
            println(s"wrong level: ${rhs.level}")
            if (constrainedTypes && rhs.level <= lvl) {
              println(s"STASHING $tv bound in extr ctx")
              val buf = ctx.extrCtx.getOrElseUpdate(tv, Buffer.empty)
              buf += false -> rhs
              cache -= lhs -> rhs
              ()
            } else {
              val rhs2 = extrudeAndCheck(rhs, lhs.level, false, MaxLevel,
                cctx._1 :: prevCctxs.unzip._1 ::: prevCctxs.unzip._2)
              println(s"EXTR RHS  ~>  $rhs2  to ${lhs.level}")
              println(s" where ${rhs2.showBounds}")
              // println(s"   and ${rhs.showBounds}")
              rec(lhs, rhs2, true)
            }
            
          case (lhs, rhs: TypeVariable) =>
            val tv = rhs
            println(s"wrong level: ${lhs.level}")
            if (constrainedTypes && lhs.level <= lvl) {
              println(s"STASHING $tv bound in extr ctx")
              val buf = ctx.extrCtx.getOrElseUpdate(tv, Buffer.empty)
              buf += true -> lhs
              cache -= lhs -> rhs
              ()
            } else {
              val lhs2 = extrudeAndCheck(lhs, rhs.level, true, MaxLevel,
                cctx._2 :: prevCctxs.unzip._2 ::: prevCctxs.unzip._1)
              println(s"EXTR LHS  ~>  $lhs2  to ${rhs.level}")
              println(s" where ${lhs2.showBounds}")
              // println(s"   and ${lhs.showBounds}")
              rec(lhs2, rhs, true)
            }
            
            
          case (TupleType(fs0), TupleType(fs1)) if fs0.size === fs1.size => // TODO generalize (coerce compatible tuples)
            fs0.lazyZip(fs1).foreach { case ((ln, l), (rn, r)) =>
              ln.foreach { ln => rn.foreach { rn =>
                if (ln =/= rn) err(
                  msg"Wrong tuple field name: found '${ln.name}' instead of '${rn.name}'",
                  lhs.prov.loco // TODO better loco
              )}}
              recLb(r, l)
              rec(l.ub, r.ub, false)
            }
          case (t: ArrayBase, a: ArrayType) =>
            recLb(a.inner, t.inner)
            rec(t.inner.ub, a.inner.ub, false)
          case (ComposedType(true, l, r), _) =>
            rec(l, rhs, true) // Q: really propagate the outerProv here?
            rec(r, rhs, true)
          case (_, ComposedType(false, l, r)) =>
            rec(lhs, l, true) // Q: really propagate the outerProv here?
            rec(lhs, r, true)
          case (p @ ProxyType(und), _) => rec(und, rhs, true)
          case (_, p @ ProxyType(und)) => rec(lhs, und, true)
          case (_, TupleType(f :: Nil)) if funkyTuples =>
            rec(lhs, f._2.ub, true) // FIXME actually needs reified coercion! not a true subtyping relationship
          case (err @ ClassTag(ErrTypeId, _), FunctionType(l1, r1)) =>
            rec(l1, err, false)
            rec(err, r1, false)
          case (FunctionType(l0, r0), err @ ClassTag(ErrTypeId, _)) =>
            rec(err, l0, false)
            rec(r0, err, false)
          case (RecordType(fs0), RecordType(fs1)) =>
            fs1.foreach { case (n1, t1) =>
              fs0.find(_._1 === n1).fold {
                reportError()
              } { case (n0, t0) =>
                recLb(t1, t0)
                rec(t0.ub, t1.ub, false)
              }
            }
          case (tup: TupleType, _: RecordType) =>
            rec(tup.toRecord, rhs, true) // Q: really support this? means we'd put names into tuple reprs at runtime
          case (err @ ClassTag(ErrTypeId, _), RecordType(fs1)) =>
            fs1.foreach(f => rec(err, f._2.ub, false))
          case (_, RecordType(fs1)) =>
            goToWork(lhs, rhs)
          case (RecordType(fs1), err @ ClassTag(ErrTypeId, _)) =>
            fs1.foreach(f => rec(f._2.ub, err, false))
            
          case (tr1: TypeRef, tr2: TypeRef)
          if tr1.defn.name =/= "Array" && tr2.defn.name =/= "Eql" =>
            if (tr1.defn === tr2.defn) {
              assert(tr1.targs.sizeCompare(tr2.targs) === 0)
              ctx.tyDefs.get(tr1.defn.name) match {
                case S(td) =>
                  val tvv = td.getVariancesOrDefault
                  td.tparamsargs.unzip._2.lazyZip(tr1.targs).lazyZip(tr2.targs).foreach { (tv, targ1, targ2) =>
                    val v = tvv(tv)
                    if (!v.isContravariant) rec(targ1, targ2, false)
                    if (!v.isCovariant) rec(targ2, targ1, false)
                  }
                case N =>
                  /* 
                  ctx.tyDefs2(tr1.defn.name).complete() match {
                    case cls: TypedNuCls =>
                      cls.tparams.map(_._2).lazyZip(tr1.targs).lazyZip(tr2.targs).foreach {
                        (tv, targ1, targ2) =>
                          val v = cls.varianceOf(tv)
                          if (!v.isContravariant) rec(targ1, targ2, false)
                          if (!v.isCovariant) rec(targ2, targ1, false)
                      }
                    // case _ => ???
                  }
                  */
                  ctx.tyDefs2.get(tr1.defn.name) match {
                    case S(lti) =>
                      lti.tparams.map(_._2).lazyZip(tr1.targs).lazyZip(tr2.targs).foreach {
                        (tv, targ1, targ2) =>
                          val v = lti.varianceOf(tv)
                          if (!v.isContravariant) rec(targ1, targ2, false)
                          if (!v.isCovariant) rec(targ2, targ1, false)
                      }
                    case N =>
                      ??? // TODO
                  }
              }
            } else {
              if (tr1.mayHaveTransitiveSelfType) rec(tr1.expand, tr2.expand, true)
              else (tr1.mkClsTag, tr2.mkClsTag) match {
                case (S(tag1), S(tag2)) if !(tag1 <:< tag2) =>
                  reportError()
                case _ =>
                  rec(tr1.expand, tr2.expand, true)
              }
            }
          case (tr: TypeRef, _) => rec(tr.expand, rhs, true)
          case (err @ ClassTag(ErrTypeId, _), tr: TypeRef) =>
            // rec(tr.copy(targs = tr.targs.map(_ => err))(noProv), tr, true)
            // * ^ Nicely propagates more errors to the result,
            // * but can incur vast amounts of unnecessary constraining in the context of recursive types!
            ()
          case (_, tr: TypeRef) =>
            rec(lhs, tr.expand, true)
          
          case (ClassTag(ErrTypeId, _), _) => ()
          case (_, ClassTag(ErrTypeId, _)) => ()
          case (_, w @ Without(b, ns)) => rec(lhs.without(ns), b, true)
          case (_, n @ NegType(w @ Without(b, ns))) =>
            rec(Without(lhs, ns)(w.prov), NegType(b)(n.prov), true) // this is weird... TODO check sound
            
            
          case (_, poly: PolymorphicType) =>
            val oldCtx = ctx
            ctx.nextLevel { implicit ctx =>
              val rigid = poly.rigidify
              println(s"BUMP TO LEVEL ${lvl}  -->  $rigid")
              println(s"where ${rigid.showBounds}")
              val res = rec(lhs, rigid, true)
              unstash(oldCtx)
              res
            }
            
          case (AliasOf(PolymorphicType(plvl, bod)), _) if bod.level <= plvl =>
            rec(bod, rhs, true)
            
          case (_, PolyFunction(newRhs)) if distributeForalls =>
            println(s"DISTRIB-R  ~>  $newRhs")
            rec(lhs, newRhs, true)
            
          // * Simple case when the parameter type vars don't need to be split
          case (AliasOf(PolymorphicType(plvl, AliasOf(FunctionType(param, bod)))), _)
          if distributeForalls
          && param.level <= plvl
          && bod.level > plvl =>
            val newLhs = FunctionType(param, PolymorphicType(plvl, bod))(rhs.prov)
            println(s"DISTRIB-L  ~>  $newLhs")
            rec(newLhs, rhs, true)
            
          // * Difficult case: split off type parameters that are quantified in body but NOT in param
          case (SplittablePolyFun(newLhs), _) if distributeForalls =>
            println(s"DISTRIB-L'  ~>  $newLhs")
            rec(newLhs, rhs, true)
            
          case (poly: PolymorphicType, _) =>
            // TODO Here it might actually be better to try and put poly into a TV if the RHS contains one
            //    ^ Note: similar remark applies inside constrainDNF
            
            // * [note:1] This assertion seems to hold most of the time,
            // *  with notable exceptions occurring in QML existential encoding tests
            // assert(lvl >= rhs.level)
            
            // * Note: we instantiate `poly` at the current context's polymorphic level.
            // * This level can either be the current typing level,
            // * at which the type variables obtained from cosntraining are expected to be;
            // * or it can be a "bumped-up" level locally introdcued
            // * when comparing against a polymorphic RHS signature that needed to be rigidified
            // * – in this case, the higher level is meant to allow further instantiations to match
            // * the rigid type variables without extrusion,
            // * while preventing the rigid variables from leaking out.
            
            // * [note:2] Hack ("heuristic"): we only start remembering `prevCctxs`
            // * after going through at least one instantiation.
            // * This is to filter out locations that were unlikely to cause
            // * any skolem extrusion down the line.
            // *  – indeed, skolem extrusions are often caused by premature instantiation.
            (if (prevCctxs.isEmpty) (Nil -> Nil) :: Nil else prevCctxs) |> {
              implicit prevCctxs => rec(poly.instantiate, rhs, true)
            }
            
          case (ConstrainedType(cs, bod), _) =>
            trace(s"DISCHARGE CONSTRAINTS") {
              cs.foreach { case (lb, ub) => 
               rec(lb, ub, false)
              }
            }()
            rec(bod, rhs, true)
          case (_, ConstrainedType(cs, bod)) => ??? // TODO?
          case (_, ComposedType(true, l, r)) =>
            goToWork(lhs, rhs)
          case (ComposedType(false, l, r), _) =>
            goToWork(lhs, rhs)
          case (ov: Overload, _) =>
            // * This is a large approximation
            // * TODO: remove approx. through use of ambiguous constraints
            rec(ov.approximatePos, rhs, true)
          case (_: NegType | _: Without, _) | (_, _: NegType | _: Without) =>
            goToWork(lhs, rhs)
          case (_: ClassTag | _: TraitTag, _: TraitTag) =>
            goToWork(lhs, rhs)
          case _ => reportError()
      }}
    }}()
    
    def reportError(failureOpt: Opt[Message] = N)(implicit cctx: ConCtx, ctx: Ctx): Unit = {
      val lhs = cctx._1.head
      val rhs = cctx._2.head
      
      println(s"CONSTRAINT FAILURE: $lhs <: $rhs")
      // println(s"CTX: ${cctx.map(_.map(lr => s"${lr._1} <: ${lr._2} [${lr._1.prov}] [${lr._2.prov}]"))}")
      
      def doesntMatch(ty: SimpleType) = msg"does not match type `${ty.expNeg}`"
      def doesntHaveField(n: Str) = msg"does not have field '$n'"
      
      val lhsChain: List[ST] = cctx._1
      val rhsChain: List[ST] = cctx._2
      
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
      
      
      // * Accumulate messages showing possibly-helpful type annotations.
      def getPossibleAnnots(cctxs: Ls[Ls[ST]]): Ls[Message -> Opt[Loc]] = {
        val suggested = MutSet.empty[Loc]
        val removed = MutSet.empty[Loc]
        def go(cctxs: Ls[Ls[ST]]): Ls[Message -> Opt[Loc]] = cctxs match {
          case reason :: reasons =>
            val possible = reason.iterator.map(_.prov).collect {
              case p @ TypeProvenance(loco @ S(loc), desc, _, _)
                if !suggested.contains(loc)
                && !p.isType
                && !suggested.exists(loc covers _)
              =>
                suggested.foreach(loc2 => if (loc2 covers loc) removed += loc2)
                suggested.add(loc)
                msg"• this ${desc}:" -> loco
            }.toList
            possible ::: go(reasons)
          case Nil => Nil
        }
        go(cctxs).filterNot(_._2.exists(removed))
      }
      
      def mk_constraintProvenanceHints = rhsProv.loco match {
        case S(rhsProv_loc) if !prov.loco.contains(rhsProv_loc) && !shownLocos(rhsProv_loc) =>
          msg"Note: constraint arises from ${rhsProv.desc}:" -> show(rhsProv.loco) :: (
            rhsProv2.loco match {
              case S(rhsProv2_loc)
                if rhsProv2_loc =/= rhsProv_loc
                && !prov.loco.contains(rhsProv2_loc)
                && !lhsProv.loco.contains(rhsProv2_loc)
                && !shownLocos(rhsProv2_loc)
                => msg"from ${rhsProv2.desc}:" -> show(rhsProv2.loco) :: Nil
              case _ => Nil
            })
        case _ => Nil
      }
      
      
      val lhsBase = lhs.typeBase
      def lhsIsPlain = lhsBase matches {
        case _: FunctionType | _: RecordType | _: TypeTag | _: TupleType
           | _: TypeRef | _: ExtrType => true
      }
      
      val failure = failureOpt.getOrElse((lhsBase, rhs.unwrapProvs) match {
        case lhs_rhs @ ((_: Extruded, _) | (_, _: Extruded)) =>
          val (mainExtr, extr1, extr2, reason) = lhs_rhs match {
            case (extr: Extruded, extr2: Extruded)
              =>
              (extr, S(extr), S(extr2), extr.reason ++ extr2.reason)
              // * ^ Note: I expect extr.reason and extr2.reason to have the same size.
              // * Interleave them for more natural reporting order?
            case (extr: Extruded, _) => (extr, S(extr), N, extr.reason)
            case (_, extr: Extruded) => (extr, N, S(extr), extr.reason)
            case _ => die
          }
          val possibleAnnots = getPossibleAnnots(reason)
          val e1loco = show(lhsProv.loco).orElse(show(mainExtr.underlying.prov.loco))
            .orElse(show(mainExtr.underlying.id.prov.loco))
          val msgs = msg"Type error in ${prov.desc}" -> show(prov.loco) ::
            msg"type variable `${mainExtr.underlying.expPos}` leaks out of its scope" ->
              e1loco :: (extr2 match {
                case S(extr2) =>
                  val e2loco = show(rhsProv.loco).orElse(show(extr2.underlying.prov.loco))
                    .orElse(show(extr2.underlying.id.prov.loco))
                  if (extr1.isDefined && e2loco =/= e1loco)
                    msg"back into type variable `${extr2.underlying.expNeg}`" -> e2loco :: Nil
                  else Nil
                case N =>
                  msg"into ${printProv(rhsProv)} `${rhs.expNeg}`" -> show(rhsProv.loco) :: Nil
              }) ::: (
                if (possibleAnnots.nonEmpty)
                  msg"adding a type annotation to any of the following terms may help resolve the problem" -> N ::
                    possibleAnnots
                else Nil
              ) ::: (
                rhsProv2.loco match {
                  case S(rhsProv2_loc)
                    if !rhsProv.loco.contains(rhsProv2_loc)
                    && !prov.loco.contains(rhsProv2_loc)
                    && !lhsProv.loco.contains(rhsProv2_loc)
                    && !shownLocos(rhsProv2_loc)
                    => msg"Note: constraint arises from ${rhsProv2.desc}:" -> show(rhsProv2.loco) :: Nil
                  case _ => Nil
                }
              )
          return raise(ErrorReport(msgs ::: mk_constraintProvenanceHints, newDefs))
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
          if lhsIsPlain && !lunw.isInstanceOf[RecordType] =>
            msg"is not a record (expected a record with field${
              if (fs.sizeCompare(1) > 0) "s" else ""}: ${fs.map(_._1.name).mkString(", ")})"
        case (lunw, RecordType(fs @ (_ :: _))) =>
          msg"does not have all required fields ${fs.map("'" + _._1.name + "'").mkString(", ")}"
        case _ => doesntMatch(rhs)
      })
      
      
      val mismatchMessage =
        msg"Type mismatch in ${prov.desc}:" -> show(prov.loco) :: (
          msg"${printProv(lhsProv)} `${lhs.expPos}` $failure"
        ) -> (if (lhsProv.loco === prov.loco) N else show(lhsProv.loco)) :: Nil
      
      val flowHint = 
        tighestRelevantFailure.map { l =>
          val expTyMsg = msg" with expected type `${rhs.expNeg}`"
          msg"but it flows into ${l.prov.desc}$expTyMsg" -> show(l.prov.loco) :: Nil
        }.toList.flatten
      
      val constraintProvenanceHints = mk_constraintProvenanceHints
      
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
      
      val msgs = Ls[Ls[Message -> Opt[Loc]]](
        mismatchMessage,
        flowHint,
        constraintProvenanceHints,
        originProvHints,
        detailedContext,
      ).flatten
      
      raise(ErrorReport(msgs, newDefs))
    }
    
    rec(lhs, rhs, true)(raise, Nil -> Nil, Nil, outerCtx, shadows)
  }}
  
  
  
  def subsume(ty_sch: ST, sign: ST)
      (implicit ctx: Ctx, raise: Raise, prov: TypeProvenance): Unit = {
    println(s"CHECKING SUBSUMPTION...")
    var errCnt = 0
    constrain(ty_sch, sign)({ err =>
      errCnt += 1
      if (errCnt > maxSuccessiveErrReports) {
        // * Silence further errors
        if (showAllErrors) notifyMoreErrors("signature-checking", prov)
        return
      }
      else if (showAllErrors || errCnt === 1) raise(err)
    }, prov, ctx, Shadows.empty)
  }
  
  
  
  /** Copies a type up to its type variables of wrong level (and their extruded bounds),
    * meaning those non-locally-quantified type variables whose level is strictly greater than `lowerLvl`.
    * Parameter `upperLvl` is used to track above which level we DON'T want to extrude variables,
    * as we may be traversing types that are quantified by polymorphic types in the process of being copied.
    * `upperLvl` tracks the lowest such current quantification level. */
  private final
  def extrude(ty: SimpleType, lowerLvl: Int, pol: Boolean, upperLvl: Level)
        (implicit ctx: Ctx, cache: MutMap[TypeVarOrRigidVar->Bool, TypeVarOrRigidVar], cache2: MutSortMap[TraitTag, TraitTag], reason: Ls[Ls[ST]])
        : SimpleType =
  // (trace(s"EXTR[${printPol(S(pol))}] $ty || $lowerLvl .. $upperLvl  ${ty.level} ${ty.level <= lowerLvl}"){
    if (ty.level <= lowerLvl) ty else ty match {
      case t @ TypeBounds(lb, ub) => if (pol) extrude(ub, lowerLvl, true, upperLvl) else extrude(lb, lowerLvl, false, upperLvl)
      case t @ FunctionType(l, r) => FunctionType(extrude(l, lowerLvl, !pol, upperLvl), extrude(r, lowerLvl, pol, upperLvl))(t.prov)
      case t @ ComposedType(p, l, r) => ComposedType(p, extrude(l, lowerLvl, pol, upperLvl), extrude(r, lowerLvl, pol, upperLvl))(t.prov)
      case t @ RecordType(fs) =>
        RecordType(fs.mapValues(_.update(extrude(_, lowerLvl, !pol, upperLvl), extrude(_, lowerLvl, pol, upperLvl))))(t.prov)
      case t @ TupleType(fs) =>
        TupleType(fs.mapValues(_.update(extrude(_, lowerLvl, !pol, upperLvl), extrude(_, lowerLvl, pol, upperLvl))))(t.prov)
      case t @ ArrayType(ar) =>
        ArrayType(ar.update(extrude(_, lowerLvl, !pol, upperLvl), extrude(_, lowerLvl, pol, upperLvl)))(t.prov)
      case w @ Without(b, ns) => Without(extrude(b, lowerLvl, pol, upperLvl), ns)(w.prov)
      case tv @ AssignedVariable(ty) =>
        cache.getOrElse(tv -> true, {
          val nv = freshVar(tv.prov, S(tv), tv.nameHint)(lowerLvl)
          cache += tv -> true -> nv
          val tyPos = extrude(ty, lowerLvl, true, upperLvl)
          val tyNeg = extrude(ty, lowerLvl, false, upperLvl)
          if (tyPos === tyNeg)
            nv.assignedTo = S(tyPos)
          else {
            assert(nv.lowerBounds.isEmpty)
            assert(nv.upperBounds.isEmpty)
            nv.lowerBounds = tyPos :: Nil
            nv.upperBounds = tyNeg :: Nil
          }
          nv
        })
      case tv: TypeVariable if tv.level > upperLvl =>
        assert(!cache.contains(tv -> false), (tv, cache))
        // * If the TV's level is strictly greater than `upperLvl`,
        // *  it means the TV is quantified by a type being copied,
        // *  so all we need to do is copy this TV along (it is not extruded).
        // * We pick `tv -> true` (and not `tv -> false`) arbitrarily.
        if (tv.lowerBounds.isEmpty && tv.upperBounds.isEmpty) tv
        else cache.getOrElse(tv -> true, {
          val nv = freshVar(tv.prov, S(tv), tv.nameHint)(tv.level)
          cache += tv -> true -> nv
          nv.lowerBounds = tv.lowerBounds.map(extrude(_, lowerLvl, true, upperLvl))
          nv.upperBounds = tv.upperBounds.map(extrude(_, lowerLvl, false, upperLvl))
          nv
        })
      case t @ SpliceType(fs) => 
        t.updateElems(extrude(_, lowerLvl, pol, upperLvl), extrude(_, lowerLvl, !pol, upperLvl), extrude(_, lowerLvl, pol, upperLvl), t.prov)
      case tv: TypeVariable => cache.getOrElse(tv -> pol, {
        val nv = freshVar(tv.prov, S(tv), tv.nameHint)(lowerLvl)
        cache += tv -> pol -> nv
        if (pol) {
          tv.upperBounds ::= nv
          nv.lowerBounds = tv.lowerBounds.map(extrude(_, lowerLvl, pol, upperLvl))
        } else {
          tv.lowerBounds ::= nv
          nv.upperBounds = tv.upperBounds.map(extrude(_, lowerLvl, pol, upperLvl))
        }
        nv
      })
      case n @ NegType(neg) => NegType(extrude(neg, lowerLvl, !pol, upperLvl))(n.prov)
      case e @ ExtrType(_) => e
      case p @ ProvType(und) => ProvType(extrude(und, lowerLvl, pol, upperLvl))(p.prov)
      case p @ ProxyType(und) => extrude(und, lowerLvl, pol, upperLvl)
      case tt @ SkolemTag(id) =>
        if (tt.level > upperLvl) {
          extrude(id, lowerLvl, pol, upperLvl) match {
            case id: TV => SkolemTag(id)(tt.prov)
            case _ => die
          }
        } else if (tt.level > lowerLvl) {
            // * When a rigid type variable is extruded,
            // * we need to essentially widen it to Top or Bot.
            // * Creating a new skolem instead, as was done at some point, is actually unsound.
            // * But for better error messages, we instead use an `Extruded` abstract tag,
            // * making sure we pick a *different* one for positive and negative positions,
            // * which achieves the same effect as Top/Bot.
            new Extruded(!pol, tt)(
              tt.prov.copy(desc = "extruded type variable reference"), reason)
        } else die // shouldn't happen
      case _: ClassTag | _: TraitTag | _: Extruded => ty
      case tr @ TypeRef(d, ts) =>
        TypeRef(d, tr.mapTargs(S(pol)) {
          case (N, targ) =>
            // * Note: the semantics of TypeBounds is inappropriuate for this use (known problem; FIXME later)
            TypeBounds.mk(extrude(targ, lowerLvl, false, upperLvl), extrude(targ, lowerLvl, true, upperLvl)) // Q: ? subtypes?
            // * A sanity-checking version, making sure the type range is correct (LB subtype of UB):
            /* 
            val a = extrude(targ, lowerLvl, false, upperLvl)
            val b = extrude(targ, lowerLvl, true, upperLvl)
            implicit val r: Raise = throw _
            implicit val p: TP = noProv
            constrain(a, b)
            TypeBounds.mk(a, b)
            */
          case (S(pol), targ) => extrude(targ, lowerLvl, pol, upperLvl)
        })(tr.prov)
      case PolymorphicType(polymLevel, body) =>
        PolymorphicType(polymLevel, extrude(body, lowerLvl, pol, upperLvl =
            // upperLvl min polymLevel // * for some crazy reason, this stopped type checking
            Math.min(upperLvl, polymLevel)
          ))
      case ConstrainedType(cs, bod) =>
        ConstrainedType(cs.map { case (lo, hi) =>
          extrude(lo, lowerLvl, true, upperLvl) -> extrude(hi, lowerLvl, false, upperLvl)
        }, extrude(bod, lowerLvl, pol, upperLvl))
      case o @ Overload(alts) =>
        o.mapAlts(extrude(_, lowerLvl, !pol, upperLvl))(extrude(_, lowerLvl, pol, upperLvl))
    }
    // }(r => s"=> $r"))
  
  
  def err(msg: Message, loco: Opt[Loc])(implicit raise: Raise): SimpleType = {
    err(msg -> loco :: Nil)
  }
  def err(msgs: List[Message -> Opt[Loc]])(implicit raise: Raise): SimpleType = {
    err(ErrorReport(msgs, newDefs))
  }
  def err(diag: Diagnostic)(implicit raise: Raise): SimpleType = {
    raise(diag)
    errType
  }
  def errType: SimpleType = ClassTag(ErrTypeId, Set.empty)(noProv)
  
  def warn(msg: Message, loco: Opt[Loc])(implicit raise: Raise): Unit =
    warn(msg -> loco :: Nil)

  def warn(msgs: List[Message -> Opt[Loc]])(implicit raise: Raise): Unit =
    raise(WarningReport(msgs, newDefs))
  
  
  
  def unify(lhs: ST, rhs: ST)(implicit raise: Raise, prov: TypeProvenance, ctx: Ctx, 
          shadows: Shadows = Shadows.empty
        ): Unit = {
    trace(s"$lvl. U $lhs =! $rhs") {
      
      def rec(lhs: ST, rhs: ST, swapped: Bool): Unit =
        if (!lhs.mentionsTypeBounds && lhs === rhs) () else
        (lhs, rhs) match {
          
          // TODO handle more cases
          
          case (tv: TV, bound) if bound.level <= tv.level =>
            tv.assignedTo match {
              case S(et) =>
                unify(et, bound)
              case N =>
                println(s"$tv := $bound")
                val lbs = tv.lowerBounds
                val ubs = tv.upperBounds
                tv.assignedTo = S(bound)
                lbs.foreach(constrainImpl(_, bound))
                ubs.foreach(constrainImpl(bound, _))
            }
            
          case _ =>
            if (swapped) {
              constrain(lhs, rhs)
              constrain(rhs, lhs)
            } else rec(rhs, lhs, true)
            
        }
      rec(lhs, rhs, false)
    }()
  }
  
  
  
  /** Freshens all the type variables whose level is comprised in `(above, below]`
    *   or which have bounds and whose level is greater than `above`. */
  def freshenAbove(above: Level, ty: SimpleType,
          rigidify: Bool = false, below: Level = MaxLevel, leaveAlone: Set[TV] = Set.empty)
        (implicit ctx: Ctx, freshened: MutMap[TV, ST])
        : SimpleType =
  {
    def freshenImpl(ty: SimpleType, below: Level): SimpleType =
    // (trace(s"${lvl}. FRESHEN $ty || $above .. $below  ${ty.level} ${ty.level <= above}")
    {
      // * Cannot soundly freshen if the context's level is above the current polymorphism level,
      // * as that would wrongly capture the newly-freshened variables.
      require(below >= lvl)
      
      def freshen(ty: SimpleType): SimpleType = freshenImpl(ty, below)
      
      if (
        // * Note that commenting this broke the old semantics of wildcard TypeBound-s in signatures:
        /* !rigidify // Rigidification now also substitutes TypeBound-s with fresh vars;
                    // since these have the level of their bounds, when rigidifying
                    // we need to make sure to copy the whole type regardless of level...
        && */ ty.level <= above) ty else ty match {
      
      case tv: TypeVariable if leaveAlone(tv)  => tv
      
      case tv @ AssignedVariable(ty) =>
        freshened.getOrElse(tv, {
          val nv = freshVar(tv.prov, S(tv), tv.nameHint)(if (tv.level > below) tv.level else lvl)
          freshened += tv -> nv
          val ty2 = freshen(ty)
          nv.assignedTo = S(ty2)
          nv
        })
      
      // * Note: I forgot why I though this was unsound...
      /*
      case tv: TypeVariable // THIS IS NOT SOUND: WE NEED TO REFRESH REGARDLESS!!
        if tv.level > below
        // It is not sound to ignore the bounds here,
        //    as the bounds could contain references to other TVs with lower level;
        //  OTOH, we don't want to traverse the whole bounds graph every time just to check
        //    (using `levelBelow`),
        //    so if there are any bounds registered, we just conservatively freshen the TV.
        && tv.lowerBounds.isEmpty
        && tv.upperBounds.isEmpty
        => tv
      */
      
      case tv: TypeVariable => freshened.get(tv) match {
        case Some(tv) => tv
        case None if rigidify && tv.level <= below =>
          // * Rigid type variables (ie, skolems) are encoded as SkolemTag-s
          val rv = SkolemTag(freshVar(noProv, S(tv), tv.nameHint/* .orElse(S("_"))*/))(tv.prov)
          println(s"New skolem: $tv ~> $rv")
          if (tv.lowerBounds.nonEmpty || tv.upperBounds.nonEmpty) { // TODO just add bounds to skolems! should lead to simpler constraints
            // The bounds of `tv` may be recursive (refer to `tv` itself),
            //    so here we create a fresh variabe that will be able to tie the presumed recursive knot
            //    (if there is no recursion, it will just be a useless type variable)
            val tv2 = freshVar(tv.prov, S(tv), tv.nameHint)(lvl)
            freshened += tv -> tv2
            // Assuming there were no recursive bounds, given L <: tv <: U,
            //    we essentially need to turn tv's occurrence into the type-bounds (rv | L)..(rv & U),
            //    meaning all negative occurrences should be interpreted as rv | L
            //    and all positive occurrences should be interpreted as rv & U
            //    where rv is the rigidified variables.
            // Now, since there may be recursive bounds, we do the same
            //    but through the indirection of a type variable tv2:
            tv2.lowerBounds ::= tv.upperBounds.map(freshen).foldLeft(rv: ST)(_ & _)
            println(s"$tv2 :> ${tv2.lowerBounds}")
            tv2.upperBounds ::= tv.lowerBounds.map(freshen).foldLeft(rv: ST)(_ | _)
            println(s"$tv2 <: ${tv2.upperBounds}")
            tv2
          } else {
            // NOTE: tv.level may be different from lvl; is that OK?
            freshened += tv -> rv
            rv
          }
        case None =>
          val v = freshVar(tv.prov, S(tv), tv.nameHint)(if (tv.level > below) tv.level else {
            assert(lvl <= below, "this condition should be false for the result to be correct")
            lvl
          })
          val freshentsc = tv.tsc.flatMap { case (tsc,_) =>
            if (tsc.tvs.values.map(_.unwrapProxies).forall {
              case tv: TV => !freshened.contains(tv)
              case _ => true
            }) S(tsc) else N
          }
          freshened += tv -> v
          v.lowerBounds = tv.lowerBounds.mapConserve(freshen)
          v.upperBounds = tv.upperBounds.mapConserve(freshen)
          freshentsc.foreach { tsc =>
            val t = new TupleSetConstraints(tsc.constraints, tsc.tvs)
            t.constraints = t.constraints.map(_.map(freshen))
            t.tvs = t.tvs.map(x => (x._1,freshen(x._2)))
            t.tvs.values.map(_.unwrapProxies).zipWithIndex.foreach {
              case (tv: TV, i) => tv.tsc.updateWith(t)(_.map(_ + i).orElse(S(Set(i))))
              case _ => ()
            }
          }
          v
      }
      
      case t @ TypeBounds(lb, ub) =>
        
        // * This was done to make `?` behave similarly to an existential.
        // * But this niche treatment just needlessly complicates things;
        // * better implement proper existentials later on!
        /*
        if (rigidify) {
          val tv = freshVar(t.prov, N) // FIXME coudl N here result in divergence? cf. absence of shadow
          tv.lowerBounds ::= freshen(lb)
          tv.upperBounds ::= freshen(ub)
          tv
        } else TypeBounds(freshen(lb), freshen(ub))(t.prov)
        */
        
        TypeBounds(freshen(lb), freshen(ub))(t.prov)
        
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
      case s @ SkolemTag(id) if s.level > above && s.level <= below =>
        freshen(id)
      case _: ClassTag | _: TraitTag | _: SkolemTag | _: Extruded => ty
      case w @ Without(b, ns) => Without(freshen(b), ns)(w.prov)
      case tr @ TypeRef(d, ts) => TypeRef(d, ts.map(freshen(_)))(tr.prov)
      case pt @ PolymorphicType(polyLvl, bod) if pt.level <= above => pt // is this really useful?
      case pt @ PolymorphicType(polyLvl, bod) =>
        if (lvl > polyLvl) freshen(pt.raiseLevelToImpl(lvl, leaveAlone))
        else PolymorphicType(polyLvl, freshenImpl(bod, below = below min polyLvl))
      case ct @ ConstrainedType(cs, bod) =>
        val cs2 = cs.map(lu => freshen(lu._1) -> freshen(lu._2))
        ConstrainedType(cs2, freshen(bod))
      case o @ Overload(alts) =>
        o.mapAlts(freshen)(freshen)
    }}
    // (r => s"=> $r"))
    
    freshenImpl(ty, below)
  }
  
  
  
}
