package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class ConstraintSolver extends NormalForms { self: Typer =>
  def verboseConstraintProvenanceHints: Bool = verbose
  
  private var constrainCalls = 0
  private var annoyingCalls = 0
  def stats: (Int, Int) = (constrainCalls, annoyingCalls)
  def resetStats(): Unit = {
    constrainCalls = 0
    annoyingCalls  = 0
  }
  
  /** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. */
  def constrain(lhs: SimpleType, rhs: SimpleType)(implicit raise: Raise, prov: TypeProvenance, ctx: Ctx): Unit = {
    // We need a cache to remember the subtyping tests in process; we also make the cache remember
    // past subtyping tests for performance reasons (it reduces the complexity of the algoritghm):
    val cache: MutSet[(SimpleType, SimpleType)] = MutSet.empty
    
    println(s"CONSTRAIN $lhs <! $rhs")
    println(s"  where ${FunctionType(lhs, rhs)(noProv).showBounds}")
    
    type ConCtx = Ls[Ls[SimpleType -> SimpleType]]
    
    
    def mkCase[A](str: Str)(k: Str => A)(implicit dbgHelp: Str): A = {
      val newStr = dbgHelp + "." + str
      println(newStr)
      k(newStr)
    }
    
    /* Solve annoying constraints,
        which are those that involve either unions and intersections at the wrong polarities, or negations.
        This works by constructing all pairs of "conjunct <: disjunct" implied by the conceptual
        "DNF <: CNF" form of the constraint. */
    def annoying(ls: Ls[SimpleType], done_ls: LhsNf, rs: Ls[SimpleType], done_rs: RhsNf)
          (implicit cctx: ConCtx, dbgHelp: Str = "Case"): Unit = {
        annoyingCalls += 1
        
        // TODO to improve performance, avoid re-normalizing already-normalized types!!
        annoyingImpl(ls.mapHead(_.normalize(true)), done_ls, rs, done_rs)
        
        // TODO strenghten normalization in negative position and use the following instead:
        // annoyingImpl(ls.mapHead(_.normalize(true)), done_ls, rs.mapHead(_.normalize(false)), done_rs)
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
      (ls, rs) match {
        // If we find a type variable, we can weasel out of the annoying constraint by delaying its resolution,
        // saving it as negations in the variable's bounds!
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
          
        case ((tr @ TypeRef(_, _)) :: ls, rs) => annoying(tr.expand :: ls, done_ls, rs, done_rs)
        case (ls, (tr @ TypeRef(_, _)) :: rs) => annoying(ls, done_ls, tr.expand :: rs, done_rs)
        
        case (Without(b: TypeVariable, ns) :: ls, rs) => rec(b, mkRhs(ls).without(ns))
        case (Without(NegType(b: TypeVariable), ns) :: ls, rs) => rec(b, NegType(mkRhs(ls).without(ns))(noProv))
        case (Without(_, _) :: ls, rs) => lastWords(s"`pushPosWithout` should have removed this Without")
        case (ls, Without(_, _) :: rs) => lastWords(s"unexpected Without in negative position not at the top level")
          
        case ((l: BaseTypeOrTag) :: ls, rs) => annoying(ls, done_ls & l getOrElse
          (return println(s"OK  $done_ls & $l  =:=  ${BotType}")), rs, done_rs)
        case (ls, (r: BaseTypeOrTag) :: rs) => annoying(ls, done_ls, rs, done_rs | r getOrElse
          (return println(s"OK  $done_rs | $r  =:=  ${TopType}")))
          
        case ((l: RecordType) :: ls, rs) => annoying(ls, done_ls & l, rs, done_rs)
        case (ls, (r @ RecordType(Nil)) :: rs) => ()
        case (ls, (r @ RecordType(f :: Nil)) :: rs) => annoying(ls, done_ls, rs, done_rs | f getOrElse
          (return println(s"OK  $done_rs | $f  =:=  ${TopType}")))
        case (ls, (r @ RecordType(fs)) :: rs) => annoying(ls, done_ls, r.toInter :: rs, done_rs)
          
        case (Nil, Nil) =>
          def fail = reportError(doesntMatch(cctx.head.head._2))
          (done_ls, done_rs) match { // TODO missing cases
            case (LhsTop, _) | (LhsRefined(N, empty(), RecordType(Nil)), _)
              | (_, RhsBot) | (_, RhsBases(Nil, N)) =>
              // TODO ^ actually get rid of LhsTop and RhsBot...? (might make constraint solving slower)
              fail
            case (LhsRefined(_, ts, _), RhsBases(pts, _)) if ts.exists(pts.contains) =>
            case (LhsRefined(S(f0@FunctionType(l0, r0)), ts, r)
                , RhsBases(_, S(L(f1@FunctionType(l1, r1))))) =>
              rec(f0, f1)
            case (LhsRefined(S(f: FunctionType), ts, r), RhsBases(pts, _)) =>
              annoying(Nil, LhsRefined(N, ts, r), Nil, done_rs)
            case (LhsRefined(S(pt: ClassTag), ts, r), RhsBases(pts, bf)) =>
              if (pts.contains(pt) || pts.exists(p => pt.parentsST.contains(p.id)))
                println(s"OK  $pt  <:  ${pts.mkString(" | ")}")
              // else f.fold(fail)(f => annoying(Nil, done_ls, Nil, f))
              else annoying(Nil, LhsRefined(N, ts, r), Nil, RhsBases(Nil, bf))
            case (LhsRefined(bo, ts, r), RhsField(n, t2)) =>
              r.fields.find(_._1 === n) match {
                case S(nt1) => rec(nt1._2, t2)
                case N => fail
              }
            case (LhsRefined(bo, ts, r), RhsBases(_, S(R(RhsField(n, t2))))) => // Q: missing anything in prev fields?
              // TODO dedup with above
              r.fields.find(_._1 === n) match {
                case S(nt1) => rec(nt1._2, t2)
                case N => fail
              }
            case (LhsRefined(N, ts, r), RhsBases(pts, N | S(L(_: FunctionType)))) => fail
            case (LhsRefined(S(b), ts, r), RhsBases(pts, _)) =>
              lastWords(s"TODO ${done_ls} <: ${done_rs} (${b.getClass})") // TODO
          }
          
      }
    }()
    
    def rec(lhs: SimpleType, rhs: SimpleType, outerProv: Opt[TypeProvenance]=N)
          (implicit raise: Raise, cctx: ConCtx): Unit = {
      constrainCalls += 1
      val pushed = lhs.pushPosWithout
      if (pushed isnt lhs) println(s"Push LHS  $lhs  ~>  $pushed")
      recImpl(pushed, rhs, outerProv)
    }
    def recImpl(lhs: SimpleType, rhs: SimpleType, outerProv: Opt[TypeProvenance]=N)
          (implicit raise: Raise, cctx: ConCtx): Unit =
    trace(s"C $lhs <! $rhs") {
      // println(s"  where ${FunctionType(lhs, rhs)(primProv).showBounds}")
      ((lhs -> rhs :: cctx.headOr(Nil)) :: cctx.tailOr(Nil)) |> { implicit cctx =>
        if (lhs is rhs) return
        val lhs_rhs = lhs -> rhs
        lhs_rhs match {
          // There is no need to remember the subtyping tests performed that did not involve
          // type variables or type references, as these will necessary be part of any possible
          // cycles. Since these types form regular trees, there will necessarily be a point where
          // a variable or type ref part of a cycle will be matched against the same type periodically.
          case (_: TypeVariable | _: TypeRef, _) | (_, _: TypeVariable | _: TypeRef) =>
            if (cache(lhs_rhs)) return
            cache += lhs_rhs
          case _ => ()
        }
        lhs_rhs match {
          case (ExtrType(true), _) => ()
          case (_, ExtrType(false) | RecordType(Nil)) => ()
          case (TypeBounds(lb, ub), _) => rec(ub, rhs)
          case (_, TypeBounds(lb, ub)) => rec(lhs, lb)
          case (NegType(lhs), NegType(rhs)) => rec(rhs, lhs)
          case (FunctionType(l0, r0), FunctionType(l1, r1)) =>
            rec(l1, l0)(raise, Nil)
            // ^ disregard error context: keep it from reversing polarity (or the messages become redundant)
            rec(r0, r1)(raise, Nil :: cctx)
          case (prim: ClassTag, _) if rhs === prim => ()
          case (prim: ClassTag, ClassTag(id:Var, _)) if prim.parents.contains(id) => ()
          case (lhs: TypeVariable, rhs) if rhs.level <= lhs.level =>
            val newBound = outerProv.fold(rhs)(ProvType(rhs)(_))
            lhs.upperBounds ::= newBound // update the bound
            lhs.lowerBounds.foreach(rec(_, rhs)) // propagate from the bound
          case (lhs, rhs: TypeVariable) if lhs.level <= rhs.level =>
            val newBound = outerProv.fold(lhs)(ProvType(lhs)(_))
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
          case (TupleType(fs0), TupleType(fs1)) if fs0.size === fs1.size => // TODO generalize (coerce compatible tuples)
            fs0.lazyZip(fs1).foreach { case ((ln, l), (rn, r)) =>
              ln.foreach { ln => rn.foreach { rn =>
                if (ln =/=rn) err(
                  msg"Wrong tuple field name: found '${ln.name}' instead of '${rn.name}'", lhs.prov.loco) } } // TODO better loco
              rec(l, r)
            }
          case (ComposedType(true, l, r), _) =>
            rec(l, rhs, outerProv.orElse(S(lhs.prov))) // Q: really propagate the outerProv here?
            rec(r, rhs, outerProv.orElse(S(lhs.prov)))
          case (_, ComposedType(false, l, r)) =>
            rec(lhs, l, outerProv.orElse(S(lhs.prov))) // Q: really propagate the outerProv here?
            rec(lhs, r, outerProv.orElse(S(lhs.prov)))
          case (p @ ProxyType(und), _) => rec(und, rhs, outerProv.orElse(S(p.prov)))
          case (_, p @ ProxyType(und)) => rec(lhs, und, outerProv.orElse(S(p.prov)))
          case (_, TupleType(f :: Nil)) =>
            rec(lhs, f._2) // FIXME actually needs reified coercion! not a true subtyping relationship
          case (err @ ClassTag(ErrTypeId, _), FunctionType(l1, r1)) =>
            rec(l1, err)
            rec(err, r1)
          case (FunctionType(l0, r0), err @ ClassTag(ErrTypeId, _)) =>
            rec(err, l0)
            rec(r0, err)
          case (tup: TupleType, _: RecordType) =>
            rec(tup.toRecord, rhs)
          case (err @ ClassTag(ErrTypeId, _), RecordType(fs1)) =>
            fs1.foreach(f => rec(err, f._2))
          case (RecordType(fs1), err @ ClassTag(ErrTypeId, _)) =>
            fs1.foreach(f => rec(f._2, err))
          case (tr: TypeRef, _) => rec(tr.expand, rhs)
          case (_, tr: TypeRef) => rec(lhs, tr.expand)
          case (ClassTag(ErrTypeId, _), _) => ()
          case (_, ClassTag(ErrTypeId, _)) => ()
          case (_, w @ Without(b, ns)) => rec(Without(lhs, ns)(w.prov), b)
          case (_, n @ NegType(w @ Without(b, ns))) => rec(Without(lhs, ns)(w.prov), NegType(b)(n.prov))
          case (_, ComposedType(true, l, r)) =>
            annoying(lhs :: Nil, LhsTop, l :: r :: Nil, RhsBot)
          case (ComposedType(false, l, r), _) =>
            annoying(l :: r :: Nil, LhsTop, rhs :: Nil, RhsBot)
          case (_: NegType | _: Without, _) | (_, _: NegType | _: Without) =>
            annoying(lhs :: Nil, LhsTop, rhs :: Nil, RhsBot)
          case _ =>
            val failureOpt = lhs_rhs match {
              case (RecordType(fs0), RecordType(fs1)) =>
                var fieldErr: Opt[Message] = N
                fs1.foreach { case (n1, t1) =>
                  fs0.find(_._1 === n1).fold {
                    if (fieldErr.isEmpty) fieldErr = S(doesntHaveField(n1.name))
                  } { case (n0, t0) => rec(t0, t1) }
                }
                fieldErr
              case (_, FunctionType(_, _)) => S(msg"is not a function")
              case (_, RecordType((n, _) :: Nil)) => S(doesntHaveField(n.name))
              case _ => S(doesntMatch(lhs_rhs._2))
            }
            failureOpt.foreach(f => reportError(f))
      }
    }}()
    
    def doesntMatch(ty: SimpleType) = msg"does not match type `${ty.expNeg}`"
    def doesntHaveField(n: Str) = msg"does not have field '$n'"
    def reportError(error: Message)(implicit cctx: ConCtx): Unit = {
      val (lhs_rhs @ (lhs, rhs)) = cctx.head.head
      val failure = error
      println(s"CONSTRAINT FAILURE: $lhs <: $rhs")
      println(s"CTX: ${cctx.map(_.map(lr => s"${lr._1} <: ${lr._2} [${lr._1.prov}] [${lr._2.prov}]"))}")
      
      val detailedContext =
        if (explainErrors)
          msg"[info] Additional Explanations below:" -> N ::
          cctx.reverseIterator.flatMap { case subCtx => if (subCtx.isEmpty) Nil else {
            val (lhss, rhss) = subCtx.unzip
            val prefixes = "" #:: LazyList.continually("i.e., ")
            msg"[info] While constraining..." -> N ::
            lhss.filter(_.prov =/= noProv).filterOutConsecutive(_.prov.loco === _.prov.loco).zip(prefixes).map {
              case (l, pre) => msg"[info]     ${pre}${l.prov.desc} of type ${l.expPos}" -> l.prov.loco
            } :::
            rhss.filter(_.prov =/= noProv).filterOutConsecutive(_.prov.loco === _.prov.loco).zip(prefixes).map {
              case (r, pre) => msg"[info]     ${pre}to match type ${r.expNeg} from ${r.prov.desc}" -> r.prov.loco
            }
          }}.toList
        else Nil
      
      val lhsProv = cctx.head.find(_._1.prov.loco.isDefined).map(_._1.prov).getOrElse(lhs.prov)
      
      // TODO re-enable
      // assert(lhsProv.loco.isDefined) // TODO use soft assert
      
      val relevantFailures = cctx.zipWithIndex.map { case (subCtx, i) =>
        subCtx.collectFirst {
          case (l, r)
            if l.prov.loco =/= lhsProv.loco
            && l.prov.loco.exists(ll => prov.loco/* .exists */.forall(ll touches _))
          => (l, r, i === 0)
        }
      }
      val tighestRelevantFailure = relevantFailures.firstSome
      // Don't seem to make a difference in the tests:
      // val tighestRelevantFailure = relevantFailures.collect { case Some(v) => v }.reverse
      // val tighestRelevantFailure = relevantFailures.reverse.firstSome // TODO try w/o rev
      
      var shownLocs = MutSet.empty[Loc]
      
      val tighestLocatedRHS = cctx.flatMap { subCtx =>
        subCtx.flatMap { case (l, r) =>
          val considered = (true, r, r.prov) :: Nil
          considered.filter { case (isMainProv, _, p) =>
            p.loco =/= prov.loco && (p.loco match {
              case Some(loco) =>
                !shownLocs(loco) &&
                (verboseConstraintProvenanceHints && isMainProv || !shownLocs.exists(loco touches _)) && {
                  shownLocs += loco
                  true
                }
              case None => false
            })
          }
        }
      }
      
      var first = true
      val constraintProvenanceHints = tighestLocatedRHS.map { case (isMainProv, r, p) =>
        if (isMainProv) {
          val msgHead = if (first) msg"Note: constraint arises " else msg""
          first = false
          msg"${msgHead}from ${p.desc}:" -> p.loco
        }
        else msg"in the context of ${p.desc}" -> p.loco
      }
      
      val msgs: Ls[Message -> Opt[Loc]] = List(
        msg"Type mismatch in ${prov.desc}:" -> prov.loco :: Nil,
        msg"expression of type `${lhs.expPos}` $failure" ->
          (if (lhsProv.loco === prov.loco) N else lhsProv.loco) :: Nil,
        tighestRelevantFailure.map { case (l, r, isSameType) =>
          // Note: used to have `val isSameType = l.unwrapProxies === lhs.unwrapProxies`
          //  which was only an approximation, and considered things like `?a | int` not the same as `int`.
          val expTyMsg =
            if (isSameType) msg" with expected type `${r.expNeg}`"
            // ^ This used to say "of expected type", but in fact we're describing a term with the wrong type;
            //   the expected type is not its type so that was not a good formulation.
            else msg" of type `${l.expPos}`"
          val lunw = l.unwrapProxies
          lazy val fail = (l, r) match {
            case (RecordType(fs0), RecordType(fs1)) =>
              (fs0.map(_._1).toSet -- fs1.map(_._1).toSet).headOption.fold(doesntMatch(r)) { n1 =>
                doesntHaveField(n1.name)
              }
            case (_, FunctionType(_, _))
              if !lunw.isInstanceOf[FunctionType]
              && !lunw.isInstanceOf[TypeVariable]
              => msg"is not a function"
            case (_, RecordType((n, _) :: Nil))
              if !lunw.isInstanceOf[RecordType]
              && !lunw.isInstanceOf[TypeVariable]
              => doesntHaveField(n.name)
            case _ => doesntMatch(r)
          }
          msg"but it flows into ${l.prov.desc}$expTyMsg" -> l.prov.loco ::
          (if (isSameType) Nil else msg"which $fail" -> N :: Nil)
        }.toList.flatten,
        constraintProvenanceHints,
        detailedContext,
      ).flatten
      raise(TypeError(msgs))
    }
    
    rec(lhs, rhs, N)(raise, Nil)
  }
  
  
  def subsume(ty_sch: PolymorphicType, sign: PolymorphicType)
      (implicit ctx: Ctx, raise: Raise, prov: TypeProvenance): Unit = {
    constrain(ty_sch.instantiate, sign.rigidify)
  }
  
  
  /** Copies a type up to its type variables of wrong level (and their extruded bounds). */
  def extrude(ty: SimpleType, lvl: Int, pol: Boolean)
      (implicit cache: MutMap[TV, TV] = MutMap.empty): SimpleType =
    if (ty.level <= lvl) ty else ty match {
      case t @ TypeBounds(lb, ub) => if (pol) extrude(ub, lvl, true) else extrude(lb, lvl, false)
      case t @ FunctionType(l, r) => FunctionType(extrude(l, lvl, !pol), extrude(r, lvl, pol))(t.prov)
      case t @ ComposedType(p, l, r) => ComposedType(p, extrude(l, lvl, pol), extrude(r, lvl, pol))(t.prov)
      case t @ RecordType(fs) => RecordType(fs.map(nt => nt._1 -> extrude(nt._2, lvl, pol)))(t.prov)
      case t @ TupleType(fs) => TupleType(fs.map(nt => nt._1 -> extrude(nt._2, lvl, pol)))(t.prov)
      case w @ Without(b, ns) => Without(extrude(b, lvl, pol), ns)(w.prov)
      case tv: TypeVariable => cache.getOrElse(tv, {
        val nv = freshVar(tv.prov, tv.nameHint)(lvl)
        cache += (tv -> nv)
        if (pol) { tv.upperBounds ::= nv
          nv.lowerBounds = tv.lowerBounds.map(extrude(_, lvl, pol)) }
        else { tv.lowerBounds ::= nv
          nv.upperBounds = tv.upperBounds.map(extrude(_, lvl, pol)) }
        nv
      })
      case n @ NegType(neg) => NegType(extrude(neg, lvl, pol))(n.prov)
      case e @ ExtrType(_) => e
      case p @ ProvType(und) => ProvType(extrude(und, lvl, pol))(p.prov)
      case p @ ProxyType(und) => extrude(und, lvl, pol)
      case _: ClassTag | _: TraitTag => ty
      case tr @ TypeRef(d, ts) =>
        /* Note: we could try to preserve TypeRef-s through extrusion,
            but in the absence of variance analysis it's a bit wasteful
            to always extrude in both directions: */
        // TypeRef(d, ts.map(t =>
        //   TypeBounds(extrude(t, lvl, pol), extrude(t, lvl, pol))(noProv)))(tr.prov, tr.ctx) // FIXME pol...
        extrude(tr.expand(_ => ()), lvl, pol).withProvOf(tr)
    }
  
  
  def err(msg: Message, loco: Opt[Loc])(implicit raise: Raise, prov: TypeProvenance): SimpleType = {
    err(msg -> loco :: Nil)
  }
  def err(msgs: List[Message -> Opt[Loc]])(implicit raise: Raise, prov: TypeProvenance): SimpleType = {
    raise(TypeError(msgs))
    errType
  }
  def errType(implicit prov: TypeProvenance): SimpleType = ClassTag(ErrTypeId, Set.empty)(prov)
  
  def warn(msg: Message, loco: Opt[Loc])(implicit raise: Raise): Unit =
    warn(msg -> loco :: Nil)

  def warn(msgs: List[Message -> Opt[Loc]])(implicit raise: Raise): Unit =
    raise(Warning(msgs))
  
  
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
            Var(tv.nameHint.getOrElse("_"+freshVar(noProv).toString).toString))(tv.prov)
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
      case t @ RecordType(fs) => RecordType(fs.map(ft => ft._1 -> freshen(ft._2)))(t.prov)
      case t @ TupleType(fs) => TupleType(fs.map(nt => nt._1 -> freshen(nt._2)))(t.prov)
      case n @ NegType(neg) => NegType(freshen(neg))(n.prov)
      case e @ ExtrType(_) => e
      case p @ ProvType(und) => ProvType(freshen(und))(p.prov)
      case p @ ProxyType(und) => freshen(und)
      case _: ClassTag | _: TraitTag => ty
      case w @ Without(b, ns) => Without(freshen(b), ns)(w.prov)
      case tr @ TypeRef(d, ts) => TypeRef(d, ts.map(freshen(_)))(tr.prov, tr.ctx)
    }
    freshen(ty)
  }
  
  
}
