package funtypes

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import funtypes.utils._, shorthands._
import funtypes.Message._

class ConstraintSolver extends TyperDatatypes { self: Typer =>
  def verboseConstraintProvenanceHints: Bool = verbose
  
  type ConstraintSet = MutSet[(TV, Bool, SimpleType)]
  object DryRunFailure extends Throwable
  
  /** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. */
  def constrain(lhs: SimpleType, rhs: SimpleType)(implicit raise: Raise, prov: TypeProvenance): Unit = {
    // We need a cache to remember the subtyping tests in process; we also make the cache remember
    // past subtyping tests for performance reasons (it reduces the complexity of the algoritghm):
    val cache: MutSet[(SimpleType, SimpleType)] = MutSet.empty
    
    println(s"CONSTRAIN $lhs <! $rhs")
    println(s"  where ${FunctionType(lhs, rhs)(noProv).showBounds}")
    
    type ConCtx = Ls[Ls[SimpleType -> SimpleType]]
    
    /* Solve annoying constraints,
        which are those that involve either unions and intersections at the wrong polarities, or negations.
        This works by constructing all pairs of "conjunctive-normal-form <: disjunctive-normal-form"
        implied by the constraint, where each conjunct and disjunct is a ConstructedType
          (i.e., has a proper type constructor, as opposed to "data flow" types like unions/intrsections,
          top/bottom, negations, and type variables).
        We then perform constraining dry runs between all possible "conjunct <: disjunct" sub-pairs of these,
        and at the end we check that we're left with exactly one possible set of unambiguous constraints. */
    def annoying(ls: Ls[SimpleType], done_ls: Ls[ConstructedType], rs: Ls[SimpleType], done_rs: Ls[ConstructedType])
          (implicit ctx: ConCtx, outerDryRuns: Ls[ConstraintSet]): Unit = {
      (ls, rs) match {
        // If we find a type variable, we can weasel out of the annoying constraint by delaying its resolution,
        // saving it as negations in the variable's bounds!
        case ((tv: TypeVariable) :: ls, _) =>
          def tys = (ls.iterator ++ done_ls.iterator).map(NegType(_)(noProv)) ++ rs.iterator ++ done_rs.iterator
          val rhs = tys.reduceOption(ComposedType(true, _, _)(noProv)).getOrElse(ExtrType(true)(noProv))
          rec(tv, rhs)
        case (_, (tv: TypeVariable) :: rs) =>
          def tys = ls.iterator ++ done_ls.iterator ++ (rs.iterator ++ done_rs.iterator).map(NegType(_)(noProv))
          val lhs = tys.reduceOption(ComposedType(false, _, _)(noProv)).getOrElse(ExtrType(false)(noProv))
          rec(lhs, tv)
        case (ComposedType(true, ll, lr) :: ls, _) =>
          annoying(ll :: ls, done_ls, rs, done_rs)
          annoying(lr :: ls, done_ls, rs, done_rs)
        case (_, ComposedType(false, rl, rr) :: rs) =>
          annoying(ls, done_ls, rl :: rs, done_rs)
          annoying(ls, done_ls, rr :: rs, done_rs)
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
        case ((l: ConstructedType) :: ls, rs) => annoying(ls, l :: done_ls, rs, done_rs)
        case (ls, (r: ConstructedType) :: rs) => annoying(ls, done_ls, rs, r :: done_rs)
        case (Nil, Nil) =>
          // TODO what to do with VarTypes? When to widen them?
          // TODO check whether the intersection is known to be empty (if so, we are done)
          println(s"CN ${done_ls} <: ${done_rs}")
          // First find all the ways this constraint could be solved
          var successfulDryRuns: Ls[ConstraintSet -> Ls[Warning]] = Nil
          for {
            l <- done_ls
            r <- done_rs
          } {
            // Do dry-runs of constraint solving
            var warnings = mutable.ListBuffer.empty[Warning]
            val dr: ConstraintSet = MutSet.empty
            val dryRuns: Ls[ConstraintSet] = dr :: outerDryRuns
            val raise: Raise = {
              case _: TypeError => throw DryRunFailure // constraint fails!
              case w: Warning => warnings += w; () // we'll only report the warning if the dry run succeeds
            }
            trace("DRY RUN") {
              try {
                rec(l, r)(raise, ctx, dryRuns)
                println(s"SUCCESS: ${dr.toList}")
                if (dr.isEmpty) // We have a clear winner! No need for bounds updates!
                  return ()
                successfulDryRuns ::= dr -> warnings.toList
                // ^ Note: in principle, no need to propagate these bounds — it's already done in the `rec` function.
              } catch { case DryRunFailure => }
            }()
          }
          if (successfulDryRuns.isEmpty)
            reportError(L(doesntMatch(ctx.head.head._2)))
          else {
            val successfulDryRunConstraints = successfulDryRuns.map(_._1)
            mergeConstraintSets(successfulDryRunConstraints) match {
              case S(c) =>
                println(s"MERGED ${c}")
                // Apply the resulting merged constraint set:
                outerDryRuns.headOption match { // if we're already in an outer dry run, we need to update that dry run!
                  case S(dr) => c.foreach(dr.+=)
                  case N => // otherwise, we actually commit the bounds directly:
                    c.foreach {
                      case (tv, true, rhs) => tv.upperBounds ::= rhs
                      case (tv, false, lhs) => tv.lowerBounds ::= lhs
                    }
                }
                successfulDryRuns.foreach(_._2.foreach(raise)) // raise all the warnings found while constraining
              case N =>
                // Note: if dryRun.nonEmpty, this will actually throw a DryRunFailure to be handled upstream:
                reportError(R(successfulDryRunConstraints))
            }
          }
      }
    }
    def mergeConstraintSets(cs: Ls[ConstraintSet]): Opt[ConstraintSet] = cs.head optionIf (cs.size === 1) orElse S {
      val res = MutMap.empty[TV -> Bool, SimpleType]
      cs.foreach { c =>
        c.foreach { case (tv, pol, ty) =>
          // Give up merging if it involves more than one variable bound (we can probably do something better):
          res.find(kv => kv._1._2 =/= pol || kv._1._1 =/= tv).foreach { _ => return N }
          res(tv -> pol) = res.get(tv -> pol).fold(ty)(ComposedType(pol, _, ty)(noProv))
        }
      }
      MutSet.from(res.iterator.map(kv => (kv._1._1, kv._1._2, kv._2)))
    }
    
    def rec(lhs: SimpleType, rhs: SimpleType, outerProv: Opt[TypeProvenance]=N)
          (implicit raise: Raise, ctx: ConCtx, dryRuns: Ls[ConstraintSet]): Unit =
    trace(s"C $lhs <! $rhs") {
      // println(s"  where ${FunctionType(lhs, rhs)(primProv).showBounds}")
      ((lhs -> rhs :: ctx.headOr(Nil)) :: ctx.tailOr(Nil)) |> { implicit ctx =>
        if (lhs is rhs) return
        val lhs_rhs = lhs -> rhs
        lhs_rhs match {
          // There is no need to remember the subtyping tests performed that did not involve
          // type variables, as type variables will necessary be part of any possible cycles.
          // Since these types form regular trees, there will necessarily be a point where a
          // variable part of a cycle will be matched against the same type periodically.
          case (_: TypeVariable, _) | (_, _: TypeVariable) =>
            if (cache(lhs_rhs)) return
            cache += lhs_rhs
          case _ => ()
        }
        lhs_rhs match {
          case (ExtrType(true), _) => ()
          case (_, ExtrType(false)) => ()
          case (NegType(lhs), NegType(rhs)) => rec(rhs, lhs)
          case (FunctionType(l0, r0), FunctionType(l1, r1)) =>
            rec(l1, l0)(raise, Nil, dryRuns)
            // ^ disregard error context: keep it from reversing polarity (or the messages become redundant)
            rec(r0, r1)(raise, Nil :: ctx, dryRuns)
          case (prim: PrimType, _) if rhs === prim || rhs === prim.widen => ()
          case (lhs: TypeVariable, rhs) if rhs.level <= lhs.level =>
            // TODO should we directly constrain those variables created after the dry run began...?
            val newBound = outerProv.fold(rhs)(ProxyType(rhs)(_, S(prov)))
            dryRuns.headOption match {
              case Some(dr) => dr += ((lhs, true, newBound)) // update the dry-run bound
              case None => lhs.upperBounds ::= newBound // update the actual bound if not dry-running
            }
            dryRuns.foreach { dr => // propagate in all outer dry runs
              dr.foreach { case (`lhs`, false, l) => rec(l, rhs); case _ => () }
            }
            lhs.lowerBounds.foreach(rec(_, rhs)) // propagate from the actual bound
          case (lhs, rhs: TypeVariable) if lhs.level <= rhs.level =>
            val newBound = outerProv.fold(lhs)(ProxyType(lhs)(_, S(prov)))
            dryRuns.headOption match {
              case Some(dr) => dr += ((rhs, false, newBound)) // update the bound
              case None => rhs.lowerBounds ::= newBound // update the actual bound if not dry-running
            }
            dryRuns.foreach { dr => // propagate in all outer dry runs
              dr.foreach { case (`rhs`, true, r) => rec(lhs, r); case _ => () }
            }
            rhs.upperBounds.foreach(rec(lhs, _)) // propagate from the actual bound
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
          case (vt: VarType, wt: VarType) if vt.vi === wt.vi => () // Q: do not constr the sign?
          case (_, vt: VarType) if vt.isAlias => rec(lhs, vt.sign)
          case (TupleType(fs0), TupleType(fs1)) if fs0.size === fs1.size => // TODO generalize (coerce compatible tuples)
            fs0.lazyZip(fs1).foreach { case ((ln, l), (rn, r)) =>
              ln.foreach { ln => rn.foreach { rn =>
                if (ln =/=rn) err(
                  msg"Wrong tuple field name: found '${ln}' instead of '${rn}'", lhs.prov.loco) } } // TODO better loco
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
          case (_, ComposedType(true, l, r)) =>
            annoying(lhs :: Nil, Nil, l :: r :: Nil, Nil)
          case (ComposedType(false, l, r), _) =>
            annoying(l :: r :: Nil, Nil, rhs :: Nil, Nil)
          case (_: NegType, _) | (_, _: NegType) =>
            annoying(lhs :: Nil, Nil, rhs :: Nil, Nil)
          case (vt: VarType, _) => rec(vt.sign, rhs)
          case (_, TupleType(f :: Nil)) =>
            rec(lhs, f._2) // FIXME actually needs reified coercion! not a true subtyping relationship
          case (err @ PrimType(ErrTypeId), FunctionType(l1, r1)) =>
            rec(l1, err)
            rec(err, r1)
          case (FunctionType(l0, r0), err @ PrimType(ErrTypeId)) =>
            rec(err, l0)
            rec(r0, err)
          case (AppType(fun0, args0), AppType(fun1, args1)) if fun0.isInjective && fun1.isInjective =>
            rec(fun0, fun1)
            if (args0.size =/= args1.size) ??? // TODO: compute baseType args, accounting for class inheritance
            else args0.lazyZip(args1).foreach(rec(_, _))
          case (_, a @ AppType(fun, arg :: Nil)) =>
            rec(FunctionType(arg, lhs)(fun.prov), fun)(raise, Nil, dryRuns) // disregard error context?
            // TODO make reporting better... should forget about the function expansion if it doesn't work out!
          case (_, AppType(fun, args)) => lastWords(s"$rhs") // TODO
          case (AppType(fun, arg :: Nil), _) =>
            rec(fun, FunctionType(arg, rhs)(lhs.prov))(raise, Nil, dryRuns) // disregard error context?
          case (AppType(fun, args :+ arg), _) =>
            rec(AppType(fun, args)(lhs.prov), FunctionType(arg, rhs)(lhs.prov))(raise, Nil, dryRuns) // Q: disregard error context?
          case (tup: TupleType, _: RecordType) =>
            rec(tup.toRecord, rhs)
          case (err @ PrimType(ErrTypeId), RecordType(fs1)) =>
            fs1.foreach(f => rec(err, f._2))
          case (RecordType(fs1), err @ PrimType(ErrTypeId)) =>
            fs1.foreach(f => rec(f._2, err))
          case (PrimType(ErrTypeId), _) => ()
          case (_, PrimType(ErrTypeId)) => ()
          case _ =>
            val failureOpt = lhs_rhs match {
              case (RecordType(fs0), RecordType(fs1)) =>
                var fieldErr: Opt[Message] = N
                fs1.foreach { case (n1, t1) =>
                  fs0.find(_._1 === n1).fold {
                    if (fieldErr.isEmpty) fieldErr = S(doesntHaveField(n1))
                  } { case (n0, t0) => rec(t0, t1) }
                }
                fieldErr
              case (_, FunctionType(_, _)) => S(msg"is not a function")
              case (_, RecordType((n, _) :: Nil)) => S(doesntHaveField(n))
              case _ => S(doesntMatch(lhs_rhs._2))
            }
            failureOpt.foreach(f => reportError(L(f)))
      }
    }}()
    
    def doesntMatch(ty: SimpleType) = msg"does not match type `${ty.expNeg}`"
    def doesntHaveField(n: Str) = msg"does not have field '$n'"
    def reportError(error: Message \/ Ls[ConstraintSet])(implicit ctx: ConCtx, dryRuns: Ls[ConstraintSet]): Unit = {
      val (lhs_rhs @ (lhs, rhs)) = ctx.head.head
      val failure = error match {
        case L(msg) => msg
        case R(_) => msg"matches several possible instantiations"
      }
      println(s"CONSTRAINT FAILURE: $lhs <: $rhs")
      println(s"CTX: ${ctx.map(_.map(lr => s"${lr._1} <: ${lr._2} [${lr._1.prov}]"))}")
      
      if (dryRuns.nonEmpty) throw DryRunFailure
      
      val detailedContext =
        if (explainErrors)
          msg"[info] Additional Explanations below:" -> N ::
          ctx.reverseIterator.flatMap { case subCtx => if (subCtx.isEmpty) Nil else {
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
      
      val lhsProv = ctx.head.find(_._1.prov.loco.isDefined).map(_._1.prov).getOrElse(lhs.prov)
      assert(lhsProv.loco.isDefined) // TODO use soft assert
      
      val relevantFailures = ctx.zipWithIndex.map { case (subCtx, i) =>
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
      
      val tighestLocatedRHS = ctx.flatMap { subCtx =>
        subCtx.flatMap { case (l, r) =>
          val considered = (true, r, r.prov) :: r.ctxProv.dlof((false, r, _) :: Nil)(Nil)
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
        msg"${if (error.isLeft) msg"Type mismatch" else "Ambiguous constraint"} in ${prov.desc}:" -> prov.loco :: Nil,
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
          if (error.isLeft) {
            val lunw = l.unwrapProxies
            lazy val fail = (l, r) match {
              case (RecordType(fs0), RecordType(fs1)) =>
                (fs0.map(_._1).toSet -- fs1.map(_._1).toSet).headOption.fold(doesntMatch(r)) { n1 =>
                  doesntHaveField(n1)
                }
              case (_, FunctionType(_, _))
                if !lunw.isInstanceOf[FunctionType]
                && !lunw.isInstanceOf[TypeVariable]
                => msg"is not a function"
              case (_, RecordType((n, _) :: Nil))
                if !lunw.isInstanceOf[RecordType]
                && !lunw.isInstanceOf[TypeVariable]
                => doesntHaveField(n)
              case _ => doesntMatch(r)
            }
            msg"but it flows into ${l.prov.desc}$expTyMsg" -> l.prov.loco ::
            (if (isSameType) Nil else msg"which $fail" -> N :: Nil)
          } else msg"where it is used in ${l.prov.desc}$expTyMsg" -> l.prov.loco :: Nil
        }.toList.flatten,
        error match {
          case L(_) => Nil
          case R(cs) =>
            val shownCs = cs.take(4)
            assert(shownCs.size > 0)
            val notShownNum = cs.size - shownCs.size
            val notSownMsg =
              if (notShownNum > 0)
                msg"(And ${notShownNum.toString} more instantiations not shown.)" -> N :: Nil
              else Nil
            var isFirst = true
            shownCs.flatMap { c =>
              msg"${
                if (isFirst) {
                  isFirst = false
                  msg"A"
                } else msg"Another"
              } possible instantiation is:" -> N ::
              c.toList.sortBy(_._1.uid).map { // TODO limit the number of constraints shown here?
                case (tv, true, ty) =>
                  msg"    ${tv.expPos} <: ${ty.expNeg}" -> N
                case (tv, false, ty) =>
                  msg"    ${tv.expNeg} :> ${ty.expPos}" -> N
              }
            } ::: notSownMsg ::: msg"Use an explicit type annotation to fix the problem." -> N :: Nil
        },
        constraintProvenanceHints,
        detailedContext,
      ).flatten
      raise(TypeError(msgs))
    }
    
    rec(lhs, rhs, N)(raise, Nil, Nil)
  }
  
  
  /** Copies a type up to its type variables of wrong level (and their extruded bounds). */
  def extrude(ty: SimpleType, lvl: Int, pol: Boolean)
      (implicit cache: MutMap[Variable, Variable] = MutMap.empty): SimpleType =
    if (ty.level <= lvl) ty else ty match {
      case t @ FunctionType(l, r) => FunctionType(extrude(l, lvl, !pol), extrude(r, lvl, pol))(t.prov)
      case t @ ComposedType(p, l, r) => ComposedType(p, extrude(l, lvl, pol), extrude(r, lvl, pol))(t.prov)
      case a @ AppType(f, as) => AppType(extrude(f, lvl, !pol), as.map(extrude(_, lvl, pol)))(a.prov)
      case t @ RecordType(fs) => RecordType(fs.map(nt => nt._1 -> extrude(nt._2, lvl, pol)))(t.prov)
      case t @ TupleType(fs) => TupleType(fs.map(nt => nt._1 -> extrude(nt._2, lvl, pol)))(t.prov)
      case tv: TypeVariable => cache.getOrElse(tv, {
        val nv = freshVar(tv.prov)(lvl)
        cache += (tv -> nv)
        if (pol) { tv.upperBounds ::= nv
          nv.lowerBounds = tv.lowerBounds.map(extrude(_, lvl, pol)) }
        else { tv.lowerBounds ::= nv
          nv.upperBounds = tv.upperBounds.map(extrude(_, lvl, pol)) }
        nv
      })
      case vt: VarType => cache.getOrElse(vt, VarType(
        if (vt.vi.lvl <= lvl) vt.vi
        else new VarIdentity(lvl, vt.vi.v), extrude(vt.sign, lvl, pol), vt.isAlias)(vt.prov))
      case n @ NegType(neg) => NegType(extrude(neg, lvl, pol))(n.prov)
      case e @ ExtrType(_) => e
      case p @ ProxyType(und) => ProxyType(extrude(und, lvl, pol))(p.prov)
      case PrimType(_) => ty
    }
  
  
  def err(msg: Message, loco: Opt[Loc])(implicit raise: Raise, prov: TypeProvenance): SimpleType = {
    raise(TypeError((msg, loco) :: Nil))
    errType
  }
  def errType(implicit prov: TypeProvenance): SimpleType = PrimType(ErrTypeId)(prov)
  
  def warn(msg: Message, loco: Opt[Loc])(implicit raise: Raise): Unit =
    raise(Warning((msg, loco) :: Nil))
  
  
  // Note: maybe this and `extrude` should be merged?
  def freshenAbove(lim: Int, ty: SimpleType)(implicit lvl: Int): SimpleType = {
    val freshened = MutMap.empty[Variable, Variable]
    def freshen(ty: SimpleType): SimpleType = if (ty.level <= lim) ty else ty match {
      case tv: TypeVariable => freshened.get(tv) match {
        case Some(tv) => tv
        case None =>
          val v = freshVar(tv.prov)
          freshened += tv -> v
          // v.lowerBounds = tv.lowerBounds.mapConserve(freshen)
          // v.upperBounds = tv.upperBounds.mapConserve(freshen)
          //  ^ the above are more efficient, but they lead to a different order
          //    of fresh variable creations, which leads to some types not being
          //    simplified the same when put into the RHS of a let binding...
          v.lowerBounds = tv.lowerBounds.reverse.map(freshen).reverse
          v.upperBounds = tv.upperBounds.reverse.map(freshen).reverse
          v
      }
      case vt: VarType => VarType(
        if (vt.vi.lvl > lim) new VarIdentity(lvl, vt.vi.v)
        else vt.vi, freshen(vt.sign), vt.isAlias
      )(vt.prov)
      case t @ FunctionType(l, r) => FunctionType(freshen(l), freshen(r))(t.prov)
      case t @ ComposedType(p, l, r) => ComposedType(p, freshen(l), freshen(r))(t.prov)
      case a @ AppType(lhs, args) => AppType(freshen(lhs), args.map(freshen))(a.prov)
      case t @ RecordType(fs) => RecordType(fs.map(ft => ft._1 -> freshen(ft._2)))(t.prov)
      case t @ TupleType(fs) => TupleType(fs.map(nt => nt._1 -> freshen(nt._2)))(t.prov)
      case n @ NegType(neg) => NegType(freshen(neg))(n.prov)
      case e @ ExtrType(_) => e
      case p @ ProxyType(und) => ProxyType(freshen(und))(p.prov)
      case PrimType(_) => ty
    }
    freshen(ty)
  }
  
  
}
