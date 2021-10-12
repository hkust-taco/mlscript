package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class ConstraintSolver extends TyperDatatypes { self: Typer =>
  def verboseConstraintProvenanceHints: Bool = verbose
  
  private var constrainCalls = 0
  private var annoyingCalls = 0
  def stats: (Int, Int) = (constrainCalls, annoyingCalls)
  def resetStats(): Unit = {
    constrainCalls = 0
    annoyingCalls  = 0
  }
  
  /** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. */
  def constrain(lhs: SimpleType, rhs: SimpleType)(implicit raise: Raise, prov: TypeProvenance): Unit = {
    // We need a cache to remember the subtyping tests in process; we also make the cache remember
    // past subtyping tests for performance reasons (it reduces the complexity of the algoritghm):
    val cache: MutSet[(SimpleType, SimpleType)] = MutSet.empty
    
    println(s"CONSTRAIN $lhs <! $rhs")
    println(s"  where ${FunctionType(lhs, rhs)(noProv).showBounds}")
    
    type ConCtx = Ls[Ls[SimpleType -> SimpleType]]
    
    
    sealed abstract class LhsNf {
      def toTypes: Ls[SimpleType] = toType :: Nil
      def toType: SimpleType = this match {
        case LhsRefined(N, r, Nil) => r
        // case LhsRefined(N, RecordType(Nil), ws) => ws.reduce(_ & _)
        case LhsRefined(N, r, ws) => r & (ws:Ls[SimpleType]).reduce(_ & _)
        case LhsRefined(S(b), RecordType(Nil), Nil) => b
        case LhsRefined(S(b), r, ws) => b & r & (ws:Ls[SimpleType]).reduceOption(_ & _).getOrElse(TopType)
        case LhsTop => TopType
      }
      def & (that: BaseType): Opt[LhsNf] = (this, that) match {
        case (LhsTop, _) => S(LhsRefined(S(that), RecordType(Nil)(noProv), Nil))
        case (LhsRefined(b1, r1, w1), _) =>
          ((b1, that) match {
            case (S(p0 @ PrimType(pt0, ps0)), p1 @ PrimType(pt1, ps1)) =>
              println(s"!GLB! ${p0.glb(p1)}")
              p0.glb(p1)
            case (S(FunctionType(l0, r0)), FunctionType(l1, r1)) => S(FunctionType(l0 | l1, r0 & r1)(noProv/*TODO*/))
            case (S(AppType(l0, as0)), AppType(l1, as1)) => ???
            case (S(TupleType(fs0)), TupleType(fs1)) => ???
            case (S(VarType(_, _, _)), VarType(_, _, _)) => ???
            case (S(_), _) => N
            case (N, _) => S(that)
          }) map { b => LhsRefined(S(b), r1, w1) }
      }
      def & (that: RecordType): LhsNf = this match {
        case LhsTop => LhsRefined(N, that, Nil)
        case LhsRefined(b1, r1, w1) =>
          LhsRefined(b1, RecordType(mergeMap(r1.fields, that.fields)(_ & _).toList)(noProv/*TODO*/), w1)
      }
      def & (that: WithType): LhsNf = this match {
        case LhsTop => LhsRefined(N, RecordType(Nil)(noProv), that :: Nil)
        case LhsRefined(b1, r1, w1) =>
          LhsRefined(b1, r1, that :: w1)
      }
    }
    case class LhsRefined(base: Opt[BaseType], reft: RecordType, ws: Ls[WithType]) extends LhsNf {
      override def toString: Str = s"${base.getOrElse("")}${reft}${ws.map(" & " + _).mkString}"
    }
    case object LhsTop extends LhsNf
    
    sealed abstract class RhsNf {
      def toTypes: Ls[SimpleType] = toType :: Nil
      def toType: SimpleType = this match {
        case RhsField(n, t) => RecordType(n -> t :: Nil)(noProv) // FIXME prov
        case RhsBases(ps, b, f) => ps.foldLeft(b.getOrElse(BotType) | f.fold(BotType:SimpleType)(_.toType))(_ | _)
        case RhsBot => BotType
      }
      def | (that: BaseType): Opt[RhsNf] = (this, that) match {
        case (RhsBot, p: PrimType) => S(RhsBases(p::Nil,N,N))
        case (RhsBot, _) => S(RhsBases(Nil,S(that),N))
        case (RhsBases(ps, b, f), p: PrimType) =>
          S(RhsBases(if (ps.contains(p)) ps else p :: ps , b, f))
        case (RhsBases(ps, N, f), _) => S(RhsBases(ps, S(that), f))
        case (RhsBases(_, S(TupleType(_)), f), TupleType(_)) =>
          // ??? // TODO
          err("TODO handle tuples", prov.loco)
          N
        case (RhsBases(_, _, _), _) => N
        case (f @ RhsField(_, _), p: PrimType) => S(RhsBases(p::Nil, N, S(f)))
        case (f @ RhsField(_, _), _) => S(RhsBases(Nil, S(that), S(f)))
      }
      def | (that: (Str, SimpleType)): Opt[RhsNf] = this match {
        case RhsBot => S(RhsField(that._1, that._2))
        case RhsField(n1, t1) if n1 === that._1 => S(RhsField(n1, t1 | that._2))
        case RhsBases(p, b, N) => S(RhsBases(p, b, S(RhsField(that._1, that._2))))
        case RhsBases(p, b, S(RhsField(n1, t1))) if n1 === that._1 => S(RhsBases(p, b, S(RhsField(n1, t1 | that._2))))
        case _: RhsField | _: RhsBases => N
      }
    }
    case class RhsField(name: Str, ty: SimpleType) extends RhsNf
    case class RhsBases(prims: Ls[PrimType], bty: Opt[BaseType], f: Opt[RhsField]) extends RhsNf {
      assert(!bty.exists(_.isInstanceOf[PrimType]))
      // TODO assert we don't have both bases and a field? -> should make that an either...
      override def toString: Str = s"${prims.mkString("|")}|$bty|$f"
    }
    case object RhsBot extends RhsNf
    
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
          (implicit ctx: ConCtx, dbgHelp: Str = "Case"): Unit = {
        annoyingCalls += 1
        annoyingImpl(ls.mapHead(_.pushPosWithout), done_ls, rs, done_rs)
      }
    def annoyingImpl(ls: Ls[SimpleType], done_ls: LhsNf, rs: Ls[SimpleType], done_rs: RhsNf)
          (implicit ctx: ConCtx, dbgHelp: Str = "Case"): Unit = trace(s"A  $done_ls  %  $ls  <!  $rs  %  $done_rs") {
      // (ls, rs) match {
      (ls.mapHead(_.pushPosWithout), rs) match {
        // If we find a type variable, we can weasel out of the annoying constraint by delaying its resolution,
        // saving it as negations in the variable's bounds!
        case ((tv: TypeVariable) :: ls, _) =>
          def tys = (ls.iterator ++ done_ls.toTypes).map(_.neg()) ++ rs.iterator ++ done_rs.toTypes
          val rhs = tys.reduceOption(_ | _).getOrElse(BotType)
          rec(tv, rhs)
        case (_, (tv: TypeVariable) :: rs) =>
          def tys = ls.iterator ++ done_ls.toTypes ++ (rs.iterator ++ done_rs.toTypes).map(_.neg())
          val lhs = tys.reduceOption(_ & _).getOrElse(TopType)
          rec(lhs, tv)
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
        
        case ((l: BaseType) :: ls, rs) => annoying(ls, done_ls & l getOrElse
          (return println(s"OK  $done_ls & $l  =:=  ${BotType}")), rs, done_rs)
        case (ls, (r: BaseType) :: rs) => annoying(ls, done_ls, rs, done_rs | r getOrElse
          (return println(s"OK  $done_rs | $r  =:=  ${TopType}")))
          
        case ((l: RecordType) :: ls, rs) => annoying(ls, done_ls & l, rs, done_rs)
        case (ls, (r @ RecordType(Nil)) :: rs) => ()
        case (ls, (r @ RecordType(f :: Nil)) :: rs) => annoying(ls, done_ls, rs, done_rs | f getOrElse
          (return println(s"OK  $done_rs | $f  =:=  ${TopType}")))
        case (ls, (r @ RecordType(fs)) :: rs) => annoying(ls, done_ls, r.toInter :: rs, done_rs)
          
        // case ((w @ WithType(b, r)) :: ls, rs) =>
        case ((w: WithType) :: ls, rs) =>
          annoying(ls, done_ls & w, rs, done_rs)
        
        case (Without(rt:RecordType, ns) :: ls, rs) =>
          annoying(RecordType(rt.fields.filterNot(ns contains _._1))(rt.prov) :: ls, done_ls, rs, done_rs)
        // case (ls, Without(rt:RecordType, ns) :: rs) =>
        //   annoying(ls, done_ls, RecordType(rt.fields.filterNot(ns contains _._1))(rt.prov) :: rs, done_rs)
          
        case (Without(b:TypeVariable, ns) :: ls, rs) =>
          // println("!" + (ls.iterator ++ done_ls.toTypes).map(_.neg()).toList)
          // println("!" + ((ls.iterator ++ done_ls.toTypes).map(_.neg()) ++ rs.iterator ++ done_rs.toTypes).reduceOption(_ | _))
          def tys = (ls.iterator ++ done_ls.toTypes).map(_.neg()) ++ rs.iterator ++ done_rs.toTypes
          val rhs = tys.reduceOption(_ | _).getOrElse(ExtrType(true)(noProv))
          rec(b, rhs.without(ns))
        // case (Without(_, ns) :: ls, rs) => die
        // case (ls, Without(b:TypeVariable, ns) :: rs) =>
        case (ls, Without(b, ns) :: Nil) if done_rs === RhsBot =>
          def tys = ls.iterator ++ done_ls.toTypes
          val lhs = tys.reduceOption(_ & _).getOrElse(ExtrType(false)(noProv))
          rec(lhs.without(ns), b)
        case (ls, Without(b, ns) :: rs) =>
          def tys = ls.iterator ++ done_ls.toTypes ++ (rs.iterator ++ done_rs.toTypes).map(_.neg())
          val lhs = tys.reduceOption(_ & _).getOrElse(ExtrType(false)(noProv))
          rec(lhs.without(ns), b)
        
          /* 
        case (Without(np @ NegType(_: PrimType), ns) :: ls, rs) =>
          annoying(np :: ls, done_ls, rs, done_rs)
        case (ls, Without(np @ NegType(_: PrimType), ns) :: rs) =>
          annoying(ls, done_ls, np :: rs, done_rs)
        case (Without(ty, ns) :: ls, rs) => 
          // println(s"$ty --> ${ty.without(ns)}")
          annoying(ty.without(ns) :: ls, done_ls, rs, done_rs)
        case (ls, Without(ty, ns) :: rs) =>
          // println(s"$ty --> ${ty.without(ns)}")
          annoying(ls, done_ls, ty.without(ns) :: rs, done_rs)
          */
          
        case (Nil, Nil) =>
          def fail = reportError(doesntMatch(ctx.head.head._2))
          (done_ls, done_rs) match { // TODO missing cases
            case (LhsTop, _) | (LhsRefined(N, RecordType(Nil), Nil), _) | (_, RhsBot) | (_, RhsBases(Nil, N, N)) => fail  // TODO actually get rid of LhsTop and RhsBot...
            // case (_, RhsBases(Nil, N, N)) => fail
            case (LhsRefined(S(f0@FunctionType(l0, r0)), r, ws), RhsBases(_, S(f1@FunctionType(l1, r1)), fo)) =>
              // FIXME shoudn't we check the reft is empty?:
              // if (fo.isEmpty)
                rec(f0, f1)
              // else ()
            case (LhsRefined(S(f: FunctionType), r, ws), RhsBases(pts, _, _)) => // Q: ws nonEmpty okay here?!
              // fail
              annoying(Nil, LhsRefined(N, r, ws), Nil, done_rs)
            case (LhsRefined(S(pt: PrimType), r, Nil), RhsBases(pts, bs, f)) =>
              if (pts.contains(pt) || pts.exists(p => pt.parentsST.contains(p.id)))
                println(s"OK  $pt  <:  ${pts.mkString(" | ")}")
              // else f.fold(fail)(f => annoying(Nil, done_ls, Nil, f))
              else annoying(Nil, LhsRefined(N, r, Nil), Nil, RhsBases(Nil, bs, f))
            case (LhsRefined(bo, r, Nil), RhsField(n, t2)) =>
              r.fields.find(_._1 === n) match {
                case S(nt1) => rec(nt1._2, t2)
                case N => fail
              }
            case (LhsRefined(bo, r, Nil), RhsBases(_, _, S(RhsField(n, t2)))) => // Q: missing anything in prev fields?
              // TODO dedup with above
              r.fields.find(_._1 === n) match {
                case S(nt1) => rec(nt1._2, t2)
                case N => fail
              }
            case (LhsRefined(b, r, ws), RhsField(n, t)) =>
              // val ws2 = ws.filter(_.reft.fields.exists(_._1 === n))
              val (ws2, ws3) = (WithType(TopType, r)(noProv) :: ws).partition(_.reft.fields.exists(_._1 === n))
              // if (ws2.size < ws.size)
              println(s"$ws2 $ws3")
              // if (ws3.isEmpty)
              if (ws3.forall(_.isEmpty))
                // annoying(Nil,
                //   ws2.flatMap(_.reft.fields.filter(_._1 === n).map(_._2)).reduceOption(_ & _).getOrElse(BotType),
                //   Nil, done_rs)
                rec(
                  ws2.flatMap(_.reft.fields.filter(_._1 === n).map(_._2)).reduceOption(_ & _).getOrElse(BotType),
                  // done_rs.toType
                  t
                )
              else annoying(ws3.map(_.base), LhsRefined(b, r, ws2), Nil, done_rs)
            case (LhsRefined(b, r, ws), RhsBases(ps, bty, N)) =>
              annoying(ws.map(_.base), LhsRefined(b, r, Nil), Nil, done_rs)
            case (LhsRefined(b, r, ws), RhsBases(ps, bty, S(rf@RhsField(n, t)))) =>
              ???
            case (LhsRefined(b, r, Nil), RhsBases(ps, bty, S(rf@RhsField(n, t)))) =>
              // val (ws2, ws3) = ws.partition(_.reft.fields.exists(_._1 === n))
              // if (ws3.isEmpty)
              // else annoying(ws3.map(_.base), LhsRefined(b, r, ws2), Nil, done_rs)
              // ???
              annoying(Nil, done_ls, Nil, rf)
            case (LhsRefined(S(b), r, Nil), RhsBases(pts, _, _)) =>
              lastWords(s"TODO ${done_ls} <: ${done_rs} (${b.getClass})") // TODO
          }
          
      }
    }()
    
    def rec(lhs: SimpleType, rhs: SimpleType, outerProv: Opt[TypeProvenance]=N)
          (implicit raise: Raise, ctx: ConCtx): Unit = {
      constrainCalls += 1
      val pushed = lhs.pushPosWithout
      if (pushed isnt lhs) println(s"Push LHS  $lhs  ~>  $pushed")
      recImpl(pushed, rhs, outerProv)
    }
    def recImpl(lhs: SimpleType, rhs: SimpleType, outerProv: Opt[TypeProvenance]=N)
          (implicit raise: Raise, ctx: ConCtx): Unit =
    trace(s"C $lhs <! $rhs") {
      // println(s"  where ${FunctionType(lhs, rhs)(primProv).showBounds}")
      ((lhs -> rhs :: ctx.headOr(Nil)) :: ctx.tailOr(Nil)) |> { implicit ctx =>
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
          case (_, ExtrType(false)) => ()
          case (NegType(lhs), NegType(rhs)) => rec(rhs, lhs)
          case (FunctionType(l0, r0), FunctionType(l1, r1)) =>
            rec(l1, l0)(raise, Nil)
            // ^ disregard error context: keep it from reversing polarity (or the messages become redundant)
            rec(r0, r1)(raise, Nil :: ctx)
          case (prim: PrimType, _) if rhs === prim => ()
          case (prim: PrimType, PrimType(id:Var, _)) if prim.parents.contains(id) => ()
          case (lhs: TypeVariable, rhs) if rhs.level <= lhs.level =>
            val newBound = outerProv.fold(rhs)(ProxyType(rhs)(_, S(prov)))
            lhs.upperBounds ::= newBound // update the bound
            lhs.lowerBounds.foreach(rec(_, rhs)) // propagate from the bound
          case (lhs, rhs: TypeVariable) if lhs.level <= rhs.level =>
            val newBound = outerProv.fold(lhs)(ProxyType(lhs)(_, S(prov)))
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
          case (vt: VarType, _) => rec(vt.sign, rhs)
          case (_, TupleType(f :: Nil)) =>
            rec(lhs, f._2) // FIXME actually needs reified coercion! not a true subtyping relationship
          case (err @ PrimType(ErrTypeId, _), FunctionType(l1, r1)) =>
            rec(l1, err)
            rec(err, r1)
          case (FunctionType(l0, r0), err @ PrimType(ErrTypeId, _)) =>
            rec(err, l0)
            rec(r0, err)
          case (AppType(fun0, args0), AppType(fun1, args1)) if fun0.isInjective && fun1.isInjective =>
            rec(fun0, fun1)
            if (args0.size =/= args1.size) ??? // TODO: compute baseType args, accounting for class inheritance
            else args0.lazyZip(args1).foreach(rec(_, _))
          case (_, a @ AppType(fun, arg :: Nil)) =>
            rec(FunctionType(arg, lhs)(fun.prov), fun)(raise, Nil) // disregard error context?
            // TODO make reporting better... should forget about the function expansion if it doesn't work out!
          case (_, AppType(fun, args)) => lastWords(s"$rhs") // TODO
          case (AppType(fun, arg :: Nil), _) =>
            rec(fun, FunctionType(arg, rhs)(lhs.prov))(raise, Nil) // disregard error context?
          case (AppType(fun, args :+ arg), _) =>
            rec(AppType(fun, args)(lhs.prov), FunctionType(arg, rhs)(lhs.prov))(raise, Nil) // Q: disregard error context?
          case (tup: TupleType, _: RecordType) =>
            rec(tup.toRecord, rhs)
          case (err @ PrimType(ErrTypeId, _), RecordType(fs1)) =>
            fs1.foreach(f => rec(err, f._2))
          case (RecordType(fs1), err @ PrimType(ErrTypeId, _)) =>
            fs1.foreach(f => rec(f._2, err))
          case (tr: TypeRef, _) => rec(tr.expand, rhs)
          case (_, tr: TypeRef) => rec(lhs, tr.expand)
          case (PrimType(ErrTypeId, _), _) => ()
          case (_, PrimType(ErrTypeId, _)) => ()
          case (_, ComposedType(true, l, r)) =>
            annoying(lhs :: Nil, LhsTop, l :: r :: Nil, RhsBot)
          case (ComposedType(false, l, r), _) =>
            annoying(l :: r :: Nil, LhsTop, rhs :: Nil, RhsBot)
          // case (WithType(b, r), r @ RecordType(fs)) =>
          //   // fs.foreach(f => r.find(_._1 === f._1).foreach(f0 => rec(f0._2, f1._2))
          //   val captured = fs.partitionMap()
          // case (_: NegType, _) | (_, _: NegType) =>
          case (_: NegType | _: Without | _: WithType, _) | (_, _: NegType | _: Without) =>
            annoying(lhs :: Nil, LhsTop, rhs :: Nil, RhsBot)
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
            failureOpt.foreach(f => reportError(f))
      }
    }}()
    
    def doesntMatch(ty: SimpleType) = msg"does not match type `${ty.expNeg}`"
    def doesntHaveField(n: Str) = msg"does not have field '$n'"
    def reportError(error: Message)(implicit ctx: ConCtx): Unit = {
      val (lhs_rhs @ (lhs, rhs)) = ctx.head.head
      val failure = error
      println(s"CONSTRAINT FAILURE: $lhs <: $rhs")
      println(s"CTX: ${ctx.map(_.map(lr => s"${lr._1} <: ${lr._2} [${lr._1.prov}]"))}")
      
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
      
      // TODO re-enable
      // assert(lhsProv.loco.isDefined) // TODO use soft assert
      
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
        }.toList.flatten,
        constraintProvenanceHints,
        detailedContext,
      ).flatten
      raise(TypeError(msgs))
    }
    
    rec(lhs, rhs, N)(raise, Nil)
  }
  
  
  def subsume(ty_sch: PolymorphicType, sign: PolymorphicType)(implicit ctx: Ctx, raise: Raise, prov: TypeProvenance): Unit = {
    constrain(ty_sch.instantiate, sign.rigidify)
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
      case w @ Without(b, ns) => Without(extrude(b, lvl, pol), ns)(w.prov)
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
      case PrimType(_, _) => ty
      // case TypeRef(d, ts) => TypeRef(d, ts.map(extrude(_, lvl, pol))) // FIXME pol...
    }
  
  
  def err(msg: Message, loco: Opt[Loc])(implicit raise: Raise, prov: TypeProvenance): SimpleType = {
    raise(TypeError((msg, loco) :: Nil))
    errType
  }
  def errType(implicit prov: TypeProvenance): SimpleType = PrimType(ErrTypeId, Set.empty)(prov)
  
  def warn(msg: Message, loco: Opt[Loc])(implicit raise: Raise): Unit =
    raise(Warning((msg, loco) :: Nil))
  
  
  // Note: maybe this and `extrude` should be merged?
  def freshenAbove(lim: Int, ty: SimpleType, rigidify: Bool = false)(implicit lvl: Int): SimpleType = {
    val freshened = MutMap.empty[Variable, SimpleType]
    def freshen(ty: SimpleType): SimpleType = if (ty.level <= lim) ty else ty match {
      case tv: TypeVariable => freshened.get(tv) match {
        case Some(tv) => tv
        case None if rigidify =>
          val v = PrimType(Var("_"+freshVar(tv.prov).toString), Set.empty)(noProv/*TODO*/)
          freshened += tv -> v
          // TODO support bounds on rigidified variables (intersect/union them in):
          assert(tv.lowerBounds.isEmpty)
          assert(tv.upperBounds.isEmpty)
          v
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
      case PrimType(_, _) => ty
      case w @ WithType(b, r) => WithType(freshen(b), freshen(r).asInstanceOf[RecordType]/*FIXME*/)(w.prov)
      case w @ Without(b, ns) => Without(freshen(b), ns)(w.prov)
      case tr @ TypeRef(d, ts) => TypeRef(d, ts.map(freshen(_)))(tr.prov, tr.ctx)
    }
    freshen(ty)
  }
  
  
}
