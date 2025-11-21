package hkmc2
package semantics
package flow

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.TraceLogger
import Message.MessageContext
import semantics.*, semantics.Term.*
import typing.*

import syntax.SpreadKind
import syntax.Tree
import Elaborator.{State, Ctx, ctx}
import Producer as P
import Consumer as C
import hkmc2.semantics.BuiltinSymbol
import P.Unknown
import hkmc2.semantics.BlockMemberSymbol



type FlowPoint = FlowSymbol | VarSymbol

type Path = Vector[FlowPoint]

type ProdCtor = Producer.Ctor | Producer.Fun | Producer.Typ | Producer.Tup

case class ConcreteProd(path: Path, ctor: ProdCtor)


enum SelectionTarget:
  case ObjectMember(sym: FieldSymbol)
  case CompanionMember(comp: Term, sym: FieldSymbol)



class FlowAnalysis(using tl: TraceLogger)(using Raise, State, Ctx):
  import tl.*
  
  val MAX_FUEL = 1000

  val deconstructConsumer = true
  val deconstructType = true
  
  val collectedConstraints: mutable.Stack[(src: Term, c: Constraint)] = mutable.Stack.empty
  
  val selsToExpand: mutable.Buffer[Sel] = mutable.Buffer.empty
  val leadingDotSelsToExpand: mutable.Buffer[LeadingDotSel] = mutable.Buffer.empty
  
  def typeBody(b: ObjBody): Unit = typeProd(b.blk)
  
  def typeProd(t: Term): Producer = typeProdImpl(t.expanded)
  
  def typeProdImpl(t: Term): Producer =
  trace[P](s"Typing producer: ${t.showDbg}", post = res => s": ${res.showDbg}"):
    
    def constrain(lhs: P, rhs: C): Unit = collectedConstraints += ((src = t, c = Constraint(lhs, rhs)))
    
    t match
    
    case Ref(sym) =>
      sym match
      case sym: VarSymbol => P.Flow(sym)
      case cls: ClassSymbol => P.Ctor(cls, Nil)(t)
      case cls: ModuleOrObjectSymbol => P.Ctor(cls, Nil)(t)
      case ts: TermSymbol => die
      case bs: BuiltinSymbol => bs.signature 
      case bms: BlockMemberSymbol => P.Flow(bms.flow)
      case _: Symbol =>
        log(s"/!\\ Unhandled symbol type: ${sym} (${sym.getClass.getSimpleName}) /!\\")
        P.Unknown(t)
        
    case Blk(stats, res) =>
      stats.foreach:
        case stmt: LetDecl => ()
        case stmt: DefineVar =>
          val rhs = typeProd(stmt.rhs)
          stmt.sym match
          case sym: FlowSymbol => constrain(rhs, C.Flow(sym))
          case _ => ()
        case t: TermDefinition =>
          val sign_ty = t.sign.map(typeProd) // TODO use sign_ty
          val ps = t.params.map(typeParamList)
          t.body.foreach: bod =>
            val bod_ty = typeProd(bod)
            val fun_ty = ps.foldRight(bod_ty): (pl, acc) =>
              P.Fun(C.Tup(pl, N), acc, Nil)
            constrain(fun_ty, C.Flow(t.sym.flow))
        case t: Term => typeProd(t)
          
        case cd: ClassDef =>

          typeBody(cd.body)

          val prod = cd.paramsOpt match
            case S(ps) =>
              ps.restParam match
              case S(_) => ???
              case N =>
                P.Fun(
                  C.Tup(ps.params.map(typeParam), N),
                  P.Ctor(cd.sym, ps.params.flatMap(_.subTerms).map(typeProd) // Good?
                    )(
                      cd.body.blk // Good?
                    ),
                  Nil,
                )
            case N => P.Unknown(cd)

          log(s"Class member type: ${prod.showDbg}")

          constrain(prod, C.Flow(cd.bsym.flow))
          
        case md: ModuleOrObjectDef =>
          // TODO
          log(s"Module: ${md.path}")
          typeBody(md.body)
          
        case _: Import =>
          // TODO?
        
        case stt =>
          log(s"/!\\ Unhandled statement: ${stt} /!\\")
          P.Unknown(t)
          
      typeProd(res)
    
    case Lit(lit) => P.Ctor(LitSymbol(lit), Nil)(t)

    case sel @ LeadingDotSel(nme) =>
      leadingDotSelsToExpand += sel
      log(s"Leading dot selection ${sel.showDbg}")
      P.LeadingDotSel(nme)(sel)
    
    case sel @ Sel(pre, nme) =>
      selsToExpand += sel
      log(s"Selection ${sel.showDbg} ${sel.typ}")
      val pre_t = typeProd(pre)
      sel.resolvedSym match
      case S(sym: BlockMemberSymbol) => P.Flow(sym.flow)
      case S(_) => P.Unknown(sel)
      case N =>
        val sym = sel.resSym
        constrain(pre_t, C.Sel(nme, C.Flow(sym))(sel))
        P.Flow(sym)
    
    case nw @ New(cls, args, rft) =>
      rft match
      case N =>
        cls.resolvedSym.flatMap(_.asCls) match
        case N => P.Unknown(nw)
        case S(sym) =>
          sym match
          case sym: ClassSymbol =>
            val args_t = args.map(typeProd)
            P.Ctor(sym, args_t)(t)
    
    case app @ App(lhs, rhs) =>
      val sym = app.resSym
      val c = C.Fun(typeProd(rhs), C.Flow(sym))
      constrain(typeProd(lhs), c)
      P.Flow(sym)
    
    case Lam(pl, bod) =>
      val ps = typeParamList(pl)
      val pl_t = C.Tup(ps, N)
      val bod_t = typeProd(bod)
      P.Fun(pl_t, bod_t, Nil)
    
    case FunTy(lhs, rhs, _) =>
      P.Fun(typeCons(lhs), typeProd(rhs), Nil)
    
    case Tup(fields) =>
      P.Tup(fields.map:
        case f: Fld => N -> typeProd(f.term))
    
    case Error => P.Ctor(Extr(false), Nil)(t)
    
    case _ => P.Flow(FlowSymbol("TODO"))
  
  
  def typeType(t: Term): Type =
    t.resolvedTyp.getOrElse:
      raise:
        ErrorReport:
          msg"Cannot use this ${t.describe} as a type, as it could not be resolved" -> t.toLoc :: Nil
      Type.Error
  
  def typeParam(p: Param): C =
    val fs = FlowSymbol(p.sym.name)
    p.flow = S(fs)
    p.signType match
    case S(typ) =>
      fs.producers += ConcreteProd(Vector.empty, P.Typ(typ))
      C.Typ(typ)
    case N =>
      C.Flow(fs)
  
  def typeParamList(ps: ParamList): Ls[C] =
    if ps.restParam.nonEmpty then
      ???
    ps.params.map(typeParam)
    // ps.restParam.map(typeParam)
  
  def typeCons(t: Term): Consumer =
  trace[C](s"Typing consumer: ${t.showDbg}", post = res => s": ${res.showDbg}"):
    t match
    case Ref(sym: VarSymbol) => C.Flow(sym)
    case Ref(cls: ClassSymbol) => C.Ctor(cls, Nil)
    case Ref(ts: TermSymbol) => ???
    case Tup(fields) =>
      C.Tup(
        fields.map:
          case f: Fld => typeCons(f.term)
        , N)
    case _ => TODO(t)
  
  def expandTerms() =
    import SelectionTarget.*
    selsToExpand.foreach: sel =>
      log(s"Resolved targets for ${sel.showDbg}: ${sel.resolvedTargets.mkString(", ")}")
      assert(sel.expansion.isEmpty)
      sel.resolvedTargets match
      case ObjectMember(sym) :: Nil =>
        assert(sel.sym.isEmpty)
        sel.expansion = S(S(sel.copy()(sym = S(sym), sel.typ, sel.originalCtx)))
      case CompanionMember(comp, sym) :: Nil =>
        val base = Sel(comp, Tree.Ident(sym.nme))(S(sym), N, N)
        val app = App(base, Tup(sel.prefix :: Nil)(Tree.DummyTup))(Tree.DummyApp, N, FlowSymbol.app())
        log(s"Expansion: ${app.showDbg}")
        sel.expansion = S(S(app))
      case Nil =>
        // FIXME: actually allow that in dead code (use floodfill constraints from exported members to detect)
        if !sel.isErroneous then raise:
          ErrorReport:
            msg"Cannot resolve selection" -> sel.toLoc :: Nil
        // * An error should alsoready be reported in this case
      case targets => raise:
        ErrorReport:
          msg"Ambiguous selection with multiple apparent targets" -> sel.toLoc
          :: targets.map:
            case ObjectMember(sym) => msg"object member ${sym.nme}" -> sym.toLoc
            case CompanionMember(_, sym) => msg"companion member ${sym.nme}" -> sym.toLoc
  
  def expandLeadingDotSels() =
    import SelectionTarget.*
    leadingDotSelsToExpand.foreach: sel =>
      log(s"Resolved targets for ${sel.showDbg}: ${sel.resolvedTargets.mkString(", ")}")
      assert(sel.expansion.isEmpty)
      sel.resolvedTargets match
      case CompanionMember(comp, sym) :: Nil =>
        val base = Sel(comp, Tree.Ident(sym.nme))(S(sym), N, N)
        log(s"Leading dot expansion: ${base.showDbg}")
        sel.expansion = S(S(base))
      case Nil =>
        // FIXME: actually allow that in dead code (use floodfill constraints from exported members to detect)
        raise:
          ErrorReport:
            msg"Cannot resolve selection" -> sel.toLoc :: Nil
      case targets => raise:
        ErrorReport:
          msg"Ambiguous selection with multiple apparent targets" -> sel.toLoc
          :: targets.map:
            case CompanionMember(_, sym) => msg"companion member ${sym.nme}" -> sym.toLoc

  def findConsumerSymbols(cons: Consumer): Ls[Symbol] =
    cons match
    case C.Typ(typ) => findTypeSymbols(typ) ::: Nil
    case _ if !deconstructConsumer => Nil
    case C.Fun(lhs, rhs) => findProducerSymbols(lhs) ::: findConsumerSymbols(rhs)
    case C.Tup(init, N) => init.flatMap(findConsumerSymbols)
    case C.Tup(init, S((_, fst, rest))) =>init.flatMap(findConsumerSymbols) ::: findConsumerSymbols(fst) ::: rest.flatMap(findConsumerSymbols)
    case C.Ctor(sym, args) => sym :: args.flatMap(findConsumerSymbols)
    case _ => Nil

  def findProducerSymbols(prod: Producer): Ls[Symbol] =
    prod match
    case P.Typ(typ) => findTypeSymbols(typ) ::: Nil
    case P.Fun(lhs, rhs, _) => findConsumerSymbols(lhs) ::: findProducerSymbols(rhs)
    case P.Tup(elems) => elems.map(_._2).flatMap(findProducerSymbols)
    case P.Ctor(sym, args) => sym :: args.flatMap(findProducerSymbols)
    case _ => Nil

  def findTypeSymbols(typ: Type): Ls[Symbol] =
    import Type.*
    typ match
    case Ref(sym, _) => sym :: Nil
    case _ if !deconstructType => Nil
    case Error | Top | Bot => Nil
    case Union(t1, t2) => findTypeSymbols(t1) ::: findTypeSymbols(t2)
    case Inter(t1, t2) => findTypeSymbols(t1) ::: findTypeSymbols(t2)
    case Neg(t) => findTypeSymbols(t)
    case Fun(args, ret, eff) => args.flatMap(findTypeSymbols) ::: findTypeSymbols(ret)
    case _ => Nil

  def getCompanionMember(sel: Term.LeadingDotSel, sym: Symbol, nme: String): Opt[(Term, BlockMemberSymbol)] = sym match
    case ms : ModuleOrObjectSymbol =>
      ms.defn match
      case S(d) => 
        d.body.members.get(nme) match
        case S(memb: BlockMemberSymbol) =>
          // S((d.body.blk, memb))
          sel.originalCtx
            .flatMap(ctx => findAccessPath(ctx, d.path, ms))
            .map(x => (x, memb))
        case _ => N
      case _ => N
    case cs : ClassSymbol =>
      cs.defn match
      case S(d) => 
        d.moduleCompanion match
        case S(comp) =>
          comp.defn match
          case S(d) => 
            d.body.members.get(nme) match
            case S(memb: BlockMemberSymbol) =>
              // S((d.body.blk, memb))
              sel.originalCtx
                .flatMap(ctx => findAccessPath(ctx, d.path, comp))
                .map(x => (x, memb))
            case _ => N
          case _ => N
        case _ => N
      case _ => N
    case _ => N

  def solveConstraints(): Unit =
    
    var fuel = MAX_FUEL
    val toSolve: mutable.Stack[Constraint] = mutable.Stack.empty
    val inCache: mutable.Set[FlowSymbol -> C] = mutable.Set.empty
    val outCache: mutable.Set[P -> FlowSymbol] = mutable.Set.empty
    
    while fuel > 0 && collectedConstraints.nonEmpty
    do
      val (trm, cc) = collectedConstraints.pop()
      toSolve.push(cc)
      
      trace(s"Handling constraint: ${cc.showDbg} (from ${trm.showDbg})"):
        
        while fuel > 0 && toSolve.nonEmpty
        do
          fuel -= 1
          val c = toSolve.pop()
          
          def dig(lhs: P, rhs: C, path: Path): Unit =
            
            log(s"Solving: ${lhs.showDbg} <: ${rhs.showDbg}   (${lhs.getClass.getSimpleName}, ${rhs.getClass.getSimpleName})   [${path.mkString(", ")}]")
            
            (lhs, rhs) match
            case (P.Flow(sym), rhs) if inCache.contains(sym -> rhs) => log(s"In (in) cache!")
            case (lhs, C.Flow(sym)) if outCache.contains(lhs -> sym) => log(s"In (out) cache!")
            case (P.Flow(lsym), C.Flow(rsym)) =>
              log(s"New flow: ${lsym.showDbg} ~> ${rsym.showDbg}")
              lsym.outFlows += rsym
              lsym.producers.foreach(cp => dig(cp.ctor, rhs, cp.path ++ path))
            case (lhs: ProdCtor, C.Flow(sym)) =>
              log(s"New flow: ${lhs.showDbg} ~> ${sym.showDbg}")
              sym.producers += ConcreteProd(path, lhs)
              sym.consumers.foreach(c => dig(lhs, c, path))
            case (P.Flow(sym), rhs) =>
              log(s"New flow: ${sym.showDbg} ~> ${rhs.showDbg}")
              sym.consumers += rhs
              sym.producers.foreach(cp => dig(cp.ctor, rhs, cp.path ++ path))
              sym.outFlows.foreach(fs => dig(P.Flow(fs), rhs, sym +: path)) // TODO sym or fs?
            case (P.Fun(pl, pr, _), C.Fun(cl, cr)) =>
              dig(cl, pl, path) // FIXME path
              dig(pr, cr, path) // FIXME path
            case (P.Ctor(sym1, args1), C.Ctor(sym2, args2))
            if (sym1 is sym2) && args1.size === args2.size // TODO generalize
              =>
              args1.zip(args2).foreach: (a1, a2) =>
                dig(a1, a2, path) // FIXME path
            case (P.Tup(args), C.Tup(ini, rst)) =>
              def zip(args: Ls[Opt[SpreadKind] -> P], cons: Ls[C], rst: Opt[(SpreadKind, C, Ls[C])], path: Path): Unit =
                (args, cons) match
                case (Nil, Nil) => ()
                case ((N, a1) :: args, c1 :: cons) =>
                  dig(a1, c1, path) // FIXME path
                  zip(args, cons, rst, path)
                case ((S(spd), a1) :: args, Nil) =>
                  ???
                case ((spdo, a1) :: args, Nil) =>
                  // extra producers can be matched by spread in consumer
                  rst match
                  case S((spd, a2, post)) => ???
                  case N =>
                    raise(ErrorReport(
                      msg"Tuple arity mismatch: too many elements on the consumer side"->trm.toLoc
                      :: Nil
                    ))
              zip(args, ini, rst, path)
            case (sel @ P.LeadingDotSel(nme), rhs) =>
              findConsumerSymbols(rhs).foreach: sym => 
                log(s"Examining ${sym} for leading dot selection resolution")
                getCompanionMember(sel.trm, sym, nme.name) match
                case S((path, memb)) => sel.trm.resolvedTargets ::= SelectionTarget.CompanionMember(path, memb)
                case _ => ()
            case (lhs, sel: C.Sel) => lhs match
              case P.Typ(Type.Ref(sym: ClassSymbol, targs)) =>
                if targs.nonEmpty then TODO(targs)
                toSolve.push(Constraint(P.Ctor(sym, Nil)(Term.Missing), sel))
              case P.Ctor(sym: ClassSymbol, args) =>
                log(s"Selection result: ${sel.res}")
                val d = sym.defn.getOrElse(die)
                d.body.members.get(sel.nme.name) match
                case S(memb: BlockMemberSymbol) =>
                  sel.trm.resolvedTargets ::= SelectionTarget.ObjectMember(memb)
                  log(s"Found immediate member ${memb}")
                  val lhs = P.Flow(memb.flow)
                  toSolve.push(Constraint(lhs, sel.res))
                case S(memb) => TODO(memb)
                case N =>
                  d.moduleCompanion match
                  case S(comp) =>
                    val cd = comp.defn.getOrElse(die)
                    cd.body.members.get(sel.nme.name) match
                    case S(memb) =>
                      log(s"Found companion member ${memb}")
                      sel.trm.originalCtx match
                      case S(oc) =>
                        val patho = findAccessPath(oc, cd.path, comp)
                        log(s"Access path: ${patho}")
                        patho match
                        case S(path) =>
                          sel.trm.resolvedTargets ::= SelectionTarget.CompanionMember(path, memb)
                          val lhs = memb match
                            case memb: BlockMemberSymbol => P.Flow(memb.flow)
                            case _ => TODO(memb)
                          toSolve.push(Constraint(lhs, sel.res))
                        case N => raise:
                          sel.trm.isErroneous = true
                          ErrorReport:
                            msg"Cannot access companion ${comp.name} from the context of this selection" -> sel.trm.toLoc
                            :: Nil
                      case N => ???
                    case N => ???
                  case N => raise:
                    sel.trm.isErroneous = true
                    ErrorReport(
                      // TODO construct proper error message
                      msg"Field ${sel.nme.name} is not a member of ${d.kind.desc} ${d.sym.name}" -> trm.toLoc :: Nil)
              case _ => raise:
                sel.trm.isErroneous = true
                ErrorReport(
                  // TODO construct proper error message
                  msg"Unresolved selection:" -> sel.trm.toLoc
                  :: msg"Type `${lhs.showDbg}` does not contain member '${sel.nme.name}'" -> lhs.toLoc
                  :: Nil)
            case _ =>
              log(s"/!\\ Unhandled constraint /!\\")
          end dig
          
          dig(c.lhs, c.rhs, Vector.empty)
          
        if fuel === 0 then
          raise(ErrorReport(
            msg"Could not solve all constraints within $MAX_FUEL iterations." -> N :: Nil
          ))
  
  def findAccessPath(src: Ctx, dst: Ctx, moduleSym: ModuleOrObjectSymbol): Opt[Term] =
    log(s"outermostAcessibleBase ${dst.outermostAcessibleBase}")
    val (outermostBase, outermostPath) = dst.outermostAcessibleBase
    var cur = src
    while cur isnt outermostBase do
      cur.parent match
      case N =>
        return N
      case S(p) =>
        cur = p
    assert(cur is outermostBase)
    (moduleSym :: outermostPath).reverse match
    case Nil => die
    case sym :: syms => S:
      syms.foldLeft(sym.bms.getOrElse(die).ref(): Term): (a, b) =>
        Sel(a, Tree.Ident(b.nme))(S(b.bms.getOrElse(die)), N, N)
  
  
  import hkmc2.document.*
  import utils.Scope
  
  def showFlows(using Scope, ShowCfg): Document =
    val syms = summon[ShowCfg].shownSymbols.toIndexedSeq.sortBy(_.uid)
    doc" #{  # ${
      syms.collect:
        case sym: FlowSymbol =>
          (
            if sym.producers.isEmpty then Nil else doc"${sym.showName}  <~  ${
              sym.producers.toSeq.map(_.ctor.show).mkDocument(doc"  ")}" :: Nil
          ) ::: (
            if sym.consumers.isEmpty then Nil else doc"${sym.showName}  ~>  ${
                sym.consumers.toSeq.map(_.show).mkDocument(doc"  ")}" :: Nil
          ) ::: (
            if sym.outFlows.isEmpty then Nil else doc"${sym.showName}  ->  ${
                sym.outFlows.toSeq.map(_.showName).mkDocument(doc"  ")}" :: Nil
          ) ::: Nil
      .flatten.mkDocument(doc" # ")
    } #} "
  
end FlowAnalysis

