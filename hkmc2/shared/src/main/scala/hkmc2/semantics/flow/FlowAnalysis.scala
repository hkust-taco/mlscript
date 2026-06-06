package hkmc2
package semantics
package flow

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*
import utils.TraceLogger
import Message.MessageContext
import semantics.*, semantics.Term.*, semantics.AnySelTerm
import typing.*

import syntax.SpreadKind
import syntax.Tree
import Elaborator.{State, Ctx, ctx}
import Producer as P
import Consumer as C



type FlowPoint = FlowSymbol | VarSymbol

type Path = Vector[FlowPoint]

type ProdCtor = Producer.Ctor | Producer.Fun | Producer.Typ | Producer.Tup | Producer.LeadingDotSel

case class ConcreteProd(path: Path, ctor: ProdCtor)


enum SelectionTarget:
  case ObjectMember(sym: MemberSymbol)
  case CompanionMember(comp: Term, sym: MemberSymbol)


/** This is a very sketchy exploration/proof of concept of flow analysis
  * that can be used to help compile programs in a type-directed way without having to perform full type inference. */
class FlowAnalysis(using tl: TraceLogger)(using Raise, State, Ctx):
  import tl.*
  
  val MAX_FUEL = 1000
  
  def typeBody(b: ObjBody): Unit =
    typeProd(b.blk)
  
  def typeProd(t: Term, insideSelAppChain: Boolean = false): Producer =
    typeProdImpl(t.expanded, insideSelAppChain)
  
  def typeProdImpl(t: Term, insideSelAppChain: Boolean): Producer =
  trace[P](s"Typing producer: ${t.showDbg}", post = res => s": ${res.showDbg}"):
    
    def constrain(lhs: P, rhs: C): Unit = collectedConstraints += ((src = t, c = Constraint(lhs, rhs)))
    
    def checkLDS(sub: Term)(res: Producer => Producer): Producer =
      t.ldsRoot match
      case S(lds) if !insideSelAppChain =>
        val sym = FlowSymbol("bind")
        log(s"Constraining leading dot selection ${lds.showDbg} at the top level")
        constrain(P.LeadingDotSel(lds), C.Flow(sym))
        constrain(res(typeProd(sub, insideSelAppChain = true)), C.Flow(sym))
        P.Flow(sym)
      case _ => res(typeProd(sub, insideSelAppChain = insideSelAppChain))
    
    t match
    
    case Resolved(trm, sym) =>
      val _ = typeProd(trm) // * Discard the base producer because it's already resolved and `sym` is the real one
      sym match
      case cls: ClassSymbol => P.Ctor(cls, Nil)(t)
      case cls: ModuleOrObjectSymbol => P.Ctor(cls, Nil)(t)
      case ts: TermSymbol => getFlowSymOrType(ts.bms.get)
      case _ => lastWords(s"Unexpected resolved symbol in producer position: $sym")
    
    case Ref(sym) =>
      sym match
      case sym: VarSymbol => P.Flow(sym)
      case cls: ClassSymbol => P.Ctor(cls, Nil)(t)
      case cls: ModuleOrObjectSymbol => P.Ctor(cls, Nil)(t)
      case ts: TermSymbol => die
      case bs: BuiltinSymbol =>
        bs.signature
      case bms: BlockMemberSymbol =>
        if bms.asTrm.isEmpty then raise:
          ErrorReport:
            msg"Cannot use non-term member ${bms.nme} in term position" -> t.toLoc :: Nil
        getFlowSymOrType(bms)
      case _: Symbol =>
        log(s"/!\\ Unhandled symbol type: ${sym} (${sym.getClass.getSimpleName}) /!\\")
        P.Unknown(t)
        
    case Blk(stats, res) =>
      stats.foreach:
        case stmt: LetDecl => ()
        case stmt: DefineVar =>
          val rhs = typeProd(stmt.rhs)
          stmt.sym match
          case sym: FlowSymbol =>
            constrain(rhs, C.Flow(sym))
          case _ => lastWords(s"Unexpected DefineVar symbol: ${stmt.sym}")
        case t: TermDefinition =>
          val sign_ty = t.sign.map(typeType(_)) // TODO use sign_ty
          val ps = t.params.map(typeParamList)
          t.body.foreach: bod =>
            val bod_ty = typeProd(bod)
            val fun_ty = ps.foldRight(bod_ty): (pl, acc) =>
              P.Fun(C.Tup(pl, N), acc, Nil)
            constrain(fun_ty, C.Flow(t.sym.flow))
        case t: Term =>
          typeProd(t)
          
        case cd: ClassDef =>
          
          typeBody(cd.body)
          
          val prod = cd.paramsOpt match
            case S(ps) =>
              ps.restParam match
              case S(_) => ???
              case N =>
                P.Fun(
                  C.Tup(ps.params.map(typeParam), N),
                  P.Ctor(cd.sym, Nil // FIXME: Nil
                    )(
                      Term.Missing // FIXME
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
          P.Unknown(stt)
          
      typeProd(res)
    
    case Lit(lit) =>
      P.Ctor(LitSymbol(lit), Nil)(t)

    case sel @ LeadingDotSel(nme) =>
      leadingDotSelsToExpand += sel
      log(s"Leading dot selection ${sel.showDbg}")
      val sym = sel.resSym
      constrain(P.LeadingDotSel(sel), C.Flow(sym))
      P.Flow(sym)
    
    case sel @ AnySel(pre, nme, cls) =>
      log(s"Selection ${sel.showDbg} ${sel.typ}")
      checkLDS(pre): pre_t =>
        sel.resolvedSym match
        case S(sym: BlockMemberSymbol) =>
          log(s"RES ${sym.nme} in ${sel.showDbg}")
          getFlowSymOrType(sym)
        case S(sym) =>
          selsToExpand += sel
          log(s"Unhandled symbol reference ${sym.nme} in ${sel.showDbg}")
          P.Unknown(sel)
        case N =>
          selsToExpand += sel
          val sym = sel.resSym
          constrain(pre_t, C.Sel(nme, C.Flow(sym))(sel))
          P.Flow(sym)
    
    case nw @ New(cls, args, rft) =>
      rft match
      case N =>
        cls.resolvedSym.flatMap(_.asCls) match
        case N =>
          log(s"Unresolved or invalid class symbol in ${cls.showDbg}")
          P.Unknown(nw)
        case S(sym) =>
          sym match
          case sym: ClassSymbol =>
            val args_t = args.map(typeProd(_, insideSelAppChain = insideSelAppChain))
            P.Ctor(sym, args_t)(t)
      case S(_) => TODO("New with refinement not yet supported in flow analysis")
    
    case app @ App(lhs, rhs) =>
      checkLDS(lhs): pre_t =>
        val sym = app.resSym
        val c = C.Fun(typeProd(rhs), C.Flow(sym))
        constrain(pre_t, c)
        P.Flow(sym)
    
    case Lam(pl, bod) =>
      val ps = typeParamList(pl)
      val pl_t = C.Tup(ps, N)
      val bod_t = typeProd(bod)
      P.Fun(pl_t, bod_t, Nil)
    
    case ft: FunTy =>
      P.Typ(typeType(ft))
    
    case Tup(fields) =>
      P.Tup(fields.map:
        case f: Fld => N -> typeProd(f.term)
        case s: Spd => TODO("tuple spread in flow analysis")
      )
    
    case Error =>
      P.Ctor(Extr(false), Nil)(t)
    
    // case _ => P.Flow(FlowSymbol("TODO"))
    case _ => TODO(t)
  
  /* 
  def getType(t: Term): Type =
    t.resolvedTyp.getOrElse:
      raise:
        ErrorReport:
          msg"Cannot use this ${t.describe} as a type, as it could not be resolved" -> t.toLoc :: Nil
      Type.Error
  */
  
  def typeParam(p: Param): C =
  trace[C](s"Typing param: ${p.showDbg}", post = res => s": ${res.showDbg}"):
    p.signType match
    case S(typ) =>
      p.flow.producers += ConcreteProd(Vector.empty, P.Typ(typ))
      C.Typ(typ)
    case N =>
      C.Flow(p.flow)
  
  def typeParamList(ps: ParamList): Ls[C] =
    if ps.restParam.nonEmpty then
      ??? // TODO
    ps.params.map(typeParam)
  
  def typeType(t: Term): Type =
  trace[Type](s"Typing consumer: ${t.showDbg}", post = res => s": ${res.showDbg}"):
    t match
    case Ref(sym: VarSymbol) => Type.Ref(sym, Nil) // unparameterized type variable
    case Ref(cls: ClassSymbol) => Type.Ref(cls, Nil)
    case Ref(ts: BlockMemberSymbol) =>
      Type.Ref(ts.asTpe.getOrElse(TODO(t)), Nil)
    case Tup(fields) =>
      Type.Tup:
        fields.map:
          case f: Fld => typeType(f.term)
          case Spd(eager, term) => (???, typeType(term))
    case FunTy(lhs, rhs, _) =>
      Type.Fun(typeType(lhs), typeType(rhs), N)
    case _ => TODO(t)
  
  val collectedConstraints: mutable.Stack[(src: Term, c: Constraint)] = mutable.Stack.empty
  
  val selsToExpand: mutable.Buffer[AnySelTerm] = mutable.Buffer.empty
  val leadingDotSelsToExpand: mutable.Buffer[LeadingDotSel] = mutable.Buffer.empty
  
  def expandTerms() =
    import SelectionTarget.*
    selsToExpand.foreach: sel =>
      log(s"Resolved targets for ${sel.showDbg}: ${sel.resolvedTargets.mkString(", ")}")
      assert(sel.expansion.isEmpty)
      sel.resolvedTargets match
        case ObjectMember(sym) :: Nil =>
          assert(sel.sym.isEmpty)
          sel.expansion = S(S(sel.withSym(sym)))
        case CompanionMember(comp, sym) :: Nil =>
          val base = Sel(comp, Tree.Ident(sym.nme))(S(sym), FlowSymbol.sel(sym.nme), N, N)
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
    leadingDotSelsToExpand.foreach: sel =>
      log(s"Resolved targets for ${sel.showDbg}: ${sel.resolvedTargets.mkString(", ")}")
      assert(sel.expansion.isEmpty)
      sel.resolvedTargets match
      case CompanionMember(comp, sym) :: Nil =>
        val base = Sel(comp, Tree.Ident(sym.nme))(S(sym), FlowSymbol.sel(sym.nme), N, N)
        log(s"Leading dot expansion: ${base.showDbg}")
        sel.expansion = S(S(base))
      case Nil =>
        // FIXME: actually allow that in dead code (use floodfill constraints from exported members to detect)
        sel.expansion = S(S(Error))
        raise:
          ErrorReport:
            msg"Cannot resolve leading dot selection" -> sel.toLoc :: Nil
      case targets => sel.expansion = S(S(Error)); raise:
        ErrorReport:
          msg"Ambiguous selection with multiple apparent targets:" -> sel.toLoc
          :: targets.map:
            case CompanionMember(_, sym) => msg"companion member ${sym.nme}" -> sym.toLoc

  def getCompanionMember(name: Str, oc: Opt[SrcScope], sym: Symbol): Opt[(Term, BlockMemberSymbol)] = sym match
    case ms: ModuleOrObjectSymbol => ms.defn.flatMap: d =>
      d.body.members.get(name) match
      case S(memb: BlockMemberSymbol) =>
        oc
        .flatMap(findAccessPath(_, d.path, ms))
        .map((_, memb))
      case _ => N
    case cs: ClassSymbol =>
      cs.defn
      .flatMap(_.moduleCompanion)
      .flatMap(x => x.defn.map((x, _)))
      .flatMap: (comp, d) =>
        d.body.members.get(name) match
        case S(memb: BlockMemberSymbol) =>
          oc
          .flatMap(findAccessPath(_, d.path, comp))
          .map((_, memb))
        case _ => N
    case _ => N
  
  
  // * This is a rather hacky way to check whether we're looking at a BMS from the same compilation unit/file,
  // * in which case we should get access to its internal flow symbol, or whether it's from another file,
  // * in which case we shouldn't, as flow analysis is supposed to be local
  // * (if not, we'd notably get race conditions and inconsistencies in compilation).
  // * ASSUMPTION: This relies on the fact that each file is always elaborated in a distinct State instance.
  def getFlowSymOrType(bms: BlockMemberSymbol): P =
    if bms.getState is summon[State]
    then P.Flow(bms.flow)
    else P.Typ(Type.Top) // TODO: should get a frozen inferred type view of the internally inferred flow
  
  
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
            
            log(s"Solving: ${lhs.showDbg} <: ${rhs.showDbg}   (${lhs.getClass.getSimpleName}, ${rhs.getClass.getSimpleName})")
            
            (lhs, rhs) match
            case (P.Flow(sym), rhs)
            if inCache.contains(sym -> rhs)
              => log(s"In (in) cache!")
            case (lhs, C.Flow(sym))
            if outCache.contains(lhs -> sym)
              => log(s"In (out) cache!")
            case (P.Flow(sym), C.Flow(sym2)) =>
              log(s"New flow $sym ~> $sym2")
              sym.outFlows += sym2
              sym.producers.foreach(cp =>
                dig(cp.ctor, rhs, cp.path ++ path))
            case (lhs: ProdCtor, C.Flow(sym)) =>
              log(s"New flow $lhs ~> $sym")
              sym.producers += ConcreteProd(path, lhs)
              sym.consumers.foreach: c =>
                dig(lhs, c, path)
            case (P.Flow(sym), rhs) =>
              log(s"New flow $sym ~> $rhs")
              sym.consumers += rhs
              sym.producers.foreach: cp =>
                dig(cp.ctor, rhs, cp.path ++ path)
              sym.outFlows.foreach: fs =>
                dig(P.Flow(fs), rhs, fs +: path)
            case (P.Fun(pl, pr, _), C.Fun(cl, cr)) =>
              dig(cl, pl, path) // FIXME path
              dig(pr, cr, path) // FIXME path
            case (P.Ctor(sym1, args1), C.Ctor(sym2, args2))
            if (sym1 is sym2) && args1.size === args2.size // TODO generalize
              =>
              args1.zip(args2).foreach: (a1, a2) =>
                dig(a1, a2, path) // FIXME path
            case (P.Tup(args), C.Tup(ini, rst)) =>
              def zip(args: Ls[Opt[SpreadKind] -> P], cons: Ls[C], rst: Opt[(SpreadKind, C, Ls[C])], path: Path): Unit
                    = (args, cons) match
                case (Nil, Nil) => ()
                case ((N, a1) :: args, c1 :: cons) =>
                  dig(a1, c1, path) // FIXME path
                  zip(args, cons, rst, path)
                case ((S(spd), a1) :: args, Nil) =>
                  ???
                case ((N, a1) :: args, Nil) =>
                  // extra producers can be matched by spread in consumer
                  rst match
                  case S((spd, a2, post)) => ???
                  case N =>
                    raise(ErrorReport(
                      msg"Tuple arity mismatch: too many elements on the producer side" -> trm.toLoc :: Nil))
                case (Nil, _ :: _) =>
                  raise(ErrorReport(
                    msg"Tuple arity mismatch: too few elements on the producer side" -> trm.toLoc :: Nil))
                case ((S(_), _) :: _, _ :: _) => ??? // TODO: producer-side spread vs remaining consumers
              zip(args, ini, rst, path)
            case (sel @ P.LeadingDotSel(trm), rhs) => rhs match
              case C.Typ(Type.Ref(sym, _)) =>
                log(s"Examining ${sym} for leading dot selection resolution")
                getCompanionMember(trm.nme.name, trm.originalCtx, sym) match
                case S((path, memb)) =>
                  sel.trm.resolvedTargets ::= SelectionTarget.CompanionMember(path, memb)
                  log(s"Found member ${memb}")
                  toSolve.push(Constraint(getFlowSymOrType(memb), C.Flow(trm.resSym)))
                case _ =>
                  log(s"Could not find member ${trm.nme.name} in ${sym}")
              case _ => log("Unhandled RHS for leading dot selections")
            case (lhs, sel: C.Sel) =>
              lhs match
              case P.Typ(Type.Ref(sym: ClassSymbol, targs)) =>
                if targs.nonEmpty then TODO(targs)
                toSolve.push(Constraint(P.Ctor(sym, Nil)(Term.Missing), sel))
              case P.Ctor(sym: ClassSymbol, args) =>
                val d = sym.defn.getOrElse(die)
                d.body.members.get(sel.nme.name) match
                case S(memb: BlockMemberSymbol) =>
                  sel.trm.resolvedTargets ::= SelectionTarget.ObjectMember(memb)
                  log(s"Found immediate member ${memb}")
                  toSolve.push(Constraint(getFlowSymOrType(memb), sel.res))
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
                          val newlhs = getFlowSymOrType(memb)
                          toSolve.push(Constraint(newlhs, C.Fun(P.Tup((N, lhs) :: Nil), sel.res)))
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
            msg"Could not solve all constraints within $MAX_FUEL iterations." -> N :: Nil))
  
  def findAccessPath(src: SrcScope, dst: SrcScope, moduleSym: ModuleOrObjectSymbol): Opt[Term] =
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
      syms.foldLeft(sym.asInstanceOf[DefinitionSymbol[?]]//FIXME
        .bms.getOrElse(die).ref(): Term): (a, b) =>
        Sel(a, Tree.Ident(b.nme))(S(b.asInstanceOf[DefinitionSymbol[?]]//FIXME
          .bms.getOrElse(die)), FlowSymbol.sel(b.nme), N, N)
  
  
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

