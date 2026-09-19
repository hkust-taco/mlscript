package hkmc2
package semantics

import scala.collection.mutable
import scala.annotation.tailrec

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.Message.MessageContext
import hkmc2.io
import utils.TraceLogger
import syntax.*
// import Tree.*
import Term.*

import Elaborator.*
import hkmc2.syntax.LetBind


class NewResolver:
  self: Elaborator =>
  import tl.*
  
  /* 
  class Constraint(val lhs: Term, val rhs: Term):
    override def equals(obj: Any): Bool = obj match
      case that: Constraint => (this.lhs is that.lhs) && (this.rhs is that.rhs)
      case _ => false
    private var _hash: Int = 0
    override def hashCode(): Int = 
      if _hash =/= 0 then _hash
      else
        var h = lhs.hashCode() * 31 + rhs.hashCode()
        if h === 0 then h += 1
        _hash = h
        h
    def showDbg(using DebugPrinter): Str =
      s"${lhs.showDbg} <: ${rhs.showDbg}"
  
  val processedConstraints: mutable.Set[Constraint] = mutable.Set.empty
  val collectedConstraints: mutable.Buffer[Constraint] = mutable.Buffer.empty
  */
  
  // * The `FlowSymbol`s are currently used to uniquely identify terms
  val appShapes: mutable.Map[(TermShape, FlowSymbol), AppShape] = mutable.Map.empty
  val newShapes: mutable.Map[(ClassLikeSymbol, Ls[Marks], FlowSymbol), NewShape] = mutable.Map.empty
  val introShapes: mutable.Map[IntroTerm, IntroShape] = mutable.Map.empty // TODO use symbols for faster lookup?
  val symShapes: mutable.Map[(BlockMemberSymbol, FlowSymbol, Ls[Marks]), SymShape] = mutable.Map.empty
  val defnShapes: mutable.Map[DefinitionSymbol[?], DefnShape] = mutable.Map.empty
  
  def isOwnedSym(sym: Symbol): Bool =
    sym.getState is state
  
  def resolError(src: Term | Pattern, msgs: Ls[(Message, Opt[Loc])]): Unit = raise:
    ErrorReport(msg"Resolution error in ${src.describe}" -> src.toLoc ::msgs, source = Diagnostic.Source.Compilation)
  
  def zipArgs(mss: Ls[Marks], ps: Ls[Param], r: Opt[Param], args: Ls[Elem], src: Term, funSh: TermShape): Unit =
    (ps, args) match
    case (Nil, Nil) => ()
    // case (Nil, Spd(k, t) :: args) =>
    //   zip(Nil, r, args)
    case (Nil, args) =>
      r match
      case N =>
        resolError(src,
          msg"${funSh.describe.capitalize} expected ${ps.length} ${
            "argument".pluralized(ps.length)}, but got ${args.length}" -> funSh.toLoc :: Nil)
      case S(p) =>
        val packaged = new Tup(args)(Tree.DummyTup).withLoc(Loc.mk(args.iterator.flatMap(_.toLoc)))
        val sh = IntroShape(packaged)
        p.sym.shapeListeners.foreach(_(sh))
    case (p :: ps, Fld(fls, trm, asc) :: args) =>
    // case ((p, mss) :: ps, Fld(fls, trm, asc) :: args) =>
      listenTerm(trm): sh0 =>
        // val sh = sh0.enter(mss)
        // log(s"zipArg: p = ${p.showDbg}, trm = ${trm.showDbg}, sh = ${sh.shwDbg}")
        // if isOwnedSym(p.sym) && p.sym.shapes.add(sh) then
        //   p.sym.shapeListeners.foreach(listener => listener(sh))
        sh0.enter(mss) match
        case NoShape =>
        case sh: TermShape =>
          log(s"zipArg: p = ${p.showDbg}, trm = ${trm.showDbg}, sh = ${sh.shwDbg} ${isOwnedSym(p.sym)}, ${p.sym.shapes.contains(sh)}")
          if isOwnedSym(p.sym) && p.sym.shapes.add(sh) then
            // log(s"!!!! ${p.sym.shapeListeners}")
            p.sym.shapeListeners.foreach(listener => listener(sh))
      zipArgs(mss, ps, r, args, src, funSh)
    case _ =>
      resolError(src,
        msg"${funSh.describe.capitalize} expected ${ps.length} ${
          "argument".pluralized(ps.length)}, but got ${args.length}" -> funSh.toLoc :: Nil)
  
  def patApp(lhs: Term, args: Ls[Pattern], res: Pattern.Constructor): Unit = if newResolution then
    listen(lhs, discardMarks = true): sh =>
      log(s"patApp: lhs = ${lhs.showDbg}, args = ${args.map(_.showDbg)}, res = ${res.showDbg}, sh = ${sh.shwDbg}")
      def checkEmpty = () // TODO
      sh match
      case sh: TermShape =>
        // zipArgs(sh.unappliedParams.map(_._2), args, N, res.args, res, lhs)
        ???
      case sh: SymShape =>
        // softAssert(res.isErroneous)
        val bms = sh.sym
        bms.onComplete: () =>
          bms.asPat match
          case S(pat) =>
            checkEmpty
            res.resolvedSym = S(pat)
          case N =>
            val flow = FlowSymbol.app()
            fromBMS(bms, flow, sh.markss, sh =>
              sh match
              case sh: TermShape =>
                // zipArgs(sh.unappliedParams.map(_._2), args, N, res.args, res, lhs)
                // sh.unappliedParams
                // ???FlowSymbol.app
                sh.applicationHead match
                case (ds: DefnShape, mss) =>
                  val cls = ds.defn match
                    case cd: ClassDef => cd
                    case td: TermDefinition =>
                      td.tsym match
                      case ccs: ClassCtorSymbol => ccs.associatedCls.defn.get
                      case _ => ???
                  log(s"Pattern's class: $cls")
                  lhs.withoutCaptures match
                  case trm: NewResolvable =>
                    trm.resolvedTargets ::= cls.sym
                  res.resolvedSym = S(cls.sym)
                  cls.paramsOpt match
                  case N =>
                    res.isErroneous = true
                    resolError(res,
                      msg"${sh.describe.capitalize} does not take pattern arguments." -> sh.toLoc :: Nil)
                  case S(ps) =>
                    if ps.restParam.nonEmpty then TODO(ps.restParam)
                    if args.sizeCompare(ps.params) =/= 0 then
                      res.isErroneous = true
                      resolError(res,
                        msg"${sh.describe.capitalize} expected ${ps.params.length} ${
                          "pattern argument".pluralized(ps.params.length)}, but got ${args.length}" -> sh.toLoc :: Nil)
                    val assoc = ps.params.lazyZip(args).map: (p, a) =>
                      log(s"Pattern's param: ${p.showDbg} (${p.fldSym}), arg: ${a.showDbg}")
                      p.fldSym match
                      case S(fldSym: BlockMemberSymbol) =>
                        (fldSym, a)
                      case S(fldSym) => die
                      case N => ???
                    val psh = CtorPatternShape(cls, assoc, res, FlowSymbol.pat())
                    if res.shapes.add(psh) then
                      res.shapeListeners.foreach(listener => listener(psh))
                case _ =>
                  res.isErroneous = true
                  resolError(res,
                    msg"${sh.describe.capitalize} cannot used like an applied pattern." -> sh.toLoc :: Nil)
            , lhs)
  
  def listenPattern(pat: Pattern)(listener: PatternShape => Unit): Unit =
    // ???
    log(s"listenPattern: pat = ${pat.showDbg} ${pat.getClass.getSimpleName}")
    pat.shapeListeners += listener // FIXME: sus
    pat match
    case pat: PatternShapeHost =>
      pat.shapes.foreach(listener)
      // pat.shapeListeners += listener
    case pat: Pattern.Alias =>
      // TODO: also handle the alias symbol's shape listeners?
      // listenTerm(pat.)
      /* 
      def listen(sh: Shape): Unit =
        matchShapePat(sh, pat.pattern)
      pat.symbol.shapes.foreach(listen)
      pat.symbol.shapeListeners += listen
      listenPattern(pat.pattern)(listener)
       */
      listener(AliasPatternShape(pat.symbol, pat))
    case Pattern.Literal(_) | Pattern.Tuple(_, _) => // TODO
    case Pattern.Wildcard() =>
      ()
    // case _ => ???
  
  def matchShapePat(shape: Shape, pattern: Pattern): Unit =
    pattern match
    case al @ Pattern.Alias(pat, id) =>
      matchShapePat(shape, pat)
      log(s"TODO: $id ${al.symbol}")
      if al.symbol.shapes.add(shape) then
        al.symbol.shapeListeners.foreach(listener => listener(shape))
      // pipeTerm(id, shape)
    case Pattern.Wildcard() =>
    // case _ => ???
  
  def matchScrutPat(scrutinee: Term.Ref, pattern: Pattern): Unit =
    log(s"matchScrutPat? scrutinee = ${scrutinee.showDbg}, pattern = ${pattern.showDbg}")
    if newResolution then
      listenPattern(pattern): psh =>
        trace(s"matchScrutPat: scrutinee = ${scrutinee.showDbg}, pattern = ${pattern.showDbg}, psh = ${psh.showDbg}"):
          listenTerm(scrutinee): sh =>
            trace(s"matchScrutPat scrutinee = ${scrutinee.showDbg}, pattern = ${pattern.showDbg}, sh = ${sh.shwDbg}"):
              if !sh.isSaturated then
                ???
              psh match
              case AliasPatternShape(sym, pat) =>
                log(s"matchScrutPat: scrutinee = ${scrutinee.showDbg}, pattern = ${pattern.showDbg}, psh = ${psh.showDbg}")
                matchShapePat(sh, pat)
                if sym.shapes.add(sh) then
                  sym.shapeListeners.foreach(listener => listener(sh))
              case CtorPatternShape(cls, fs, src, resSym) =>
                sh.applicationHead match
                case (ds: DefnShape, mss) =>
                  if ds.extendsCls(cls) then
                    log(s"Subclass: ${ds.defn.sym.showDbg} of ${cls.sym.showDbg}")
                    fs.foreach: (bms, pat) =>
                      // bms.onComplete: () =>
                      val nme = bms.nme
                      sh.getMember(nme) match
                      case S((sym, mss)) =>
                        val sh = symShapes.getOrElseUpdate((bms, resSym, mss), SymShape(bms, resSym, mss))
                        // if src.trmHost.shapes.add(sh) then
                        //   src.trmHost.shapeListeners.foreach(listener => listener(sh))
                        matchShapePat(sh, pat)
                      case N =>
                        ???
                  else
                    log(s"Not a subclass: ${ds.defn.sym.showDbg} of ${cls.sym.showDbg}")
  
  def appShape(lhs: TermShape, args: Term, res: App): Unit =
    // log(s"appShape? lhs = $lhs, args = $args, res = $res")
    val sh = appShapes.getOrElseUpdate((lhs, res.resSym), {
      log(s"appShape: lhs = ${lhs.shwDbg}, args = ${args.showDbg}, res = ${res.showDbg}")
      new AppShape(lhs, args, res)
    })
    lhs.unappliedParams match
    case Nil => ()
    case (ps, mss) :: pss =>
      args match
      case args: Tup =>
        log(s"Zipping ${ps} (${mss.map(_.showDbg)}) with ${args.fields}")
        zipArgs(mss, ps.params, ps.restParam, args.fields, res, lhs)
      case _ => ???
    log(s"appShape isSaturated? ${sh.isSaturated}; head? ${sh.applicationHead}")
    def register = if res.shapes.add(sh) then
      res.shapeListeners.foreach(listener => listener(sh))
    log(s"lhs ${lhs.isSaturated} ${lhs.unappliedParams.map(_.mapFirst(_.showDbg).mapSecond(_.map(_.showDbg)))}")
    if lhs.isSaturated && !res.isErroneous then
      res.isErroneous = true
      if lhs.applicationHead._1 is lhs
      then resolError(res,
          msg"${lhs.describe.capitalize} cannot be called like a function." -> lhs.toLoc :: Nil)
      else resolError(res,
          msg"${lhs.describe.capitalize} cannot receive more argument lists." -> lhs.toLoc :: Nil)
    if sh.isSaturated then
      def go(body: Term, mss: Ls[Marks]) =
        listenTerm(body): sh =>
          sh.exit(mss) match
          case NoShape =>
          case sh: TermShape =>
            if res.shapes.add(sh) then
              res.shapeListeners.foreach(listener => listener(sh))
      sh.applicationHead match
      case (ds: DefnShape, mss) =>
        ds.defn match
        case cd: ClassDef =>
          // TODO: resolve ctor?
          // TODO: handle `mss`
          register
        case td: TermDefinition =>
          // listenTerm(td.body, sh => newShape(sh, args, res))
          td.tsym match
          case ccs: ClassCtorSymbol => // TOOD: to avoid the special case, give this the actual body?
            softAssert(td.body.isEmpty)
            // ccs.associatedCls
            // TODO: handle `mss`
            register
          case _ =>
            log(s"appShape: td.body = ${td.body}")
            td.body.foreach: body =>
              go(body, mss)
        case _ =>
          softAssert(res.isErroneous)
      case (sh: IntroShape, _) =>
        sh.trm match
        case Lam(params, body) =>
          go(body, Nil)
        case _ =>
          softAssert(res.isErroneous)
      case _ =>
        softAssert(res.isErroneous)
    else register
  
  def newSel(sel: NewSel): Unit =
    log(s"newSel? sel = ${sel.showDbg}")
    listenTerm(sel.prefix): shape =>
      log(s"newSel: sel = ${sel.showDbg}, shape = ${shape.shwDbg}")
      shape.getMember(sel.id.name) match
        case S((bms, mss)) =>
          log(s"newSel member: bms = ${bms.showDbg}, mss = ${mss.map(_.showDbg)}")
          sel.resolvedMembers ::= bms
          val sh = symShapes.getOrElseUpdate((bms, sel.resSym, mss), SymShape(bms, sel.resSym, mss))
          if sel.shapes.add(sh) then
            sel.shapeListeners.foreach(listener => listener(sh))
          // symShapes.getOrElseUpdate((bms, sel.resSym), SymShape(bms, sel.resSym))
          //   .exit(mss) match
          //     case NoShape =>
          //     case sh: TermShape =>
          //       if sel.shapes.add(sh) then
          //         sel.shapeListeners.foreach(listener => listener(sh))
        case N =>
          sel.isErroneous = true
          resolError(sel, msg"${shape.describe.capitalize} does not contain member '${sel.id.name}'" -> shape.toLoc :: Nil)
  
  def resolveNew(nw: Term.New): Unit =
    log(s"resolveNew? res = ${nw.showDbg}")
    // listenTerm(nw.cls, shape => newShape(shape, nw.args, nw))
    nw.cls.withoutCaptures match
    case trm: NewResolvable =>
      listen(trm): shape =>
        def reject =
          nw.isErroneous = true
          resolError(nw,
            msg"${shape.describe.capitalize} cannot be instantiated with keyword 'new'." -> trm.toLoc :: Nil)
        shape match
        case ss: SymShape =>
          // TODO handle ss.resSym
          val bms = ss.sym
          bms.onComplete: () =>
            bms.asCls match
            case S(cls) =>
              trm.resolvedTargets ::= cls
              val cd = cls.defn.get
              listenExt(cd.ext, extsh => {
                val dsh = DefnShape(cd, extsh)
                val sh = newShapes.getOrElseUpdate((cls, ss.markss, nw.resSym), {
                  dsh.unappliedParams.lazyZip(nw.args).foreach:
                    case ((ps, mss), args) =>
                      args match
                      case args: Tup =>
                        zipArgs(mss, ps.params, ps.restParam, args.fields, nw, dsh)
                      case _ => ???
                  NewShape(dsh, cls, ss.markss, nw.args, nw)
                })
                if nw.shapes.add(sh) then
                  nw.shapeListeners.foreach(listener => listener(sh))
              })
            case N =>
              reject
        case _ =>
          reject
    case _ =>
      nw.isErroneous = true
      resolError(nw,
        msg"Invalid class expression: ${nw.cls.describe}" -> nw.cls.toLoc :: Nil)
  
  def defineVar(sym: LocalSymbol | TermSymbol, rhs: Term): DefineVar =
    if newResolution then sym match
      case sym: TermSymbol =>
        // symShape(sym, rhs)
        // ???
        // sym.defn.get
        println(s"TODO: defineVar for TermSymbol ${sym.showDbg}")
      case sym: LocalSymbol =>
        listen(rhs): sh =>
          assert(isOwnedSym(sym), s"defineVar: sym = ${sym.showDbg}, rhs = ${rhs.showDbg}")
          if sym.shapes.add(sh) then
            sym.shapeListeners.foreach(listener => listener(sh))
    DefineVar(sym, rhs)
  
  def listenDefn(sym: TermSymbol, listener: TermShape => Unit): Unit =
    sym.defn match
    case S(td: TermDefinition) if td.params.isEmpty =>
      td.body match
      case S(body) =>
        listenTerm(body)(listener)
      case N =>
        ??? // TODO error
    case S(d) =>
      listener(defnShapes.getOrElseUpdate(sym, DefnShape(d, N)))
    case N =>
      sym.defnListeners += (d => listener(defnShapes.getOrElseUpdate(sym, DefnShape(d, N))))
  
  def pipeTerm(from: Term, to: ShapeHost): Unit =
    log(s"pipeTerm: from = ${from.showDbg}, to = ${to.showDbg}; ${to.shapes}")
    listenTerm(from): sh =>
      if to.shapes.add(sh) then
        to.shapeListeners.foreach(listener => listener(sh))
  
  def listenExt(ext: Opt[Term], listener: Opt[TermShape] => Unit): Unit =
    ext match
    case S(trm) =>
      listenTerm(trm): sh =>
        listener(S(sh))
    case N =>
      listener(N)
  
  def fromBMS(bms: BlockMemberSymbol, resSym: FlowSymbol, markss: Ls[Marks], listener: TermShape => Unit, trm: Term) =
    log(s"listenBMS: bms = ${bms.describe}")
    bms.onComplete: () =>
      log(s"listenedBMS: bms = ${bms.describe}")
      bms.asModOrObj orElse bms.asTrm orElse bms.asCls match
      case S(sym: (ModuleOrObjectSymbol | TermSymbol | ClassSymbol)) =>
        val wrappedListener: TermShape => Unit = sh =>
          log(s"fromBMS: bms = ${bms.showDbg}, sh = ${sh.shwDbg}, flow = ${resSym.showDbg}, markss = ${markss.map(_.showDbg)}")
          val sh0 = sh
          MarkedShape.exit(sh, sym, S(resSym)).exit(markss) match
          // sh.exit(markss) match
          // case NoShape =>
          // case sh: TermShape =>
          //   MarkedShape.exit(sh, sym, S(resSym)) match
            case NoShape =>
              log(s"FILTER OUT ${sh.shwDbg} for ${sym.showDbg} % ${resSym.showDbg}")
            case sh: TermShape =>
              // if sh is sh0
              if sh0.isInstanceOf[MarkedShape]
              then log(s"MATCH ${sh.shwDbg} for ${sym.showDbg} % ${resSym.showDbg}")
              else log(s"PUSH ${sh.shwDbg}")
              listener(sh)
        sym.defn match
        case S(td: TermDefinition) if td.params.isEmpty =>
          log(s"listenTerm: td.body = ${td.body.fold("N")(_.showDbg)}")
          td.body match
          case S(body) =>
            listenTerm(body)(wrappedListener)
          case N =>
            ??? // TODO error
        case S(d: TermDefinition) =>
          d.tsym match
          case ccs: ClassCtorSymbol =>
            val cls = ccs.associatedCls.defn.get
            listenExt(cls.ext, extsh =>
              defnShapes.get(sym).foreach: existing =>
                ??? // TODO error?
              wrappedListener(defnShapes.getOrElseUpdate(sym, DefnShape(d,  S(BaseShape(cls, extsh)))))
            )
          case _ =>
            wrappedListener(defnShapes.getOrElseUpdate(sym, DefnShape(d, N)))
        case S(d: ClassLikeDef) =>
          listenExt(d.ext, extsh =>
            // defnShapes.get(sym).foreach: existing =>
            //   ??? // TODO error?
            wrappedListener(defnShapes.getOrElseUpdate(sym, DefnShape(d, extsh)))
          )
        case N =>
          // sym.defnListeners += (d => listener(defnShapes.getOrElseUpdate(sym, DefnShape(d))))
          softAssert(false, s"Symbol definition of ${sym} is not set upon completion of ${bms}")
      case _ =>
        resolError(trm,
          msg"Expected a term; got ${bms.describe} '${bms.nme}'" -> N :: Nil,
          // msg"expected a term shape, but got ${bms.describe} (${bms.toString})" -> trm.toLoc :: Nil,
        )
  
  def listenTerm(trm: Term)(listener: TermShape => Unit): Unit =
    log(s"listenTerm: trm = ${trm.showDbg}")
    listen(trm):
      case sh: TermShape =>
        listener(sh)
      case ss: SymShape =>
        fromBMS(ss.sym, ss.resSym, ss.markss, listener, trm)
  
  def listen(trm: Term, discardMarks: Bool = false)(listener: Shape => Unit): Unit =
    log(s"listen: trm = ${trm.showDbg}")
    trm.shapeListeners += listener
    trm match
    // * Synthetic selections are not really selections from the POV of the resolver.
    // * Eg: a plain member reference or plain reference to imported symbol
    // * Later, we should make Terms more closely aligned wiht the source and remove SynthSel
    case ss: SynthSel =>
      ss.sym match
      case S(ts: TermSymbol) =>
        ???
        ts.defn.get.body match
        case S(body) =>
          listenTerm(body)(listener)
        case N =>
          ??? // TODO error? use sig
      case S(bms: BlockMemberSymbol) =>
        // TODO: add mark
        fromBMS(bms, ss.resSym, Nil//TODO?
          , listener, trm)
      case N => ???
    case intro: IntroTerm =>
      val sh = introShapes.getOrElseUpdate(intro, {
        log(s"introShape: intro = $intro")
        IntroShape(intro)
      })
      listener(sh)
    case ref @ Ref(loc: LocalSymbol) =>
      loc.shapes.foreach(listener)
      loc.shapeListeners += listener
    case ref @ SimpleRef(sym) =>
      sym match
      case loc: LocalSymbol =>
        loc.shapes.foreach(listener)
        loc.shapeListeners += listener
    case ref @ MemberRef(sym: TermSymbol) =>
      ???
      // listenDefn(sym, sh =>
      //   listener(MarkedShape.enter(sh, sym, S(ref.resSym))))
    case ref @ MemberRef(sym: BlockMemberSymbol) =>
      val fs = ref.resSym
      val sh = symShapes.getOrElseUpdate((sym, fs, Nil), SymShape(sym, fs, Nil))
      listener(sh)
    case Capture(base, thru) =>
      if discardMarks then
        listen(base)(listener)
      else listenTerm(base): sh =>
        listener(MarkedShape.enter(sh, thru, N))
    case ref @ Ref(sym: InnerSymbol) => // TODO: remove remaining occurrences of such refs
      sym.shapeListeners += listener
    case ref @ Ref(bsym: BlockMemberSymbol) =>
      ???
    case res: ResolvableImpl =>
      res.shapes.foreach(listener)
      // ???
    case sh: ShapeHost =>
      sh.shapes.foreach(listener)
      sh.shapeListeners += listener
    case Blk(sts, rs) =>
      listen(rs)(listener)
    // case u: UnitVal =>
    case Missing =>
      () // FIXME: Currently get this from light-elaborated Predef import
    case _ =>
      println(s"TODO: listen for ${trm.describe} (${trm.getClass})")
      ()
  
end NewResolver


