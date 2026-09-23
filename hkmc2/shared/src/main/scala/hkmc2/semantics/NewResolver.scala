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
  private val selfShapes: mutable.Map[InnerSymbol, BaseShape] = mutable.Map.empty
  // Aggregate nodes whose spread subscriptions have already been installed in this
  // elaboration. Term equality is structural, so key by identity: equal expressions
  // can receive their pending spread candidates through different listener lists.
  private val aggregateProducers = mutable.Set.empty[Identity[Tup | Rcd]]
  val defnShapes: mutable.Map[DefinitionSymbol[?], DefnShape] = mutable.Map.empty
  
  /** Interpret types through completed symbolic candidates, independently of term overloads. */
  def typeResolution(term: Term): TypeResolution = term.typeInterpretation match
    case S(result) => result
    case N =>
      val result = new TypeResolution(term, messages => resolError(term, messages))
      term.typeInterpretation = S(result) // Register before following a potentially recursive alias.
      def select(symbol: TypeSymbol): Unit =
        term.withoutCaptures match
          case ref: NewResolvable =>
            if !ref.resolvedTargets.contains(symbol) then ref.resolvedTargets ::= symbol
          case _ => ()
        def definition(defn: Definition): Unit = defn match
          case cls: ClassLikeDef => result.publish(TypeShape.Nominal(cls))
          case alias: TypeDef => result.publish(TypeShape.Alias(alias.sym, alias.rhs.map(typeResolution)))
          case _ => result.publish(TypeShape.Abstract)
        symbol.defn match
          case S(defn) => definition(defn)
          case N => symbol.defnListeners += definition
      def reject(shape: Shape): Unit =
        result.fail(msg"${shape.describe.capitalize} cannot be used as a type" -> shape.toLoc :: Nil)
        result.publish(TypeShape.Abstract)
      term match
        case Capture(base, _) => typeResolution(base).listen(result.publish)
        case TyApp(base, _) => typeResolution(base).listen(result.publish)
        case Forall(_, _, body) => typeResolution(body).listen(result.publish)
        case CompType(left, right, union) =>
          val l = typeResolution(left)
          val r = typeResolution(right)
          result.publish(if union then TypeShape.Union(l, r) else TypeShape.Intersection(l, r))
        case _: FunTy => result.publish(TypeShape.Function)
        case UnitVal() => result.publish(TypeShape.Unit)
        case SimpleRef(sym: VarSymbol) if sym.decl.exists(_.isInstanceOf[TyParam]) =>
          result.publish(TypeShape.Abstract)
        case _: WildcardTy | _: Neg | _: Rcd | _: Tup | _: Lit | Missing | Error() =>
          result.publish(TypeShape.Abstract)
        case _ => listen(term, discardMarks = true):
          case shape: SymShape => shape.sym.onComplete: () =>
            shape.sym.asTpe.orElse(shape.sym.asModOrObj) match
              case S(symbol) => select(symbol)
              case N => reject(shape)
          case shape: TermShape => reject(shape)
      result

  def eraseSignature(sign: Term): Opt[codegen.ErasedValueType] =
    if newResolution then
      val resolution = typeResolution(sign)
      S(new codegen.ErasedType.Deferred(resolution.erase(Set.empty)))
    else codegen.ErasedType.eraseSign(sign)

  /** Declared types provide instance members before there are any calls or assignments.
    * Recursive aliases are followed once per subscription; their operands may resolve later.
    */
  def listenTypeValues(sign: Term)(listener: TermShape => Unit): Unit =
    val visited = mutable.Set.empty[TypeResolution]
    def follow(resolution: TypeResolution): Unit = if visited.add(resolution) then
      resolution.listen:
        case TypeShape.Nominal(defn) =>
          listenExt(defn.ext, ext => listener(selfShapes.getOrElseUpdate(defn.sym, BaseShape(defn, ext))))
        case TypeShape.Alias(_, rhs) => rhs.foreach(follow)
        case TypeShape.Union(left, right) => follow(left); follow(right)
        case TypeShape.Intersection(left, right) => follow(left); follow(right)
        case _ => ()
    follow(typeResolution(sign))

  def isOwnedSym(sym: Symbol): Bool =
    sym.getState is state
  
  def resolError(src: Term | Pattern, msgs: Ls[(Message, Opt[Loc])]): Unit = raise:
    ErrorReport(msg"Resolution error in ${src.describe}" -> src.toLoc ::msgs, source = Diagnostic.Source.Compilation)
  
  /** Subscribe once to complete argument-tuple candidates. A pending spread is not
    * an argument, nor evidence of an arity mismatch; each resolved combination is.
    */
  def zipArgs(mss: Ls[Marks], ps: Ls[Param], r: Opt[Param], args: Term, src: Term, funSh: TermShape): Unit =
    val expectedCount = ps.length
    val reportedCounts = mutable.Set.empty[Int]
    def publish(p: Param, shape: TermShape | NoShape): Unit = shape match
      case NoShape => ()
      case sh: TermShape =>
        if isOwnedSym(p.sym) && p.sym.shapes.add(sh) then p.sym.shapeListeners.foreach(_(sh))
    def matchSegments(tuple: TupleShape, marks: Marks): Unit =
      val segments = tuple.segments
      val knownCount = segments.count(_.isInstanceOf[TupleShape.Field])
      val unknownLength = knownCount != segments.length
      val arityMismatch = (!unknownLength && knownCount < expectedCount) || (r.isEmpty && knownCount > expectedCount)
      if arityMismatch && reportedCounts.add(knownCount) then
        val count = if unknownLength then msg"at least ${knownCount}" else msg"${knownCount}"
        resolError(src,
          msg"${funSh.describe.capitalize} expected ${expectedCount} ${
            "argument".pluralized(expectedCount)}, but got ${count}" -> funSh.toLoc :: Nil)
      // Distribute only over successful argument counts. With no rest parameter,
      // the total arity anchors known suffix fields even after an unknown spread.
      // With a rest parameter, positions after an unknown spread have no upper
      // bound; consider every remaining fixed position and retain every rest tail.
      if !arityMismatch then
        val extra = (expectedCount - knownCount).max(0)
        def assign(segment: TupleShape.Segment, positions: Range): Unit =
          positions.foreach: index =>
            val p = ps(index)
            if p.sign.isEmpty then segment match
              case TupleShape.Field(field, inner) => listenTerm(field.term): sh =>
                publish(p, sh.exit(inner).exit(marks).enter(mss))
              case TupleShape.Unknown(source, inner) =>
                publish(p, UnknownValueShape(source).exit(inner).exit(marks).enter(mss))
        def loop(rest: Ls[TupleShape.Segment], before: Int, unknownBefore: Bool): Unit = rest match
          case Nil => ()
          case (field: TupleShape.Field) :: tail =>
            val unknownAfter = tail.exists(_.isInstanceOf[TupleShape.Unknown])
            // With no later unknown segment, preceding spreads must supply all
            // missing fixed arguments, even when the function has a rest parameter.
            val first = if unknownBefore && !unknownAfter then before + extra else before
            val last = if !unknownBefore then before
              else if r.nonEmpty then expectedCount - 1 else before + extra
            assign(field, first.max(0) until (last + 1).min(expectedCount))
            loop(tail, before + 1, unknownBefore)
          case (unknown: TupleShape.Unknown) :: tail =>
            val end = if r.nonEmpty then expectedCount else before + extra
            assign(unknown, before until end)
            loop(tail, before, true)
        loop(segments, 0, false)
        r.foreach: p =>
          // If consumption reaches an unknown segment, some subsequent fields
          // may have been consumed too. Approximate that optional prefix with an
          // unknown segment, retaining the suffix that must remain. Publishing
          // separate concrete tails here would turn uncertainty into false arity
          // failures when the rest tuple is spread into another call.
          def drop(xs: Ls[TupleShape.Segment], count: Int, approximate: Bool): Ls[TupleShape.Segment] =
            if count == 0 then xs
            else xs match
              case Nil => Nil
              case (_: TupleShape.Field) :: rest => drop(rest, count - 1, approximate)
              case (_: TupleShape.Unknown) :: rest =>
                val suffix = drop(rest, count, false)
                if approximate then TupleShape.Unknown(tuple.source, Nil) :: suffix else suffix
          val remaining = drop(segments, expectedCount, true)
          val rest = if ps.isEmpty then tuple else TupleShape(tuple.source, TupleShape.Rest(tuple, remaining) :: Nil)
          publish(p, rest.exit(marks).enter(mss))
    listenTerm(args):
      case Marked(tuple: TupleShape, marks) => matchSegments(tuple, marks)
      case _ => resolError(src, msg"Expected an argument tuple." -> args.toLoc :: Nil)
  
  /** Resolve every constructor pattern through the same symbolic interpretation.
    * A class overload takes precedence over its term companion in this context.
    * Keep every candidate so lowering can diagnose ambiguity independently of
    * the order in which definitions and receiver shapes become available. */
  def constructorPattern(res: Pattern.Constructor): Unit = if newResolution then
    val lhs = res.target
    def select(sym: DefinitionSymbol[?]): Bool =
      lhs.withoutCaptures match
        case trm: NewResolvable =>
          if !trm.resolvedTargets.contains(sym) then trm.resolvedTargets ::= sym
        case _ => ()
      if res.resolvedTargets.contains(sym) then false
      else
        res.resolvedTargets ::= sym
        true
    def reject(sh: TermShape): Unit =
      res.isErroneous = true
      resolError(res, msg"${sh.describe.capitalize} cannot be used as a constructor pattern." -> sh.toLoc :: Nil)
    def classPattern(cls: ClassLikeDef): Unit = if select(cls.sym) then
      val assoc = res.arguments match
        case N => Nil
        case S(args) => cls.paramsOpt match
          case N =>
            if args.nonEmpty || cls.isInstanceOf[ClassDef] then
              res.isErroneous = true
              resolError(res, msg"${cls.describe.capitalize} does not take pattern arguments." -> cls.toLoc :: Nil)
            Nil
          case S(ps) =>
            if ps.restParam.nonEmpty then TODO(ps.restParam)
            if args.sizeCompare(ps.params) =/= 0 then
              res.isErroneous = true
              resolError(res,
                msg"${cls.describe.capitalize} expected ${ps.params.length} ${
                  "pattern argument".pluralized(ps.params.length)}, but got ${args.length}" -> cls.toLoc :: Nil)
            ps.params.lazyZip(args).flatMap: (p, a) =>
              p.fldSym match
                case S(fldSym: BlockMemberSymbol) =>
                  // withFields reports member/alias conflicts before dropping all
                  // generated fields for recovery. Parameters retain their fldSym,
                  // so verify its identity in the recovered body: a body member may
                  // occupy the same name. Do not publish dangling pattern fields or
                  // report another error for this already-diagnosed class.
                  if cls.body.members.get(fldSym.nme).contains(fldSym) then (fldSym -> a) :: Nil
                  else
                    res.isErroneous = true
                    Nil
                case _ =>
                  res.isErroneous = true
                  resolError(res, msg"Pattern argument requires an accessible constructor field." -> p.toLoc :: Nil)
                  Nil
      if !res.isErroneous then
        val psh = CtorPatternShape(cls, assoc, res, FlowSymbol.pat())
        if res.shapes.add(psh) then res.shapeListeners.foreach(_(psh))
    def valuePattern(sh: TermShape): Unit = sh.applicationHead match
      case (ds: DefnShape, _) => ds.defn match
        case cls: ClassDef => classPattern(cls)
        case obj: ModuleOrObjectDef if obj.sym.asObj.isDefined => classPattern(obj)
        case td: TermDefinition => td.tsym match
          case ctor: ClassCtorSymbol => classPattern(ctor.associatedCls.defn.get)
          case _ => reject(sh)
        case _ => reject(sh)
      case _ => reject(sh)
    lhs.withoutCaptures match
      case Term.Error() => res.isErroneous = true
      case Term.Ref(sym: VarSymbol) if sym.decl.exists(_.isPatternConstructor) =>
        res.resolvedTargets ::= sym
      case Term.SimpleRef(sym: VarSymbol) if sym.decl.exists(_.isPatternConstructor) =>
        res.resolvedTargets ::= sym
      case _ => listen(lhs, discardMarks = true): sh =>
        sh match
          case sh: SymShape =>
            val bms = sh.sym
            bms.onComplete: () =>
              bms.asPat.orElse(bms.asCls).orElse(bms.asObj) match
                case S(sym: PatternSymbol) => select(sym)
                case S(sym: (ClassSymbol | ModuleOrObjectSymbol)) =>
                  sym.defn match
                    case S(cls) => classPattern(cls)
                    case N => softAssert(false, "Completed pattern member has no definition")
                case N =>
                  fromBMS(bms, FlowSymbol.pat(), sh.markss, valuePattern, lhs, _ => ())
          case sh: TermShape => valuePattern(sh)
  
  /** Propagate possible values to pattern bindings. Constructor tests filter by
    * nominal class; guards and literal tests may conservatively retain shapes.
    * Both scrutinee and constructor shapes can arrive after this registration. */
  def matchShapePat(shape: Shape, pattern: Pattern)(matched: Shape => Unit): Unit =
    pattern match
      case al @ Pattern.Alias(pat, _) =>
        matchShapePat(shape, pat): sh =>
          if al.symbol.shapes.add(sh) then al.symbol.shapeListeners.foreach(_(sh))
          matched(sh)
      case Pattern.Wildcard() | Pattern.Literal(_) => matched(shape)
      case Pattern.Chain(left, right) =>
        matchShapePat(shape, left)(sh => matchShapePat(sh, right)(matched))
      case Pattern.Composition(true, left, right) =>
        matchShapePat(shape, left)(matched)
        matchShapePat(shape, right)(matched)
      case Pattern.Guarded(pat, _) => matchShapePat(shape, pat)(matched)
      // Compilation-strategy annotations do not change the pattern's bindings.
      case Pattern.Annotated(pat, _) => matchShapePat(shape, pat)(matched)
      case ctor: Pattern.Constructor =>
        def listenConstructor(psh: PatternShape): Unit = psh match
          case CtorPatternShape(cls, fs, _, resSym) =>
            def check(sh: TermShape): Unit =
              if sh.isInstanceOfClass(cls) then
                fs.foreach: (bms, pat) =>
                  sh.getMember(bms.nme) match
                    case MemberLookup.Found(sym: BlockMemberSymbol, marks) =>
                      val field = symShapes.getOrElseUpdate((sym, resSym, marks), SymShape(sym, resSym, marks))
                      matchShapePat(field, pat)(_ => ())
                    case _ =>
                      // classPattern only publishes fields present in cls.body.
                      // The nominal test above admits only that class's instances,
                      // this-values, and subclasses. Their member lookup follows
                      // the same class bodies and inheritance chain; overrides are
                      // also BlockMemberSymbols. Record members cannot replace a
                      // class's own field. Thus this branch is an internal mismatch
                      // between nominal matching and member lookup, not recovery
                      // from a malformed class (filtered by classPattern above).
                      softAssert(false, "Matched constructor is missing its field")
                matched(sh)
            shape match
              case sh: TermShape => check(sh)
              case sh: SymShape => fromBMS(sh.sym, sh.resSym, sh.markss, check, ctor.target, _ => ())
        ctor.shapeListeners += listenConstructor
        ctor.shapes.foreach(listenConstructor)
      case Pattern.Tuple(_, _) => () // Tuple binding shapes are not inferred yet.
      case _ => TODO(pattern)
  
  def matchScrutPat(scrutinee: Term.Ref, pattern: Pattern): Unit = if newResolution then
    listenTerm(scrutinee)(sh => matchShapePat(sh, pattern)(_ => ()))
  
  def appShape(lhs: TermShape, args: Term, res: App): Unit =
    // An unknown element used as a callee stays a dynamic call. Propagate its
    // unknown result rather than inferring callability from a different candidate.
    lhs match
      case Marked(_: UnknownValueShape, _) =>
        if res.shapes.add(lhs) then res.shapeListeners.foreach(_(lhs))
        return
      case _ => ()
    // log(s"appShape? lhs = $lhs, args = $args, res = $res")
    val sh = appShapes.getOrElseUpdate((lhs, res.resSym), {
      log(s"appShape: lhs = ${lhs.shwDbg}, args = ${args.showDbg}, res = ${res.showDbg}")
      new AppShape(lhs, args, res)
    })
    lhs.unappliedParams match
    case Nil => ()
    case (ps, mss) :: pss =>
      zipArgs(mss, ps.params, ps.restParam, args, res, lhs)
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
      case (sh: IntroShape, mss) =>
        sh.trm match
        case Lam(params, body) =>
          // Exit the same context that zipArgs enters, filtering results from other uses.
          go(body, mss)
        case _ =>
          softAssert(res.isErroneous)
      case _ =>
        softAssert(res.isErroneous)
    else register
  
  private def publishMember(host: NewResolvable & ShapeHost, member: BlockMemberSymbol | RecordMember,
      flow: FlowSymbol, marks: Ls[Marks]): Unit =
    def publish(shape: Shape): Unit =
      if host.shapes.add(shape) then host.shapeListeners.foreach(_(shape))
    def definition(sym: BlockMemberSymbol): Unit =
      publish(symShapes.getOrElseUpdate((sym, flow, marks), SymShape(sym, flow, marks)))
    member match
      case member: BlockMemberSymbol => definition(member)
      case RecordMember(field, false) => definition(field.sym)
      case RecordMember(field, true) =>
        // Mutability affects the read, not member identity. Select the ordinary
        // term interpretation even though writes make its value shape unknown.
        if !host.resolvedTargets.contains(field.tsym) then host.resolvedTargets ::= field.tsym
        publish(UnknownValueShape(field.rhs))

  private def unknownMember(host: NewResolvable, name: Str, reason: MemberLookup.Uncertainty, loc: Opt[Loc]): Unit =
    host.isErroneous = true
    val message = reason match
      case MemberLookup.Uncertainty.ValueShape =>
        msg"Cannot resolve member '$name' of a value with unknown shape."
      case MemberLookup.Uncertainty.RecordOverwrite =>
        msg"Cannot resolve member '$name' across a computed key or unknown record spread."
    resolError(host, message -> loc :: Nil)

  def unresolvedRef(ref: UnresolvedRef): Unit =
    ref.prefixes.foreach: prefix =>
      listenTerm(prefix): shape =>
        shape.getMember(ref.id.name) match
          case MemberLookup.Found(member, marks) =>
            val candidate = prefix -> member.memberSymbol
            if !ref.resolvedMembers.contains(candidate) then ref.resolvedMembers ::= candidate
            publishMember(ref, member, ref.resSym, marks)
          case MemberLookup.Missing =>
            // A known miss in one wildcard source is not an error: another may
            // provide the name. Lowering diagnoses references with no candidates.
            ()
          case MemberLookup.Unknown(reason, loc) => unknownMember(ref, ref.id.name, reason, loc)

  /** Inspect an overload set only once its definitions have all been published. */
  private def completedClass(shape: SymShape)(selected: ClassDef => Unit, absent: () => Unit): Unit =
    shape.sym.onComplete: () =>
      shape.sym.asCls match
        case S(cls) => selected(cls.defn.get)
        case N => absent()

  /** Class interpretations wait for completed overload sets, independently of term
    * companions. Aliases can supply constructor shapes; applied instances cannot.
    * Capture marks are retained for subsequent instance-member lookup. */
  private def listenClass(trm: Term)(selected: (ClassDef, Ls[Marks]) => Unit, reject: Shape => Unit): Unit =
    def select(cls: ClassDef, marks: Ls[Marks]): Unit =
      trm.classHead match
        case ref: NewResolvable =>
          if !ref.resolvedTargets.contains(cls.sym) then ref.resolvedTargets ::= cls.sym
        case _ => ()
      selected(cls, marks)
    def value(sh: TermShape): Unit = sh match
      case Marked(ds: DefnShape, marks) => ds.defn match
        case cls: ClassDef => select(cls, marks :: Nil)
        case td: TermDefinition => td.tsym match
          case ctor: ClassCtorSymbol => select(ctor.associatedCls.defn.get, marks :: Nil)
          case _ => reject(sh)
        case _ => reject(sh)
      case _ => reject(sh)
    trm match
      case TyApp(base, _) => listenClass(base)(select, reject)
      case Capture(base, thru) =>
        listenClass(base)((cls, marks) => select(cls, marks ::: EntryMark(thru, N, NoMarks) :: Nil), reject)
      case _ => listen(trm):
        case sh: SymShape =>
          completedClass(sh)(cls => select(cls, sh.markss),
            () => fromBMS(sh.sym, sh.resSym, sh.markss, value, trm, _ => ()))
        case sh: TermShape => value(sh)

  def newSel(sel: NewSel): Unit =
    log(s"newSel? sel = ${sel.showDbg}")
    def member(info: MemberLookup, description: Message, loc: Opt[Loc]): Unit = info match
      case MemberLookup.Found(bms, marks) =>
        log(s"newSel member: bms = ${bms.memberSymbol.showDbg}, mss = ${marks.map(_.showDbg)}")
        if !sel.resolvedMembers.contains(bms.memberSymbol) then sel.resolvedMembers ::= bms.memberSymbol
        publishMember(sel, bms, sel.resSym, marks)
      case MemberLookup.Missing =>
        sel.isErroneous = true
        resolError(sel, msg"$description does not contain member '${sel.id.name}'" -> loc :: Nil)
      case MemberLookup.Unknown(reason, loc) => unknownMember(sel, sel.id.name, reason, loc)
    sel.cls match
      case N => listenTerm(sel.prefix): shape =>
        log(s"newSel: sel = ${sel.showDbg}, shape = ${shape.shwDbg}")
        member(shape.getMember(sel.id.name), msg"${shape.describe.capitalize}", shape.toLoc)
      case S(cls) =>
        listenClass(cls)((cd, marks) =>
          val candidate = cd.sym -> marks
          if !sel.resolvedClasses.contains(candidate) then sel.resolvedClasses ::= candidate
          listenExt(cd.ext, ext =>
            member(DefnShape(cd, ext).getInstanceMember(sel.id.name).withMarks(marks),
              msg"Class '${cd.sym.nme}'", cd.toLoc))
        , sh =>
          sel.isErroneous = true
          resolError(sel, msg"${sh.describe.capitalize} cannot be used as a projection class." -> sh.toLoc :: Nil)
        )
  
  def resolveNew(nw: Term.New): Unit =
    log(s"resolveNew? res = ${nw.showDbg}")
    nw.cls.classHead match
      case trm: NewResolvable => listen(trm): shape =>
        def reject(): Unit =
          nw.isErroneous = true
          resolError(nw, msg"${shape.describe.capitalize} cannot be instantiated with keyword 'new'." -> shape.toLoc :: Nil)
        shape match
          case ss: SymShape => completedClass(ss)(cd =>
            if !trm.resolvedTargets.contains(cd.sym) then trm.resolvedTargets ::= cd.sym
            listenExt(cd.ext, extsh =>
              val dsh = DefnShape(cd, extsh)
              val sh = newShapes.getOrElseUpdate((cd.sym, ss.markss, nw.resSym), {
                dsh.unappliedParams.lazyZip(nw.args).foreach:
                  case ((ps, mss), args) =>
                    zipArgs(mss, ps.params, ps.restParam, args, nw, dsh)
                NewShape(dsh, cd.sym, ss.markss, nw.args, nw)
              })
              if nw.shapes.add(sh) then nw.shapeListeners.foreach(_(sh))
            )
          , reject)
          case _ => reject()
      case _ =>
        nw.isErroneous = true
        resolError(nw, msg"Invalid class expression: ${nw.cls.describe}" -> nw.cls.toLoc :: Nil)
  
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
  
  def fromBMS(bms: BlockMemberSymbol, resSym: FlowSymbol, markss: Ls[Marks], listener: TermShape => Unit,
      trm: Term, selected: DefinitionSymbol[?] => Unit) =
    log(s"listenBMS: bms = ${bms.describe}")
    bms.onComplete: () =>
      log(s"listenedBMS: bms = ${bms.describe}")
      bms.asModOrObj orElse bms.asTrm orElse bms.asCls match
      case S(sym: (ModuleOrObjectSymbol | TermSymbol | ClassSymbol)) =>
        // Selection is independent of the selected value's shape. In particular,
        // an assignment needs its target even if the value has no inferred shape.
        // Pattern resolution supplies its own interpretation of the selected head.
        selected(sym)
        val wrappedListener: TermShape => Unit = sh =>
          log(s"fromBMS: bms = ${bms.showDbg}, sh = ${sh.shwDbg}, flow = ${resSym.showDbg}, markss = ${markss.map(_.showDbg)}")
          val sh0 = sh
          // Modules and objects introduce no enter/exit boundary of their own.
          // Adding an exit here would create a mismatch because we do not track module captures explicitly.
          val exited = sym match
            case _: ModuleOrObjectSymbol => sh
            case _ => MarkedShape.exit(sh, sym, S(resSym))
          exited.exit(markss) match
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
            // A declared value has a selected definition but no implementation
            // from which to infer a value shape (e.g. an external mutable field).
            ()
        case S(d: TermDefinition) =>
          d.tsym match
          case ccs: ClassCtorSymbol =>
            val cls = ccs.associatedCls.defn.get
            listenExt(cls.ext, extsh =>
              // Several uses (including deferred opens) can request the same
              // constructor shape. Reuse it while checking the cache invariant.
              val shape = defnShapes.getOrElseUpdate(sym, DefnShape(d, S(BaseShape(cls, extsh))))
              softAssert(shape.defn is d)
              shape.ext match
                case S(base: BaseShape) => softAssert((base.defn is cls) && base.ext == extsh)
                case _ => softAssert(false, "Constructor shape is missing its class base")
              wrappedListener(shape)
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
        def reportError = resolError(trm,
          msg"Expected a term; got ${bms.describe} '${bms.nme}'" -> N :: Nil)
        trm.withoutCaptures match
          case ref: NewResolvable =>
            if !ref.isErroneous then
              ref.isErroneous = true
              reportError
          case _ => reportError
  
  /** Request the term interpretation of a reference without requiring a consumer
    * of its value shape. Direct definition references already identify the target;
    * overload sets need listeners, including when their definitions arrive later.
    */
  def requireTerm(trm: Term): Unit = trm.withoutCaptures match
    case direct @ MemberRef(sym: TermSymbol) =>
      // Selecting a known field does not require resolving the field's value.
      softAssert(direct.resolvedTargets.forall(_ is sym))
      direct.resolvedTargets = sym :: Nil
    case _: NewResolvable => listenTerm(trm)(_ => ())
    case _ => ()

  /** Annotation identity is needed before elaborating the annotated body. Read
    * the main symbol now, without waiting for a value or inspecting unfinished
    * definitions. Keep validating selections/opens: a later distinct candidate
    * must be an error, since it cannot change an already interpreted annotation.
    */
  def annotationSymbol(trm: Term): Opt[Symbol] = trm match
    case Capture(base, _) => annotationSymbol(base)
    case TyApp(base, _) => annotationSymbol(base)
    case App(base, _) => annotationSymbol(base)
    case ref: NewRefImpl => S(ref.sym)
    case _: NewSel | _: UnresolvedRef =>
      val symbols = mutable.LinkedHashSet.empty[BlockMemberSymbol]
      var collecting = true
      var failed = false
      def fail(): Unit = if !failed then
        failed = true
        resolError(trm, msg"An annotation's main symbol must be uniquely known when the annotation is elaborated." -> N :: Nil)
      listen(trm):
        case sh: SymShape =>
          if symbols.add(sh.sym) && !collecting then fail()
        case _ => fail()
      collecting = false
      symbols.toList match
        case symbol :: Nil if !failed => S(symbol)
        case _ => fail(); N
    // TODO: Ref(sym: BuiltinSymbol) is a legacy representation that still needs
    // updating to the new reference forms, even when using new resolution.
    case Ref(sym: BuiltinSymbol) => S(sym)
    case _ =>
      resolError(trm, msg"An annotation must have a known main symbol." -> N :: Nil)
      N

  def listenTerm(trm: Term)(listener: TermShape => Unit): Unit =
    log(s"listenTerm: trm = ${trm.showDbg}")
    listen(trm):
      case sh: TermShape =>
        listener(sh)
      case ss: SymShape =>
        fromBMS(ss.sym, ss.resSym, ss.markss, listener, trm, sym =>
          trm.withoutCaptures match
          case ref: NewResolvable =>
            if !ref.resolvedTargets.contains(sym) then ref.resolvedTargets ::= sym
          case _ => ()
        )
  
  /** Install one spread subscription graph per aggregate node in this elaboration.
    * Register before following spreads, whose callbacks can synchronously request
    * this node again. An empty candidate set may be waiting for a forward definition,
    * so it cannot indicate whether subscriptions have been installed. Every new
    * consumer receives existing candidates and then subsequent publications.
    */
  private def listenAggregate(aggregate: Tup | Rcd, listener: Shape => Unit)
      (start: (TermShape => Unit) => Unit): Unit =
    val first = aggregateProducers.add(new Identity(aggregate))
    // A definition imported from another elaborator can already carry candidates.
    // Replay them even on this resolver's first subscription, before producing deltas.
    aggregate.shapes.foreach(listener)
    if first then
      start: shape =>
        if aggregate.shapes.add(shape) then aggregate.shapeListeners.foreach(_(shape))

  def listen(trm: Term, discardMarks: Bool = false)(listener: Shape => Unit): Unit =
    log(s"listen: trm = ${trm.showDbg}")
    trm.shapeListeners += listener
    trm match
    case _: SynthSel =>
      lastWords("Synthetic selections must not enter new resolution")
    case TyApp(underlying, _) => listen(underlying, discardMarks)(listener)
    case Mut(underlying) => listenTerm(underlying)(listener)
    case tuple: Tup => listenAggregate(tuple, listener): publish =>
        def expand(elems: Ls[Elem], reversed: Ls[TupleShape.Element]): Unit = elems match
          case Nil =>
            // A sole spread preserves its operand's shape and context exactly.
            // Besides avoiding wrappers, this lets recursive rest forwarding
            // reach the same fixed point as forwarding an ordinary parameter.
            val shape = reversed match
              case TupleShape.Spread(shape, NoMarks) :: Nil => shape
              case TupleShape.Spread(shape, marks: SomeMarks) :: Nil => MarkedShape(shape, marks)
              case _ => TupleShape(tuple, reversed.reverse)
            publish(shape)
          case (field: Fld) :: rest => expand(rest, TupleShape.Field(field, Nil) :: reversed)
          case Spd(_, term) :: rest =>
            val seen = mutable.Set.empty[TermShape]
            listenTerm(term): sh =>
              if seen.add(sh) then sh match
                case Marked(shape: TupleShape, marks) =>
                  // Widen an incoming candidate that already contains its own
                  // producer in this context. For `fun growing(n) = ‹...› [n, ...growing(n - 1)] ‹...›`,
                  // this replaces the recursive operand with an arbitrary sequence,
                  // retaining the surrounding `n` field and the spread's marks.
                  // Further feedback in the same context produces the same widened
                  // candidate, so the host's deduplication stops that expansion.
                  // Earlier candidates remain valid alternatives. A pending spread
                  // never reaches this branch: it waits for a shape notification.
                  val spread = if shape.containsSpread(shape.source, marks)
                    then TupleShape.unknown(shape.source)
                    else shape
                  expand(rest, TupleShape.Spread(spread, marks) :: reversed)
                case Marked(_, marks) =>
                  // Opaque iterables (e.g. external Arrays) have no resolved
                  // element layout. Their runtime spread is still permitted.
                  expand(rest, TupleShape.Spread(TupleShape.unknown(term), marks) :: reversed)
        expand(tuple.fields, Nil)
    case record: Rcd => listenAggregate(record, listener): publish =>
        def expand(stats: Ls[Statement], reversed: Ls[RecordShape.Element]): Unit = stats match
          case Nil =>
            val shape = RecordShape(record, reversed.reverse)
            publish(shape)
          case (field: RcdField) :: rest => expand(rest, RecordShape.Field(field) :: reversed)
          case RcdSpread(term) :: rest =>
            val seen = mutable.Set.empty[TermShape]
            listenTerm(term): shape =>
              if seen.add(shape) then shape match
                case Marked(shape: RecordShape, marks) =>
                  // Bound recursive record producers just as for tuple spreads.
                  // Keep surrounding explicit fields even when the spread widens.
                  val spread = if shape.containsSpread(shape.source, marks)
                    then RecordShape(shape.source, RecordShape.Unknown :: Nil)
                    else shape
                  expand(rest, RecordShape.Spread(spread, marks) :: reversed)
                case _ => expand(rest, RecordShape.Unknown :: reversed)
          case _ :: rest => expand(rest, reversed)
        expand(record.stats, Nil)
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
      case _: BuiltinSymbol =>
        lastWords("Builtin symbols must not enter new resolution as SimpleRef")
    case SelfRef(sym) =>
      // A receiver can be referenced before its body is complete or after its
      // definition has already been published. The definition listener handles both.
      def completed(defn: ClassLikeDef): Unit =
        listenExt(defn.ext, ext =>
          // Each inner symbol has one self shape; repeated notifications must agree.
          val shape = selfShapes.getOrElseUpdate(sym, BaseShape(defn, ext))
          softAssert(shape.defn is defn)
          softAssert(shape.ext == ext)
          listener(shape))
      val symbol = sym.asDefnSym
      symbol.defn match
        case S(defn) => completed(defn)
        case N => symbol.defnListeners += completed
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
    case Blk(sts, rs) =>
      listen(rs)(listener)
    // case u: UnitVal =>
    case Missing =>
      () // FIXME: Currently get this from light-elaborated Predef import
    case _ =>
      println(s"TODO: listen for ${trm.describe} (${trm.getClass})")
      ()
  
end NewResolver
