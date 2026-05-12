package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer}

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import semantics.Elaborator.State

class SymbolRefresher(existingMapping: Map[Symbol, Symbol])(using State) extends BlockTransformer(SymbolSubst.Id):
  val mapping = MutMap.from(existingMapping)
  // Stack of cleanup frames, one per scoped block. ClsLikeDefn / applyObjBody add
  // class-internal symbols to the top frame; the enclosing applyScopedBlock pops
  // and removes them from `mapping` when its body finishes. Initialized with a
  // bottom frame so callers that hand us a non-Scoped entry block still have a
  // valid `cleanupStack.head` to add to (the bottom frame is never popped).
  private var toRemoveSymbols: List[MutSet[Symbol]] = MutSet.empty[Symbol] :: Nil

  override def applyScopedBlock(b: Block): Block =
    toRemoveSymbols = MutSet.empty[Symbol] :: toRemoveSymbols
    val res = b match
    case Scoped(syms, body) =>
      val newSyms = MutSet.empty[Symbol]
      val oldSyms = MutSet.empty[Symbol]
      for s <- syms.toList.sortBy(_.uid) do
        assert(!mapping.isDefinedAt(s), s"already defined: $s")
        val newS = s match
          case tmpSym: TempSymbol => new TempSymbol(N, tmpSym.nme)
          case bms: BlockMemberSymbol =>
            val newBms = new BlockMemberSymbol(bms.nme, Nil, bms.nameIsMeaningful)
            newBms.tsym = bms.tsym.map: t =>
              val newOwner: Opt[InnerSymbol] = t.owner.map: o =>
                existingMapping.get(o) match
                  case Some(inner: InnerSymbol) => inner
                  case _ => o
              val nt = new TermSymbol(t.k, newOwner, t.id)
              mapping(t) = nt
              oldSyms.add(t)
              nt
            newBms
          case varSym: VarSymbol => new VarSymbol(varSym.id)
          case _ => lastWords(s"unexpected symbol kind: $s")
        mapping(s) = newS
        oldSyms.add(s)
        newSyms.add(newS)
      val r = Scoped(newSyms, applyBlock(body))
      for s <- oldSyms do mapping.remove(s)
      r
    case _ => super.applyScopedBlock(b)
    val hd = toRemoveSymbols.head
    toRemoveSymbols = toRemoveSymbols.tail
    hd.foreach(mapping.remove)
    res
  override def applyBlock(b: Block): Block =
    b match
    case Assign(lhs, rhs, rest) =>
      applyResult(rhs): newRhs =>
        val newLhs = mapping.getOrElse(lhs, lhs)
        val newRest = applyBlock(rest)
        if (newLhs is lhs) && (newRhs is rhs) && (newRest is rest) then b else Assign(newLhs, newRhs, newRest)
    case Label(label, loop, body, rest) =>
      assert(!mapping.isDefinedAt(label))
      val newLabel = new LabelSymbol(label.trm, label.nme)
      mapping(label) = newLabel
      val newBody = applyBlock(body)
      mapping.remove(label)
      val newRest = applyBlock(rest)
      Label(newLabel, loop, newBody, newRest)
    case Break(label) => Break(mapping.getOrElse(label, label).asInstanceOf[LabelSymbol])
    case Continue(label) => Continue(mapping.getOrElse(label, label).asInstanceOf[LabelSymbol])
    case _ => super.applyBlock(b)
  
  override def applyDefn(defn: Defn)(k: Defn => Block): Block =
    defn match
    case fun: FunDefn =>
      assert(fun.owner.isEmpty)
      // because fun sym is not treated as a free var, we refresh here
      var newlyCreated = false
      val (sym2, dSym2) = mapping.get(fun.sym) match
        case Some(s: BlockMemberSymbol) => (s, s.tsym.get)
        case None =>
          newlyCreated = true
          val newBms = new BlockMemberSymbol(fun.sym.nme, fun.sym.trees, fun.sym.nameIsMeaningful)
          val newDsym = fun.sym.tsym.map: tsym =>
            assert(tsym.owner.isEmpty)
            new TermSymbol(tsym.k, N, tsym.id)
          newBms.tsym = S(newDsym.get)
          mapping(fun.sym) = newBms
          (newBms, newDsym.get)
        case _ => die
      val oldParamSyms = Buffer.empty[VarSymbol]
      val params2 = fun.params.map:
        case ParamList(flags, params, restParam) =>
          def handleSingleParam(p: Param) =
            val Param(flags, sym, sign, modulefulness) = p
            oldParamSyms.append(sym)
            val newSym = new VarSymbol(sym.id)
            assert(!mapping.isDefinedAt(sym))
            mapping(sym) = newSym
            Param(flags, newSym, sign, modulefulness)
          val params2 = params.map(handleSingleParam)
          val rest2 = restParam.map(handleSingleParam)
          ParamList(flags, params2, rest2)
      val body2 = applyFunBodyLikeBlock(fun.body)
      for s <- oldParamSyms do mapping.remove(s)
      if newlyCreated then
        Scoped(Set.single(sym2), k(FunDefn(N, sym2, dSym2, params2, body2)(fun.configOverride, fun.annotations)))
      else
        k(FunDefn(N, sym2, dSym2, params2, body2)(fun.configOverride, fun.annotations))
    case defn @ ValDefn(tsym, sym, rhs) =>
      val (tsym2, sym2) = mapping.get(sym) match
        case None =>
          val newBms = new BlockMemberSymbol(sym.nme, sym.trees, sym.nameIsMeaningful)
          val newTsym = new TermSymbol(tsym.k, tsym.owner, tsym.id)
          newBms.tsym = S(newTsym)
          (newTsym, newBms)
        case S(bms: BlockMemberSymbol) =>
          (bms.tsym.get, bms)
        case _ => die
      applyPath(rhs): rhs2 =>
        k(ValDefn(tsym2, sym2, rhs2)(defn.configOverride, defn.annotations))
    case defn: ClsLikeDefn =>
      val hd = toRemoveSymbols.head
      val oldIsym = defn.isym
      assert(!mapping.isDefinedAt(oldIsym), s"isym already in mapping: $oldIsym")
      val newIsym: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol = oldIsym match
        case c: ClassSymbol => new ClassSymbol(c.tree, c.id)
        case m: ModuleOrObjectSymbol => new ModuleOrObjectSymbol(m.tree, m.id)
        case p: PatternSymbol => new PatternSymbol(p.id, p.params, p.body)
        case _ => lastWords(s"unexpected isym kind: $oldIsym")
      mapping(oldIsym) = newIsym
      hd += oldIsym

      var newlyCreatedSym = false
      val newSym: BlockMemberSymbol = mapping.get(defn.sym) match
        case Some(bms: BlockMemberSymbol) => bms
        case None =>
          newlyCreatedSym = true
          val nb = new BlockMemberSymbol(defn.sym.nme, Nil, defn.sym.nameIsMeaningful)
          mapping(defn.sym) = nb
          nb
        case _ => die

      val newCtorSym: Opt[ClassCtorSymbol] = defn.ctorSym.map: cs =>
        assert(!mapping.isDefinedAt(cs))
        val newOwner = newIsym match
          case cls: ClassSymbol => cls
          case _ => lastWords(s"ClassCtorSymbol for non-class: $newIsym")
        val ncs = new ClassCtorSymbol(cs.k, S(newOwner), cs.id)
        mapping(cs) = ncs
        hd += cs
        ncs

      val newOwn: Opt[InnerSymbol] = defn.owner.map: o =>
        mapping.get(o) match
          case Some(inner: InnerSymbol) => inner
          case _ => o

      def freshenParamList(pl: ParamList): ParamList =
        def handleParam(p: Param) =
          val ns = new VarSymbol(p.sym.id)
          assert(!mapping.isDefinedAt(p.sym))
          mapping(p.sym) = ns
          hd += p.sym
          Param(p.flags, ns, p.sign, p.modulefulness)
        ParamList(pl.flags, pl.params.map(handleParam), pl.restParam.map(handleParam))
      val newParamsOpt = defn.paramsOpt.map(freshenParamList)
      val newAuxParams = defn.auxParams.map(freshenParamList)

      val newPrivateFields = freshenPrivateFields(defn.privateFields, newIsym)
      val newPublicFields = freshenPublicFields(defn.publicFields, newIsym)
      val newMethods = freshenMethods(defn.methods, oldIsym, newIsym)

      val newPreCtor = applyFunBodyLikeBlock(defn.preCtor)
      val newCtor = applyFunBodyLikeBlock(defn.ctor)
      val newMod = defn.companion.map(applyObjBody)

      def buildResult(newParentPath: Opt[Path]): Block =
        val newDefn = ClsLikeDefn(newOwn, newIsym, newSym, newCtorSym, defn.k,
          newParamsOpt, newAuxParams, newParentPath, newMethods,
          newPrivateFields, newPublicFields, newPreCtor, newCtor, newMod, defn.bufferable)(defn.configOverride, defn.annotations)
        if newlyCreatedSym then
          Scoped(Set.single(newSym), k(newDefn))
        else
          k(newDefn)

      defn.parentPath match
        case Some(pp) => applyPath(pp): pp2 =>
          buildResult(if pp2 is pp then defn.parentPath else Some(pp2))
        case None => buildResult(None)
  
  override def applyPath(p: Path)(k: Path => Block): Block = p match
    case p @ Select(qual, name) =>
      applyPath(qual): qual2 =>
        val sym2 = p.symbol.map: s =>
          mapping.get(s) match
            case Some(ds: DefinitionSymbol[?]) => ds
            case _ => s
        k(if (qual2 is qual) && (sym2 is p.symbol) then p else Select(qual2, name)(sym2).withLocOf(p))
    case _ => super.applyPath(p)(k)

  override def applyValue(v: Value)(k: Value => Block): Block = v match
    case Value.Ref(l, x) =>
      mapping.get(l) match
        case None => super.applyValue(v)(k)
        case Some(newBms: BlockMemberSymbol) =>
          val newDisamb = x match
            case Some(oldDisamb) =>
              mapping.get(oldDisamb) match
                case Some(nd: DefinitionSymbol[?]) => Some(nd)
                case _ => newBms.tsym.orElse(x)
            case None => newBms.tsym
          k(Value.Ref(newBms, newDisamb))
        case Some(newSym) => k(Value.Ref(newSym, N))
    case Value.This(sym) =>
      mapping.get(sym) match
        case Some(inner: InnerSymbol) => k(Value.This(inner).withLocOf(v))
        case _ => super.applyValue(v)(k)
    case _ => super.applyValue(v)(k)
  
  private def freshenPrivateFields(
    fields: Ls[TermSymbol], ownerIsym: InnerSymbol
  ): Ls[TermSymbol] = fields.map: ts =>
    assert(!mapping.isDefinedAt(ts))
    val nts = new TermSymbol(ts.k, S(ownerIsym), ts.id)
    mapping(ts) = nts
    toRemoveSymbols.head += ts
    nts

  private def freshenPublicFields(
    fields: Ls[BlockMemberSymbol -> TermSymbol], ownerIsym: InnerSymbol
  ): Ls[BlockMemberSymbol -> TermSymbol] = fields.map:
    case (bms, ts) =>
      assert(!mapping.isDefinedAt(bms))
      assert(!mapping.isDefinedAt(ts))
      val nbms = new BlockMemberSymbol(bms.nme, Nil, bms.nameIsMeaningful)
      val nts = new TermSymbol(ts.k, S(ownerIsym), ts.id)
      nbms.tsym = S(nts)
      mapping(bms) = nbms
      mapping(ts) = nts
      toRemoveSymbols.head.addAll(Seq(bms, ts))
      nbms -> nts

  private def freshenMethods(
    methods: Ls[FunDefn], oldIsym: InnerSymbol, newIsym: InnerSymbol
  ): Ls[FunDefn] =
    val methodsAndNewSyms = methods.map: m =>
      assert(m.owner.contains(oldIsym), s"method owner mismatch: ${m.owner} vs S($oldIsym)")
      assert(!mapping.isDefinedAt(m.sym))
      assert(!mapping.isDefinedAt(m.dSym))
      val newMsym = new BlockMemberSymbol(m.sym.nme, Nil, m.sym.nameIsMeaningful)
      val newDsym = new TermSymbol(m.dSym.k, S(newIsym), m.dSym.id)
      newMsym.tsym = S(newDsym)
      mapping(m.sym) = newMsym
      mapping(m.dSym) = newDsym
      toRemoveSymbols.head.addAll(Seq(m.sym, m.dSym))
      (m, newMsym, newDsym)
    methodsAndNewSyms.map: (m, newMsym, newDsym) =>
      val methodParamOlds = MutSet.empty[VarSymbol]
      val newParams = m.params.map: pl =>
        def handleParam(p: Param) =
          val ns = new VarSymbol(p.sym.id)
          assert(!mapping.isDefinedAt(p.sym))
          mapping(p.sym) = ns
          methodParamOlds += p.sym
          Param(p.flags, ns, p.sign, p.modulefulness)
        ParamList(pl.flags, pl.params.map(handleParam), pl.restParam.map(handleParam))
      val newBody = applyFunBodyLikeBlock(m.body)
      methodParamOlds.foreach(mapping.remove)
      FunDefn(S(newIsym), newMsym, newDsym, newParams, newBody)(m.configOverride, m.annotations)
  
  override def applyObjBody(defn: ClsLikeBody): ClsLikeBody =
    val hd = toRemoveSymbols.head
    val oldIsym = defn.isym
    assert(!mapping.isDefinedAt(oldIsym), s"companion isym already in mapping: $oldIsym")
    val newIsym: DefinitionSymbol[? <: ModuleOrObjectDef] & InnerSymbol = oldIsym match
      case m: ModuleOrObjectSymbol => new ModuleOrObjectSymbol(m.tree, m.id)
      case _ => lastWords(s"unexpected companion isym kind: $oldIsym")
    mapping(oldIsym) = newIsym
    hd += oldIsym

    val newPrivateFields = freshenPrivateFields(defn.privateFields, newIsym)
    val newPublicFields = freshenPublicFields(defn.publicFields, newIsym)
    val newMethods = freshenMethods(defn.methods, oldIsym, newIsym)
    val newCtor = applyFunBodyLikeBlock(defn.ctor)

    ClsLikeBody(newIsym, newMethods, newPrivateFields, newPublicFields, newCtor, defn.annotations)
