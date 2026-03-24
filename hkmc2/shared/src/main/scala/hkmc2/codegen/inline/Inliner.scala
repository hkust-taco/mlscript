package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import semantics.Elaborator.State

object Inliner:

  // Reference to a function body can occur as a.f or f, this handles both cases.
  object TermSymbolPath:
    def unapply(p: Path) = p match
      case Value.Ref(l, S(ts: TermSymbol)) => S(ts)
      case s: Select => s.symbol match
        case S(ts: TermSymbol) => S(ts)
        case _ => N
      case _ => N
  
  def matchArgs(args: List[Arg], params: ParamList): Option[List[(Local, Result)]] =
    if args.exists(_.spread.isDefined) then
      // we require a precise match when any arg is a spread arg
      if params.restParam.isEmpty then return N
      if args.exists(_.spread.exists(!_.isEager)) then return N
      val pairs = args.zip(params.params.iterator.map((_, false)) ++ params.restParam.map((_, true)))
      if pairs.exists((arg, param) => arg.spread.isDefined =/= param._2) then return N
      S(pairs.map((arg, param) => (param._1.sym, arg.value)))
    else
      // otherwise arg list is a simple list, and
      // we can perform manual array instantiation if params contain a spread param
      if params.restParam.isEmpty then
        if args.size =/= params.params.size then return N
        S(args.zip(params.params).map((arg, param) => (param.sym, arg.value)))
      else
        if args.size < params.params.size then return N
        val (fixedArgs, restArgs) = args.splitAt(params.params.size)
        S(fixedArgs.zip(params.params).map((arg, param) => (param.sym, arg.value)) ++
          List((params.restParam.get.sym, Tuple(true, restArgs))))

import Inliner.*

object InlinerAnalyzer:
  case class InlinerFunInfo(
    defn: FunDefn,
    isMethod: Bool,
    isPrivate: Bool,
    retCnt: Int,
    private[InlinerAnalyzer] var useCount: Int,
    private[InlinerAnalyzer] var hasNakedRef: Bool,
  ):
    def canBeInlineEliminated =
      isPrivate && !isMethod && useCount <= 1 && !hasNakedRef
      // false

    def shouldBeInlined(newBlk: Block)(using Config.Inliner): Bool =
      // method requires the capturing of `this`, which is not supported currently.
      if isMethod then return false
      val threshold = summon[Config.Inliner].inlineThreshold
      newBlk.size <= threshold || canBeInlineEliminated

  type InlinerMap = Map[TermSymbol, InlinerFunInfo]

  case class FunLikeContext(
    var retCnt: Int,
  )

  class Traverser extends BlockTraverser:
    var map: InlinerMap = Map.empty
    val useCnt = mutable.Map.WithDefault(mutable.Map.empty[TermSymbol, Int], _ => 0)
    val usages = mutable.Map.WithDefault(mutable.Map.empty[TermSymbol, List[Call]], _ => Nil)
    val hasNakedRef = mutable.Map.WithDefault(mutable.Map.empty[TermSymbol, Bool], _ => false)
    var contextList: List[FunLikeContext] = FunLikeContext(0) :: Nil

    def isNested = contextList.tail =/= Nil

    def currentContext = contextList.head
    
    def nested(thunk: => Unit) =
      contextList = FunLikeContext(0) :: contextList
      thunk
      val res = contextList.head
      contextList = contextList.tail
      res

    def addFunctionAndApplyBody(f: FunDefn, isMethod: Bool) =
      val r = nested:
        applyBlock(f.body)
      map = map + (f.dSym -> InlinerFunInfo(f, isMethod, isNested, r.retCnt, 0, false))
    
    override def applyDefn(defn: Defn): Unit = defn match
      case f: FunDefn =>
        addFunctionAndApplyBody(f, false)
      case c: ClsLikeDefn =>
        c.methods.foreach: f =>
          addFunctionAndApplyBody(f, true)
        nested:
          applySubBlock(c.preCtor)
          applySubBlock(c.ctor)
        c.companion.foreach: m =>
          m.methods.foreach: f =>
            addFunctionAndApplyBody(f, true)
          applySubBlock(m.ctor)
      case _ => super.applyDefn(defn)

    override def applyResult(r: Result): Unit = r match
      case c @ Call(TermSymbolPath(ts), args) =>
        useCnt(ts) += 1
        usages(ts) ::= c
        args.foreach(applyArg)
      case _ => super.applyResult(r)
    
    override def applySymbol(sym: Symbol): Unit =
      sym.asTrm.foreach: ts =>
        useCnt(ts) += 1
        hasNakedRef(ts) = true

    override def applyBlock(b: Block): Unit = b match
      case Return(r, false) =>
        currentContext.retCnt += 1
        super.applyBlock(b)
      case _ => super.applyBlock(b)
    
    def analyze(blk: Block): InlinerMap =
      applyBlock(blk)
      map.foreach: (sym, info) =>
        info.useCount = useCnt(sym)
      usages.foreach: (sym, calls) =>
        calls.foreach: call =>
          if map.contains(sym) then
          map(sym).hasNakedRef = map(sym).hasNakedRef ||
            map(sym).defn.params.sizeCompare(1) =/= 0 || matchArgs(call.args, map(sym).defn.params.head).isEmpty
      map

  def walk(blk: Block): InlinerMap = Traverser().analyze(blk)

import InlinerAnalyzer.InlinerMap


object InlinerReplacer:

  class Copier(doRename: Bool, k: Option[Result => Block])(using State):
    val resSym = TempSymbol(N, "inlinedVal")
    val lblSym = LabelSymbol(N, "inlinedLbl")

    object SubstMap extends SymbolSubst:
      val needsSub = mutable.Set.empty[Symbol]
      val subMap = mutable.Map.empty[Symbol, Symbol]
  
      def addRenamedSymbol(sym: Symbol) =
        assert(!subMap.contains(sym), s"Symbol ${sym} is already renamed.")
        if doRename then
          needsSub += sym
      
      def doSymbolSubst(orig: Symbol, newSym: => Symbol): Symbol =
        if needsSub(orig) then
          subMap.getOrElseUpdate(orig, newSym)
        else
          orig

      override def mapBlockMemberSym(s: BlockMemberSymbol): BlockMemberSymbol =
        doSymbolSubst(s, BlockMemberSymbol(s.nme, s.trees, s.nameIsMeaningful)).asInstanceOf
      override def mapFlowSym(s: FlowSymbol): FlowSymbol =
        doSymbolSubst(s, FlowSymbol(s.nme)).asInstanceOf
      override def mapTempSym(s: TempSymbol): TempSymbol =
        doSymbolSubst(s, TempSymbol(s.trm, s.nme)).asInstanceOf
      override def mapVarSym(s: VarSymbol): VarSymbol =
        doSymbolSubst(s, VarSymbol(s.id)).asInstanceOf
      override def mapInstSym(s: InstSymbol): InstSymbol =
        doSymbolSubst(s, InstSymbol(s.origin)).asInstanceOf
      override def mapBuiltInSym(s: BuiltinSymbol): BuiltinSymbol =
        // We shouldn't define any builtin so this doesn't make sense.
        doSymbolSubst(s, ???).asInstanceOf
      override def mapTermSym(s: TermSymbol): TermSymbol =
        doSymbolSubst(s, TermSymbol(s.k, s.owner, s.id)).asInstanceOf
      override def mapCtorSym(s: CtorSymbol): CtorSymbol =
        doSymbolSubst(s, ???).asInstanceOf
      override def mapClsSym(s: ClassSymbol): ClassSymbol =
        doSymbolSubst(s, ClassSymbol(s.tree, s.id)).asInstanceOf
      override def mapModuleSym(s: ModuleOrObjectSymbol): ModuleOrObjectSymbol =
        doSymbolSubst(s, ModuleOrObjectSymbol(s.tree, s.id)).asInstanceOf
      override def mapTypeAliasSym(s: TypeAliasSymbol): TypeAliasSymbol =
        doSymbolSubst(s, TypeAliasSymbol(s.id)).asInstanceOf
      override def mapPatSym(s: PatternSymbol): PatternSymbol =
        doSymbolSubst(s, PatternSymbol(s.id, s.params, s.body)).asInstanceOf
      override def mapTopLevelSym(s: TopLevelSymbol): TopLevelSymbol =
        doSymbolSubst(s, TopLevelSymbol(s.nme)).asInstanceOf
      override def mapErrorSym(s: ErrorSymbol): ErrorSymbol =
        doSymbolSubst(s, ErrorSymbol(s.nme, s.tree)).asInstanceOf
      override def mapLabelSym(s: LabelSymbol): LabelSymbol =
        doSymbolSubst(s, LabelSymbol(s.trm, s.nme)).asInstanceOf

    object Copier extends BlockTransformer(SubstMap):
      var currentlyNested = false

      override def applyFunBodyLikeBlock(b: Block): Block =
        val saved = currentlyNested
        currentlyNested = true
        val res = super.applyFunBodyLikeBlock(b)
        currentlyNested = saved
        res

      override def applyBlock(b: Block): Block = b match
        case Return(res, false) if !currentlyNested =>
          applyResult(res): r2 =>
            k.fold(Assign(resSym, r2, Break(lblSym)))(k => k(r2))
        case _ => super.applyBlock(b)

      override def applyScopedBlock(b: Block): Block = b match
        case Scoped(syms, body) if !currentlyNested =>
          syms.foreach(SubstMap.addRenamedSymbol)
          Scoped(syms.map(_.subst), applySubBlock(body))
        case _ => super.applyScopedBlock(b)

    def applyBlock(blk: Block) =
      val newBlk = Copier.applyBlock(blk)
      (k.fold(Label(lblSym, false, newBlk, _))(_ => _ => newBlk), resSym)

  class Transformer(m: InlinerMap)(using Config.Inliner, State, TL) extends BlockTransformer(SymbolSubst()):

    // The call graph may be cyclic, in which case we break the infinite loop using this map by
    // assuring that the block corresponding to a term symbol may only be transformed once.
    // This map also allows the function block to be optimized on first use before its declaration.
    // Key not in map -> not yet analyzed
    // Key in map but value is None -> the optimized body is being computed
    // Key in map with value -> the function is optimized
    val newFunctionBody = mutable.Map.empty[TermSymbol, Option[Block]]

    override def applyBlock(blk: Block) = blk match
      case Define(defn: FunDefn, rest) if m(defn.dSym).canBeInlineEliminated =>
        applyBlock(rest)
      case _ => super.applyBlock(blk)
    
    override def applyFunDefn(fun: FunDefn): FunDefn =
      newFunctionBody.get(fun.dSym) match
        case N =>
          newFunctionBody(fun.dSym) = N
          val newBdy = applyBlock(fun.body)
          newFunctionBody(fun.dSym) = S(newBdy)
          FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, newBdy)(fun.forceTailRec)
        case S(N) =>
          // The expansion of the function body itself reaches its own definition, which is impossible
          lastWords("Function body contains its own definition.")
        case S(S(blk)) => FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, blk)(fun.forceTailRec)
    
    override def applyResult(r: Result)(k: Result => Block): Block = r match
      case Call(TermSymbolPath(ts), args) if m.contains(ts) =>
        newFunctionBody.get(ts)
        .getOrElse:
          newFunctionBody(ts) = N
          val newBdy = applyBlock(m(ts).defn.body)
          newFunctionBody(ts) = S(newBdy)
          S(newBdy)
        .fold(super.applyResult(r)(k)): blk =>
          val info = m(ts)
          if !info.shouldBeInlined(blk) || info.defn.params.size =/= 1 then super.applyResult(r)(k)
          else
            val matchedArgs = matchArgs(args, info.defn.params.head)
            matchedArgs match
            case N => super.applyResult(r)(k)
            case S(matchedArgs) =>
              // Depends on whether the source is eliminated, we can reuse symbol from the original block.
              val isSimple = info.retCnt === 1
              val copier = Copier(doRename = !info.canBeInlineEliminated, k = k.optionIf(isSimple))
              def go(acc: Block => Block, args: List[(Local, Result)]): Block =
                args match
                case Nil =>
                  val (newBlk, resSym) = copier.applyBlock(blk)
                  if isSimple then
                    // the continuation is already baked into newBlk via the copier
                    acc(newBlk(End()))
                  else
                    acc(Scoped(Set.single(copier.resSym), newBlk(k(Value.Ref(resSym)))))
                case (sym, value) :: rest =>
                  copier.SubstMap.addRenamedSymbol(sym)
                  go(acc.assignScoped(sym.subst(using copier.SubstMap), value), rest)
              go(blockBuilder, matchedArgs)
      case _ => super.applyResult(r)(k)

  def replace(m: InlinerMap, blk: Block)(using Config.Inliner, State, TL): Block =
    Transformer(m).applyBlock(blk)

class Inliner(using Config.Inliner, State, TL):
  def applyBlock(blk: Block) =
    val m = InlinerAnalyzer.walk(blk)
    InlinerReplacer.replace(m, blk)
