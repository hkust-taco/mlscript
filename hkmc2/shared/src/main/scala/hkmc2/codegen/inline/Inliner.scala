package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*

import scala.collection.mutable

object Inliner:
  object TermSymbolPath:
    def unapply(p: Path) = p match
      case Value.Ref(l, S(ts: TermSymbol)) => S(ts)
      case s: Select => s.symbol match
        case S(ts: TermSymbol) => S(ts)
        case _ => N
      case _ => N

import Inliner.*

object InlinerAnalyzer:
  case class InlinerFunInfo(
    defn: FunDefn,
    isMethod: Bool,
    isPrivate: Bool,
    private[InlinerAnalyzer] var useCount: Int,
    private[InlinerAnalyzer] var hasNakedRef: Bool,
  ):
    def canBeInlineEliminated =
      isPrivate && !isMethod && useCount <= 1 && !hasNakedRef

    def shouldBeInlined(newBlk: Block)(using Config.Inliner) =
      val threshold = summon[Config.Inliner].inlineThreshold
      newBlk.size <= threshold || canBeInlineEliminated

  type InlinerMap = Map[TermSymbol, InlinerFunInfo]

  class Traverser extends BlockTraverser:
    var map: InlinerMap = Map.empty
    val useCnt = mutable.Map.WithDefault(mutable.Map.empty[TermSymbol, Int], _ => 0)
    val hasNakedRef = mutable.Map.WithDefault(mutable.Map.empty[TermSymbol, Bool], _ => false)
    var isNested = false
    
    def nested(thunk: => Unit) =
      val saved = isNested
      isNested = true
      thunk
      isNested = saved

    def addFunctionAndApplyBody(f: FunDefn, isMethod: Bool) =
      map = map + (f.dSym -> InlinerFunInfo(f, isMethod, !isNested, 0, false))
      nested:
        applyBlock(f.body)
    
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
          nested:
            applySubBlock(m.ctor)
      case _ => super.applyDefn(defn)

    override def applyResult(r: Result): Unit = r match
      case c @ Call(TermSymbolPath(ts), args) =>
        useCnt(ts) += 1
        args.foreach(applyArg)
      case _ => super.applyResult(r)
    
    override def applySymbol(sym: Symbol): Unit =
      sym.asTrm.foreach: ts =>
        useCnt(ts) += 1
        hasNakedRef(ts) = true
    
    def analyze(blk: Block): InlinerMap =
      applyBlock(blk)
      map.foreach: (sym, info) =>
        info.useCount = useCnt(sym)
      map

  def walk(blk: Block): InlinerMap = Traverser().analyze(blk)

import InlinerAnalyzer.InlinerMap


object InlinerReplacer:

  object Copier extends BlockTransformer(SymbolSubst())

  class Transformer(m: InlinerMap)(using Config.Inliner) extends BlockTransformer(SymbolSubst()):

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
      case _ => applyBlock(blk)
    
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
          if !m(ts).shouldBeInlined(blk) then super.applyResult(r)(k)
          else
            // Depends on whether the source is eliminated, we can reuse the original block.
            // Otherwise, we need to change all the symbols defined within Scoped blocks.
            val copied = if m(ts).canBeInlineEliminated then blk else
              ???
      case _ => super.applyResult(r)(k)

  def replace(m: InlinerMap, blk: Block)(using Config.Inliner): Block =
    Transformer(m).applyBlock(blk)

class Inliner(using Config.Inliner, TL):
  def applyBlock(blk: Block) =
    val m = InlinerAnalyzer.walk(blk)
    InlinerReplacer.replace(m, blk)
