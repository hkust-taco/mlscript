package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer}

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import semantics.Elaborator.State

class SymbolRefresherWalker(mapping: MutMap[Symbol, Symbol])(using State) extends BlockTraverser:

  private def assertUpdate[T <: Symbol](k: T, v: T) =
    assert(!mapping.isDefinedAt(k), s"already defined: $k")
    mapping(k) = v
  
  private def refreshTempSymbol(s: TempSymbol) =
    assertUpdate(s, new TempSymbol(s.trm, s.nme))

  private def refreshVarSymbol(s: VarSymbol) =
    assertUpdate(s, new VarSymbol(s.id))
  
  private def refreshBlockMemberSymbol(s: BlockMemberSymbol) =
    assertUpdate(s, new BlockMemberSymbol(s.nme, s.trees, s.nameIsMeaningful))

  private def refreshLabelSymbol(s: LabelSymbol) =
    assertUpdate(s, new LabelSymbol(s.trm, s.nme))

  private def refreshTermSymbol(s: TermSymbol) =
    // Inner symbol (if present) must be traversed at this point.
    assertUpdate(s, new TermSymbol(s.k, s.owner.map(o => mapping.getOrElse(o, o).asInstanceOf[InnerSymbol]), s.id))

  private def refreshClassSymbol(s: ClassSymbol) =
    val ns = new ClassSymbol(s.tree, s.id)
    assertUpdate(s, ns)
    // defn is relied by JSBuilder to identify whether a class should be lifted
    ns.defn = s.defn

  private def refreshModuleOrObjectSymbol(s: ModuleOrObjectSymbol) =
    assertUpdate(s, new ModuleOrObjectSymbol(s.tree, s.id))

  private def refreshPatternSymbol(s: PatternSymbol) =
    assertUpdate(s, new PatternSymbol(s.id, s.params, s.body))

  private def refreshTopLevelSymbol(s: TopLevelSymbol) =
    assertUpdate(s, new TopLevelSymbol(s.nme))

  private def refreshClassCtorSymbol(s: ClassCtorSymbol) =
    assertUpdate(s, new ClassCtorSymbol(s.k, S(mapping.getOrElse(s.owner.value, s.owner.value).asInstanceOf[ClassSymbol]), s.id))

  private def refreshParamList(pl: ParamList) =
    for
      p <- pl.restParam ++: pl.params
    do
      refreshVarSymbol(p.sym)

  override def applyBlock(b: Block) = b match
    case Scoped(syms, body) =>
      for s <- syms.toList.sortBy(_.uid) do
        s match
          case s: TempSymbol => refreshTempSymbol(s)
          case s: VarSymbol => refreshVarSymbol(s)
          case s: BlockMemberSymbol => refreshBlockMemberSymbol(s)
      applyBlock(body)
    case Label(label, loop, body, rest) =>
      refreshLabelSymbol(label)
      applyBlock(body)
      applyBlock(rest)
    case _ => super.applyBlock(b)
  
  override def applyFunDefn(fun: FunDefn): Unit =
    val FunDefn(owner, sym, dSym, params, body) = fun
    assert(mapping.isDefinedAt(sym), s"BlockMemberSymbol ${sym} for FunDefn is a free variable for this block")
    refreshTermSymbol(dSym)
    params.foreach(refreshParamList)
    applyBlock(body)
  
  override def applyValDefn(defn: ValDefn): Unit =
    val ValDefn(tsym, sym, result) = defn
    assert(mapping.isDefinedAt(sym), s"BlockMemberSymbol ${sym} for ValDefn is a free variable for this block")
    refreshTermSymbol(tsym)
    applyResult(result)
  
  override def applyClsLikeDefn(defn: ClsLikeDefn): Unit =
    val ClsLikeDefn(
      owner, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath,
      methods, privateFields, publicFields, preCtor, ctor, companion,
      bufferable) = defn
    assert(mapping.isDefinedAt(sym), s"BlockMemberSymbol ${sym} for ClsLikeDefn is a free variable for this block")
    isym match
      case s: ClassSymbol => refreshClassSymbol(s)
      case s: ModuleOrObjectSymbol => refreshModuleOrObjectSymbol(s)
      case s: PatternSymbol => refreshPatternSymbol(s)
      case s: TopLevelSymbol => refreshTopLevelSymbol(s)
    ctorSym.foreach(refreshClassCtorSymbol)
    paramsOpt.foreach(refreshParamList)
    auxParams.foreach(refreshParamList)
    methods.foreach: mtd =>
      // For methods, the BlockMemberSymbol is owned by the class itself
      refreshBlockMemberSymbol(mtd.sym)
      applyFunDefn(mtd)
    privateFields.foreach(refreshTermSymbol)
    publicFields.foreach: p =>
      refreshBlockMemberSymbol(p._1)
      // For public fields, we have ValDefn for defining the variable
      // refreshTermSymbol(p._2)
    applyBlock(preCtor)
    applyBlock(ctor)
    companion.foreach(applyClsLikeBody)

  def applyClsLikeBody(b: ClsLikeBody): Unit =
    val ClsLikeBody(
      isym, methods, privateFields, publicFields, ctor, annotations
    ) = b
    isym match
      case s: ModuleOrObjectSymbol => refreshModuleOrObjectSymbol(s)
      case s: TopLevelSymbol => refreshTopLevelSymbol(s)
    methods.foreach: mtd =>
      // For methods, the BlockMemberSymbol is owned by the class itself
      refreshBlockMemberSymbol(mtd.sym)
      applyFunDefn(mtd)
    privateFields.foreach(refreshTermSymbol)
    publicFields.foreach: p =>
      refreshBlockMemberSymbol(p._1)
      // For public fields, we have ValDefn for defining the variable
      // refreshTermSymbol(p._2)
    applyBlock(ctor)

object SymbolRefresher:
  
  def initSymbolSubst(m: collection.Map[Symbol, Symbol]) =
    new SymbolSubst:
      override def mapBlockMemberSym(s: BlockMemberSymbol): BlockMemberSymbol = m.getOrElse(s, s).asInstanceOf[BlockMemberSymbol]
      override def mapTempSym(s: TempSymbol): TempSymbol = m.getOrElse(s, s).asInstanceOf[TempSymbol]
      override def mapVarSym(s: VarSymbol): VarSymbol = m.getOrElse(s, s).asInstanceOf[VarSymbol]
      override def mapTermSym(s: TermSymbol): TermSymbol = m.getOrElse(s, s).asInstanceOf[TermSymbol]
      override def mapClassCtorSym(s: ClassCtorSymbol): ClassCtorSymbol = m.getOrElse(s, s).asInstanceOf[ClassCtorSymbol]
      override def mapClsSym(s: ClassSymbol): ClassSymbol = m.getOrElse(s, s).asInstanceOf[ClassSymbol]
      override def mapModuleSym(s: ModuleOrObjectSymbol): ModuleOrObjectSymbol = m.getOrElse(s, s).asInstanceOf[ModuleOrObjectSymbol]
      override def mapPatSym(s: PatternSymbol): PatternSymbol = m.getOrElse(s, s).asInstanceOf[PatternSymbol]
      override def mapTopLevelSym(s: TopLevelSymbol): TopLevelSymbol = m.getOrElse(s, s).asInstanceOf[TopLevelSymbol]
      override def mapLabelSym(s: LabelSymbol): LabelSymbol = m.getOrElse(s, s).asInstanceOf[LabelSymbol]

// An internal class so that the actual map can be used
private class SymbolRefresherInternal(m: MutMap[Symbol, Symbol])(using State) extends BlockTransformer(SymbolRefresher.initSymbolSubst(m)):
  // We have a pretty weird setup here, where we store a mutable state inside the SymbolRefresher
  // We must initialize the SymbolRefresher by walking before applyBlock
  def apply(b: Block) =
    SymbolRefresherWalker(m).applyBlock(b)
    applyBlock(b)

  // Although the types created during walking can always be symbol substituted, the user may pass in extra symbol that map across different types
  override def applySimpleSymbol(s: SimpleSymbol): SimpleSymbol = m.getOrElse(s, s).asInstanceOf[SimpleSymbol]

  override def applyImportSymbol(s: ImportSymbol): ImportSymbol = m.getOrElse(s, s).asInstanceOf[ImportSymbol]
  
  override def applyAssignLhs(s: Assignable): Assignable = s match
    case NoSymbol => NoSymbol
    case s: LocalVarSymbol => m.getOrElse(s, s).asInstanceOf[LocalVarSymbol]
  
class SymbolRefresher(m: Map[Symbol, Symbol])(using State) extends SymbolRefresherInternal(MutMap.from(m))
