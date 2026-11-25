package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import sourcecode.Line

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.Message.MessageContext

import semantics.*
import semantics.Elaborator.State


/** Checks two invariants of the IR:
  *  - each symbol is bound at most once (this simplifies various analyses and transformations);
  *  - each definition is its symbol's current `irDefn`. Code that works on the IR reads a definition's signature
  *    through its symbol (see `TermSymbol.irErasure`), and cross-unit inlining reads its body; a pass that builds a
  *    definition and then discards it leaves `irDefn` pointing at the discarded one.
  */
class BlockChecker()(using DebugPrinter, State, Raise) extends BlockTraverser:
  
  val definedSyms = MutSet.empty[ScopedSymbol]
  
  private def checkSymbol(sym: ScopedSymbol, info: => Any): Unit =
    if !definedSyms.add(sym) then
      raise:
        InternalError(
          msg"[BlockChecker] Invalid IR: symbol ${sym.showAsPlain} is bound more than once" -> sym.toLoc
            :: Nil,
          extraInfo = S(info)
        )
  
  override def applyBlock(b: Block): Unit =
    b match
    case Scoped(syms, body) =>
      syms.foreach(checkSymbol(_, b))
    case _ => ()
    super.applyBlock(b)
  
  override def applyParamList(pl: LoweredParamList): Unit =
    pl.paramSyms.foreach(checkSymbol(_, pl))
    super.applyParamList(pl)
  
  private def checkIrDefn(sym: DefinitionSymbol[?], defn: Defn): Unit =
    if !sym.irDefn.exists(_ is defn) then raise:
      InternalError(
        msg"[BlockChecker] Invalid IR: the recorded IR definition of ${sym.showAsPlain} is not the one in the program" ->
          sym.toLoc :: Nil,
        extraInfo = S(defn)
      )
  
  override def applyFunDefn(fun: FunDefn): Unit =
    checkIrDefn(fun.dSym, fun)
    super.applyFunDefn(fun)
  
  override def applyClsLikeDefn(defn: ClsLikeDefn): Unit =
    checkIrDefn(defn.isym, defn)
    super.applyClsLikeDefn(defn)
  
  override def applyValDefn(defn: ValDefn): Unit =
    checkIrDefn(defn.tsym, defn)
    super.applyValDefn(defn)
  
end BlockChecker

object BlockChecker:
  
  /** Checks that `optimized` defines each definition of `source` that other compilation units can refer to under its
    * `source` symbol. Those are the non-private top-level definitions, and the non-private members of the classes and
    * modules among them.
    *
    * Other compilation units, and later worksheet blocks, are lowered against `source`'s symbols. Code generation that
    * links definitions by symbol needs a definition to keep its symbol, and so does cross-unit inlining, which reads a
    * symbol's `irDefn`. A pass may delete such a definition, or keep it and add other definitions, but must not define
    * its binding under a new symbol in its place.
    */
  def checkDefinitionIdentity(source: Program, optimized: Program)(using Raise): Unit =
    val visible = collection.mutable.ArrayBuffer.empty[BlockMemberSymbol -> DefinitionSymbol[?]]
    def addFun(fun: FunDefn): Unit =
      if fun.visibility isnt Visibility.Private then visible += fun.sym -> fun.dSym
    new BlockTraverserShallow:
      override def applyDefn(defn: Defn): Unit = defn match
        case fun: FunDefn => addFun(fun)
        case cls: ClsLikeDefn if cls.visibility isnt Visibility.Private =>
          visible += cls.sym -> cls.isym
          cls.methods.foreach(addFun)
          cls.companion.foreach: body =>
            body.methods.foreach(addFun)
            // A module's members can themselves be classes and modules.
            applyBlock(body.ctor)
        case _ => super.applyDefn(defn)
    .applyBlock(source.main)
    
    val defined = MutSet.empty[DefinitionSymbol[?]]
    val definedBindings = MutSet.empty[BlockMemberSymbol]
    def define(sym: BlockMemberSymbol, defnSym: DefinitionSymbol[?]): Unit =
      definedBindings += sym
      defined += defnSym
    new BlockTraverser:
      override def applyFunDefn(fun: FunDefn): Unit =
        define(fun.sym, fun.dSym)
        super.applyFunDefn(fun)
      override def applyClsLikeDefn(cls: ClsLikeDefn): Unit =
        define(cls.sym, cls.isym)
        super.applyClsLikeDefn(cls)
    .applyBlock(optimized.main)
    
    visible.foreach: (sym, defnSym) =>
      if !defined(defnSym) && definedBindings(sym) then raise:
        InternalError(
          msg"[BlockChecker] Invalid IR: definition `${sym.nme}` is replaced by one with another symbol" -> sym.toLoc
            :: Nil,
          extraInfo = S(defnSym),
        )
  end checkDefinitionIdentity
  
end BlockChecker

