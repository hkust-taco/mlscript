package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import sourcecode.Line

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.Message.MessageContext

import semantics.*
import semantics.Elaborator.State


/** An invariant of the IR is that each symbol should be bound at most once
  * (this simplifies various analyses and transformations).
  * This class checks this invariant. */
class BlockChecker()(using DebugPrinter, State, Raise) extends BlockTraverser:
  
  val definedSyms = MutSet.empty[BoundSymbol]
  
  private def checkSymbol(sym: BoundSymbol, info: => Any): Unit =
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
  
  override def applyParamList(pl: ParamList): Unit =
    pl.paramSyms.foreach(checkSymbol(_, pl))
    super.applyParamList(pl)
  
end BlockChecker

