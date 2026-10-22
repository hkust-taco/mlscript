package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.utils.*


class SymbolPrinter(val dbgScp: Scope)(using owner: Elaborator.State) extends DebugPrinter(S(owner)):
  override protected def symbolName(sym: Symbol): Str =
    sym.showFullName(using dbgScp, ShowCfg.internal, throw _)
  
  def printSymbol(sym: Symbol)(using Raise, ShowCfg): Str =
    sym.showName(using dbgScp, summon)
  
end SymbolPrinter


