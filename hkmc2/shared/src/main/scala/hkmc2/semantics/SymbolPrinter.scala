package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.utils.*


class SymbolPrinter(val dbgScp: Scope) extends DebugPrinter:
  
  override def printPlain(v: Any): Str = v match
    case sym: Symbol =>
      sym.showFullName(using dbgScp, semantics.ShowCfg.internal, throw _)
    case _ => super.printPlain(v)
    
  def printSymbol(sym: Symbol)(using Raise, ShowCfg): Str =
    sym.showName(using dbgScp, summon)
  
end SymbolPrinter


