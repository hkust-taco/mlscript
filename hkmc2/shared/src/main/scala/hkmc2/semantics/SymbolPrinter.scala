package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.utils.*


class SymbolPrinter(
  val dbgScp: Scope,
  preprocess: Product => Product,
  postprocess: Product => Str,
)(using owner: Elaborator.State) extends DebugPrinter(false, S(owner),
    sym => sym.showFullName(using dbgScp, semantics.ShowCfg.internal, throw _),
    preprocess, postprocess):
  def this(dbgScp: Scope)(using Elaborator.State) = this(dbgScp, identity, _ => "")
  
  def printSymbol(sym: Symbol)(using Raise, ShowCfg): Str =
    sym.showName(using dbgScp, summon)
  
end SymbolPrinter


