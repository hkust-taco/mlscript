package hkmc2
package codegen

import utils.*
import hkmc2.Message.MessageContext

class Instrumentation(using Raise) extends BlockTransformer(new SymbolSubst()):
  def transform(prgm: Program) = Program(prgm.imports, applyBlock(prgm.main))

  override def applyDefn(d: Defn)(k: Defn => Block): Block = d match 
    case defn: ClsLikeDefn =>
      if defn.sym.defn.exists(_.hasStagedModifier.isDefined) && defn.companion.isDefined
      then raise(WarningReport(msg"`staged` keyword doesn't do anything currently." -> defn.sym.toLoc :: Nil))
      super.applyDefn(defn)(k)
    case b => super.applyDefn(b)(k)
