package hkmc2
package codegen

import utils.*


class Defunctionalization extends BlockTransformer(new SymbolSubst):
  override def applyBlock(b: Block): Block = b
