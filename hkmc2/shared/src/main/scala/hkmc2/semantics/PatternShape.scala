package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*



type PatternShapePublisher = Publisher[PatternShape]
type PatternShapeHost = Host[PatternShape]


sealed abstract class PatternShape:
  def showDbg(using DebugPrinter): Str


// TODO: not a case class...?
case class CtorPatternShape(
    cls: ClassDef | ModuleOrObjectDef,
    fs: Ls[BlockMemberSymbol -> Pattern],
    src: Pattern.Constructor,
    resSym: FlowSymbol,
    marks: Ls[Marks],
) extends PatternShape:
  def showDbg(using DebugPrinter): Str = src.showDbg


