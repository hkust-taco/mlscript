package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*



type PatternShapePublisher = Publisher[PatternShape]
type PatternShapeHost = Host[PatternShape]


sealed abstract class PatternShape extends ValueKey:
  def showDbg(using DebugPrinter): Str


final case class CtorPatternShape(
    cls: ClassDef | ModuleOrObjectDef,
    fs: Ls[BlockMemberSymbol -> Pattern],
    src: Pattern.Constructor,
    resSym: FlowSymbol,
    marks: Ls[Marks],
) extends PatternShape:
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), System.identityHashCode(cls), fs.hashCode,
    System.identityHashCode(src), System.identityHashCode(resSym), marks.hashCode)
  protected def sameValue(other: ValueKey): Bool = other match
    case that: CtorPatternShape =>
      (cls eq that.cls) && fs == that.fs && (src eq that.src) && (resSym eq that.resSym) && marks == that.marks
    case _ => false
  def showDbg(using DebugPrinter): Str = src.showDbg
