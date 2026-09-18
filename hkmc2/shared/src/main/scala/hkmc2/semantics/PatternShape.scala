package hkmc2
package semantics

import scala.collection.mutable.{Buffer, Set as MutSet, LinkedHashSet}

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.utils.Scope
import hkmc2.utils.Scope.scope
import hkmc2.document.*
import hkmc2.document.Document.*

import Elaborator.State
import hkmc2.typing.Type
import hkmc2.semantics.Elaborator.{Ctx, ctx}
import hkmc2.Message.MessageContext
import hkmc2.semantics.flow.{SelectionTarget, AppTarget}



type PatternShapePublisher = Publisher[PatternShape]
type PatternShapeHost = Host[PatternShape]


sealed abstract class PatternShape:
  def showDbg(using DebugPrinter): Str


// TODO: not a case class...?
case class CtorPatternShape(
    cls: ClassDef,
    fs: Ls[BlockMemberSymbol -> Pattern],
    src: Pattern.Constructor,
    resSym: FlowSymbol,
) extends PatternShape:
  def showDbg(using DebugPrinter): Str = src.showDbg


case class AliasPatternShape(
    sym: VarSymbol,
    src: Pattern.Alias,
) extends PatternShape:
  def showDbg(using DebugPrinter): Str = src.showDbg


