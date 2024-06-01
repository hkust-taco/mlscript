package hkmc2
package typing

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import semantics.*


// class FlowPoint(val sym: VarSymbol):
//   override def equals(x: Any): Bool = x match
//     case that: FlowPoint => sym === that.sym
//     case _ => false
//   override def hashCode: Int = sym.hashCode

enum Producer:
  case Flow(sym: FlowSymbol)
  case Fun(lhs: Consumer, rhs: Producer, captures: Ls[(Producer, Consumer)])
  case Ctor(sym: CtorSymbol, args: List[Producer])
  case Lab(base: Producer, label: Label)
object Producer:
  def exitIf(p: Producer, sym: Symbol, id: Int, rc: Int) =
    if rc === 1 then p
    else Lab(p, Label.Exit(sym, id, false))
  def enterIf(p: Producer, sym: Symbol, id: Int, rc: Int) =
    if rc === 1 then p
    else Lab(p, Label.Enter(sym, id, false))
enum Consumer:
  // case Flow(fp: FlowPoint)
  case Flow(sym: FlowSymbol)
  case Fun(lhs: Producer, rhs: Consumer)
  case Ctor(sym: CtorSymbol, args: List[Consumer])
  case Lab(base: Consumer, label: Label)

enum Label:
  case Enter(sym: Symbol, id: Int, repeated: Bool)
  case Exit(sym: Symbol, id: Int, repeated: Bool)
  case Dup(sym: Symbol, id: Int, repeated: Bool)

enum Path:
  case Plain(labels: List[Label])
  case Repeated(rep: List[Label], rest: Path)
  def ::(l: Label): Path = this match
    case Plain(ls) => Plain(l :: ls)
    case Repeated(rep, rest) =>
      // Repeated(l :: rep, rest)
      ???

case class ConcreteProd(path: Path, ctor: Producer.Ctor | Producer.Fun)

