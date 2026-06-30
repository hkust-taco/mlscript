package hkmc2
package semantics
package flow

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.Scope
import hkmc2.utils.Scope.scope
import hkmc2.document.*

import typing.*
import semantics.*
import hkmc2.syntax.SpreadKind
import hkmc2.syntax.Tree.{UnitLit, Ident}
import hkmc2.semantics.AnySelTerm


case class Constraint(lhs: Producer, rhs: Consumer):
  def showDbg(using DebugPrinter): Str =
    s"${lhs.showDbg} <: ${rhs.showDbg}"


enum Producer:
  case Flow(sym: FlowSymbol)
  case Fun(lhs: Consumer, rhs: Producer, captures: Ls[(Producer, Consumer)])
  case Tup(elems: Ls[Opt[SpreadKind] -> Producer])
  case Ctor(sym: CtorSymbol, args: List[Producer])(val trm: Term) extends Producer, CtorImpl
  case LeadingDotSel(trm: Term.LeadingDotSel)
  case Typ(typ: Type)
  case Unknown(s: Statement) // `s` is just for error reporting/debugging purposes
  
  
  def toLoc: Opt[Loc] = this match
    case self: Ctor => self.trm.toLoc
    case self: LeadingDotSel => self.trm.toLoc
    case Unknown(t) => t.toLoc
    case _ => None
  
  
  def show(using Scope, Raise): Document = this match
    case Flow(sym) => scope.allocateOrGetName(sym)
    case Fun(lhs, rhs, caps) => doc"(${lhs.showAsParams} -> ${rhs.show})"
    case tup: Tup => Document.bracketed("[", "]")(showTupElems(tup))
    case Ctor(LitSymbol(UnitLit(false)), Nil) => "()"
    case Ctor(sym, args) => doc"${sym.nme}${args.map(_.showAsParams).mkDocument()}"
    case LeadingDotSel(trm) =>
      given ShowCfg = ShowCfg.internal
      doc"_?_.${trm.show}"
    case Typ(typ) => doc"type ${typ.show}"
    case Unknown(t) =>
      given ShowCfg = ShowCfg.internal
      doc"¿${t.show}?"
  
  def showAsParams(using Scope, Raise): Document = this match
    case tup: Tup => "(" :: showTupElems(tup) :: doc")"
    case _ => Document.text(s"...$show")
  
  private def showTupElems(tup: Tup)(using Scope, Raise): Document =
    tup.elems.map:
      case (None, c) => c.show
      case (Some(spd), c) => spd.str :: " " :: c.show
    .mkDocument(", ")
  
  
  def showDbg(using DebugPrinter): Str = this match
    case Flow(sym) => sym.showDbg
    case Fun(lhs, rhs, caps) => s"(${lhs.showDbgAsParams} -> ${rhs.showDbg})"
    case Ctor(LitSymbol(UnitLit(false)), Nil) => "()"
    case Ctor(sym, Nil) => sym.nme
    case Tup(args) => s"[${args.map((spd, a) => spd.fold("")(_.str) + a.showDbg).mkString(", ")}]"
    case Ctor(sym, args) => s"${sym.nme}${args.map(_.showDbgAsParams).mkString}"
    case sel @ LeadingDotSel(trm) => trm.showDbg
    case Typ(typ) => s"type ${typ.showDbg}"
    case Unknown(t) => s"¿${t.showDbg}?"
  
  def showDbgAsParams(using DebugPrinter): Str = this match
    case Tup(args) => args.map:
        case (None, c) => c.showDbg
        case (Some(spd), c) => s"${spd.str} ${c.showDbg}"
      .mkString("(", ", ", ")")
    case _ => s"(...$showDbg)"
  
  
end Producer


enum Consumer:
  case Flow(sym: FlowSymbol)
  case Fun(lhs: Producer, rhs: Consumer)
  case Tup(init: Ls[Consumer], rest: Opt[(SpreadKind, Consumer, Ls[Consumer])])
  case Ctor(sym: CtorSymbol, args: List[Consumer])
  case Sel(nme: Ident, res: Consumer)(val trm: AnySelTerm)
  case Typ(typ: Type)
  
  
  def show(using Scope, Raise): Document = this match
    case Flow(sym) => scope.allocateOrGetName(sym)
    case Fun(lhs, rhs) => doc"(${lhs.showAsParams} -> ${rhs.show})"
    case tup: Tup => Document.bracketed("[", "]")(showTupElems(tup))
    case Ctor(sym, args) => doc"${sym.nme}${args.map(_.showAsParams).mkDocument()}"
    case Sel(nme, res) => doc"{${nme.name}: ${res.show}}"
    case Typ(typ) => doc"type ${typ.show}"
  
  def showAsParams(using Scope, Raise): Document = this match
    case tup: Tup => "(" :: showTupElems(tup) :: doc")"
    case _ => doc"(...$show)"
  
  private def showTupElems(tup: Tup)(using Scope, Raise): Document = (
      tup.init.iterator.map(_.show) ++ tup.rest.iterator.flatMap:
        case (spd, c, post) =>
          (spd.str :: c.show) :: post.map(_.show)
    ).toSeq.mkDocument(", ")
  
  
  def showDbg(using DebugPrinter): Str = this match
    case Flow(sym) => sym.showDbg
    case Fun(lhs, rhs) => s"(${lhs.showDbgAsParams} -> ${rhs.showDbg})"
    case Ctor(sym, Nil) => sym.nme
    case tup: Tup => "[" + showDbgTupElems(tup) + "]"
    case Ctor(sym, args) => s"${sym.nme}(${args.map(_.showDbg).mkString(", ")})"
    case Sel(id, res) => s"{${id.name}: ${res.showDbg}}"
    case Typ(typ) => s"type ${typ.showDbg}"
  
  private def showDbgTupElems(tup: Tup)(using DebugPrinter): Str = (
      tup.init.iterator.map(_.showDbg) ++ tup.rest.iterator.flatMap:
        case (spd, c, post) =>
          s"${spd.str}${c.showDbg}" :: post.map(_.showDbg)
    ).mkString(", ")
  
  def showDbgAsParams(using DebugPrinter): Str = this match
    case tup: Tup => "(" + showDbgTupElems(tup) + ")"
    case _ => s"(...$showDbg)"
  
  
end Consumer


trait CtorImpl:
  self: Producer.Ctor =>
    
end CtorImpl


