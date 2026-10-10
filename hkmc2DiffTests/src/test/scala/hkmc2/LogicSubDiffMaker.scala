package hkmc2

import hkmc2.utils.*, shorthands.*

import hkmc2.semantics.*
import hkmc2.typing.*
import utils.Scope
import hkmc2.syntax.Keyword.undefined


abstract class LogicSubDiffMaker extends WasmDiffMaker:

  lazy val infctx =
    given Elaborator.Ctx = curCtx
    logicsub.InfCtx.init

  var typer: Opt[logicsub.Typer] = None

  override def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    super.processTerm(trm, inImport)
    if summon[Config].language.typeCheck.isDefined then
      given Scope = Scope.empty(Scope.Cfg.default)
      if typer.isEmpty then
        given Elaborator.Ctx = curCtx
        typer = S(logicsub.Typer())
      given logicsub.InfCtx = infctx
      val ty = typer.get.typePurely(trm)
      output(s"Type: ${ty.show}")
      ty match
        case x: logicsub.InfVar =>
          output(s"  >: ${infctx.lbs(x.sym).foldLeft(logicsub.Bot:logicsub.Type)(_|_).toBasic.show}")
        case _ =>

