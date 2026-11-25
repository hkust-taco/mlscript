package hkmc2

import hkmc2.utils.*, shorthands.*

import hkmc2.semantics.*
import hkmc2.typing.*
import utils.Scope


abstract class LogicSubDiffMaker extends WasmDiffMaker:

  lazy val infctx =
    given Elaborator.Ctx = curCtx
    given Config = mkConfig
    logicsub.InfCtx.init

  var typer: Opt[logicsub.Typer] = None

  override def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    super.processTerm(trm, inImport)
    Config.extractConfigFromStats(trm).givenIn:
      if summon[Config].language.typeCheck.isDefined then
        given Scope = Scope.empty(Scope.Cfg.default)
        if typer.isEmpty then
          given Elaborator.Ctx = curCtx
          given codegen.Erasure = codegen.Erasure(trm)
          typer = S(logicsub.Typer())
        given logicsub.InfCtx = infctx
        val ty = typer.get.typePurely(trm)
        val printer = logicsub.PrettyPrinter(output(_))
        printer.print(ty)

