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

  override def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    super.processTerm(trm, inImport)
    Config.extractConfigFromStats(trm).givenIn:
      if summon[Config].language.typeCheck.isDefined then
        given Scope = Scope.empty(Scope.Cfg.default)
        // Each block has its own diagnostic expectations. Only the inference
        // context carries definitions and bounds from earlier blocks.
        given Elaborator.Ctx = curCtx
        given codegen.Erasure = codegen.Erasure(trm, summon[Raise]) // FIXME: don't rerun erasure!
        given logicsub.InfCtx = infctx
        val ty = logicsub.Typer().typePurely(trm)
        val printer = logicsub.PrettyPrinter(output(_))
        if debug.isSet then printer.printRaw(ty)
        printer.print(ty)

