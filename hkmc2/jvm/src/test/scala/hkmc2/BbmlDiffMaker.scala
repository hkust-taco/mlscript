package hkmc2

import mlscript.utils.*, shorthands.*

import hkmc2.bbml.*


abstract class BbmlDiffMaker extends JSBackendDiffMaker:
  
  val bbmlOpt = new NullaryCommand("bbml"):
    override def onSet(): Unit =
      super.onSet()
      if isGlobal then typeCheck.disable.isGlobal = true
      typeCheck.disable.setCurrentValue(())
      importFile("bbPredef.mls", verbose = false)
  
  
  lazy val bbCtx = bbml.Ctx.init(_ => die, curCtx.members)
  
  
  var bbmlTyper: Opt[BBTyper] = None
  
  
  override def processTerm(trm: semantics.Term, inImport: Bool)(using Raise): Unit =
    super.processTerm(trm, inImport)
    if bbmlOpt.isSet && !inImport then
      if bbmlTyper.isEmpty then
        bbmlTyper = S(BBTyper())
      given hkmc2.bbml.Ctx = bbCtx.copy(raise = summon)
      val typer = bbmlTyper.get
      val ty = typer.typePurely(trm)
      val printer = PrettyPrinter((msg: String) => output(msg))
      if debug.isSet then printer.print(ty)
      val simplif = TypeSimplifier(tl)
      val sty = simplif(true, 0)(ty)
      printer.print(sty)
  

