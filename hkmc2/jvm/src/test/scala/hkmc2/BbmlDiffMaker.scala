package hkmc2

import mlscript.utils.*, shorthands.*

import hkmc2.semantics.*
import hkmc2.bbml.*


abstract class BbmlDiffMaker extends JSBackendDiffMaker:
  
  val bbPredefFile = file / os.up / os.RelPath("bbPredef.mls")
  
  val bbmlOpt = new NullaryCommand("bbml"):
    override def onSet(): Unit =
      super.onSet()
      if isGlobal then typeCheck.disable.isGlobal = true
      typeCheck.disable.setCurrentValue(())
      if file =/= bbPredefFile then
        importFile(bbPredefFile, verbose = false)
  
  
  lazy val bbCtx =
    given Elaborator.Ctx = curCtx
    bbml.BbCtx.init(_ => die)
  
  
  var bbmlTyper: Opt[BBTyper] = None
  
  
  override def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Raise): Unit =
    super.processTerm(trm, inImport)
    if bbmlOpt.isSet then
      if bbmlTyper.isEmpty then
        bbmlTyper = S(BBTyper())
      given hkmc2.bbml.BbCtx = bbCtx.copy(raise = summon)
      val typer = bbmlTyper.get
      val ty = typer.typePurely(trm)
      val printer = PrettyPrinter((msg: String) => output(msg))
      if debug.isSet then printer.print(ty)
      val simplif = TypeSimplifier(tl)
      val sty = simplif(true, 0)(ty)
      printer.print(sty)
  

