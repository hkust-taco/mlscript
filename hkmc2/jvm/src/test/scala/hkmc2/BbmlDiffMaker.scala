package hkmc2

import mlscript.utils.*, shorthands.*

import hkmc2.bbml.*


abstract class BbmlDiffMaker extends MLsDiffMaker:
  
  val bbmlOpt = new NullaryCommand("bbml"):
    override def onSet(): Unit =
      super.onSet()
      importFile("bbPredef.mls", verbose = false)
  
  
  lazy val bbCtx = bbml.Ctx.init(_ => die, curCtx.members)
  
  
  var bbmlTyper: Opt[BBTyper] = None
  
  
  override def processTerm(trm: semantics.Term)(using Raise): Unit =
  if bbmlOpt.isUnset then super.processTerm(trm)
  else
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
  

