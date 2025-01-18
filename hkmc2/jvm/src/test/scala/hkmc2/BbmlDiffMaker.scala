package hkmc2

import mlscript.utils.*, shorthands.*

import hkmc2.semantics.*
import hkmc2.bbml.*
import utils.Scope


abstract class BbmlDiffMaker extends JSBackendDiffMaker:
  
  val bbPreludeFile = file / os.up / os.RelPath("bbPrelude.mls")
  
  val bbmlOpt = new NullaryCommand("bbml"):
    override def onSet(): Unit =
      super.onSet()
      noSanityCheck.isGlobal = true
      noSanityCheck.set
      if file =/= bbPreludeFile then
        curCtx = Elaborator.State.init
        importFile(bbPreludeFile, verbose = false)
  
  
  override def init(): Unit =
    super.init()

  lazy val bbCtx =
    given Elaborator.Ctx = curCtx
    bbml.BbCtx.init(_ => die)
  
  var bbmlTyper: Opt[BBTyper] = None
  
  
  override def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Raise): Unit =
    super.processTerm(trm, inImport)
    if bbmlOpt.isSet then
      given Scope = Scope.empty
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
  

