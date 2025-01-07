package hkmc2

import mlscript.utils.*, shorthands.*

import hkmc2.semantics.*
import hkmc2.bbml.*
import utils.Scope


abstract class BbmlDiffMaker extends JSBackendDiffMaker:
  
  val bbPreludeFile = file / os.up / os.RelPath("bbPrelude.mls")
  val bbPredefFile = file / os.up / os.up / os.up /"mlscript-compile"/"bbml"/"Predef.mls"
  
  val bbmlOpt = new NullaryCommand("bbml"):
    override def onSet(): Unit =
      super.onSet()
      if isGlobal then typeCheck.disable.isGlobal = true
      typeCheck.disable.setCurrentValue(())
      if file =/= bbPreludeFile then
        curCtx = Elaborator.State.init
        importFile(bbPreludeFile, verbose = false)
        curCtx = curCtx.nest(N)
  
  
  override def init(): Unit =
    if bbmlOpt.isSet then
      import syntax.*
      import Tree.*
      import Keyword.*
      given raise: Raise = d =>
        output(s"Error: $d")
        ()
      processTrees(
        Modified(`import`, N, StrLit(bbPredefFile.toString))
        :: Open(Ident("Predef"))
        :: Nil)
    super.init()

  lazy val bbCtx =
    given Elaborator.Ctx = curCtx
    bbml.BbCtx.init(_ => die)
  
  
  
  
  override def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Raise): Unit =
    super.processTerm(trm, inImport)
    if bbmlOpt.isSet then
      given Scope = Scope.empty
      val bbmlTyper = S(BBTyper())
      given hkmc2.bbml.BbCtx = bbCtx.copy(raise = summon)
      val typer = bbmlTyper.get
      val ty = typer.typePurely(trm)
      val printer = PrettyPrinter((msg: String) => output(msg))
      if debug.isSet then printer.print(ty)
      val simplif = TypeSimplifier(tl)
      val sty = simplif(true, 0)(ty)
      printer.print(sty)
  

