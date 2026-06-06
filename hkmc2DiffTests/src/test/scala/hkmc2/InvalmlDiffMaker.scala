package hkmc2

import hkmc2.utils.*, shorthands.*

import hkmc2.semantics.*
import hkmc2.invalml.*
import utils.Scope


abstract class InvalMLDiffMaker extends JSBackendDiffMaker:
  
  val invalPreludeFile = io.Path(rootPath) / "hkmc2" / "shared" / "src" / "test" / "mlscript" / "invalml" / "InvalMLPrelude.mls"
  
  val invalmlOpt = new NullaryCommand("invalml"):
    override def onSet(): Unit =
      super.onSet()
      noSanityCheck.isGlobal = true
      noSanityCheck.set
      if file =/= invalPreludeFile then
        curCtx = Elaborator.State.init
        given Config = mkConfig
        importFile(invalPreludeFile, verbose = false)
  
  
  override def init(): Unit =
    super.init()

  lazy val invalCtx =
    given Elaborator.Ctx = curCtx
    invalml.InvalCtx.init(_ => die)
  
  var invalmlTyper: Opt[InvalTyper] = None
  
  
  override def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    super.processTerm(trm, inImport)
    if invalmlOpt.isSet then
      given Scope = Scope.empty(Scope.Cfg.default)
      if invalmlTyper.isEmpty then
        given Elaborator.Ctx = curCtx
        invalmlTyper = S(InvalTyper())
      given hkmc2.invalml.InvalCtx = invalCtx.copy(raise = summon)
      val typer = invalmlTyper.get
      val ty = typer.typePurely(trm)
      val printer = PrettyPrinter((msg: String) => output(msg))
      if debug.isSet then printer.print(ty)
      val simplif = TypeSimplifier(tl)
      val sty = simplif(true, 0)(ty)
      printer.print(sty)
  

