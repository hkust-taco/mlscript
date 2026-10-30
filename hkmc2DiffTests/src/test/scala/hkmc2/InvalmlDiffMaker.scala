package hkmc2

import hkmc2.utils.*, shorthands.*

import hkmc2.semantics.*
import hkmc2.invalml.*
import utils.Scope


abstract class InvalMLDiffMaker extends JSBackendDiffMaker:
  
  val invalPredefFile = io.Path(rootPath) / "hkmc2" / "shared" / "src" / "test" / "mlscript" / "invalml" / "InvalMLPredef.mls"
  
  val invalmlOpt = new NullaryCommand("invalml"):
    override def onSet(): Unit =
      super.onSet()
      noSanityCheck.isGlobal = true
      noSanityCheck.set
      if file =/= invalPredefFile then
        curCtx = prelude
        given Config = mkConfig
        importFile(invalPredefFile, verbose = false, includeDirectives = false)
        // The JS backend recognizes InvalML's typed operator declarations in the builtin scope.
        // Extend this worksheet's prelude without recreating or changing the shared host symbols.
        curCtx = prelude.copy(env = prelude.env ++ curCtx.env)
  
  
  override def init(): Unit =
    super.init()

  lazy val invalCtx =
    given Elaborator.Ctx = curCtx
    given Config = mkConfig
    invalml.InvalCtx.init(_ => die)
  
  var invalmlTyper: Opt[InvalTyper] = None
  
  
  override def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    super.processTerm(trm, inImport)
    if invalmlOpt.isSet then
      given Scope = Scope.empty(Scope.Cfg.default)
      given Elaborator.Ctx = curCtx
      // Typing may lower patterns even when executable code generation is disabled.
      given codegen.Erasure = codegen.Erasure(trm)
      if invalmlTyper.isEmpty then
        invalmlTyper = S(InvalTyper())
      given hkmc2.invalml.InvalCtx = invalCtx.copy(raise = summon)
      val typer = invalmlTyper.get
      val ty = typer.typePurely(trm)
      val printer = PrettyPrinter((msg: String) => output(msg))
      if debug.isSet then printer.print(ty)
      val simplif = TypeSimplifier(tl)
      val sty = simplif(true, 0)(ty)
      printer.print(sty)
  

