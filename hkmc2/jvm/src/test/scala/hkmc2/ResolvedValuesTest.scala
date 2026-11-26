package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.utils.*

/** Checks the ownership and lifetime of resolution observations. Imports and later worksheet blocks
  * must preserve completed snapshots without keeping a copy of the observations, and temporary field
  * discovery must release its graph references. */
class ResolvedValuesTest extends AnyFunSuite:
  test("completed observations are isolated from worksheet and import consumers"):
    given owner: Elaborator.State = new Elaborator.State
    given defining: ResolutionContext = owner.newResolverState.context
    val inputs = owner.newResolverState.resolvedValues
    val symbol = VarSymbol(new syntax.Tree.Ident("value"), mut = true)
    val source = new TermShapeHost
    inputs.register(symbol)(source.subscribeToShapes)((shape, record) => record(shape))
    val initial = DynShape()
    source.publish(initial)
    defining.completeBlock(Term.UnitVal())
    def observations = inputs.observations(symbol).toList
    val snapshot = observations
    val first = new Elaborator.State().newResolverState.context
    val second = new Elaborator.State().newResolverState.context
    val later = UnknownValueShape.at(Term.UnitVal())
    val other = UnknownValueShape.at(Term.Lit(syntax.Tree.IntLit(1)))
    source.publish(later)(using first)
    source.publish(other)(using second)
    source.publish(other)(using defining)
    assert(source.currentShapes(using first).toSet == Set(initial, later))
    assert(source.currentShapes(using second).toSet == Set(initial, other))
    assert(source.currentShapes(using defining).toSet == Set(initial, other))
    assert(snapshot == List(initial))
    assert(observations == snapshot)
    // Each consumer copies the source that it published to, and no host of the observations.
    assert(first.copiedHostCount == 1)
    assert(second.copiedHostCount == 1)
    assert(defining.copiedHostCount == 1)

  // Diff tests can check the fields of each block, but cannot detect temporary observers accumulating
  // in the sealed graph. Reuse the syntax so no new source hosts contribute to its size.
  test("completing field discovery does not grow the sealed graph"):
    import io.PlatformPath.given
    given owner: Elaborator.State = new Elaborator.State
    val graph = owner.newResolverState
    given ResolutionContext = graph.context
    given Raise = diagnostic => fail(diagnostic.theMsg)
    given DebugPrinter = new DebugPrinter
    val directory = TestFolders.mainTestDir(os.pwd)
    given Config = Config.default(directory)
    given CompilerCtx = CompilerCtx.fresh(io.FileSystem.default, TestFolders.compilerPaths(os.pwd), summon[Config])
    val resolver = Elaborator(TraceLogger.silent, directory, Elaborator.Ctx.empty)
    val block = new Term.Blk(Nil, Term.UnitVal())
    def complete(): Unit =
      graph.resolvedValues.observeBlock(block, resolver)(())
      graph.context.completeBlock(block)
    complete()
    val size = graph.completedNodes.size
    (1 to 10).foreach(_ => complete())
    assert(graph.completedNodes.size == size)
