package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.syntax.{Fun, Tree}
import hkmc2.utils.*, shorthands.*


/** Algebraic laws over paths and activation sites complement worksheet examples:
  * in particular, check all wildcard/identified combinations and regroupings.
  */
class MarksTest extends AnyFunSuite:
  private class Harness:
    given Elaborator.State = new Elaborator.State
    given DebugPrinter = new DebugPrinter
    given TraceLogger = new TraceLogger:
      override def doTrace: Boolean = false
    val value = DynShape()
    val outer = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("outer")))
    val left = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("left")))
    val right = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("right")))
    val scopes = List(Nil, List(outer), List(outer, left), List(outer, right))
    val sites = List(N, S(FlowSymbol.app()), S(FlowSymbol.app()))
    def entries(scopes: List[ResolutionBoundary], site: Opt[FlowSymbol]): Marks =
      scopes.foldLeft[Marks](NoMarks)((rest, boundary) => EntryMark(boundary, site, rest))
    def exits(scopes: List[ResolutionBoundary], site: Opt[FlowSymbol]): Marks =
      scopes.foldRight[ExitMarks](NoMarks)((boundary, rest) => ExitMark(boundary, site, rest))
    def path(from: List[ResolutionBoundary], to: List[ResolutionBoundary],
        exitSite: Opt[FlowSymbol], entrySite: Opt[FlowSymbol]): List[Marks] =
      List(exits(from, exitSite), entries(to, entrySite))
    def normalized(path: List[Marks]): List[Marks] = value.exit(path) match
      case Marked(_, NoMarks) => Nil
      case Marked(_, marks) => List(marks)
      case NoShape => fail("A path with no cancellable entry cannot reject its source")

  test("scope transport agrees with matching activation stacks"):
    val h = new Harness
    import h.given
    for from <- h.scopes; to <- h.scopes; origin <- h.sites; leaving <- h.sites; arriving <- h.sites do
      val input = h.value.exit(h.entries(from, origin))
      val path = h.path(from, to, leaving, arriving)
      // Exiting consumes the entire input stack. A capture matches either site;
      // otherwise different identified activations have disjoint value flow.
      val compatible = from.isEmpty || origin.isEmpty || leaving.isEmpty || origin == leaving
      val expected = if compatible then h.value.exit(h.entries(to, arriving)) else NoShape
      assert(input.exit(path) == expected)
      assert(input.exit(h.normalized(path)) == expected)

  test("normalizing fragments preserves composition and argument transport reverses their order"):
    val h = new Harness
    import h.given
    for from <- h.scopes; via <- h.scopes; to <- h.scopes; first <- h.sites; second <- h.sites do
      val p = h.path(from, via, first, first)
      val q = h.path(via, to, second, second)
      val parts = h.normalized(p) ::: h.normalized(q)
      val input = h.value.exit(h.entries(from, first))
      assert(input.exit(p ::: q) == input.exit(parts))
      assert(input.exit(parts) == input.exit(h.normalized(p)).exit(h.normalized(q)))
      val output = h.value.exit(h.entries(to, second))
      assert(output.enter(parts) == output.enter(h.normalized(q)).enter(h.normalized(p)))
      assert(output.enter(p ::: q) == output.enter(parts))

  test("regrouping three normalized paths preserves filtering"):
    val h = new Harness
    import h.given
    def compose(value: TermShape | NoShape, path: TermShape | NoShape): TermShape | NoShape = path match
      case NoShape => NoShape
      case Marked(_, marks) => value.exit(marks)
    for start <- h.scopes; middle <- h.scopes; finish <- h.scopes
        a <- h.sites; b <- h.sites; c <- h.sites do
      val p = h.value.exit(h.path(start, middle, a, b))
      val q = h.value.exit(h.path(middle, finish, c, a))
      val r = h.value.exit(h.path(finish, start, b, c))
      assert(compose(compose(p, q), r) == compose(p, compose(q, r)))

  test("wildcard exit followed by entry preserves provenance but loses the consumed site"):
    val h = new Harness
    import h.given
    val scope = List(h.outer)
    val source = h.value.exit(h.entries(scope, h.sites(1)))
    val transferred = source.exit(h.path(scope, scope, N, N))
    assert(transferred != source)
    assert(source.exit(h.exits(scope, h.sites(2))) == NoShape)
    assert(transferred.exit(h.exits(scope, h.sites(2))) == h.value)
    val uncancelled = h.value.exit(h.path(scope, scope, N, N))
    assert(uncancelled != h.value)
    assert(uncancelled.exit(h.exits(scope, h.sites(2))) == h.value.exit(h.exits(scope, N)))
