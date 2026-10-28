package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.utils.*, shorthands.*
import syntax.Tree
import codegen.Erasure


/** Diff tests observe spans, but cannot tell whether cloning eagerly fills the
  * source tree's location caches. This checks that laziness independently of timing.
  */
class CloneLocationTest extends AnyFunSuite:
  test("cloning preserves cached spans without computing uncached subterm spans"):
    import io.PlatformPath.given
    given Elaborator.State = new Elaborator.State
    given Elaborator.Ctx = Elaborator.Ctx.empty
    given Config = Config.default(TestFolders.mainTestDir(os.pwd))
    given Raise = diagnostic => fail(diagnostic.theMsg)
    given Erasure = Erasure(Term.UnitVal())
    val origin = Origin(TestFolders.mainTestDir(os.pwd) / "CloneLocation.mls", 0, new FastParseHelpers("42"))
    val leaf = Term.Lit(new Tree.IntLit(42).withLoc(0, 2, origin))
    val cached = Term.Neg(leaf).withLoc(0, 2, origin)
    val uncached = Term.Neg(leaf)
    val root = Term.Try(cached, uncached)

    val copy = root.mkClone
    assert(root.getLoc.isEmpty && uncached.getLoc.isEmpty && leaf.getLoc.isEmpty)
    assert(copy.getLoc.isEmpty)
    copy match
      case Term.Try(first, second) =>
        assert(first.getLoc == cached.getLoc)
        assert(second.getLoc.isEmpty)
      case _ => fail("Expected a copied try expression")
    assert(copy.toLoc == cached.getLoc)
    assert(root.getLoc.isEmpty && uncached.getLoc.isEmpty && leaf.getLoc.isEmpty)
