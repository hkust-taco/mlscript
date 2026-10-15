package hkmc2

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.utils.ValueKey


/** Diff tests cannot observe repeated traversal of shared key components. */
class ValueKeyTest extends AnyFunSuite:
  import ValueKeyTest.Key
  test("hashing a shared immutable DAG visits each node once"):
    var hashes = 0
    val atom = new Object:
      override def hashCode: Int =
        hashes += 1
        0
    val leaf = new Key(Nil, Some(atom))
    val root = (1 to 30).foldLeft(leaf)((child, _) => new Key(List(child, child), None))
    val hash = root.hashCode
    assert(hashes == 1)
    (1 to 100).foreach(_ => assert(root.hashCode == hash))
    assert(hashes == 1)
    val equal = new Key(Nil, Some(atom))
    assert(leaf == equal && leaf.hashCode == equal.hashCode)
    assert(Set(leaf, equal, new Key(Nil, None)).size == 2)

object ValueKeyTest:
  final class Key(val children: List[Key], val leaf: Option[Object]) extends ValueKey:
    protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), children.hashCode, leaf.hashCode)
    protected def sameValue(other: ValueKey): Boolean = other match
      case that: Key => children == that.children && leaf == that.leaf
      case _ => false
