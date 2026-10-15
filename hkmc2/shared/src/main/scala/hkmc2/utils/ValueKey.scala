package hkmc2
package utils

/** Explicit equality for immutable construction data. Subclasses name their
  * fields directly: no tuple or Product is allocated merely to hash or compare
  * them. Each hash starts from the class's tag (ValueKey.tag), so that variants
  * with equal fields hash differently. Final equals/hashCode preserve this
  * policy even for case subclasses, which can use generated extractors without
  * generated structural equality.
  * Mutable inference nodes must use IdentityEquality instead. A plain subclass
  * has no generated toString: define one in case-class form, so that debug
  * traces printing it stay readable and do not depend on identity hashes.
  */
abstract class ValueKey:
  protected val valueHash: Int
  final override def hashCode: Int = valueHash
  protected def sameValue(other: ValueKey): Boolean
  final override def equals(other: Any): Boolean = other match
    case that: ValueKey => (this eq that) || (hashCode == that.hashCode && sameValue(that))
    case _ => false

object ValueKey:
  /** The hash of a value's class name. Unlike `getClass.hashCode`, an identity
    * hash, it is the same in every run, and it cannot fall out of sync with the
    * class as a hand-written tag can. It is computed once per value, as part of
    * `valueHash`; on the JVM, the class's name and its hash are also cached.
    * Only final classes and objects may tag themselves with `tag(this)`: a
    * subclass would get another tag while possibly comparing equal.
    */
  def tag(value: AnyRef): Int = value.getClass.getName.hashCode

  /** Compose field hashes without a tuple, iterator, or varargs array. */
  inline def mix(hash: Int, field: Int): Int = scala.util.hashing.MurmurHash3.mix(hash, field)

  inline def hash(a: Int, b: Int): Int = mix(a, b)
  inline def hash(a: Int, b: Int, c: Int): Int = mix(hash(a, b), c)
  inline def hash(a: Int, b: Int, c: Int, d: Int): Int = mix(hash(a, b, c), d)
  inline def hash(a: Int, b: Int, c: Int, d: Int, e: Int): Int = mix(hash(a, b, c, d), e)
  inline def hash(a: Int, b: Int, c: Int, d: Int, e: Int, f: Int): Int = mix(hash(a, b, c, d, e), f)
  inline def hash(a: Int, b: Int, c: Int, d: Int, e: Int, f: Int, g: Int): Int = mix(hash(a, b, c, d, e, f), g)
  inline def hash(a: Int, b: Int, c: Int, d: Int, e: Int, f: Int, g: Int, h: Int): Int = mix(hash(a, b, c, d, e, f, g), h)

  /** Hash a flat immutable map without allocating entry tuples or traversing
    * the data behind its references. Addition makes insertion order irrelevant.
    */
  inline def mapHash[K, V](values: Map[K, V])(inline keyHash: K => Int, inline valueHash: V => Int): Int =
    var sum = 0
    values.foreachEntry: (key, value) =>
      sum += mix(keyHash(key), valueHash(value))
    hash(values.size, sum)

/** Occurrences remain distinct even when their immutable fields agree.
  * Final methods also prevent case subclasses from deriving structural equality.
  * As for ValueKey, give a plain subclass a toString in case-class form.
  */
trait IdentityEquality:
  final override def equals(other: Any): Boolean = other match
    case that: AnyRef => this eq that
    case _ => false
  final override def hashCode: Int = System.identityHashCode(this)
