package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*

/** We need a unique representation of the scrutinee that is independent of
 *  names and symbol IDs in splits that are being expanded.
 */
enum ScrutineeStub:
  /** This represents the first subject to be matched in current expanded split.
   *  For example, `x` in `x is Letter` and `x is Digit`, but not the `y` in
   *  `x is Cons(y, _) and y is Letter`.
   */
  case Root
  /** The scrutinee was obtained from a product-like destructible patterns
   *  (including classes, patterns, and tuples). The `index` is the index of the
   *  extracted subject.
   */
  case Project(target: ScrutineeStub, index: Int)
  
  def showDbg: Str = this match
    case Root => "@"
    case Project(target, index) => s"$target.$index"
