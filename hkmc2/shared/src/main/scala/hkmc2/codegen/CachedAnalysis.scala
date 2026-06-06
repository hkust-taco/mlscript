package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet}

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*


trait CachedAnalysis[A, R]:
  
  def analyzeUncached(a: A): R
  
  import java.util.IdentityHashMap
  
  val cache: IdentityHashMap[A, R] = new IdentityHashMap
  extension (a: A) def analyze: R =
    cache.get(a) match
      case null =>
        val res = analyzeUncached(a)
        cache.put(a, res)
        res
      case res => res

end CachedAnalysis


