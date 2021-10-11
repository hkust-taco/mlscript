package mlscript

import mlscript.utils._, shorthands._

object JSBackend {
  
  def apply(pgrm: Pgrm): Str = {
    
    val res = new collection.mutable.StringBuilder
    
    pgrm.typeDefs.foreach { case TypeDef(k, n, tps, b) =>
      // ...
    }
    // ...
    
    res.toString
  }
  
}
