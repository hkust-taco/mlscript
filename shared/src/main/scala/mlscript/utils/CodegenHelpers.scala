package mlscript

import mlscript.utils._, shorthands._

class ShadowNameResolver {
  private val nameShadowingCount = collection.mutable.HashMap[Str, Int]()

  def apply(name: Str): Str = {
    nameShadowingCount get name match {
      // It is a shadowed name.
      case Some(count) =>
        nameShadowingCount += name -> (count + 1)
        s"$name@$count"
      // This is the first time we meet this name.
      case None =>
        nameShadowingCount += name -> 1
        name
    }
  }
}
