package mlscript.ucs.context

import collection.mutable.{Map => MutMap}
import mlscript.utils._, shorthands._

/**
  * A trait for "things" (e.g., variables, functions, symbols, etc) that can be
  * matched in a UCS term. This trait holds everything that is needed to track
  * scrutinee information.
  */
trait Matchable {
  /**
    * A map from the context to the scrutinee associated with the symbol in the
    * context. The reason why we need this map is that the same symbol may be
    * matched in different UCS terms. Each context corresponds to a UCS term. 
    */
  private val scrutinees: MutMap[Context, Scrutinee] = MutMap.empty
    
  /**
    * Get the scrutinee associated with the symbol in the given context. If
    * there's no scrutinee associated with the symbol, create a new one in the
    * given context. **Note**: This function should only be called from the
    * UCS desugarer.
    */
  private[ucs] def getOrCreateScrutinee(implicit context: Context): Scrutinee =
    scrutinees.getOrElseUpdate(context, context.freshScrutinee)

  /** Get the scrutinee associated with the symbol in the given context. */
  def getScrutinee(implicit context: Context): Opt[Scrutinee] = scrutinees.get(context)

  /** Check if the symbol is associated with a scrutinee in the given context. */
  def isScrutinee(implicit context: Context): Bool = scrutinees.contains(context)

  /** Associate the symbol with a scrutinee in the given context. */
  private[ucs] def addScrutinee(scrutinee: Scrutinee)(implicit context: Context): Unit = {
    require(!isScrutinee) // It should be impossible to add a scrutinee twice.
    scrutinees += context -> scrutinee
  }

  /** Associate the symbol with a scrutinee in the given context and returns the current object. */
  private[ucs] def withScrutinee(scrutinee: Scrutinee)(implicit context: Context): this.type = {
    addScrutinee(scrutinee)
    this
  }
}
