package mlscript.ucs

import collection.mutable.{Buffer, Map => MutMap, SortedMap => MutSortedMap, SortedSet => MutSortedSet}
import mlscript.{Loc, Located, NuFunDef, NuTypeDef, TypeName, Var}
import mlscript.{Cls, Trt, Mxn, Als, Mod}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.utils._, shorthands._
import mlscript.ucs.context.CaseSet

class ClassPatternInfo(scrutinee: ScrutineeData) {
  private val locationsBuffer: Buffer[Loc] = Buffer.empty
  private var unappliedVarOpt: Opt[Var] = N
  private val parameters: MutSortedMap[Int, ScrutineeData] = MutSortedMap.empty

  /**
    * Get or create a sub-scrutinee for the given parameter index.
    *
    * @param index the index of the parameter.
    * @return a `ScrutineeData` for the parameter whose parent scrutinee is the
    *         current scrutinee
    */
  def getParameter(index: Int): ScrutineeData = {
    require(index >= 0)
    parameters.getOrElseUpdate(index, scrutinee.freshSubScrutinee)
  }

  def addLocation(located: Located): Unit = located.getLoc.foreach(locationsBuffer += _)

  def addLocation(location: Opt[Loc]): Unit = locationsBuffer ++= location

  def getUnappliedVar(default: => Var): Var =
    unappliedVarOpt.getOrElse {
      val unappliedVar = default
      unappliedVarOpt = S(unappliedVar)
      unappliedVar
    }

  def arity: Opt[Int] = parameters.keysIterator.maxOption.map(_ + 1)

  def firstOccurrence: Option[Loc] = locationsBuffer.headOption

  def locations: Ls[Loc] = locationsBuffer.toList
}

class TuplePatternInfo(scrutinee: ScrutineeData) {
  private val locationsBuffer: Buffer[Loc] = Buffer.empty
  private val fields: MutSortedMap[Int, ScrutineeData] = MutSortedMap.empty

  def getField(index: Int): ScrutineeData =
    fields.getOrElseUpdate(index, scrutinee.freshSubScrutinee)

  def arity: Opt[Int] = fields.keysIterator.maxOption.map(_ + 1)

  def locations: Ls[Loc] = locationsBuffer.toList
}

class ScrutineeData(val context: Context, parent: Opt[ScrutineeData]) {
  private val locations: Buffer[Loc] = Buffer.empty
  private var generatedVarOpt: Opt[Var] = N
  private val classLikePatterns: MutMap[TypeSymbol, ClassPatternInfo] = MutMap.empty
  // Currently we only support simple tuple patterns, so there is only _one_
  // slot for tuple patterns. After we support complex tuple patterns, we need
  // to extend this fields to a map from tuple arity to `TuplePatternInfo`.
  //    private val tuplePatterns: MutMap[Int, TuplePatternInfo] = MutMap.empty
  // If we support tuple pattern splice, we need a more expressive key in the
  // map's type.
  private var tuplePatternOpt: Opt[TuplePatternInfo] = N
  private var alisesSet: MutSortedSet[Var] = MutSortedSet.empty

  def +=(alias: Var): Unit = alisesSet += alias

  def withAlias(alias: Var): ScrutineeData = { this += alias; this }

  def aliasesIterator: Iterator[Var] = alisesSet.iterator

  /**
    * If there is already a `ClassPatternInfo` for the given symbol, return it.
    * Otherwise, create a new `ClassPatternInfo` and return it.
    */
  def getOrCreateClassPattern(classLikeSymbol: TypeSymbol): ClassPatternInfo =
    classLikePatterns.getOrElseUpdate(classLikeSymbol, new ClassPatternInfo(this))

  /**
    * Get the class pattern but DO NOT create a new one if there isn't. This
    * function is mainly used in post-processing because we don't want to
    * accidentally create new patterns.
    */
  def getClassPattern(classLikeSymbol: TypeSymbol): Opt[ClassPatternInfo] =
    classLikePatterns.get(classLikeSymbol)

  /**
   * If there is already a `TuplePatternInfo`, return it. Otherwise, create a
   * new `TuplePatternInfo` and return it.
   * 
   * **NOTE**: There's only one slot for tuple patterns because we cannot
   * differentiate tuple types in underlying MLscript case terms. In the future,
   * we will support complex tuple patterns, so we need to extend this method to
   * a signature like this.
   * 
   * ```scala
   * def getOrCreateTuplePattern(dimension: TupleDimension): TuplePatternInfo
   * case class TupleDimension(knownArity: Int, hasSplice: Bool)
   * ```
   */
  def getOrCreateTuplePattern: TuplePatternInfo =
    tuplePatternOpt.getOrElse {
      val tuplePattern = new TuplePatternInfo(this)
      tuplePatternOpt = S(tuplePattern)
      tuplePattern
    }

  def classLikePatternsIterator: Iterator[TypeSymbol -> ClassPatternInfo] = classLikePatterns.iterator

  /** Get the name representation of patterns. Only for debugging. */
  def patterns: Iterator[Str] = {
    val classLikePatternsStr = classLikePatterns.iterator.map { case (symbol, pattern) =>
      s"${symbol.name}(${pattern.arity.fold("?")(_.toString)})"
    }
    val tuplePatternStr = tuplePatternOpt.iterator.map { tuplePattern =>
      s"tuple(${tuplePattern.arity.fold("?")(_.toString)})"
    }
    classLikePatternsStr ++ tuplePatternStr
  }

  def freshSubScrutinee: ScrutineeData = context.freshScrutinee(this)

  def toCaseSet: CaseSet = {
    import mlscript.ucs.context.Pattern
    val cases = classLikePatterns.iterator.map { case (symbol, pattern) =>
      Pattern.ClassLike(symbol) -> pattern.locations
    }.toMap[Pattern, Ls[Loc]]
    val tuplePattern = tuplePatternOpt.map { tuplePattern =>
      Pattern.Tuple() -> tuplePattern.locations
    }.toMap[Pattern, Ls[Loc]]
    CaseSet(cases ++ tuplePattern, false)
  }
}

object ScrutineeData {
  // We might need to move these method to a private `VarOps` because they may
  // emit diagnostics.

  import mlscript.Term
  import mlscript.pretyper.symbol.TermSymbol

  def unapply(term: Term)(implicit context: Context): Opt[ScrutineeData] = term match {
    case v: Var => v.symbol match {
      case symbol: TermSymbol => symbol.getScrutinee
      case _ => N
    }
    case _ => N
  }

  object WithVar {
    def unapply(term: Term)(implicit context: Context): Opt[(ScrutineeData, Var)] = term match {
      case v @ Var(_) => v.symbol match {
        case symbol: TermSymbol => symbol.getScrutinee.map(_ -> v)
        case _ => N
      }
      case _ => N
    }
  }
}