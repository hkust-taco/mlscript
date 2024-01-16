package mlscript.ucs.context

import collection.mutable.{Buffer, SortedMap => MutSortedMap, SortedSet => MutSortedSet}
import mlscript.{Lit, Loc, Var}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.utils._, shorthands._
import mlscript.ucs.context.CaseSet
import mlscript.DecLit
import mlscript.IntLit
import mlscript.StrLit
import mlscript.UnitLit

class Scrutinee(val context: Context, parent: Opt[Scrutinee]) {
  import Scrutinee._

  private val locations: Buffer[Loc] = Buffer.empty
  private var generatedVarOpt: Opt[Var] = N
  private val classLikePatterns: MutSortedMap[TypeSymbol, PatternInfo.ClassLike] = MutSortedMap.empty(classLikeSymbolOrdering)
  // Currently we only support simple tuple patterns, so there is only _one_
  // slot for tuple patterns. After we support complex tuple patterns, we need
  // to extend this fields to a map from tuple arity to `PatternInfo.Tuple`.
  //    private val tuplePatterns: MutMap[Int, PatternInfo.Tuple] = MutMap.empty
  // If we support tuple pattern splice, we need a more expressive key in the
  // map's type.
  private var tuplePatternOpt: Opt[PatternInfo.Tuple] = N
  private var aliasVarSet: MutSortedSet[Var] = MutSortedSet.empty

  private val literalPatterns: MutSortedMap[Lit, PatternInfo.Literal] = MutSortedMap.empty(literalOrdering)
  /**
    * The key should be either `Var("true")` or `Var("false")`. We want to keep
    * the type symbol of the variable so that it still work in following stages.
    */
  private val booleanPatterns: MutSortedMap[Var, PatternInfo.Boolean] = MutSortedMap.empty(varNameOrdering)

  def addAliasVar(alias: Var): Unit = aliasVarSet += alias

  def withAliasVar(alias: Var): Scrutinee = { addAliasVar(alias); this }

  def aliasesIterator: Iterator[Var] = aliasVarSet.iterator

  /**
    * If there is already a `PatternInfo.ClassLike` for the given symbol, return it.
    * Otherwise, create a new `PatternInfo.ClassLike` and return it.
    */
  def getOrCreateClassPattern(classLikeSymbol: TypeSymbol): PatternInfo.ClassLike =
    classLikePatterns.getOrElseUpdate(classLikeSymbol, new PatternInfo.ClassLike(classLikeSymbol, this))

  /**
    * Get the class pattern but DO NOT create a new one if there isn't. This
    * function is mainly used in post-processing because we don't want to
    * accidentally create new patterns.
    */
  def getClassPattern(classLikeSymbol: TypeSymbol): Opt[PatternInfo.ClassLike] =
    classLikePatterns.get(classLikeSymbol)

  /**
   * If there is already a `PatternInfo.Tuple`, return it. Otherwise, create a
   * new `PatternInfo.Tuple` and return it.
   * 
   * **NOTE**: There's only one slot for tuple patterns because we cannot
   * differentiate tuple types in underlying MLscript case terms. In the future,
   * we will support complex tuple patterns, so we need to extend this method to
   * a signature like this.
   * 
   * ```scala
   * def getOrCreateTuplePattern(dimension: TupleDimension): PatternInfo.Tuple
   * case class TupleDimension(knownArity: Int, hasSplice: Bool)
   * ```
   */
  def getOrCreateTuplePattern: PatternInfo.Tuple =
    tuplePatternOpt.getOrElse {
      val tuplePattern = new PatternInfo.Tuple(this)
      tuplePatternOpt = S(tuplePattern)
      tuplePattern
    }

  /** Get the tuple pattern and create a new one if there isn't. */
  def getOrCreateLiteralPattern(literal: Lit): PatternInfo.Literal =
    literalPatterns.getOrElseUpdate(literal, new PatternInfo.Literal(literal))

  /**
    * The key should be either `Var("true")` or `Var("false")`. We want to keep
    * the type symbol of the variable so that it still work in following stages.
    */
  def getOrCreateBooleanPattern(value: Var): PatternInfo.Boolean =
    booleanPatterns.getOrElseUpdate(value, new PatternInfo.Boolean(value))

  def classLikePatternsIterator: Iterator[PatternInfo.ClassLike] = classLikePatterns.valuesIterator

  def patternsIterator: Iterator[PatternInfo] =
    classLikePatterns.valuesIterator ++ literalPatterns.valuesIterator ++ booleanPatterns.valuesIterator

  /** Get a list of string representation of patterns. Only for debugging. */
  private[ucs] def showPatternsDbg: Str = {
    val classLikePatternsStr = classLikePatterns.iterator.map { case (symbol, pattern) =>
      s"${symbol.name}(${pattern.arity.fold("?")(_.toString)})"
    }
    val tuplePatternStr = tuplePatternOpt.iterator.map { tuplePattern =>
      s"tuple(${tuplePattern.arity.fold("?")(_.toString)})"
    }
    (classLikePatternsStr ++ tuplePatternStr).mkString(", ")
  }

  def freshSubScrutinee: Scrutinee = context.freshScrutinee(this)

  def toCaseSet: CaseSet = {
    import mlscript.ucs.context.Pattern
    val cases = classLikePatterns.iterator.map { case (symbol, pattern) =>
      Pattern.ClassLike(symbol) -> pattern.locations
    }.toMap[Pattern, Ls[Loc]]
    val tuplePattern = tuplePatternOpt.map { tuplePattern =>
      Pattern.Tuple() -> tuplePattern.locations
    }.toMap[Pattern, Ls[Loc]]
    val literalPatterns = this.literalPatterns.iterator.map { case (literal, pattern) =>
      Pattern.Literal(literal) -> pattern.locations
    }.toMap[Pattern, Ls[Loc]]
    CaseSet(cases ++ tuplePattern)
  }
}

object Scrutinee {
  // We might need to move these method to a private `VarOps` because they may
  // emit diagnostics.

  import mlscript.Term
  import mlscript.pretyper.symbol.TermSymbol

  def unapply(term: Term)(implicit context: Context): Opt[Scrutinee] = term match {
    case v: Var => v.symbol match {
      case symbol: TermSymbol => symbol.getScrutinee
      case _ => N
    }
    case _ => N
  }

  object WithVar {
    def unapply(term: Term)(implicit context: Context): Opt[(Scrutinee, Var)] = term match {
      case v @ Var(_) => v.symbol match {
        case symbol: TermSymbol => symbol.getScrutinee.map(_ -> v)
        case _ => N
      }
      case _ => N
    }
  }

  private def literalInternalOrder(literal: Lit): Int = literal match {
    case UnitLit(true) => 0
    case UnitLit(false) => 1
    case _: DecLit => 2
    case _: IntLit => 3
    case _: StrLit => 4
  }

  private implicit val classLikeSymbolOrdering: Ordering[TypeSymbol] = new Ordering[TypeSymbol] {
    override def compare(x: TypeSymbol, y: TypeSymbol): Int = x.name.compareTo(y.name)
  }

  private implicit val literalOrdering: Ordering[Lit] = new Ordering[Lit] {
    override def compare(x: Lit, y: Lit): Int = (x, y) match {
      case (DecLit(x), DecLit(y)) => x.compare(y)
      case (IntLit(x), IntLit(y)) => x.compare(y)
      case (StrLit(x), StrLit(y)) => x.compare(y)
      case _ => literalInternalOrder(x).compare(literalInternalOrder(y))
    }
  }

  private implicit val varNameOrdering: Ordering[Var] = new Ordering[Var] {
    override def compare(x: Var, y: Var): Int = x.name.compareTo(y.name)
  }
}