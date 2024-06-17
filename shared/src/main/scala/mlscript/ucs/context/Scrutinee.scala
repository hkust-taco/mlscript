package mlscript
package ucs.context

import collection.mutable.{Buffer, SortedMap => MutSortedMap, SortedSet => MutSortedSet}
import pretyper.symbol.{ClassLikeSymbol, TermSymbol, TypeSymbol}, utils._, shorthands._
import scala.annotation.tailrec

class Scrutinee(val context: Context, parent: Opt[Scrutinee]) {
  import Scrutinee._

  private val locations: Buffer[Loc] = Buffer.empty
  private var generatedVarOpt: Opt[Var] = N
  private val classLikePatterns: MutSortedMap[TypeSymbol, Pattern.ClassLike] = MutSortedMap.empty(classLikeSymbolOrdering)
  // Currently we only support simple tuple patterns, so there is only _one_
  // slot for tuple patterns. After we support complex tuple patterns, we need
  // to extend this fields to a map from tuple arity to `Pattern.Tuple`.
  //    private val tuplePatterns: MutMap[Int, Pattern.Tuple] = MutMap.empty
  // If we support tuple pattern splice, we need a more expressive key in the
  // map's type.
  private var tuplePatternOpt: Opt[Pattern.Tuple] = N
  private var aliasVarSet: MutSortedSet[Var] = MutSortedSet.empty

  private val literalPatterns: MutSortedMap[Lit, Pattern.Literal] = MutSortedMap.empty(literalOrdering)

  def addAliasVar(alias: Var): Unit = aliasVarSet += alias

  def withAliasVar(alias: Var): Scrutinee = { addAliasVar(alias); this }

  def aliasesIterator: Iterator[Var] = aliasVarSet.iterator

  /**
    * If there is already a `Pattern.ClassLike` for the given symbol, return it.
    * Otherwise, create a new `Pattern.ClassLike` and return it.
    */
  def getOrCreateClassPattern(classLikeSymbol: ClassLikeSymbol, refined: Bool): Pattern.ClassLike =
    classLikePatterns.getOrElseUpdate(classLikeSymbol, Pattern.ClassLike(classLikeSymbol, this)(refined))

  /**
    * Get the class pattern but DO NOT create a new one if there isn't. This
    * function is mainly used in post-processing because we don't want to
    * accidentally create new patterns.
    */
  def getClassPattern(classLikeSymbol: TypeSymbol): Opt[Pattern.ClassLike] =
    classLikePatterns.get(classLikeSymbol)

  /**
   * If there is already a `Pattern.Tuple`, return it. Otherwise, create a
   * new `Pattern.Tuple` and return it.
   * 
   * **NOTE**: There's only one slot for tuple patterns because we cannot
   * differentiate tuple types in underlying MLscript case terms. In the future,
   * we will support complex tuple patterns, so we need to extend this method to
   * a signature like this.
   * 
   * ```scala
   * def getOrCreateTuplePattern(dimension: TupleDimension): Pattern.Tuple
   * case class TupleDimension(knownArity: Int, hasSplice: Bool)
   * ```
   */
  def getOrCreateTuplePattern: Pattern.Tuple =
    tuplePatternOpt.getOrElse {
      val tuplePattern = Pattern.Tuple(this)
      tuplePatternOpt = S(tuplePattern)
      tuplePattern
    }

  /** Get the tuple pattern and create a new one if there isn't. */
  def getOrCreateLiteralPattern(literal: Lit): Pattern.Literal =
    literalPatterns.getOrElseUpdate(literal, Pattern.Literal(literal))

  def classLikePatternsIterator: Iterator[Pattern.ClassLike] = classLikePatterns.valuesIterator

  def patternsIterator: Iterator[Pattern] =
    classLikePatterns.valuesIterator ++ literalPatterns.valuesIterator

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

  def getReadableName(scrutineeVar: Var): Str = {
    parent match {
      case N if context.isGeneratedVar(scrutineeVar) => "term"
      case N => s"`${scrutineeVar.name}`"
      case S(parentScrutinee) =>
        parentScrutinee.classLikePatterns.iterator.flatMap { case (symbol, pattern) =>
          pattern.findSubScrutinee(this).map(_ -> symbol.name)
        }.nextOption() match {
          case S(index -> typeName) => s"the ${index.toOrdinalWord} argument of `${typeName}`"
          case N => s"`${scrutineeVar.name}`" // Still not the best.
        }
    }
  }

  @tailrec
  final def isSubScrutineeOf(scrutinee: Scrutinee): Bool = this === scrutinee || (parent match {
    case Some(parentScrutinee) => parentScrutinee.isSubScrutineeOf(scrutinee)
    case N => false
  })
}

object Scrutinee {
  // We might need to move these method to a private `VarOps` because they may
  // emit diagnostics.
  def unapply(term: Term)(implicit context: Context): Opt[Scrutinee] = term match {
    case v: Var => v.symbol match {
      case symbol: TermSymbol => symbol.getScrutinee
      case _ => N
    }
    case _ => N
  }

  type WithVar = Var -> Scrutinee

  object WithVar {
    def unapply(term: Term)(implicit context: Context): Opt[WithVar] = term match {
      case v @ Var(_) => v.symbol match {
        case symbol: TermSymbol => symbol.getScrutinee.map(v -> _)
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