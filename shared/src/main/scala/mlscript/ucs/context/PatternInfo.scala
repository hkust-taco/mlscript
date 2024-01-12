package mlscript.ucs.context

import collection.mutable.{Buffer, SortedMap => MutSortedMap}
import mlscript.{Lit, Loc, Located, SimpleTerm, TypeName, Var}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.utils._, shorthands._

abstract class PatternInfo {
  private val locationsBuffer: Buffer[Loc] = Buffer.empty

  def addLocation(located: Located): Unit = located.getLoc.foreach(locationsBuffer += _)

  def addLocation(location: Opt[Loc]): Unit = locationsBuffer ++= location

  /** Get the location of this pattern's first occurrence. */
  def firstOccurrence: Option[Loc] = locationsBuffer.headOption

  def locations: Ls[Loc] = locationsBuffer.toList

  def arity: Opt[Int]

  def showDbg: Str

  /**
    * Checks if the pattern is same as expressed by the given `SimpleTerm`. Note
    * that we should pass `pat` of `Case` to this function.
    */
  def matches(pat: SimpleTerm): Bool

  /** Create a `SimpleTerm` which can be used as `pat` of `Case`. */
  def toCasePattern: SimpleTerm
}

object PatternInfo {
  class ClassLike(val classLikeSymbol: TypeSymbol, scrutinee: ScrutineeData) extends PatternInfo {
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

    def getUnappliedVar(default: => Var): Var =
      unappliedVarOpt.getOrElse {
        val unappliedVar = default
        unappliedVarOpt = S(unappliedVar)
        unappliedVar
      }

    override def arity: Opt[Int] = parameters.keysIterator.maxOption.map(_ + 1)

    override def showDbg: Str = s"${classLikeSymbol.name}"

    override def matches(pat: SimpleTerm): Bool =
      pat match {
        case pat: Var => pat.symbolOption.exists(_ === classLikeSymbol)
        case _: Lit => false
      }

    override def toCasePattern: SimpleTerm =
      Var(classLikeSymbol.name).withLoc(firstOccurrence).withSymbol(classLikeSymbol)
  }

  class Tuple(scrutinee: ScrutineeData) extends PatternInfo {
    private val fields: MutSortedMap[Int, ScrutineeData] = MutSortedMap.empty

    def getField(index: Int): ScrutineeData =
      fields.getOrElseUpdate(index, scrutinee.freshSubScrutinee)

    override def arity: Opt[Int] = fields.keysIterator.maxOption.map(_ + 1)

    override def showDbg: Str = s"tuple#${arity.getOrElse("?")}"

    override def matches(pat: SimpleTerm): Bool = false

    /**
      * Note that currently we only support simple tuple patterns. They should
      * disappear after desugaring stage, therefore, it will be an error if you
      * find an instance of this class.
      */
    override def toCasePattern: SimpleTerm = ???
  }

  class Literal(val literal: Lit) extends PatternInfo {
    override def arity: Opt[Int] = N

    override def showDbg: Str = literal.idStr

    override def matches(pat: SimpleTerm): Bool =
      pat match {
        case _: Var => false
        case pat => pat === literal
      }

    override def toCasePattern: SimpleTerm = literal.withLoc(firstOccurrence)
  }

  /**
    * This can be actually merged with `LiteralPatternInfo`. However, there's no
    * `Lit` sub-classes for Boolean types, so the representation is a little bit
    * awkward, also, it makes sense to consider Boolean patterns separately
    * because we can check the Boolean exhaustiveness with them.
    */
  class Boolean(val value: Var) extends PatternInfo {
    require(value.name === "true" || value.name === "false")

    override def arity: Opt[Int] = N

    override def showDbg: Str = value.toString

    override def matches(pat: SimpleTerm): Bool =
      pat match {
        case Var(name) => value.name === name
        case _ => false
      }

    override def toCasePattern: SimpleTerm = value.withLoc(firstOccurrence)
  }
}
