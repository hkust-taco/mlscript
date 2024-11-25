package mlscript
package ucs.context

import collection.mutable.{Buffer, SortedMap => MutSortedMap}
import utils._, shorthands._
import pretyper.symbol.{ClassLikeSymbol, DummyClassSymbol, ModuleSymbol, TypeSymbol}

sealed abstract class Pattern {
  private val locationsBuffer: Buffer[Loc] = Buffer.empty

  def addLocation(located: Located): Unit = located.getLoc.foreach(locationsBuffer += _)

  def addLocation(location: Opt[Loc]): Unit = locationsBuffer ++= location

  /** Get the location of this pattern's first occurrence. */
  def firstOccurrence: Option[Loc] = locationsBuffer.headOption

  def locations: Ls[Loc] = locationsBuffer.toList

  def arity: Opt[Int]

  def showDbg: Str

  /** Get a string suitable for diagnostics. */
  def showInDiagnostics: Str

  /**
    * Checks if the pattern is same as expressed by the given `SimpleTerm`. Note
    * that we should pass `pat` of `Case` to this function.
    */
  def matches(pat: SimpleTerm): Bool

  /** Create a `SimpleTerm` which can be used as `pat` of `Case`. */
  def toCasePattern: SimpleTerm

  def refined: Bool
}

object Pattern {
  final case class ClassLike(
      val classLikeSymbol: ClassLikeSymbol,
      scrutinee: Scrutinee
  )(override val refined: Bool) extends Pattern {
    private var unappliedVarOpt: Opt[Var] = N
    private val parameters: MutSortedMap[Int, Scrutinee] = MutSortedMap.empty

    private[context] def findSubScrutinee(scrutinee: Scrutinee): Opt[Int] =
      parameters.find(_._2 === scrutinee).map(_._1)

    /**
      * Get or create a sub-scrutinee for the given parameter index.
      *
      * @param index the index of the parameter.
      * @return a `ScrutineeData` for the parameter whose parent scrutinee is the
      *         current scrutinee
      */
    def getParameter(index: Int): Scrutinee = {
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

    override def showDbg: Str =
      (if (refined) "refined " else "") + s"${classLikeSymbol.name}"

    override def showInDiagnostics: Str = s"${(classLikeSymbol match {
      case dummySymbol: DummyClassSymbol => "class"
      case s: ModuleSymbol if s.name === "true" || s.name === "false" => s"Boolean value"
      case otherSymbol: TypeSymbol => otherSymbol.defn.kind.str
    })} `${classLikeSymbol.name}`"

    /** Checks whether this pattern can cover the given pattern. */
    override def matches(pat: SimpleTerm): Bool =
      pat match {
        case pat: Var => pat.getClassLikeSymbol.fold(false)(_ <:< classLikeSymbol)
        case _: Lit => false
      }

    override def toCasePattern: SimpleTerm =
      Var(classLikeSymbol.name).withLoc(firstOccurrence).withSymbol(classLikeSymbol)
  }

  final case class Tuple(scrutinee: Scrutinee) extends Pattern {
    private val fields: MutSortedMap[Int, Scrutinee] = MutSortedMap.empty

    def getField(index: Int): Scrutinee =
      fields.getOrElseUpdate(index, scrutinee.freshSubScrutinee)

    override def arity: Opt[Int] = fields.keysIterator.maxOption.map(_ + 1)

    override def showDbg: Str = s"tuple#${arity.getOrElse("?")}"

    override def showInDiagnostics: Str =
      "tuple of " + (arity match {
        case N => "certain number of elements"
        case S(1) => "1 element"
        case S(n) => s"${n} elements"
      })

    override def matches(pat: SimpleTerm): Bool = false

    /**
      * Note that currently we only support simple tuple patterns. They should
      * disappear after desugaring stage, therefore, it will be an error if you
      * find an instance of this class.
      */
    override def toCasePattern: SimpleTerm = ???

    override def refined: Bool = ???
  }

  final case class Literal(val literal: Lit) extends Pattern {
    override def arity: Opt[Int] = N

    override def showDbg: Str = literal.idStr

    override def showInDiagnostics: Str = s"literal ${literal.idStr}"

    override def matches(pat: SimpleTerm): Bool =
      pat match {
        case _: Var => false
        case pat => pat === literal
      }

    override def toCasePattern: SimpleTerm = literal.withLoc(firstOccurrence)

    override def refined: Bool = false
  }
}
